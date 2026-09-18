(*
  We time the OCaml code extracted from FlocqKernel.v, not the Rocq checker and
  not a hand-written replacement. Flocq is the external proved reference:
  https://flocq.gitlabpages.inria.fr/

  We construct the shared exact fixtures before timing and use the same
  result-dependent fixture chain as the other scalar lanes.
*)

module Zarith = Z

open Flocq_kernel

(* The extracted module also defines a type named [float]. Returning integer
   nanoseconds from the C clock keeps the timer independent of that generated
   name and avoids a conversion inside the measured interval. *)
external monotonic_nanos : unit -> int64 = "floatlib_monotonic_nanos"

(* Storage width, exponent-field width, and significand precision match the
   FloatLib and MPFR adapters. Flocq's certified IEEE interface requires
   precision < emax, excluding the 4-, 5-, and 7-bit custom layouts. *)
let formats =
  [|
    (6, 3, 3);
    (8, 4, 4);
    (16, 5, 11);
    (32, 8, 24);
    (64, 11, 53);
    (128, 15, 113);
    (256, 19, 237);
    (512, 19, 493);
    (1024, 19, 1005);
    (2048, 19, 2029);
    (4096, 19, 4077);
  |]
let operations = [| "add"; "sub"; "mul"; "div"; "sqrt"; "fma" |]

let z_of_int = Big_int_Z.big_int_of_int

let positive_env name default =
  match Sys.getenv_opt name with
  | None | Some "" -> default
  | Some text ->
      let value = int_of_string text in
      if value <= 0 then invalid_arg (name ^ " must be positive");
      value

let optional_width () =
  match Sys.getenv_opt "FORMAT_COMPARE_WIDTH" with
  | None | Some "" -> None
  | Some text ->
      let width = int_of_string text in
      if not (Array.exists (fun (candidate, _, _) -> candidate = width) formats)
      then invalid_arg ("unsupported FORMAT_COMPARE_WIDTH: " ^ text);
      Some width

let optional_operation () =
  match Sys.getenv_opt "FORMAT_COMPARE_OPERATION" with
  | None | Some "" -> None
  | Some operation ->
      if not (Array.exists (( = ) operation) operations)
      then invalid_arg ("unsupported FORMAT_COMPARE_OPERATION: " ^ operation);
      Some operation

let default_iterations width =
  if width <= 32 then 25_000
  else if width <= 64 then 10_000
  else if width <= 128 then 2_500
  else if width <= 256 then 500
  else if width <= 512 then 100
  else if width <= 1024 then 20
  else if width <= 2048 then 5
  else 1

let exact_input precision emax salt negative index =
  let numerator = ((index * salt + salt + 1) mod 113) + 7 in
  let denominator = ((index * 11 + salt) mod 29) + 32 in
  flocq_from_ratio
    (z_of_int precision)
    (z_of_int emax)
    negative
    (z_of_int numerator)
    (z_of_int denominator)

let inputs_x precision emax =
  Array.init 16 (fun index ->
      exact_input precision emax 37 (index mod 5 = 0) index)

let inputs_y precision emax =
  Array.init 16 (fun index ->
      exact_input precision emax 61 (index mod 3 = 0) index)

let inputs_sqrt precision emax =
  Array.init 16 (fun index -> exact_input precision emax 43 false index)

let mix_sink sink value =
  Int64.mul (Int64.logxor sink value) 1_099_511_628_211L

(* The unsigned FNV offset basis represented as an Int64 bit pattern. *)
let dependency_seed = Int64.of_string "-3750763034362895579"
let exponent_mix = Zarith.of_string "11400714819323198485"
let sign_mix = Zarith.of_string "9223372036854775808"
let zero_tag = Zarith.of_string "3257665815644502181"
let infinity_tag = Zarith.of_string "10067880064238660809"
let nan_tag = Zarith.of_string "5700357408180978091"
let two_to_64 = Zarith.shift_left Zarith.one 64

(* We use the preceding result to choose the next ordinary fixture. *)
let dependent_index sink =
  let folded =
    Int64.logxor sink (Int64.shift_right_logical sink 32)
  in
  let folded =
    Int64.logxor folded (Int64.shift_right_logical folded 16)
  in
  Int64.to_int (Int64.logand folded 15L)

let int64_of_uint64 value =
  let unsigned = Zarith.extract value 0 64 in
  let signed =
    if Zarith.testbit unsigned 63
    then Zarith.sub unsigned two_to_64
    else unsigned
  in
  Zarith.to_int64 signed

let special_fingerprint tag negative =
  int64_of_uint64 (if negative then Zarith.logxor tag sign_mix else tag)

let finite_fingerprint precision negative mantissa exponent =
  let used = Zarith.numbits mantissa in
  let normalized = Zarith.shift_left mantissa (precision - used) in
  if precision > 64 then
    int64_of_uint64 normalized
  else
    let normalized_exponent = Zarith.add exponent (Zarith.of_int used) in
    let mixed_exponent = Zarith.mul normalized_exponent exponent_mix in
    let fingerprint = Zarith.logxor normalized mixed_exponent in
    let fingerprint =
      if negative then Zarith.logxor fingerprint sign_mix else fingerprint
    in
    int64_of_uint64 fingerprint

(* Flocq stores finite values as mantissa × 2^exponent. We normalize that
   representation before hashing it, matching the token used by FloatLib,
   MPFR, native C, SoftFloat, and CPython. *)
let result_bits precision = function
  | B754_zero negative -> special_fingerprint zero_tag negative
  | B754_infinity negative -> special_fingerprint infinity_tag negative
  | B754_nan -> int64_of_uint64 nan_tag
  | B754_finite (negative, mantissa, exponent) ->
      finite_fingerprint precision negative mantissa exponent

let run_binary operation precision emax iterations xs ys =
  let operation = operation (z_of_int precision) (z_of_int emax) in
  let sink = ref dependency_seed in
  let fixture_trace = ref dependency_seed in
  for _iteration = iterations - 1 downto 0 do
    let index = dependent_index !sink in
    fixture_trace := mix_sink !fixture_trace (Int64.of_int index);
    sink := mix_sink !sink (result_bits precision (operation xs.(index) ys.(index)))
  done;
  (!sink, !fixture_trace)

let run_unary operation precision emax iterations xs =
  let operation = operation (z_of_int precision) (z_of_int emax) in
  let sink = ref dependency_seed in
  let fixture_trace = ref dependency_seed in
  for _iteration = iterations - 1 downto 0 do
    let index = dependent_index !sink in
    fixture_trace := mix_sink !fixture_trace (Int64.of_int index);
    sink := mix_sink !sink (result_bits precision (operation xs.(index)))
  done;
  (!sink, !fixture_trace)

let run_ternary operation precision emax iterations xs ys =
  let operation = operation (z_of_int precision) (z_of_int emax) in
  let sink = ref dependency_seed in
  let fixture_trace = ref dependency_seed in
  for _iteration = iterations - 1 downto 0 do
    let index = dependent_index !sink in
    let z = xs.(15 - index) in
    fixture_trace := mix_sink !fixture_trace (Int64.of_int index);
    sink :=
      mix_sink !sink
        (result_bits precision (operation xs.(index) ys.(index) z))
  done;
  (!sink, !fixture_trace)

let workload operation precision emax xs ys sqrt_xs =
  match operation with
  | "add" ->
      fun iterations -> run_binary flocq_add precision emax iterations xs ys
  | "sub" ->
      fun iterations -> run_binary flocq_sub precision emax iterations xs ys
  | "mul" ->
      fun iterations -> run_binary flocq_mul precision emax iterations xs ys
  | "div" ->
      fun iterations -> run_binary flocq_div precision emax iterations xs ys
  | "sqrt" ->
      fun iterations -> run_unary flocq_sqrt precision emax iterations sqrt_xs
  | "fma" ->
      fun iterations -> run_ternary flocq_fma precision emax iterations xs ys
  | _ -> invalid_arg ("unsupported operation: " ^ operation)

(* The fixed agreement prefix is deterministic. A campaign computes it once
   for each operation and format, then reuses it across calibration and timing
   trials. The runner supplies the SHA-256 of this compiled executable and a
   fresh cache directory; a different executable cannot reuse these records.
   This matters for the widest extracted square-root computations. *)
let agreement_prefix width precision emax operation iterations run =
  match
    Sys.getenv_opt "FORMAT_COMPARE_FLOCQ_CACHE",
    Sys.getenv_opt "FORMAT_COMPARE_FLOCQ_BINARY_SHA256"
  with
  | None, None -> run iterations
  | Some directory, Some binary_sha256 ->
      if String.length binary_sha256 <> 64 ||
         not (String.for_all
           (function '0' .. '9' | 'a' .. 'f' -> true | _ -> false)
           binary_sha256)
      then invalid_arg "invalid Flocq executable SHA-256";
      let key =
        Printf.sprintf "%s-%d-%d-%d-%s-%d"
          binary_sha256 width precision emax operation iterations
      in
      let path = Filename.concat directory (key ^ ".txt") in
      if Sys.file_exists path then begin
        let input = open_in path in
        Fun.protect ~finally:(fun () -> close_in input) (fun () ->
          if input_line input <> key then
            invalid_arg "Flocq agreement cache key mismatch";
          let sink = Int64.of_string (input_line input) in
          let trace = Int64.of_string (input_line input) in
          (try
             ignore (input_line input);
             invalid_arg "extra data in Flocq agreement cache"
           with End_of_file -> ());
          (sink, trace))
      end else begin
        let sink, trace = run iterations in
        let temporary =
          Filename.temp_file ~temp_dir:directory "agreement-" ".tmp"
        in
        let output = open_out temporary in
        Fun.protect
          ~finally:(fun () ->
            close_out_noerr output;
            if Sys.file_exists temporary then Sys.remove temporary)
          (fun () ->
            Printf.fprintf output "%s\n%Ld\n%Ld\n" key sink trace;
            close_out output;
            Sys.rename temporary path);
        (sink, trace)
      end
  | _ ->
      invalid_arg "Flocq agreement cache needs both directory and executable SHA-256"

let time_row width exponent_bits precision operation iterations
    warmup_iterations agreement_iterations =
  let emax = 1 lsl (exponent_bits - 1) in
  if precision <= 0 || precision >= emax then
    invalid_arg "Flocq requires 0 < precision < emax";
  let xs = inputs_x precision emax in
  let ys = inputs_y precision emax in
  let sqrt_xs = inputs_sqrt precision emax in
  let run = workload operation precision emax xs ys sqrt_xs in
  let agreement_sink, agreement_trace =
    agreement_prefix width precision emax operation agreement_iterations run
  in
  ignore (Sys.opaque_identity (run warmup_iterations));
  let start = monotonic_nanos () in
  let sink, fixture_trace = Sys.opaque_identity (run iterations) in
  let stop = monotonic_nanos () in
  let total_nanos = Int64.sub stop start in
  Printf.printf
    "Flocq,binary-reference,flocq-p%d,%d,%s,software-reference,\
     Flocq 4.2.2 extracted OCaml Zarith,result-dependent-fixture-chain,\
     %d,%Ld,%Ld,%Ld,%d,%Ld,%Ld\n%!"
    precision width operation iterations total_nanos sink fixture_trace
    agreement_iterations agreement_sink agreement_trace

let () =
  let selected_width = optional_width () in
  let selected_operation = optional_operation () in
  let warmup_iterations =
    positive_env "FORMAT_COMPARE_WARMUP_ITERATIONS" 64
  in
  let agreement_iterations =
    positive_env "FORMAT_COMPARE_AGREEMENT_ITERATIONS" 256
  in
  print_endline
    "implementation,family,format,totalBits,operation,executionClass,\
     backend,measurementMethod,iterations,totalNanos,sink,fixtureTraceDigest,\
     agreementIterations,agreementSink,agreementFixtureTraceDigest";
  Array.iter
    (fun (width, exponent_bits, precision) ->
      if Option.fold ~none:true ~some:(( = ) width) selected_width
      then
        let iterations =
          positive_env
            "FORMAT_COMPARE_ITERATIONS"
            (default_iterations width)
        in
        Array.iter
          (fun operation ->
            if
              Option.fold
                ~none:true
                ~some:(( = ) operation)
                selected_operation
            then
              time_row
                width exponent_bits precision operation iterations
                warmup_iterations agreement_iterations)
          operations)
    formats
