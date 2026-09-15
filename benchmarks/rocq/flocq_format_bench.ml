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

(* We match the significand precision of the binary format at each storage
   width. This does not make the Flocq row an implementation of every custom
   exponent range or exceptional-value policy. *)
let formats =
  [|
    (4, 2);
    (5, 3);
    (6, 3);
    (7, 4);
    (8, 4);
    (16, 11);
    (32, 24);
    (64, 53);
    (128, 113);
    (256, 237);
    (512, 493);
    (1024, 1005);
    (2048, 2029);
    (4096, 4077);
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
      if not (Array.exists (fun (candidate, _) -> candidate = width) formats)
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

let exact_input precision salt negative index =
  let numerator = ((index * salt + salt + 1) mod 113) + 7 in
  let denominator = ((index * 11 + salt) mod 29) + 32 in
  flocq_from_ratio
    (z_of_int precision)
    negative
    (z_of_int numerator)
    (z_of_int denominator)

let inputs_x precision =
  Array.init 16 (fun index ->
      exact_input precision 37 (index mod 5 = 0) index)

let inputs_y precision =
  Array.init 16 (fun index ->
      exact_input precision 61 (index mod 3 = 0) index)

let inputs_sqrt precision =
  Array.init 16 (fun index -> exact_input precision 43 false index)

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

let run_binary operation precision iterations xs ys =
  let operation = operation (z_of_int precision) in
  let sink = ref dependency_seed in
  let fixture_trace = ref dependency_seed in
  for _iteration = iterations - 1 downto 0 do
    let index = dependent_index !sink in
    fixture_trace := mix_sink !fixture_trace (Int64.of_int index);
    sink := mix_sink !sink (result_bits precision (operation xs.(index) ys.(index)))
  done;
  (!sink, !fixture_trace)

let run_unary operation precision iterations xs =
  let operation = operation (z_of_int precision) in
  let sink = ref dependency_seed in
  let fixture_trace = ref dependency_seed in
  for _iteration = iterations - 1 downto 0 do
    let index = dependent_index !sink in
    fixture_trace := mix_sink !fixture_trace (Int64.of_int index);
    sink := mix_sink !sink (result_bits precision (operation xs.(index)))
  done;
  (!sink, !fixture_trace)

let run_ternary operation precision iterations xs ys =
  let operation = operation (z_of_int precision) in
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

let workload operation precision xs ys sqrt_xs =
  match operation with
  | "add" ->
      fun iterations -> run_binary flocq_add precision iterations xs ys
  | "sub" ->
      fun iterations -> run_binary flocq_sub precision iterations xs ys
  | "mul" ->
      fun iterations -> run_binary flocq_mul precision iterations xs ys
  | "div" ->
      fun iterations -> run_binary flocq_div precision iterations xs ys
  | "sqrt" ->
      fun iterations -> run_unary flocq_sqrt precision iterations sqrt_xs
  | "fma" ->
      fun iterations -> run_ternary flocq_fma precision iterations xs ys
  | _ -> invalid_arg ("unsupported operation: " ^ operation)

let time_row width precision operation iterations warmup_iterations =
  let xs = inputs_x precision in
  let ys = inputs_y precision in
  let sqrt_xs = inputs_sqrt precision in
  let run = workload operation precision xs ys sqrt_xs in
  ignore (Sys.opaque_identity (run warmup_iterations));
  let start = monotonic_nanos () in
  let sink, fixture_trace = Sys.opaque_identity (run iterations) in
  let stop = monotonic_nanos () in
  let total_nanos = Int64.sub stop start in
  Printf.printf
    "Flocq,binary-reference,flocq-p%d,%d,%s,software-reference,\
     Flocq 4.2.2 extracted OCaml Zarith,result-dependent-fixture-chain,\
     %d,%Ld,%Ld,%Ld,0,0,0\n%!"
    precision width operation iterations total_nanos sink fixture_trace

let () =
  let selected_width = optional_width () in
  let selected_operation = optional_operation () in
  let warmup_iterations =
    positive_env "FORMAT_COMPARE_WARMUP_ITERATIONS" 64
  in
  print_endline
    "implementation,family,format,totalBits,operation,executionClass,\
     backend,measurementMethod,iterations,totalNanos,sink,fixtureTraceDigest,\
     agreementIterations,agreementSink,agreementFixtureTraceDigest";
  Array.iter
    (fun (width, precision) ->
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
                width precision operation iterations warmup_iterations)
          operations)
    formats
