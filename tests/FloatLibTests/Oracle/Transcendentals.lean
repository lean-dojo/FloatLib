/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
import Std.Data.HashSet

/-!
# Transcendental comparison vectors

This standalone emitter evaluates FloatLib's `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`,
`pow` and `pi` and writes one request per evaluation for `tests/oracles/transcendental_mpfr.c`:

```text
case ID op NAME mode RNDN format EXPWIDTH FRACWIDTH BIAS ieee args K BITS... floatlib BITS
```

`ID` names the evaluation by its content, `FORMAT/NAME/RNDN/ARGUMENTS` with each argument
encoding in hexadecimal, so `tests/oracles/data/transcendental-known-failures.tsv` can list it.
FloatLib's transcendental kernels round to nearest only, so every request uses `RNDN`.

The formats are binary16, bfloat16, binary32, binary64, binary128 and `ieee 31 23`. For each
format the emitter builds

* structural edges from the descriptor: zeros, the subnormal and normal boundaries, powers of two
  from `1/4` to `4` with their neighbours, tiny and large powers of two, the largest finite
  values, both infinities and the canonical quiet NaN;
* three fixed-seed samples whose sign, exponent and fraction are drawn as integers from the high
  halves of a linear congruential generator: central (`2^-12` to `2^12`), scaled (below the
  precision to beyond the exponential's overflow threshold) and broad (the whole finite range,
  or unbiased exponents from `-2^14` to `2^14` for exponent fields wider than 15 bits). Each
  sample has its own seed, so each of the three samples of a smaller count is a prefix of the
  same sample of a larger count;
* `pow` pairs: a special-value matrix, integral exponents, whose finite results FloatLib proves
  correctly rounded, and general exponents;
* `pi`.

`--hard FILE` adds the rows of the checked-in corpus whose tier is selected by `--tier`: each
`trig-cf` row is evaluated with both signs and both neighbouring encodings, and every other row
as written. `--exhaustive16` adds every binary16 and bfloat16 code for the seven unary functions.
`--shard I/N` keeps every `N`th request, starting with the `I`th, so shards run in parallel.
Duplicate requests are emitted once. Each shard starts with `# manifest` comments recording the
invocation and its shard index, and ends with the number of requests of all shards and its own
count, which `tests/oracles/transcendental_report.py` checks for a complete run.

Generated `sin` and `cos` requests skip finite arguments of `2^16385` and above, which only the
31-bit exponent field has: MPFR reduces such an argument with as many bits of `pi` as its
exponent. The corpus lists `ieee 31 23` arguments near `2^(2^20)` itself, and FloatLib reduces
them with the `2^20`- and `2^21`-bit levels of `2 / pi`. MPFR has a single NaN, so a NaN result
matches any NaN. Signaling NaNs are emitted only by the exhaustive tier, and their quieting and
payloads are checked by the Lean fixtures in `FloatLibTests.Fixtures.Transcendentals`.

These are comparison vectors for a gate keyed by case identity, not conformance vectors: the
kernels do not claim correct rounding.
-/

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Oracle.Transcendentals

private inductive Operation where
  | exp
  | log
  | sin
  | cos
  | sinh
  | cosh
  | tanh
  | pow
  | pi

private def Operation.unary : Array Operation :=
  #[.exp, .log, .sin, .cos, .sinh, .cosh, .tanh]

private def Operation.label : Operation → String
  | .exp => "exp"
  | .log => "log"
  | .sin => "sin"
  | .cos => "cos"
  | .sinh => "sinh"
  | .cosh => "cosh"
  | .tanh => "tanh"
  | .pow => "pow"
  | .pi => "pi"

private def Operation.ofLabel? (label : String) : Option Operation :=
  [Operation.exp, .log, .sin, .cos, .sinh, .cosh, .tanh, .pow, .pi].find? (·.label == label)

private def Operation.arity : Operation → Nat
  | .pow => 2
  | .pi => 0
  | _ => 1

/-- A destination format, the name used in case ids, and the seed of its samples. -/
private structure Descriptor where
  name : String
  format : FloatFormat
  seed : UInt64

/-- The compared formats. Their names match `Format.name` in `transcendental_report.py`. -/
private def descriptors : Array Descriptor :=
  #[ ⟨"binary16", FloatFormat.binary16, 0xa4093822299f31d0⟩,
     ⟨"bfloat16", FloatFormat.bfloat16, 0x082efa98ec4e6c89⟩,
     ⟨"binary32", FloatFormat.binary32, 0x243f6a8885a308d3⟩,
     ⟨"binary64", FloatFormat.binary64, 0x13198a2e03707344⟩,
     ⟨"binary128", FloatFormat.binary128, 0x452821e638d01377⟩,
     ⟨"ieee31_23", FloatFormat.ieee 31 23, 0xbe5466cf34e90c6c⟩ ]

private def Descriptor.width (descriptor : Descriptor) : Nat :=
  descriptor.format.expWidth + descriptor.format.fracWidth + 1

/-- The all-ones exponent field of infinities and NaNs. -/
private def Descriptor.specialField (descriptor : Descriptor) : Nat :=
  2 ^ descriptor.format.expWidth - 1

/-- The encoding with the given sign, biased exponent field and fraction field. -/
private def Descriptor.encode (descriptor : Descriptor) (negative : Bool) (field fraction : Nat) :
    Nat :=
  let fracWidth := descriptor.format.fracWidth
  (if negative then 2 ^ (descriptor.format.expWidth + fracWidth) else 0) +
    field * 2 ^ fracWidth + fraction

private def Descriptor.signBit (descriptor : Descriptor) : Nat :=
  2 ^ (descriptor.width - 1)

/-- The encoding nearest to `significand * 2^exponent`, rounded by FloatLib. -/
private def Descriptor.dyadic (descriptor : Descriptor) (negative : Bool) (significand : Nat)
    (exponent : Int) : Nat :=
  (Model.roundDyadic descriptor.format
    { negative := negative, significand := significand, exponent := exponent }).toNatBits

private def hexDigits (value : Nat) : List Char :=
  Nat.toDigits 16 value

/-- Lowercase hexadecimal with a `0x` prefix, zero-padded to the format width. -/
private def Descriptor.hex (descriptor : Descriptor) (bits : Nat) : String :=
  let digits := hexDigits bits
  let width := (descriptor.width + 3) / 4
  "0x" ++ String.ofList (List.replicate (width - digits.length) '0' ++ digits)

private def hexDigit? (character : Char) : Option Nat :=
  let code := character.toNat
  if 48 ≤ code ∧ code ≤ 57 then some (code - 48)
  else if 97 ≤ code ∧ code ≤ 102 then some (code - 87)
  else if 65 ≤ code ∧ code ≤ 70 then some (code - 55)
  else none

/-- Read `0x`-prefixed hexadecimal. -/
private def parseHex? (text : String) : Option Nat :=
  match text.toList with
  | '0' :: 'x' :: digits@(_ :: _) =>
      digits.foldlM (fun value character => do pure (16 * value + (← hexDigit? character))) 0
  | _ => none

/-! ## Inputs -/

/-- Structural edge inputs of a format, both signs except for the NaN. -/
private def edgeInputs (descriptor : Descriptor) : Array Nat := Id.run do
  let fmt := descriptor.format
  let fracWidth := fmt.fracWidth
  let bias := fmt.exponentBias
  let maxField := 2 ^ fmt.expWidth - 2
  let fullFraction := 2 ^ fracWidth - 1
  let precision := fracWidth + 1
  let mut positive : Array Nat := #[
    descriptor.encode false 0 0,
    descriptor.encode false 0 1,
    descriptor.encode false 0 2,
    descriptor.encode false 0 fullFraction,
    descriptor.encode false 1 0,
    descriptor.encode false 1 1,
    descriptor.encode false maxField fullFraction,
    descriptor.encode false maxField (fullFraction - 1),
    descriptor.encode false descriptor.specialField 0 ]
  -- Powers of two from 1/4 to 4 with both neighbours.
  for offset in [0:5] do
    let field := bias + offset - 2
    positive := positive ++ #[
      descriptor.encode false field 0,
      descriptor.encode false field 1,
      descriptor.encode false (field - 1) fullFraction ]
  -- Tiny powers of two around the precision, and large ones while they are finite.
  for shift in [precision - 1, precision, precision + 1, precision + 2] do
    if shift < bias then
      positive := positive.push (descriptor.encode false (bias - shift) 0)
  for power in [20, 50, 100, 1000, 10000] do
    if bias + power ≤ maxField then
      positive := positive.push (descriptor.encode false (bias + power) 0)
  let mut result := #[]
  for bits in positive do
    result := result ++ #[bits, bits + descriptor.signBit]
  return result.push (descriptor.encode false descriptor.specialField (2 ^ (fracWidth - 1)))

@[inline] private def step (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

/-- `bits` random bits from the high halves of successive generator states. -/
private def drawBits (state : UInt64) (bits : Nat) : Nat × UInt64 := Id.run do
  let mut current := state
  let mut value := 0
  for _ in [0:(bits + 31) / 32] do
    current := step current
    value := value * 2 ^ 32 + (current >>> 32).toNat
  return (value % 2 ^ bits, current)

/--
An integer in `[low, high]`: 64 generator bits reduced modulo the size of the range. The ranges
drawn here have fewer than `2^16` values, so for uniform input bits each value's probability
would be within a relative `2^-48` of uniform. The bits come from the fixed-seed generator, so
this bounds only the bias of the reduction.
-/
private def drawInt (state : UInt64) (low high : Int) : Int × UInt64 :=
  let (raw, next) := drawBits state 64
  (low + Int.ofNat (raw % (high - low + 1).toNat), next)

/--
A finite encoding with a random sign and fraction and an unbiased exponent drawn from
`[low, high]`. Exponents below the normal range give subnormals.
-/
private def drawFinite (descriptor : Descriptor) (state : UInt64) (low high : Int) :
    Nat × UInt64 :=
  let fmt := descriptor.format
  let bias := Int.ofNat fmt.exponentBias
  let maxField := Int.ofNat (2 ^ fmt.expWidth - 2)
  let (exponent, state) := drawInt state low high
  let (fraction, state) := drawBits state fmt.fracWidth
  let (sign, state) := drawBits state 1
  let field := if exponent + bias < 1 then 0 else min (exponent + bias) maxField
  (descriptor.encode (sign == 1) field.toNat fraction, state)

/-- Unbiased exponent range of a format's normal numbers. -/
private def normalRange (descriptor : Descriptor) : Int × Int :=
  let fmt := descriptor.format
  (1 - Int.ofNat fmt.exponentBias, Int.ofNat (2 ^ fmt.expWidth - 2) - Int.ofNat fmt.exponentBias)

/--
The three fixed-seed samples, `count` inputs in total, shared by the unary functions. Each sample
has its own seed, so a smaller count draws a prefix of every sample of a larger one.
-/
private def sampledInputs (descriptor : Descriptor) (count : Nat) : Array Nat := Id.run do
  let (lowest, highest) := normalRange descriptor
  let fracWidth := Int.ofNat descriptor.format.fracWidth
  let central := (max (-12) lowest, min 12 highest)
  let scaled := (max (-(fracWidth + 4)) (lowest - 1),
    min (Int.ofNat (Nat.log2 highest.toNat) + 2) highest)
  let broad :=
    if highest - lowest ≤ 2 ^ 15 then (lowest - fracWidth, highest)
    else (max (-(2 ^ 14)) lowest, min (2 ^ 14) highest)
  let centralCount := (count + 2) / 3
  let scaledCount := (count - centralCount + 1) / 2
  let samples := #[(central, centralCount), (scaled, scaledCount),
    (broad, count - centralCount - scaledCount)]
  let mut result := #[]
  for ((low, high), size) in samples, index in [0:samples.size] do
    let mut state := descriptor.seed ^^^ (UInt64.ofNat (index + 1) * 0x9e3779b97f4a7c15)
    for _ in [0:size] do
      let (bits, next) := drawFinite descriptor state low high
      state := next
      result := result.push bits
  return result

/-- Special `pow` operands: zeros, one, small integers, halves, infinities, NaN, extremes. -/
private def powSpecialPairs (descriptor : Descriptor) : Array (Array Nat) := Id.run do
  let fmt := descriptor.format
  let precision := fmt.fracWidth + 1
  let value (negative : Bool) (significand : Nat) (exponent : Int) :=
    descriptor.dyadic negative significand exponent
  let infinity := descriptor.encode false descriptor.specialField 0
  let nan := descriptor.encode false descriptor.specialField (2 ^ (fmt.fracWidth - 1))
  let largest := descriptor.encode false (2 ^ fmt.expWidth - 2) (2 ^ fmt.fracWidth - 1)
  let both (bits : Nat) := #[bits, bits + descriptor.signBit]
  let bases :=
    both 0 ++ both (value false 1 0) ++ both (value false 2 0) ++ both (value false 1 (-1)) ++
    #[value false 3 0] ++ both infinity ++ #[nan, largest] ++ both 1
  let exponents :=
    both 0 ++ both (value false 1 0) ++ both (value false 2 0) ++ both (value false 3 0) ++
    both (value false 1 (-1)) ++ #[value false 3 (-1)] ++ both infinity ++ #[nan] ++
    #[value false 1 (Int.ofNat precision), value false (2 ^ (precision - 1) + 1) 0, largest]
  let mut result := #[]
  for base in bases do
    for exponent in exponents do
      result := result.push #[base, exponent]
  return result

/-- `count` random `pow` pairs: half with integral exponents, half with central exponents. -/
private def powSampledPairs (descriptor : Descriptor) (count : Nat) : Array (Array Nat) := Id.run do
  let (lowest, highest) := normalRange descriptor
  let central := (max (-12) lowest, min 12 highest)
  let mut state := step descriptor.seed
  let mut result := #[]
  for index in [0:count] do
    let (base, next) := drawFinite descriptor state central.1 central.2
    state := next
    if index % 2 == 0 then
      let (power, next) := drawInt state (-64) 64
      state := next
      result := result.push #[base, descriptor.dyadic (power < 0) power.natAbs 0]
    else
      let (exponent, next) := drawFinite descriptor state central.1 central.2
      state := next
      result := result.push #[base, exponent]
  return result

/-! ## Requests -/

private structure Request where
  descriptor : Descriptor
  operation : Operation
  arguments : Array Nat

private def Request.id (request : Request) : String :=
  "/".intercalate
    ([request.descriptor.name, request.operation.label, "RNDN"] ++
      (request.arguments.map request.descriptor.hex).toList)

@[inline] private def Request.value (request : Request) (index : Nat) :
    Model request.descriptor.format :=
  Model.ofNatBits (request.arguments.getD index 0)

/-- FloatLib's nearest-even result for one request. -/
private def Request.evaluate (request : Request) : Nat :=
  let x := request.value 0
  match request.operation with
  | .exp => (Model.exp x).toNatBits
  | .log => (Model.log x).toNatBits
  | .sin => (Model.sin x).toNatBits
  | .cos => (Model.cos x).toNatBits
  | .sinh => (Model.sinh x).toNatBits
  | .cosh => (Model.cosh x).toNatBits
  | .tanh => (Model.tanh x).toNatBits
  | .pow => (Model.pow x (request.value 1)).toNatBits
  | .pi => (Model.pi request.descriptor.format).toNatBits

private def Request.line (request : Request) : String :=
  let descriptor := request.descriptor
  let fmt := descriptor.format
  let arguments := request.arguments.toList.map (" " ++ descriptor.hex ·)
  s!"case {request.id} op {request.operation.label} mode RNDN format {fmt.expWidth} " ++
    s!"{fmt.fracWidth} {fmt.exponentBias} ieee args {request.arguments.size}" ++
    String.join arguments ++ s!" floatlib {descriptor.hex request.evaluate}"

/--
Largest unbiased exponent of a finite `sin` or `cos` argument. MPFR reduces an argument near
`2^e` with about `e` bits of `pi`, which is impractical for the largest arguments of a 31-bit
exponent field. The catalog formats stay below this limit.
-/
private def trigExponentLimit : Int := 2 ^ 14

/-- Whether MPFR can evaluate `operation` on `bits` in reasonable time. -/
private def Descriptor.oracleFeasible (descriptor : Descriptor) (operation : Operation)
    (bits : Nat) : Bool :=
  let fmt := descriptor.format
  let field := (bits / 2 ^ fmt.fracWidth) % 2 ^ fmt.expWidth
  match operation with
  | .sin | .cos =>
      field == descriptor.specialField ||
        Int.ofNat field - Int.ofNat fmt.exponentBias ≤ trigExponentLimit
  | _ => true

/-- Requests of the default corpus for one format. -/
private def formatRequests (descriptor : Descriptor) (randomCount : Nat) : Array Request :=
  Id.run do
    let inputs := edgeInputs descriptor ++ sampledInputs descriptor randomCount
    let mut result := #[]
    for operation in Operation.unary do
      for input in inputs do
        if descriptor.oracleFeasible operation input then
          result := result.push ⟨descriptor, operation, #[input]⟩
    for pair in powSpecialPairs descriptor ++ powSampledPairs descriptor randomCount do
      result := result.push ⟨descriptor, .pow, pair⟩
    return result.push ⟨descriptor, .pi, #[]⟩

private def descriptorNamed? (name : String) : Option Descriptor :=
  descriptors.find? (·.name == name)

/-- Corpus tiers in increasing size. -/
private def tierRank? : String → Option Nat
  | "default" => some 0
  | "slow" => some 1
  | _ => none

/--
Requests from a corpus file with columns `tier set format operations arguments note`.
`operations` and `arguments` are comma-separated, and `trig-cf` rows add both signs and both
neighbouring encodings of their single argument.
-/
private def corpusRequests (path : System.FilePath) (tier : Nat) : IO (Array Request) := do
  let mut result := #[]
  let mut lineNumber := 0
  for line in ← IO.FS.lines path do
    lineNumber := lineNumber + 1
    if line.isEmpty || line.startsWith "#" then
      continue
    let fail {α : Type} (message : String) : IO α :=
      throw <| IO.userError s!"{path}:{lineNumber}: {message}"
    match line.splitOn "\t" with
    | [tierName, set, formatName, operationNames, argumentText, _note] =>
        let some rank := tierRank? tierName | fail s!"unknown tier {tierName}"
        if rank > tier then
          continue
        let some descriptor := descriptorNamed? formatName | fail s!"unknown format {formatName}"
        let mut operations := #[]
        for name in operationNames.splitOn "," do
          let some operation := Operation.ofLabel? name | fail s!"unknown operation {name}"
          operations := operations.push operation
        let mut arguments := #[]
        for text in argumentText.splitOn "," do
          let some bits := parseHex? text | fail s!"invalid encoding {text}"
          if bits ≥ 2 ^ descriptor.width then
            fail s!"encoding {text} is wider than {formatName}"
          arguments := arguments.push bits
        let argumentSets ←
          if set == "trig-cf" then
            match arguments.toList with
            | [center] =>
                let neighbours := #[center - 1, center, center + 1]
                pure <| (neighbours ++ neighbours.map (· + descriptor.signBit)).map (#[·])
            | _ => fail "a trig-cf row has one argument"
          else
            pure #[arguments]
        for operation in operations do
          for argumentSet in argumentSets do
            if argumentSet.size != operation.arity then
              fail s!"{operation.label} takes {operation.arity} arguments"
            result := result.push ⟨descriptor, operation, argumentSet⟩
    | _ => fail "expected six tab-separated fields"
  return result

/-- Every binary16 and bfloat16 code for the seven unary functions. -/
private def exhaustiveRequests : Array Request := Id.run do
  let mut result := #[]
  for descriptor in descriptors do
    if descriptor.width == 16 then
      for operation in Operation.unary do
        for bits in [0:2 ^ 16] do
          result := result.push ⟨descriptor, operation, #[bits]⟩
  return result

/-! ## Command line -/

private structure Options where
  randomCount : Nat := 32
  hard : Option System.FilePath := none
  tier : String := "default"
  exhaustive16 : Bool := false
  shardIndex : Nat := 0
  shardCount : Nat := 1

private def usage : String :=
  "usage: transcendentalEmitter [--random-count N] [--hard FILE] [--tier default|slow] " ++
    "[--exhaustive16] [--shard I/N]"

private def parseOptions : Options → List String → Except String Options
  | options, [] => .ok options
  | options, "--random-count" :: text :: rest =>
      match text.toNat? with
      | some count => parseOptions { options with randomCount := count } rest
      | none => .error s!"invalid random count: {text}"
  | options, "--hard" :: path :: rest => parseOptions { options with hard := some path } rest
  | options, "--tier" :: tier :: rest =>
      if (tierRank? tier).isSome then parseOptions { options with tier := tier } rest
      else .error s!"unknown tier: {tier}"
  | options, "--exhaustive16" :: rest => parseOptions { options with exhaustive16 := true } rest
  | options, "--shard" :: text :: rest =>
      match text.splitOn "/" with
      | [index, count] =>
          match index.toNat?, count.toNat? with
          | some i, some n =>
              if i < n then parseOptions { options with shardIndex := i, shardCount := n } rest
              else .error s!"shard index must be below the shard count: {text}"
          | _, _ => .error s!"invalid shard: {text}"
      | _ => .error s!"invalid shard: {text}"
  | _, argument :: _ => .error s!"unknown argument: {argument}\n{usage}"

/--
Emit this shard's requests, each evaluated by FloatLib, between a manifest of the invocation and
the shard index, and a trailer with the number of requests of all shards and of this one.
-/
def run (args : List String) : IO UInt32 := do
  let options ← match parseOptions {} args with
    | .ok options => pure options
    | .error message => throw <| IO.userError message
  let stdout ← IO.getStdout
  stdout.putStrLn "# manifest emitter transcendentalEmitter"
  stdout.putStrLn s!"# manifest random-count {options.randomCount}"
  for descriptor in descriptors do
    stdout.putStrLn s!"# manifest seed {descriptor.name} {descriptor.seed.toNat}"
  stdout.putStrLn s!"# manifest tier {options.tier}"
  stdout.putStrLn s!"# manifest hard {options.hard.map (·.toString) |>.getD "none"}"
  stdout.putStrLn s!"# manifest exhaustive16 {options.exhaustive16}"
  stdout.putStrLn s!"# manifest shard {options.shardIndex}/{options.shardCount}"
  let mut requests := descriptors.flatMap (formatRequests · options.randomCount)
  if let some path := options.hard then
    requests := requests ++ (← corpusRequests path (tierRank? options.tier |>.getD 0))
  if options.exhaustive16 then
    requests := requests ++ exhaustiveRequests
  let mut seen : Std.HashSet String := {}
  let mut index := 0
  let mut emitted := 0
  for request in requests do
    let id := request.id
    if seen.contains id then
      continue
    seen := seen.insert id
    if index % options.shardCount == options.shardIndex then
      stdout.putStrLn request.line
      emitted := emitted + 1
    index := index + 1
  stdout.putStrLn s!"# manifest requests {index}"
  stdout.putStrLn s!"# emitted {emitted}"
  stdout.flush
  return 0

end FloatLibTests.Oracle.Transcendentals

public def main (args : List String) : IO UInt32 :=
  FloatLibTests.Oracle.Transcendentals.run args
