/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Every rounding direction against an exact reference

The six `IEEERoundingMode` directions, with their exception flags and ternary values, are checked
against a reference written here from exact rationals. The reference does not call the library's
rounders: it tabulates the values of a small IEEE-encoded format from their fields, finds the two
neighbours of an exact result by bisection, and applies each direction's rule. The table ends with
the first grid value above the largest finite one, so overflow is decided as IEEE 754-2019
Section 7.4 decides it, on the precision grid with an unbounded exponent. Tininess is decided
after rounding on that unbounded grid. The ternary value compares the delivered value with the
exact one. NaN, invalid-operation, signed-zero, and infinity results have their own rules.

The checks cover, under all six directions:

* every ordered operand pair of `FloatFormat.ieee 4 3` for addition, subtraction, multiplication,
  and division, and every input for square root;
* the same for addition, multiplication, division, and square root of a seven-bit IEEE-encoded
  layout with a non-conventional bias, which takes the descriptor-generic rounding branches;
* 4,096 fused multiply-add triples per direction from a fixed seed;
* narrowing casts of every binary16 encoding to `ieee 4 3` and to E5M2, and the exact widening
  casts of every encoding of those two formats to binary16;
* named vectors for rounding away from zero, ties away from zero, integral rounding, integer
  conversion, and the sign of exactly cancelling sums, and boundary vectors at the tininess
  thresholds, an exact subnormal, the overflow midpoint of E4M3FN, and saturation in E2M1.

Compile-time checks confirm that `open FloatLib.Rounding` lets a directed operation take the
bare mode name in `(mode := up)`, that the open makes a pattern spelled `up` the constructor, and
that partial application and a symbolic `status` elaborate.

Exhaustive fused multiply-add over every operand triple of both eight-bit formats is the opt-in
campaign `exhaustiveFmaFailures`, run in shards by `tests/oracles/rounding-fma-exhaustive.sh`, and
is not part of this check.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only. Elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.BinaryInterchange.RoundingDirections

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLibTests.Accounting
open FloatLibTests.Regression.BinaryInterchange.Harness

/-! ## Tabulated formats -/

/-- The pattern of positive infinity, the first nonnegative pattern above every finite one. -/
def infinityPattern (fmt : FloatFormat) : Nat :=
  (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth

/--
The value of a nonnegative pattern of an IEEE-encoded format, from its exponent and fraction
fields. At `infinityPattern` the formula gives the first grid value above the largest finite one.
-/
def patternValue (fmt : FloatFormat) (pattern : Nat) : Rat :=
  let exponentField := pattern / 2 ^ fmt.fracWidth
  let fraction := pattern % 2 ^ fmt.fracWidth
  let bias : Int := fmt.exponentBias
  if exponentField = 0 then
    (fraction : Rat) * (2 : Rat) ^ (1 - bias - (fmt.fracWidth : Int))
  else
    ((2 ^ fmt.fracWidth + fraction : Nat) : Rat) *
      (2 : Rat) ^ ((exponentField : Int) - bias - (fmt.fracWidth : Int))

/-- An IEEE-encoded format with the values of its nonnegative patterns up to `infinityPattern`. -/
structure Grid where
  /-- The tabulated format. -/
  fmt : FloatFormat
  /-- `values[i]` is `patternValue fmt i` for every `i ≤ infinityPattern fmt`. -/
  values : Array Rat
  /-- `midpoints[i]` is the midpoint of `values[i]` and `values[i + 1]`. -/
  midpoints : Array Rat

/-- Tabulate the nonnegative patterns of an IEEE-encoded format. -/
def Grid.ofFormat (fmt : FloatFormat) : Grid :=
  let values := (Array.range (infinityPattern fmt + 1)).map (patternValue fmt)
  { fmt
    values
    midpoints := (Array.range (infinityPattern fmt)).map fun i =>
      (values[i]! + values[i + 1]!) / 2 }

/-- The weight of the sign bit. -/
def Grid.signBit (grid : Grid) : Nat :=
  2 ^ (grid.fmt.expWidth + grid.fmt.fracWidth)

/-- The value of a tabulated nonnegative pattern. -/
def Grid.value (grid : Grid) (pattern : Nat) : Rat :=
  grid.values[pattern]!

/-- The eight-bit IEEE layout with four exponent and three fraction bits. -/
abbrev ieee43Format : FloatFormat := FloatFormat.ieee 4 3

/--
A seven-bit IEEE-encoded layout with bias 2 instead of the conventional 3. It is not `isIEEE`, so
its arithmetic takes the descriptor-generic rounding branches.
-/
abbrev customBiasFormat : FloatFormat := FloatFormat.custom 3 3 2 .ieee

/-!
The tables are module constants, built once when the test program starts. A table bound by `let`
inside a check is a closed term that the compiler copies into the specialized loop bodies, where
it would be rebuilt for every element.
-/

/-- The tabulated `ieee 4 3`. -/
def ieee43 : Grid := Grid.ofFormat ieee43Format

/-- The tabulated E5M2. -/
def e5m2 : Grid := Grid.ofFormat FloatFormat.e5m2

/-- The tabulated binary16. -/
def binary16 : Grid := Grid.ofFormat FloatFormat.binary16

/-- The tabulated custom-bias layout. -/
def customBias : Grid := Grid.ofFormat customBiasFormat

/-! ## Operands and expected results -/

/-- An operand decoded from its bits by the reference. -/
inductive Operand where
  /-- A NaN, signaling when the most significant fraction bit is clear. -/
  | nan (signaling : Bool)
  /-- An infinity of the given sign. -/
  | infinity (negative : Bool)
  /-- A finite value: its sign bit and its exact signed value, zero for both zeros. -/
  | finite (negative : Bool) (value : Rat)
  deriving Inhabited

/-- Decode the bits of an IEEE-encoded format without the library. -/
def Grid.decode (grid : Grid) (bits : Nat) : Operand :=
  let fmt := grid.fmt
  let magnitude := bits % grid.signBit
  let negative := bits / grid.signBit % 2 == 1
  if magnitude > infinityPattern fmt then
    .nan (magnitude % 2 ^ fmt.fracWidth < 2 ^ (fmt.fracWidth - 1))
  else if magnitude == infinityPattern fmt then
    .infinity negative
  else
    let value := grid.value magnitude
    .finite negative (if negative then -value else value)

/-- An expected result: exact bits, or any NaN. -/
inductive Expected where
  /-- Exactly these bits. -/
  | bits (bits : Nat)
  /-- Any NaN encoding. -/
  | nan

/-- An expected result with its exception flags and ternary value. -/
structure Reference where
  /-- Expected delivered value. -/
  result : Expected
  /-- Expected exception flags. -/
  status : FloatLib.Numerics.IEEEStatus := {}
  /-- Expected ternary value: the delivered value compared with the exact result. -/
  ternary : Ordering := .eq

/-- A NaN result, invalid when an operand was a signaling NaN or the operation was invalid. -/
def nanResult (invalid : Bool) : Reference :=
  { result := .nan, status := { invalid := invalid } }

/-- The invalid-operation result. -/
def invalidResult : Reference :=
  nanResult true

/-- An infinite result of the given sign, exact. -/
def Grid.infinityResult (grid : Grid) (negative : Bool) : Reference :=
  { result := .bits ((if negative then grid.signBit else 0) + infinityPattern grid.fmt) }

/-- A zero result of the given sign, exact. -/
def Grid.zeroResult (grid : Grid) (negative : Bool) : Reference :=
  { result := .bits (if negative then grid.signBit else 0) }

/-- Whether a library outcome is the expected one: bits, all five flags, and ternary value. -/
def agrees {fmt : FloatFormat} (outcome : Model.IEEEOutcome fmt) (expected : Reference) :
    Bool :=
  let value := match expected.result with
    | .bits bits => outcome.value.toNatBits == bits
    | .nan => Model.isNaN outcome.value
  value && outcome.status == expected.status && outcome.ternary == expected.ternary

/-! ## Rounding an exact magnitude -/

/--
Whether a direction takes the upper of two neighbours when the exact magnitude lies strictly
between them. `position` compares the magnitude with their midpoint, and `upperEven` says whether
the upper neighbour has an even significand.
-/
def takesUpper (mode : Model.IEEERoundingMode) (negative : Bool) (position : Ordering)
    (upperEven : Bool) : Bool :=
  match mode with
  | .nearest => position == .gt || (position == .eq && upperEven)
  | .nearestAway => position != .lt
  | .towardZero => false
  | .up => !negative
  | .down => negative
  | .away => true

/--
Whether a positive magnitude below the smallest normal value is tiny after rounding: rounded to the
precision with an unbounded exponent, it stays below the smallest normal value. `compareWith t`
compares the exact magnitude with `t`.
-/
def Grid.tinyAfterRounding (grid : Grid) (mode : Model.IEEERoundingMode) (negative : Bool)
    (compareWith : Rat → Ordering) : Bool := Id.run do
  let fmt := grid.fmt
  let minNormal := grid.value (2 ^ fmt.fracWidth)
  if compareWith minNormal != .lt then
    return false
  -- The binade `[2^e, 2^(e+1))` that holds the magnitude, found by halving from `minNormal`.
  let mut binade := minNormal / 2
  for _ in [0:4096] do
    if compareWith binade == .lt then
      binade := binade / 2
    else
      break
  let spacing := binade / (2 ^ fmt.fracWidth : Nat)
  -- The largest multiple of `spacing` at most the magnitude, in `[2^fracWidth, 2^(fracWidth+1))`.
  let mut lower := 2 ^ fmt.fracWidth
  for step in [2 ^ fmt.fracWidth + 1:2 ^ (fmt.fracWidth + 1)] do
    if compareWith ((step : Rat) * spacing) != .lt then
      lower := step
  let lowerValue := (lower : Rat) * spacing
  let rounded :=
    if compareWith lowerValue == .eq then
      lowerValue
    else
      let midpoint := ((2 * lower + 1 : Nat) : Rat) * spacing / 2
      if takesUpper mode negative (compareWith midpoint) ((lower + 1) % 2 == 0) then
        lowerValue + spacing
      else
        lowerValue
  return rounded < minNormal

/--
Round a positive exact magnitude, known through `compareWith`, into `grid` under `mode` and attach
the sign. The result carries all five flags and the ternary value, which compares the delivered
value with the signed exact one.
-/
def Grid.roundMagnitude (grid : Grid) (mode : Model.IEEERoundingMode) (negative : Bool)
    (compareWith : Rat → Ordering) : Reference := Id.run do
  let infinity := infinityPattern grid.fmt
  let sign := if negative then grid.signBit else 0
  -- `compareWith v` orders the exact magnitude before `v`, and negation reverses both sides.
  let ternaryOf (pattern : Nat) : Ordering :=
    let order := compareWith (grid.value pattern)
    if negative then order else order.swap
  if compareWith (grid.value infinity) != .lt then
    -- Rounding with an unbounded exponent reaches at least the first grid value above the
    -- largest finite one: overflow, delivered as infinity or as the largest finite value.
    let pattern := if takesUpper mode negative .gt false then infinity else infinity - 1
    let ternary :=
      if pattern == infinity then (if negative then .lt else .gt) else ternaryOf pattern
    return { result := .bits (sign + pattern), status := { overflow := true, inexact := true }
             ternary }
  -- Bisection: `value low ≤ magnitude < value high`.
  let mut low := 0
  let mut high := infinity
  for _ in [0:64] do
    if high - low ≤ 1 then
      break
    let middle := (low + high) / 2
    if compareWith (grid.value middle) == .lt then
      high := middle
    else
      low := middle
  if compareWith (grid.value low) == .eq then
    return { result := .bits (sign + low) }
  let up := takesUpper mode negative (compareWith grid.midpoints[low]!) ((low + 1) % 2 == 0)
  let pattern := if up then low + 1 else low
  return { result := .bits (sign + pattern)
           status :=
             { overflow := up && low + 1 == infinity
               underflow := grid.tinyAfterRounding mode negative compareWith
               inexact := true }
           ternary :=
             if pattern == infinity then (if negative then .lt else .gt) else ternaryOf pattern }

/-- Round a nonzero exact rational into `grid` under `mode`. -/
def Grid.roundRational (grid : Grid) (mode : Model.IEEERoundingMode) (exact : Rat) :
    Reference :=
  let magnitude := if exact < 0 then -exact else exact
  grid.roundMagnitude mode (exact < 0) (compare magnitude)

/-- The sign IEEE 754-2019 Section 6.3 gives the exact zero sum of operands with these signs. -/
def cancellationSign (mode : Model.IEEERoundingMode) (left right : Bool) : Bool :=
  if mode == .down then left || right else left && right

/-! ## Operation references -/

/-- Reference addition. -/
def Grid.add (grid : Grid) (mode : Model.IEEERoundingMode) : Operand → Operand → Reference
  | .nan left, .nan right => nanResult (left || right)
  | .nan signaling, _ | _, .nan signaling => nanResult signaling
  | .infinity left, .infinity right =>
      if left == right then grid.infinityResult left else invalidResult
  | .infinity negative, _ | _, .infinity negative => grid.infinityResult negative
  | .finite left x, .finite right y =>
      if x + y == 0 then grid.zeroResult (cancellationSign mode left right)
      else grid.roundRational mode (x + y)

/-- Negate an operand. The sign of a NaN does not matter here. -/
def Operand.neg : Operand → Operand
  | .nan signaling => .nan signaling
  | .infinity negative => .infinity (!negative)
  | .finite negative value => .finite (!negative) (-value)

/-- Reference multiplication. -/
def Grid.mul (grid : Grid) (mode : Model.IEEERoundingMode) : Operand → Operand → Reference
  | .nan left, .nan right => nanResult (left || right)
  | .nan signaling, _ | _, .nan signaling => nanResult signaling
  | .infinity left, .infinity right => grid.infinityResult (left != right)
  | .infinity left, .finite right y | .finite right y, .infinity left =>
      if y == 0 then invalidResult else grid.infinityResult (left != right)
  | .finite left x, .finite right y =>
      if x * y == 0 then grid.zeroResult (left != right)
      else grid.roundRational mode (x * y)

/-- Reference division. -/
def Grid.div (grid : Grid) (mode : Model.IEEERoundingMode) : Operand → Operand → Reference
  | .nan left, .nan right => nanResult (left || right)
  | .nan signaling, _ | _, .nan signaling => nanResult signaling
  | .infinity _, .infinity _ => invalidResult
  | .infinity left, .finite right _ => grid.infinityResult (left != right)
  | .finite left _, .infinity right => grid.zeroResult (left != right)
  | .finite left x, .finite right y =>
      if y == 0 then
        if x == 0 then invalidResult
        else { (grid.infinityResult (left != right)) with status := { divideByZero := true } }
      else if x == 0 then grid.zeroResult (left != right)
      else grid.roundRational mode (x / y)

/-- Reference square root, comparing the exact root with a bound through its square. -/
def Grid.sqrt (grid : Grid) (mode : Model.IEEERoundingMode) : Operand → Reference
  | .nan signaling => nanResult signaling
  | .infinity true => invalidResult
  | .infinity false => grid.infinityResult false
  | .finite negative x =>
      if x == 0 then grid.zeroResult negative
      else if negative then invalidResult
      else grid.roundMagnitude mode false fun bound => compare x (bound * bound)

/-- Whether an operand is a NaN. -/
def Operand.isNaN : Operand → Bool
  | .nan _ => true
  | _ => false

/-- Whether an operand is a signaling NaN. -/
def Operand.isSignaling : Operand → Bool
  | .nan signaling => signaling
  | _ => false

/-- Whether an operand is infinite. -/
def Operand.isInfinite : Operand → Bool
  | .infinity _ => true
  | _ => false

/-- Whether an operand is a zero. -/
def Operand.isZero : Operand → Bool
  | .finite _ value => value == 0
  | _ => false

/-- The sign bit of a non-NaN operand. -/
def Operand.negative : Operand → Bool
  | .nan _ => false
  | .infinity negative | .finite negative _ => negative

/-- The exact value of a finite operand, zero otherwise. -/
def Operand.value : Operand → Rat
  | .finite _ value => value
  | _ => 0

/--
Reference fused multiply-add. As in `Model.fma` with `status := true`, the invalid product `0 × ∞`
raises invalid even when the addend is a quiet NaN.
-/
def Grid.fma (grid : Grid) (mode : Model.IEEERoundingMode) (x y z : Operand) : Reference :=
  let invalidProduct := (x.isInfinite || y.isInfinite) && (x.isZero || y.isZero)
  let productSign := x.negative != y.negative
  if x.isNaN || y.isNaN || z.isNaN then
    nanResult (x.isSignaling || y.isSignaling || z.isSignaling || invalidProduct)
  else if invalidProduct then
    invalidResult
  else if x.isInfinite || y.isInfinite then
    if z.isInfinite && z.negative != productSign then invalidResult
    else grid.infinityResult productSign
  else if z.isInfinite then
    grid.infinityResult z.negative
  else
    let exact := x.value * y.value + z.value
    if exact == 0 then grid.zeroResult (cancellationSign mode productSign z.negative)
    else grid.roundRational mode exact

/-- Reference conversion of an operand into the destination grid. -/
def Grid.cast (destination : Grid) (mode : Model.IEEERoundingMode) : Operand → Reference
  | .nan signaling => nanResult signaling
  | .infinity negative => destination.infinityResult negative
  | .finite negative value =>
      if value == 0 then destination.zeroResult negative
      else destination.roundRational mode value

/-! ## Exhaustive and sampled sweeps -/

/-- Every `ieee 4 3` encoding as a library value. -/
def ieee43Values : Array (Model ieee43Format) :=
  (Array.range 256).map (Model.ofNatBits (fmt := ieee43Format))

/-- Every `ieee 4 3` encoding as decoded by the reference. -/
def ieee43Operands : Array Operand :=
  (Array.range 256).map ieee43.decode

/-- Every E5M2 encoding as a library value. -/
def e5m2Values : Array (Model FloatFormat.e5m2) :=
  (Array.range 256).map (Model.ofNatBits (fmt := FloatFormat.e5m2))

/-- Every E5M2 encoding as decoded by the reference. -/
def e5m2Operands : Array Operand :=
  (Array.range 256).map e5m2.decode

/-- Every custom-bias encoding as a library value. -/
def customBiasValues : Array (Model customBiasFormat) :=
  (Array.range 128).map (Model.ofNatBits (fmt := customBiasFormat))

/-- Every custom-bias encoding as decoded by the reference. -/
def customBiasOperands : Array Operand :=
  (Array.range 128).map customBias.decode

/-- Count disagreements over every ordered operand pair of a tabulated format in every direction. -/
def pairFailures {fmt : FloatFormat} (grid : Grid) (values : Array (Model fmt))
    (operands : Array Operand)
    (operation : Model.IEEERoundingMode → Model fmt → Model fmt → Model.IEEEOutcome fmt)
    (reference : Grid → Model.IEEERoundingMode → Operand → Operand → Reference) : Nat :=
  Id.run do
    let mut failures := 0
    for mode in Model.IEEERoundingMode.all do
      for left in [0:values.size] do
        for right in [0:values.size] do
          let expected := reference grid mode operands[left]! operands[right]!
          failures := failures +
            failureCount (agrees (operation mode values[left]! values[right]!) expected)
    return failures

/-- Every addition of `ieee 4 3` in every direction. -/
def addFailures : Thunk Nat := ⟨fun _ =>
  pairFailures ieee43 ieee43Values ieee43Operands
      (fun mode x y => Model.add x y (mode := mode) (status := true))
    Grid.add⟩

/-- Every subtraction of `ieee 4 3` in every direction. -/
def subFailures : Thunk Nat := ⟨fun _ =>
  pairFailures ieee43 ieee43Values ieee43Operands
      (fun mode x y => Model.sub x y (mode := mode) (status := true))
    (fun grid mode x y => grid.add mode x y.neg)⟩

/-- Every multiplication of `ieee 4 3` in every direction. -/
def mulFailures : Thunk Nat := ⟨fun _ =>
  pairFailures ieee43 ieee43Values ieee43Operands
      (fun mode x y => Model.mul x y (mode := mode) (status := true))
    Grid.mul⟩

/-- Every division of `ieee 4 3` in every direction. -/
def divFailures : Thunk Nat := ⟨fun _ =>
  pairFailures ieee43 ieee43Values ieee43Operands
      (fun mode x y => Model.div x y (mode := mode) (status := true))
    Grid.div⟩

/--
Every addition, multiplication, and division of the custom-bias layout in every direction, and
every square root.
-/
def customBiasFailures : Thunk Nat := ⟨fun _ =>
  pairFailures customBias customBiasValues customBiasOperands
      (fun mode x y => Model.add x y (mode := mode) (status := true)) Grid.add +
    pairFailures customBias customBiasValues customBiasOperands
      (fun mode x y => Model.mul x y (mode := mode) (status := true)) Grid.mul +
    pairFailures customBias customBiasValues customBiasOperands
      (fun mode x y => Model.div x y (mode := mode) (status := true)) Grid.div +
    Model.IEEERoundingMode.all.foldl (init := 0) fun failures mode =>
      failures + countWhereFailures (List.range 128) fun bits =>
        agrees (Model.sqrt customBiasValues[bits]! (mode := mode) (status := true))
          (customBias.sqrt mode customBiasOperands[bits]!)⟩

/-- Every square root of `ieee 4 3` in every direction. -/
def sqrtFailures : Thunk Nat := ⟨fun _ =>
  Model.IEEERoundingMode.all.foldl (init := 0) fun failures mode =>
    failures + countWhereFailures (List.range 256) fun bits =>
      agrees (Model.sqrt ieee43Values[bits]! (mode := mode) (status := true))
        (ieee43.sqrt mode ieee43Operands[bits]!)⟩

/-- The next state of a 64-bit linear congruential generator (Knuth's MMIX constants). -/
@[inline] def nextState (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

/-- `count` operand triples of eight-bit encodings from `seed`, every encoding equally likely. -/
def operandTriples (seed : UInt64) (count : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let mut state := seed
  let mut triples := #[]
  for _ in [0:count] do
    state := nextState state
    let word := state.toNat
    triples := triples.push (word / 2 ^ 56 % 256, word / 2 ^ 48 % 256, word / 2 ^ 40 % 256)
  return triples

/-- The fused multiply-add operands: 4,096 fixed-seed triples of `ieee 4 3` encodings. -/
def fmaOperands : Array (Nat × Nat × Nat) :=
  operandTriples 0x9e3779b97f4a7c15 4096

/-- Fused multiply-add of the fixed-seed triples in every direction. -/
def fmaFailures : Thunk Nat := ⟨fun _ =>
  Model.IEEERoundingMode.all.foldl (init := 0) fun failures mode =>
    failures + countWhereFailures fmaOperands fun (left, right, addend) =>
      agrees
        (Model.fma ieee43Values[left]! ieee43Values[right]! ieee43Values[addend]! (mode := mode)
            (status := true))
        (ieee43.fma mode ieee43Operands[left]! ieee43Operands[right]! ieee43Operands[addend]!)⟩

/--
Count disagreements of fused multiply-add over every operand triple of a tabulated format in every
direction, restricted to first operands `left` with `left % shardCount = shardIndex`.
-/
def fmaShardFailures {fmt : FloatFormat} (grid : Grid) (values : Array (Model fmt))
    (operands : Array Operand) (shardIndex shardCount : Nat) : Nat :=
  Id.run do
    let mut failures := 0
    for mode in Model.IEEERoundingMode.all do
      for left in [0:values.size] do
        if left % shardCount == shardIndex then
          for right in [0:values.size] do
            for addend in [0:values.size] do
              let expected :=
                grid.fma mode operands[left]! operands[right]! operands[addend]!
              failures := failures + failureCount
                (agrees
                    (Model.fma values[left]! values[right]! values[addend]! (mode := mode)
                        (status := true))
                  expected)
    return failures

/--
The opt-in exhaustive fused multiply-add campaign: every operand triple of `ieee 4 3` and of E5M2
in every direction, 201,326,592 cases in all, split into `shardCount` shards by the first
operand. `check fma-exhaustive SHARD_INDEX SHARD_COUNT` runs one shard.
-/
def exhaustiveFmaFailures (shardIndex shardCount : Nat) : Nat :=
  fmaShardFailures ieee43 ieee43Values ieee43Operands shardIndex shardCount +
    fmaShardFailures e5m2 e5m2Values e5m2Operands shardIndex shardCount

/-- Count disagreements of the casts of every source encoding in every direction. -/
def castFailures (source destination : Grid) : Nat :=
  Model.IEEERoundingMode.all.foldl (init := 0) fun failures mode =>
    failures + countWhereFailures (List.range (2 * source.signBit)) fun bits =>
      agrees
        (Model.cast source.fmt destination.fmt
          (Model.ofNatBits (fmt := source.fmt) bits) mode (status := true))
        (destination.cast mode (source.decode bits))

/-- Narrowing casts of every binary16 encoding to `ieee 4 3`. -/
def narrowingIeee43Failures : Thunk Nat := ⟨fun _ => castFailures binary16 ieee43⟩

/-- Narrowing casts of every binary16 encoding to E5M2. -/
def narrowingE5M2Failures : Thunk Nat := ⟨fun _ => castFailures binary16 e5m2⟩

/-- Exact widening casts of every `ieee 4 3` and E5M2 encoding to binary16. -/
def wideningFailures : Thunk Nat := ⟨fun _ =>
  castFailures ieee43 binary16 + castFailures e5m2 binary16⟩

/-! ## Named vectors -/

/-- Whether an `ieee 4 3` outcome has these bits, flags, and ternary value. -/
def deliversIeee43 (outcome : Model.IEEEOutcome ieee43Format) (bits : Nat)
    (status : FloatLib.Numerics.IEEEStatus) (ternary : Ordering) : Bool :=
  outcome.value.toNatBits == bits && outcome.status == status && outcome.ternary == ternary

/-- The `ieee 4 3` value with these bits. -/
@[inline] def ieee43Value (bits : Nat) : Model ieee43Format :=
  Model.ofNatBits (fmt := ieee43Format) bits

/--
Named vectors in `ieee 4 3`, whose least subnormal is `2^-9` (bits `0x01`), whose one is `0x38`,
and whose largest finite value is `240` (bits `0x77`).
-/
def namedFailures : Thunk Nat := ⟨fun _ =>
  let one := ieee43Value 0x38
  let half := ieee43Value 0x30
  let minSubnormal := ieee43Value 0x01
  let negativeMinSubnormal := ieee43Value 0x81
  let largest := ieee43Value 0x77
  let negativeLargest := ieee43Value 0xf7
  let sixteenth := ieee43Value 0x18
  let negativeOne := ieee43Value 0xb8
  let positiveZero := ieee43Value 0x00
  let negativeZero := ieee43Value 0x80
  let tinyInexact : FloatLib.Numerics.IEEEStatus := { underflow := true, inexact := true }
  let overflowInexact : FloatLib.Numerics.IEEEStatus := { overflow := true, inexact := true }
  let twoAndHalf := Model.ofNatBits (fmt := FloatFormat.binary32) 0x40200000
  let negativeTwoAndHalf := Model.ofNatBits (fmt := FloatFormat.binary32) 0xc0200000
  countFailures
    [ -- Rounding away from zero takes half the least subnormal up to it, for both signs.
      deliversIeee43 (Model.mul minSubnormal half (mode := .away) (status := true)) 0x01
          tinyInexact .gt
    , deliversIeee43 (Model.mul negativeMinSubnormal half (mode := .away) (status := true)) 0x81
        tinyInexact .lt
      -- It carries a magnitude past the largest finite value to infinity, for both signs.
    , deliversIeee43 (Model.add largest minSubnormal (mode := .away) (status := true)) 0x78
        overflowInexact .gt
    , deliversIeee43
        (Model.add negativeLargest negativeMinSubnormal (mode := .away) (status := true))
        0xf8 overflowInexact .lt
      -- `1 + 1/16` is halfway between `1` and `1 + 1/8`.
    , deliversIeee43 (Model.add one sixteenth (mode := .nearestAway) (status := true)) 0x39
        { inexact := true }
        .gt
    , deliversIeee43 (Model.add one sixteenth (mode := .nearest) (status := true)) 0x38
        { inexact := true }
        .lt
      -- Half the least subnormal rounds to it under ties away, and to zero under ties to even.
    , deliversIeee43 (Model.mul minSubnormal half (mode := .nearestAway) (status := true)) 0x01
        tinyInexact .gt
    , deliversIeee43 (Model.mul minSubnormal half (mode := .nearest) (status := true)) 0x00
        tinyInexact .lt
      -- Exact cancellation and mixed zeros give positive zero under `.nearestAway` and `.away`.
    , deliversIeee43 (Model.add positiveZero negativeZero (mode := .nearestAway) (status := true))
        0x00 {} .eq
    , deliversIeee43 (Model.add positiveZero negativeZero (mode := .away) (status := true))
        0x00 {} .eq
    , deliversIeee43 (Model.add one negativeOne (mode := .nearestAway) (status := true)) 0x00 {} .eq
    , deliversIeee43 (Model.add one negativeOne (mode := .away) (status := true)) 0x00 {} .eq
    , deliversIeee43 (Model.add negativeZero negativeZero (mode := .away) (status := true))
        0x80 {} .eq
      -- Integral rounding with ties away from zero, and the integer conversion built on it.
    , Model.roundToIntegral twoAndHalf .nearestAway ==
        Model.ofNatBits (fmt := FloatFormat.binary32) 0x40400000
    , Model.roundToIntegral negativeTwoAndHalf .nearestAway ==
        Model.ofNatBits (fmt := FloatFormat.binary32) 0xc0400000
    , Model.roundToIntegral twoAndHalf .nearest ==
        Model.ofNatBits (fmt := FloatFormat.binary32) 0x40000000
    , Model.roundToIntegral twoAndHalf .away ==
        Model.ofNatBits (fmt := FloatFormat.binary32) 0x40400000
    , Model.roundToIntegral (Model.ofNatBits (fmt := FloatFormat.binary32) 0xc0000001)
        .away == Model.ofNatBits (fmt := FloatFormat.binary32) 0xc0400000
    , match ExecDType.floatToInt (width := 8) twoAndHalf .nearestAway with
      | .success value status =>
          FloatLib.Numerics.Representations.FixedInt.toInt value == 3 && status.inexact
      | .failure _ => false
    , match ExecDType.floatToInt (width := 8) negativeTwoAndHalf .nearestAway with
      | .success value status =>
          FloatLib.Numerics.Representations.FixedInt.toInt value == -3 && status.inexact
      | .failure _ => false
    , match ExecDType.floatToInt (width := 8) twoAndHalf .nearest with
      | .success value _ => FloatLib.Numerics.Representations.FixedInt.toInt value == 2
      | .failure _ => false
    ]⟩

/--
Whether casting the binary16 encoding `bits` to `ieee 4 3` delivers these bits, flags, and ternary
value.
-/
def castDelivers (bits : Nat) (mode : Model.IEEERoundingMode) (expected : Nat)
    (status : FloatLib.Numerics.IEEEStatus) (ternary : Ordering) : Bool :=
  deliversIeee43
    (Model.cast FloatFormat.binary16 ieee43Format
      (Model.ofNatBits (fmt := FloatFormat.binary16) bits) mode (status := true))
    expected status ternary

/--
Named boundary vectors around the smallest normal value `N = 2^-6` of `ieee 4 3` (bits `0x08`),
whose least subnormal is `h = 2^-9`, given as exact binary16 inputs. With an unbounded exponent the
grid just below `N` has spacing `h/2`, so nearest-away rounding is tiny below `N - h/4` and rounding
away from zero is tiny up to `N - h/2`, although both deliver `N` on the bounded grid. The vectors
also cover an exact subnormal, the overflow midpoint of E4M3FN, whose largest significand is even,
and saturation in the fully finite E2M1.
-/
def boundaryFailures : Thunk Nat := ⟨fun _ =>
  let tinyInexact : FloatLib.Numerics.IEEEStatus := { underflow := true, inexact := true }
  let inexact : FloatLib.Numerics.IEEEStatus := { inexact := true }
  let overflowInexact : FloatLib.Numerics.IEEEStatus := { overflow := true, inexact := true }
  let e4 := FloatFormat.e4m3fn
  let e4Largest := Model.ofNatBits (fmt := e4) 0x7e
  let e4Sixteen := Model.ofNatBits (fmt := e4) 0x58
  let e4MinSubnormal := Model.ofNatBits (fmt := e4) 0x01
  let e2 := FloatFormat.e2m1
  let e2Largest := Model.ofNatBits (fmt := e2) 0x7
  let e2Half := Model.ofNatBits (fmt := e2) 0x1
  let e2One := Model.ofNatBits (fmt := e2) 0x2
  let delivers {fmt : FloatFormat} (outcome : Model.IEEEOutcome fmt) (bits : Nat)
      (status : FloatLib.Numerics.IEEEStatus) (ternary : Ordering) : Bool :=
    outcome.value.toNatBits == bits && outcome.status == status && outcome.ternary == ternary
  countFailures
    [ -- `N - h/4` (binary16 `0x23c0`) is the nearest midpoint itself: not tiny.
      castDelivers 0x23c0 .nearestAway 0x08 inexact .gt
    , castDelivers 0x23c0 .nearest 0x08 inexact .gt
    , castDelivers 0x23c0 .away 0x08 inexact .gt
      -- `N - 3h/8` (`0x23a0`) delivers `N` but is tiny under both nearest modes.
    , castDelivers 0x23a0 .nearestAway 0x08 tinyInexact .gt
    , castDelivers 0xa3a0 .nearestAway 0x88 tinyInexact .lt
    , castDelivers 0x23a0 .away 0x08 inexact .gt
      -- `N - h/2` (`0x2380`) lies on the unbounded grid below `N`: tiny in every direction.
    , castDelivers 0x2380 .nearestAway 0x08 tinyInexact .gt
    , castDelivers 0x2380 .away 0x08 tinyInexact .gt
    , castDelivers 0xa380 .away 0x88 tinyInexact .lt
    , castDelivers 0x2380 .towardZero 0x07 tinyInexact .lt
      -- The least subnormal `2^-9` (`0x1800`) is exact: no underflow.
    , castDelivers 0x1800 .nearestAway 0x01 {} .eq
    , castDelivers 0x1800 .away 0x01 {} .eq
      -- E4M3FN: `448 + 16` is the overflow midpoint. Ties away overflow to the NaN pattern, which
      -- takes the sign of the exact value. Ties to even keep 448, whose significand 14 is even.
    , delivers (Model.add e4Largest e4Sixteen (mode := .nearestAway) (status := true)) 0x7f
        overflowInexact .gt
    , delivers (Model.add e4Largest e4Sixteen (mode := .nearest) (status := true)) 0x7e inexact .lt
    , delivers (Model.add e4Largest e4MinSubnormal (mode := .away) (status := true)) 0x7f
        overflowInexact
        .gt
    , delivers (Model.add e4Largest e4MinSubnormal (mode := .towardZero) (status := true)) 0x7e
        inexact .lt
      -- E2M1 has no infinity or NaN, and its overflow value is its largest value 6. Rounding
      -- `6 + 1/2` away from zero overflows. To nearest it stays at 6, and `6 + 1` is the overflow
      -- midpoint, which ties away from zero overflow. Each saturated 6 lies below the sum.
    , delivers (Model.add e2Largest e2Half (mode := .away) (status := true)) 0x7 overflowInexact .lt
    , delivers (Model.add e2Largest e2Half (mode := .nearestAway) (status := true)) 0x7 inexact .lt
    , delivers (Model.add e2Largest e2One (mode := .nearestAway) (status := true)) 0x7
        overflowInexact .lt
    ]⟩

/-! ## Bare mode names -/

open FloatLib.Rounding in
/-- After `open FloatLib.Rounding`, `(mode := up)` names `IEEERoundingMode.up`. -/
example (x : Model FloatFormat.binary32) :
    Model.sqrt x (mode := up) = Model.sqrt x (mode := .up) ∧
      (Model.sqrt x (mode := up) (status := true)).value = Model.sqrt x (mode := .up) :=
  ⟨rfl, Model.value_sqrt x .up⟩

open FloatLib.Rounding in
/--
With the bare names open, a pattern spelled `up` is the constructor `IEEERoundingMode.up`, not a
fresh variable, so this match sends `.down` to its last arm. Bind such values under other names,
and keep the `open` as narrow as `open ... in`.
-/
example : (match Model.IEEERoundingMode.down with | up => true | _ => false) = false := rfl

open FloatLib.Rounding in
/-- The open also names the mode type, so a definition can take a direction as a parameter. -/
example (mode : IEEERoundingMode) (x : Model FloatFormat.binary32) :
    Model.sqrt x (mode := mode) = Model.sqrt x (mode := (mode : Model.IEEERoundingMode)) := rfl

/-- `toString` prints the constructor names, while `name` keeps the interchange-file spellings. -/
example :
    Model.IEEERoundingMode.all.map toString =
        ["nearest", "nearestAway", "towardZero", "up", "down", "away"] ∧
      Model.IEEERoundingMode.all.map Model.IEEERoundingMode.name =
        ["nearestEven", "nearestAway", "towardZero", "towardPositive", "towardNegative",
          "awayFromZero"] := by
  decide

set_option linter.constructorNameAsVariable false in
/-- Without the open, the same spelling binds a variable that matches every mode. -/
example : (match Model.IEEERoundingMode.down with | up => up) = .down := rfl

/-- Partial application keeps the default options of a one-name operation. -/
example (xs : List (Model FloatFormat.binary32)) :
    xs.map Model.sqrt = xs.map (fun x => Model.sqrt x (mode := .nearest)) := rfl

/-- A symbolic `status` determines the result type by cases. -/
example (x y : Model FloatFormat.binary32) (status : Bool) :
    Model.add x y (mode := .down) (status := status) =
      match status with
      | true => Model.add x y (mode := .down) (status := true)
      | false => Model.add x y (mode := .down) := by
  cases status <;> rfl

/-! ## Report -/

/-- Named failure counters for the rounding-direction checks. -/
def failureRows : Thunk (List (String × Nat)) := ⟨fun _ =>
  [ ("addPairs", addFailures.get)
  , ("subPairs", subFailures.get)
  , ("mulPairs", mulFailures.get)
  , ("divPairs", divFailures.get)
  , ("sqrtInputs", sqrtFailures.get)
  , ("fmaTriples", fmaFailures.get)
  , ("narrowingToIeee43", narrowingIeee43Failures.get)
  , ("narrowingToE5M2", narrowingE5M2Failures.get)
  , ("wideningToBinary16", wideningFailures.get)
  , ("customBias", customBiasFailures.get)
  , ("namedVectors", namedFailures.get)
  , ("boundaryVectors", boundaryFailures.get)
  ]⟩

/-- Aggregate failure count for the rounding-direction checks. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  namedFailureTotal failureRows.get⟩

/-- Human-readable report. Every row should be zero. -/
def report : Thunk String := ⟨fun _ =>
  renderFailureReport failureRows.get⟩

end FloatLibTests.Regression.BinaryInterchange.RoundingDirections
