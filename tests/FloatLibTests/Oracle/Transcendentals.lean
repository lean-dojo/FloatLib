/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals

/-!
# Bounded transcendental comparison vectors

This standalone emitter evaluates FloatLib's deterministic binary32 and binary64 approximations
for `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, and `tanh`. Its tab-separated stream is consumed by
`tests/oracles/transcendental_compare.sh`.

The corpus combines named boundary and range-reduction inputs with two fixed-seed samples:

* central values span ordinary magnitudes around one;
* broad values cover the finite encoding space, including subnormals and extreme exponents.

These are comparison vectors, not conformance vectors. The current FloatLib kernels are
deterministic approximations and do not claim correct rounding.
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

private def Operation.all : Array Operation :=
  #[.exp, .log, .sin, .cos, .sinh, .cosh, .tanh]

private def Operation.label : Operation → String
  | .exp => "exp"
  | .log => "log"
  | .sin => "sin"
  | .cos => "cos"
  | .sinh => "sinh"
  | .cosh => "cosh"
  | .tanh => "tanh"

@[inline] private def Operation.apply {format : FloatFormat}
    (operation : Operation) (value : Model format) : Model format :=
  match operation with
  | .exp => Model.exp value
  | .log => Model.log value
  | .sin => Model.sin value
  | .cos => Model.cos value
  | .sinh => Model.sinh value
  | .cosh => Model.cosh value
  | .tanh => Model.tanh value

private structure InputCase where
  name : String
  bits : Nat

private def binary32Edges : Array InputCase :=
  #[
    ⟨"positive-zero", 0x00000000⟩,
    ⟨"negative-zero", 0x80000000⟩,
    ⟨"smallest-subnormal", 0x00000001⟩,
    ⟨"largest-subnormal", 0x007fffff⟩,
    ⟨"smallest-normal", 0x00800000⟩,
    ⟨"largest-finite", 0x7f7fffff⟩,
    ⟨"tiny-positive", 0x35800000⟩,
    ⟨"tiny-negative", 0xb5800000⟩,
    ⟨"quarter", 0x3e800000⟩,
    ⟨"negative-quarter", 0xbe800000⟩,
    ⟨"half", 0x3f000000⟩,
    ⟨"negative-half", 0xbf000000⟩,
    ⟨"below-one", 0x3f7fffff⟩,
    ⟨"one", 0x3f800000⟩,
    ⟨"above-one", 0x3f800001⟩,
    ⟨"negative-one", 0xbf800000⟩,
    ⟨"two", 0x40000000⟩,
    ⟨"negative-two", 0xc0000000⟩,
    ⟨"pi-over-six", 0x3f060a92⟩,
    ⟨"pi-over-four", 0x3f490fdb⟩,
    ⟨"pi-over-two", 0x3fc90fdb⟩,
    ⟨"pi", 0x40490fdb⟩,
    ⟨"negative-pi", 0xc0490fdb⟩,
    ⟨"two-pi", 0x40c90fdb⟩,
    ⟨"ten", 0x41200000⟩,
    ⟨"negative-ten", 0xc1200000⟩,
    ⟨"twenty", 0x41a00000⟩,
    ⟨"negative-twenty", 0xc1a00000⟩,
    ⟨"eighty", 0x42a00000⟩,
    ⟨"negative-eighty", 0xc2a00000⟩,
    ⟨"exp-overflow-neighborhood", 0x42b17218⟩,
    ⟨"exp-underflow-neighborhood", 0xc2cff1b5⟩,
    ⟨"two-to-20", 0x49800000⟩,
    ⟨"two-to-50", 0x58800000⟩,
    ⟨"positive-infinity", 0x7f800000⟩,
    ⟨"negative-infinity", 0xff800000⟩,
    ⟨"quiet-nan", 0x7fc00000⟩
  ]

private def binary64Edges : Array InputCase :=
  #[
    ⟨"positive-zero", 0x0000000000000000⟩,
    ⟨"negative-zero", 0x8000000000000000⟩,
    ⟨"smallest-subnormal", 0x0000000000000001⟩,
    ⟨"largest-subnormal", 0x000fffffffffffff⟩,
    ⟨"smallest-normal", 0x0010000000000000⟩,
    ⟨"largest-finite", 0x7fefffffffffffff⟩,
    ⟨"tiny-positive", 0x3eb0000000000000⟩,
    ⟨"tiny-negative", 0xbeb0000000000000⟩,
    ⟨"quarter", 0x3fd0000000000000⟩,
    ⟨"negative-quarter", 0xbfd0000000000000⟩,
    ⟨"half", 0x3fe0000000000000⟩,
    ⟨"negative-half", 0xbfe0000000000000⟩,
    ⟨"below-one", 0x3fefffffffffffff⟩,
    ⟨"one", 0x3ff0000000000000⟩,
    ⟨"above-one", 0x3ff0000000000001⟩,
    ⟨"negative-one", 0xbff0000000000000⟩,
    ⟨"two", 0x4000000000000000⟩,
    ⟨"negative-two", 0xc000000000000000⟩,
    ⟨"pi-over-six", 0x3fe0c152382d7365⟩,
    ⟨"pi-over-four", 0x3fe921fb54442d18⟩,
    ⟨"pi-over-two", 0x3ff921fb54442d18⟩,
    ⟨"pi", 0x400921fb54442d18⟩,
    ⟨"negative-pi", 0xc00921fb54442d18⟩,
    ⟨"two-pi", 0x401921fb54442d18⟩,
    ⟨"ten", 0x4024000000000000⟩,
    ⟨"negative-ten", 0xc024000000000000⟩,
    ⟨"twenty", 0x4034000000000000⟩,
    ⟨"negative-twenty", 0xc034000000000000⟩,
    ⟨"hundred", 0x4059000000000000⟩,
    ⟨"negative-hundred", 0xc059000000000000⟩,
    ⟨"exp-overflow-neighborhood", 0x40862e42fefa39ef⟩,
    ⟨"exp-underflow-neighborhood", 0xc0874910d52d3050⟩,
    ⟨"two-to-20", 0x4130000000000000⟩,
    ⟨"two-to-50", 0x4310000000000000⟩,
    ⟨"two-to-100", 0x4630000000000000⟩,
    ⟨"positive-infinity", 0x7ff0000000000000⟩,
    ⟨"negative-infinity", 0xfff0000000000000⟩,
    ⟨"quiet-nan", 0x7ff8000000000000⟩
  ]

@[inline] private def nextState (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

private def centralInputs (format : FloatFormat) (seed : UInt64) (count : Nat) :
    Array InputCase := Id.run do
  let width := format.expWidth + format.fracWidth + 1
  let signShift := width - 1
  let fractionMask := 2 ^ format.fracWidth - 1
  let radius := Nat.min 12 (format.exponentBias - 1)
  let exponentCount := 2 * radius + 1
  let mut state := seed
  let mut result := #[]
  for index in [0:count] do
    state := nextState state
    let fraction := state.toNat &&& fractionMask
    state := nextState state
    let exponent := format.exponentBias - radius + state.toNat % exponentCount
    state := nextState state
    let sign := (state.toNat &&& 1) <<< signShift
    let bits := sign ||| (exponent <<< format.fracWidth) ||| fraction
    result := result.push ⟨s!"central-{index}", bits⟩
  return result

private def broadInputs (format : FloatFormat) (seed : UInt64) (count : Nat) :
    Array InputCase := Id.run do
  let width := format.expWidth + format.fracWidth + 1
  let widthMask := 2 ^ width - 1
  let exponentMask := (2 ^ format.expWidth - 1) <<< format.fracWidth
  let finiteExponentBit := 1 <<< format.fracWidth
  let mut state := seed
  let mut result := #[]
  for index in [0:count] do
    state := nextState state
    let raw := state.toNat &&& widthMask
    let bits :=
      if raw &&& exponentMask == exponentMask then
        raw ^^^ finiteExponentBit
      else
        raw
    result := result.push ⟨s!"broad-{index}", bits⟩
  return result

private def sampledInputs (format : FloatFormat) (seed : UInt64) (count : Nat) :
    Array InputCase :=
  let centralCount := (count + 1) / 2
  centralInputs format seed centralCount ++
    broadInputs format (nextState seed) (count - centralCount)

private def emitCase (formatName : String) (format : FloatFormat)
    (operation : Operation) (input : InputCase) : IO Unit := do
  let value := Model.ofNatBits (fmt := format) input.bits
  let result := operation.apply value
  IO.println <| String.intercalate "\t"
    [input.name, formatName, operation.label, toString input.bits, toString result.toNatBits]

private def emitFormat (formatName : String) (format : FloatFormat)
    (edges : Array InputCase) (seed : UInt64) (randomCount : Nat) : IO Unit := do
  let inputs := edges ++ sampledInputs format seed randomCount
  for operation in Operation.all do
    for input in inputs do
      emitCase formatName format operation input

private def usage : String :=
  "usage: transcendentalEmitter [RANDOM_CASES_PER_FORMAT]"

private def parseRandomCount : List String → IO Nat
  | [] => pure 32
  | [text] =>
      match text.toNat? with
      | some count =>
          if count ≤ 256 then
            pure count
          else
            throw <| IO.userError "random case count must be at most 256"
      | none => throw <| IO.userError s!"invalid random case count: {text}"
  | _ => throw <| IO.userError usage

/-- Emit deterministic FloatLib transcendental comparison vectors. -/
def run (args : List String) : IO UInt32 := do
  let randomCount ← parseRandomCount args
  IO.println "# case\tformat\top\tinput_bits\tfloatlib_bits"
  emitFormat "binary32" FloatFormat.binary32 binary32Edges 0x243f6a8885a308d3 randomCount
  emitFormat "binary64" FloatFormat.binary64 binary64Edges 0x13198a2e03707344 randomCount
  return 0

end FloatLibTests.Oracle.Transcendentals

public def main (args : List String) : IO UInt32 :=
  FloatLibTests.Oracle.Transcendentals.run args
