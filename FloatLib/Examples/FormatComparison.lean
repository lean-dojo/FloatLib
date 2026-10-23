/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats

/-!
# Native, IEEE, and posit arithmetic side by side

If we evaluate `((1.5 + 2.25) * 2) / 3` as a Lean `Float`, a `Float32`, a FloatLib binary64, a
FloatLib binary32, and a 32-bit posit, do we get the same answer? Yes, 2.5 in every case, because
every intermediate value is exactly representable. The interesting comparison is `1 / 3`, where
the formats and rounding directions disagree, and that is the second half of this file. Run the
printed comparison from the repository root with:

```bash
lake -d tests exe check example
```

Compiled arithmetic on Lean's builtin `Float` and `Float32` uses native runtime primitives.
FloatLib operations have reference semantics and refinement proofs. Opt-in calls through
`Configured.NativeFPU.Unchecked` also depend on the compiler, host FPU, and environment. Posit32
uses nearest-even rounding and has no selectable IEEE rounding mode.

References:

* IEEE 754-2019, <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* Posit Working Group, *Standard for Posit Arithmetic (2022)*,
  <https://posithub.org/docs/posit_standard-2.pdf>.
-/

public section

namespace FloatLib.Examples.FormatComparison

open FloatLib.Floats
open FloatLib.Rounding

/-! ## Evaluate the same expression -/

private def native64Result : Float :=
  ((1.5 + 2.25) * 2) / 3
-- 2.500000

private def native32Result : Float32 :=
  ((1.5 + 2.25) * 2) / 3
-- 2.500000

private def binary64Result : Binary64 :=
  ((1.5 + 2.25) * 2) / 3
-- 2.5

private def binary32Result : Binary32 :=
  ((1.5 + 2.25) * 2) / 3
-- 2.5

private def posit32Result : Posit32 :=
  ((1.5 + 2.25) * 2) / 3
-- 2.5

/-
Only the type annotation differs between these five definitions. Lean calls its native binary64
type `Float`, `Binary64` is the FloatLib type with the same layout, and `Binary32` and `Posit32`
are the standard names of the other two FloatLib formats. The native types print with six
decimals. FloatLib binary values print a decimal that reads back as their stored value, and posits
print their exact value.
-/

/-! ## Convert when another API expects a different type -/

-- These functions preserve finite native values through their IEEE interchange words.
-- Native conversion canonicalizes NaNs, so use the `ofBits32`/`toBits32` API for stored payloads.
example (value : Float32) : Binary32 :=
  ExecFloat.Binary.ofFloat32 value

-- For example, a foreign function may require a native `Float32` argument.
example (value : Binary32) : Float32 :=
  ExecFloat.Binary.toFloat32 value

-- A cast between FloatLib formats names its destination and returns an outcome carrying the
-- value and its conversion status, or a failure. `value?` keeps just the value.
example (value : Binary32) : ExecFloat.ConversionOutcome Posit32 :=
  value.cast (target := Posit32)

/-! ## Compare the exact values produced by rounding -/

private def third (mode : IEEERoundingMode) : Binary32 :=
  ExecFloat.Binary.div 1 3 (mode := mode)
-- third nearest = 0.33333334
-- third towardZero = 0.3333333
-- third up = 0.33333334
-- third down = 0.3333333

/-
One third lies between two binary32 neighbours, 0.3333333 below and 0.33333334 above. Nearest-even
and `up` choose the upper one. `towardZero` and `down` choose the lower one, and they
agree because the value is positive. In Posit32 the same quotient is `178956971 * 2^-29`, closer to
one third than either binary32 neighbour because a 32-bit posit has more fraction bits near one.
-/

private def showArithmetic : IO Unit := do
  IO.println "((1.5 + 2.25) * 2) / 3 = 2.5"
  IO.println s!"  Lean native Float (binary64): {native64Result}"
  IO.println s!"  Lean native Float32: {native32Result}"
  IO.println s!"  FloatLib binary64: {binary64Result}"
  IO.println s!"  FloatLib binary32: {binary32Result}"
  IO.println s!"  FloatLib Posit32: {posit32Result}"

private def showRounding : IO Unit := do
  IO.println "Binary32 1 / 3: exact stored values"
  let modes : List (String × IEEERoundingMode) :=
    [("nearest, ties to even", nearest), ("toward zero", towardZero),
     ("toward +infinity", up), ("toward -infinity", down)]
  for (label, mode) in modes do
    IO.println s!"  {label}: {third mode}"
  IO.println "  Nearest-even selects the upper neighbor for this input."

/-
String interpolation uses the shared `ToString` instance, so these lines print what `#eval`
prints: a round-trip decimal for binary values and the exact decimal for posits. The
formatters also handle signed zero, infinities, NaNs, and NaR where the format has them.
-/

/-- Print the two calculations above. Run with `lake -d tests exe check example`. -/
def showComparison : IO Unit := do
  showArithmetic
  IO.println ""
  showRounding

end FloatLib.Examples.FormatComparison
