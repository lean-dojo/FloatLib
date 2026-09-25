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
FloatLib operations have reference semantics and refinement proofs. Explicit calls through
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
open FloatLib.Floats.Formats.BinaryInterchange

/-! ## Choose the types -/

/-- FloatLib's IEEE binary32 configuration. -/
abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/-- FloatLib's IEEE binary64 configuration. -/
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

/-- A 32-bit posit as defined by the Posit Standard (2022). -/
abbrev Posit32 :=
  ExecFloat.Posit (bits := 32)

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
type `Float`; `Binary64` is the FloatLib type with the same layout. The native types print with
six decimals, FloatLib types print their exact stored value.
-/

/-! ## Convert when another API expects a different type -/

-- These functions preserve finite native values through their IEEE interchange words.
-- Native conversion canonicalizes NaNs; use the `ofBits32`/`toBits32` API for stored payloads.
example (value : Float32) : Binary32 :=
  ExecFloat.Binary.ofFloat32 value

-- For example, a foreign function may require a native `Float32` argument.
example (value : Binary32) : Float32 :=
  ExecFloat.Binary.toFloat32 value

-- A cast between FloatLib formats names its destination and returns an outcome carrying the
-- value and its conversion status, or an explicit failure. `value?` keeps just the value.
example (value : Binary32) : ExecFloat.ConversionOutcome Posit32 :=
  value.cast (target := Posit32)

/-! ## Compare the exact values produced by rounding -/

private def third (rounding : Model.IEEERoundingMode) : Binary32 :=
  ExecFloat.Binary.divWithRounding 1 3 (rounding := rounding)
-- third .nearestEven = 11184811 * 2^-25
-- third .towardZero = 5592405 * 2^-24
-- third .towardPositiveInfinity = 11184811 * 2^-25
-- third .towardNegativeInfinity = 5592405 * 2^-24

/-
One third lies between two binary32 neighbours, 0.33333331 below and 0.33333334 above. Nearest-even
and toward `+∞` choose the upper one; toward zero and toward `-∞` choose the lower one, and they
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
  let modes : List (String × Model.IEEERoundingMode) :=
    [("nearest, ties to even", .nearestEven), ("toward zero", .towardZero),
     ("toward +infinity", .towardPositiveInfinity), ("toward -infinity", .towardNegativeInfinity)]
  for (label, mode) in modes do
    IO.println s!"  {label}: {third mode}"
  IO.println "  Nearest-even selects the upper neighbor for this input."

/-
String interpolation uses the shared `ToString` instance. Binary values and posits display exactly:
a short decimal when one is exact, otherwise an integer times a power of two. The formatters also
handle signed zero, infinities, NaNs, and NaR where the format has them.
-/

/-- Print the two calculations above. Run with `lake -d tests exe check example`. -/
def showComparison : IO Unit := do
  showArithmetic
  IO.println ""
  showRounding

end FloatLib.Examples.FormatComparison
