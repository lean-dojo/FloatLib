/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Functions.Recommended.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime
public meta import FloatLib.Floats.Formats.P3109.Functions.Recommended.Runtime
public meta import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime

/-!
# The functions of IEEE 754-2019 clause 9.2 on P3109 formats

`identityCases` compare the functions of `Functions.Recommended` with the operations of the
P3109 report that compute the same real function, on every word of Binary8p3se and of
Binary8p4se and in six rounding modes: `Rootn x 2` is `Sqrt x`, `Rootn x (-2)` is `RSqrt x`,
`Pown x 2` and `Pow x 2` are `Multiply x x`, `Pown x (-1)` and `Pow x (-1)` are `Recip x`,
`Pow x (1/2)` and `Powr x (1/2)` are `Sqrt x` (except `Pow (-∞) (1/2)`, which is `+∞`),
`Pow 2 x` and `Powr 2 x` are `Exp2 x`, and `Pown x 1` and `Rootn x 1` return the operand. Each
side rounds its exact value once, so the words agree. `specialCases` are the results at zeros,
infinities, NaN and outside the domains, and exact values. Compiled evaluation checks both
lists when this module is elaborated. The values at ordinary operands are compared with MPFR by
`tests/oracles/p3109_functions.py`.

The second half applies the theorems, which hold for independent source and target formats,
every rounding mode and every saturation mode.
-/

@[expose] public section

namespace FloatLibTests.Conformance.P3109.RecommendedFunctions

open FloatLib.Numerics FloatLib.Floats
open Formats.P3109 ExecFloat.P3109

/-- The six deterministic rounding modes. -/
def modes : List RoundingMode := [.nearest, .nearestAway, .towardZero, .up, .down, .toOdd]

/-- The word of `format` with the exact value `value`, or the NaN word when there is none. -/
def wordOf (format : Format) (value : Rat) : ExecFloat.P3109 format :=
  match (List.range (2 ^ format.bitWidth)).find? fun word =>
      (ExecFloat.P3109.ofNatBits (format := format) word).toClosedRat == .finite value with
  | some word => ExecFloat.P3109.ofNatBits word
  | none => ExecFloat.P3109.nan

/-- Whether two results are the same word. -/
def same {format : Format} (left right : ExecFloat.P3109 format) : Bool :=
  left.toNatBits == right.toNatBits

/-- The identities with the operations of the report, on every word of a format. -/
def identityCasesOn (name : String) (format : Format) : List (String × Bool) :=
  let two := wordOf format 2
  let half := wordOf format (1 / 2)
  let minusOne := wordOf format (-1)
  (List.range (2 ^ format.bitWidth)).flatMap fun word =>
    let x : ExecFloat.P3109 format := ExecFloat.P3109.ofNatBits word
    modes.flatMap fun mode =>
      [(s!"{name} word {word}: Rootn x 2 is Sqrt x",
          same (Rootn x 2 format mode) (Sqrt x format mode)),
        (s!"{name} word {word}: Rootn x (-2) is RSqrt x",
          same (Rootn x (-2) format mode) (RSqrt x format mode)),
        (s!"{name} word {word}: Cbrt x is Rootn x 3",
          same (Cbrt x format mode) (Rootn x 3 format mode)),
        (s!"{name} word {word}: Pown x 2 is Multiply x x",
          same (Pown x 2 format mode) (Multiply x x format mode)),
        (s!"{name} word {word}: Pown x (-1) is Recip x",
          same (Pown x (-1) format mode) (Recip x format mode)),
        (s!"{name} word {word}: Pow x 2 is Multiply x x",
          same (Pow x two format mode) (Multiply x x format mode)),
        (s!"{name} word {word}: Pow x (-1) is Recip x",
          same (Pow x minusOne format mode) (Recip x format mode)),
        (s!"{name} word {word}: Pow x (1/2) is Sqrt x, except at -inf, where it is +inf",
          if x.toClosedRat == .infinity true then
            (Pow x half format mode).toClosedRat == .infinity false
          else same (Pow x half format mode) (Sqrt x format mode)),
        (s!"{name} word {word}: Powr x (1/2) is Sqrt x",
          same (Powr x half format mode) (Sqrt x format mode)),
        (s!"{name} word {word}: Pow 2 x is Exp2 x",
          same (Pow two x format mode) (Exp2 x format mode)),
        (s!"{name} word {word}: Powr 2 x is Exp2 x",
          same (Powr two x format mode) (Exp2 x format mode)),
        (s!"{name} word {word}: Pown x 1 is x", same (Pown x 1 format mode) x),
        (s!"{name} word {word}: Rootn x 1 is x", same (Rootn x 1 format mode) x)]

/-- The identities on Binary8p3se and Binary8p4se. -/
def identityCases : List (String × Bool) :=
  identityCasesOn "Binary8p3se" Format.binary8p3se ++
    identityCasesOn "Binary8p4se" Format.binary8p4se

/-- The special cases and exact values on Binary8p3se. -/
def specialCases : List (String × Bool) :=
  let f := Format.binary8p3se
  let value (q : Rat) : ExecFloat.P3109 f := wordOf f q
  let nan : ExecFloat.P3109 f := ExecFloat.P3109.nan
  let posInf : ExecFloat.P3109 f := ExecFloat.P3109.positiveInfinity
  let negInf : ExecFloat.P3109 f := ExecFloat.P3109.negativeInfinity
  [ ("Exp10 0 is 1", same (Exp10 (value 0)) (value 1)),
    ("Exp10 1 is 10", same (Exp10 (value 1)) (value 10)),
    ("Exp10 (-inf) is 0", same (Exp10 negInf) (value 0)),
    ("Exp10 (+inf) is +inf", same (Exp10 posInf) posInf),
    ("Exp10 NaN is NaN", same (Exp10 nan) nan),
    ("Exp2MinusOne 0 is 0", same (Exp2MinusOne (value 0)) (value 0)),
    ("Exp2MinusOne 1 is 1", same (Exp2MinusOne (value 1)) (value 1)),
    ("Exp2MinusOne (-inf) is -1", same (Exp2MinusOne negInf) (value (-1))),
    ("Exp10MinusOne 0 is 0", same (Exp10MinusOne (value 0)) (value 0)),
    ("Exp10MinusOne (-inf) is -1", same (Exp10MinusOne negInf) (value (-1))),
    ("Log10 1 is 0", same (Log10 (value 1)) (value 0)),
    ("Log10 10 is 1", same (Log10 (value 10)) (value 1)),
    ("Log10 0 is -inf", same (Log10 (value 0)) negInf),
    ("Log10 (-1) is NaN", same (Log10 (value (-1))) nan),
    ("Log10 (+inf) is +inf", same (Log10 posInf) posInf),
    ("Log10 (-inf) is NaN", same (Log10 negInf) nan),
    ("Log2OnePlus 1 is 1", same (Log2OnePlus (value 1)) (value 1)),
    ("Log2OnePlus 3 is 2", same (Log2OnePlus (value 3)) (value 2)),
    ("Log2OnePlus (-1) is -inf", same (Log2OnePlus (value (-1))) negInf),
    ("Log2OnePlus (-2) is NaN", same (Log2OnePlus (value (-2))) nan),
    ("Log10OnePlus 0 is 0", same (Log10OnePlus (value 0)) (value 0)),
    ("Log10OnePlus (-1) is -inf", same (Log10OnePlus (value (-1))) negInf),
    ("Cbrt 8 is 2", same (Cbrt (value 8)) (value 2)),
    ("Cbrt (-8) is -2", same (Cbrt (value (-8))) (value (-2))),
    ("Cbrt 0 is 0", same (Cbrt (value 0)) (value 0)),
    ("Cbrt (-inf) is -inf", same (Cbrt negInf) negInf),
    ("Rootn 4 0 is NaN", same (Rootn (value 4) 0) nan),
    ("Rootn (-4) 2 is NaN", same (Rootn (value (-4)) 2) nan),
    ("Rootn 0 (-3) is NaN", same (Rootn (value 0) (-3)) nan),
    ("Rootn (-8) (-3) is -1/2", same (Rootn (value (-8)) (-3)) (value (-1 / 2))),
    ("Rootn (-inf) 2 is NaN", same (Rootn negInf 2) nan),
    ("Rootn (+inf) (-2) is 0", same (Rootn posInf (-2)) (value 0)),
    ("Pown 2 3 is 8", same (Pown (value 2) 3) (value 8)),
    ("Pown (-2) 3 is -8", same (Pown (value (-2)) 3) (value (-8))),
    ("Pown 0 0 is 1", same (Pown (value 0) 0) (value 1)),
    ("Pown (+inf) 0 is 1", same (Pown posInf 0) (value 1)),
    ("Pown NaN 0 is NaN", same (Pown nan 0) nan),
    ("Pown 0 (-2) is NaN", same (Pown (value 0) (-2)) nan),
    ("Pown (-inf) 3 is -inf", same (Pown negInf 3) negInf),
    ("Pown (-inf) 2 is +inf", same (Pown negInf 2) posInf),
    ("Pown (-inf) (-3) is 0", same (Pown negInf (-3)) (value 0)),
    ("Pow 2 3 is 8", same (Pow (value 2) (value 3)) (value 8)),
    ("Pow (-2) 3 is -8", same (Pow (value (-2)) (value 3)) (value (-8))),
    ("Pow (-2) 2 is 4", same (Pow (value (-2)) (value 2)) (value 4)),
    ("Pow (-2) (1/2) is NaN", same (Pow (value (-2)) (value (1 / 2))) nan),
    ("Pow 0 0 is 1", same (Pow (value 0) (value 0)) (value 1)),
    ("Pow 0 (-1) is NaN", same (Pow (value 0) (value (-1))) nan),
    ("Pow 0 (-inf) is +inf", same (Pow (value 0) negInf) posInf),
    ("Pow (1/2) (+inf) is 0", same (Pow (value (1 / 2)) posInf) (value 0)),
    ("Pow (-1) (+inf) is 1", same (Pow (value (-1)) posInf) (value 1)),
    ("Pow 2 (+inf) is +inf", same (Pow (value 2) posInf) posInf),
    ("Pow (-inf) 3 is -inf", same (Pow negInf (value 3)) negInf),
    ("Pow (-inf) 2 is +inf", same (Pow negInf (value 2)) posInf),
    ("Pow (-inf) (-1) is 0", same (Pow negInf (value (-1))) (value 0)),
    ("Pow (+inf) 0 is 1", same (Pow posInf (value 0)) (value 1)),
    ("Pow NaN 0 is NaN", same (Pow nan (value 0)) nan),
    ("Powr (-2) 2 is NaN", same (Powr (value (-2)) (value 2)) nan),
    ("Powr 0 0 is NaN", same (Powr (value 0) (value 0)) nan),
    ("Powr 0 2 is 0", same (Powr (value 0) (value 2)) (value 0)),
    ("Powr 1 (+inf) is NaN", same (Powr (value 1) posInf) nan),
    ("Powr (+inf) 0 is NaN", same (Powr posInf (value 0)) nan),
    ("Powr (+inf) (-1) is 0", same (Powr posInf (value (-1))) (value 0)),
    ("Compound 1 3 is 8", same (Compound (value 1) 3) (value 8)),
    ("Compound (-1) 2 is 0", same (Compound (value (-1)) 2) (value 0)),
    ("Compound (-1) 0 is 1", same (Compound (value (-1)) 0) (value 1)),
    ("Compound (-1) (-1) is NaN", same (Compound (value (-1)) (-1)) nan),
    ("Compound (-2) 2 is NaN", same (Compound (value (-2)) 2) nan),
    ("Compound (+inf) (-2) is 0", same (Compound posInf (-2)) (value 0)),
    ("Compound (-inf) 2 is NaN", same (Compound negInf 2) nan) ]

#eval show IO Unit from do
  let failures := (identityCases ++ specialCases).filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"cases that fail: {(failures.map (·.1)).take 20}"
  IO.println <| s!"{identityCases.length} identities with the operations of the report hold, " ++
    s!"and {specialCases.length} special cases"

/-! ## The theorems -/

example {format : Format} (input : ExecFloat.P3109 format) (degree : Int) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Rootn input degree target mode saturation))
      (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
        (Formats.P3109.Functions.root degree input.toClosedRat)) :=
  decode_Rootn input degree target mode saturation

example {format exponentFormat : Format} (base : ExecFloat.P3109 format)
    (exponent : ExecFloat.P3109 exponentFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (Pow base exponent target mode saturation))
      (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
        (Formats.P3109.Functions.power base.toClosedRat exponent.toClosedRat)) :=
  decode_Pow base exponent target mode saturation

example {format : Format} (input : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Exp10 input target mode saturation))
      (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
        (Formats.P3109.Functions.exponential 10 (by decide) false input.toClosedRat)) :=
  decode_Exp10 input target mode saturation

example (x y : Rat) (hx : 0 < x) :
    ∃ expression, Formats.P3109.Functions.power (.finite x) (.finite y) = .finite expression ∧
      expression.toReal = (x : ℝ) ^ (y : ℝ) :=
  Formats.P3109.Functions.power_of_pos hx y

example (x : Rat) (hx : x < 0) :
    ∃ expression, Formats.P3109.Functions.root 3 (.finite x) = .finite expression ∧
      expression.toReal = -((-x : ℝ) ^ (((3 : Int) : ℝ)⁻¹)) :=
  Formats.P3109.Functions.root_of_neg (by decide) hx

/-- The other exponentials and logarithms, the cube root, `Pown`, `Powr` and `Compound` are one
projection of their reference value too. -/
example {format exponentFormat : Format} (input : ExecFloat.P3109 format)
    (exponent : ExecFloat.P3109 exponentFormat) (n : Int) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Exp2MinusOne input target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.exponential 2 (by decide) true input.toClosedRat)) ∧
      Format.SameDatum (decode (Exp10MinusOne input target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.exponential 10 (by decide) true input.toClosedRat)) ∧
      Format.SameDatum (decode (Log10 input target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.logarithmIn 10 (by decide) 0 input.toClosedRat)) ∧
      Format.SameDatum (decode (Log2OnePlus input target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.logarithmIn 2 (by decide) 1 input.toClosedRat)) ∧
      Format.SameDatum (decode (Log10OnePlus input target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.logarithmIn 10 (by decide) 1 input.toClosedRat)) ∧
      Format.SameDatum (decode (Cbrt input target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.root 3 input.toClosedRat)) ∧
      Format.SameDatum (decode (Pown input n target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.integerPower n input.toClosedRat)) ∧
      Format.SameDatum (decode (Powr input exponent target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.positivePower input.toClosedRat exponent.toClosedRat)) ∧
      Format.SameDatum (decode (Compound input n target mode saturation))
        (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
          (Formats.P3109.Functions.compound n input.toClosedRat)) :=
  ⟨decode_Exp2MinusOne input target mode saturation,
    decode_Exp10MinusOne input target mode saturation, decode_Log10 input target mode saturation,
    decode_Log2OnePlus input target mode saturation,
    decode_Log10OnePlus input target mode saturation, decode_Cbrt input target mode saturation,
    decode_Pown input n target mode saturation, decode_Powr input exponent target mode saturation,
    decode_Compound input n target mode saturation⟩

/-- The reference values at finite operands in the domains are the real functions. -/
example (x y : Rat) (n : Int) (hx : 0 < x) (hn : n ≠ 0) :
    (∃ expression, Formats.P3109.Functions.exponential 10 (by decide) true (.finite y) =
        .finite expression ∧ expression.toReal = ((10 : Rat) : ℝ) ^ (y : ℝ) - 1) ∧
      (∃ expression, Formats.P3109.Functions.logarithmIn 10 (by decide) 0 (.finite x) =
        .finite expression ∧ expression.toReal = Real.logb (10 : Rat) ((x : ℝ) + (0 : Rat))) ∧
      (∃ expression, Formats.P3109.Functions.root n (.finite x) = .finite expression ∧
        expression.toReal = (x : ℝ) ^ ((n : ℝ)⁻¹)) ∧
      (∃ expression, Formats.P3109.Functions.integerPower n (.finite x) = .finite expression ∧
        expression.toReal = (x : ℝ) ^ n) ∧
      (∃ expression, Formats.P3109.Functions.power (.finite (-x)) (.finite (n : Rat)) =
        .finite expression ∧ expression.toReal = ((-x : Rat) : ℝ) ^ n) ∧
      (∃ expression, Formats.P3109.Functions.positivePower (.finite x) (.finite y) =
        .finite expression ∧ expression.toReal = (x : ℝ) ^ (y : ℝ)) ∧
      (∃ expression, Formats.P3109.Functions.compound n (.finite x) = .finite expression ∧
        expression.toReal = (1 + (x : ℝ)) ^ n) :=
  ⟨by simpa using Formats.P3109.Functions.exponential_finite 10 (by decide) true y,
    Formats.P3109.Functions.logarithmIn_of_pos 10 (by decide) 0 (by simpa using hx),
    Formats.P3109.Functions.root_of_pos hn hx,
    Formats.P3109.Functions.integerPower_of_ne_zero n hx.ne',
    Formats.P3109.Functions.power_of_neg (neg_lt_zero.mpr hx) n,
    Formats.P3109.Functions.positivePower_of_pos hx y,
    Formats.P3109.Functions.compound_of_gt n (by linarith)⟩

end FloatLibTests.Conformance.P3109.RecommendedFunctions
