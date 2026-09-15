/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core
public import FloatLib.Numerics.Capabilities.Elementary

/-!
# `NF`: a rounded scalar type

`FloatRep` (the record with a mantissa/exponent) is useful for *talking about the grid* and for
stating format predicates like `FLTFormat`. Higher-level specifications are easier to state with
a scalar carrier that already performs the rounding step.

`NF β fexp rnd` is that scalar carrier:

- it stores a semantic value `val : ℝ`,
- and every primitive arithmetic operation rounds back to the format using `round`.

The public constructor remains available because proof developments sometimes embed an arbitrary
real as a comparison value. Such a value need not be representable. `NF.IsRepresentable` records the
grid invariant when a theorem needs it; `NF.ofReal` and arithmetic results establish that invariant.

Addition, for example, satisfies:

`val(a + b) = round( val(a) + val(b) )`

This is the standard textbook model used for floating-point error analysis: compute in reals, then
incur a rounding error at each step (Higham/Goldberg style).

Trust boundary:
- `NF` and `FloatRep` model real values and rounding in Lean.
- Instantiating `NF` with IEEE single parameters + round-to-nearest-even models domain-valid,
  finite, no-overflow arithmetic with binary32's precision and gradual-underflow grid. The format
  has no upper exponent bound, and Mathlib's real division, square root, and logarithm are totalized;
  exceptional IEEE behavior belongs to
  `ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)` and its binary-interchange model.
- Correspondence to hardware float32 / Lean's builtin `Float` is not proved in this file; that
  connection is an external assumption/interface boundary (or requires a separate verified kernel).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

open FloatLib.Numerics

/--
Rounded scalar value at a given radix/format/rounding mode.

`β` is the radix (typically `2`), `fexp` selects the exponent grid, and `rnd` rounds the scaled
mantissa to an integer.
-/
structure NF (β : Numerics.Radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) where
  /-- Exact real value represented by this rounded-real model value. -/
  val : ℝ

namespace NF

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} {rnd : ℝ → ℤ}
variable [ValidExp fexp] [ValidRnd rnd]

/-- The rounding operator associated with the format: `roundR x = round … x`. -/
@[inline] noncomputable def roundR (x : ℝ) : ℝ := round (β := β) (fexp := fexp) rnd x

/-- Inject a real into `NF` by rounding it onto the target grid. -/
@[inline] noncomputable def ofReal (x : ℝ) : NF β fexp rnd := ⟨roundR (β := β) (fexp := fexp) (rnd
  := rnd) x⟩

/-- Forgetful projection (semantic view): treat an `NF` as a real number. -/
@[inline] noncomputable def toReal (x : NF β fexp rnd) : ℝ := x.val

/-- The semantic value of an `NF` lies on its declared radix/exponent grid. -/
def IsRepresentable (x : NF β fexp rnd) : Prop :=
  genericFormat β fexp x.val

omit [ValidRnd rnd] in
/-- `toReal (ofReal x)` is definitionally the rounded real `roundR x`. -/
@[simp] lemma toReal_ofReal (x : ℝ) :
    toReal (β := β) (fexp := fexp) (rnd := rnd) (ofReal (β := β) (fexp := fexp) (rnd := rnd) x) =
      roundR (β := β) (fexp := fexp) (rnd := rnd) x := rfl

omit [ValidRnd rnd] in
/-- The underlying `val` field of `ofReal x` is `roundR x`. -/
@[simp] lemma val_ofReal (x : ℝ) :
    (ofReal (β := β) (fexp := fexp) (rnd := rnd) x).val =
      roundR (β := β) (fexp := fexp) (rnd := rnd) x := rfl

/-- A default inhabitant (rounded zero). -/
noncomputable instance : Inhabited (NF β fexp rnd) where
  default := ofReal (β := β) (fexp := fexp) (rnd := rnd) 0

/-- Cast a natural number into `NF` by rounding `(n : ℝ)` onto the grid. -/
noncomputable instance : NatCast (NF β fexp rnd) where
  natCast n := ofReal (β := β) (fexp := fexp) (rnd := rnd) (n : ℝ)

/-- `0` and `1` for `NF` are defined via `ofReal`, so they live on the target grid. -/
noncomputable instance : Zero (NF β fexp rnd) where
  zero := ofReal (β := β) (fexp := fexp) (rnd := rnd) 0

/-- `1 : NF` is `ofReal 1`, i.e. the rounded real `1` on the target grid. -/
noncomputable instance : One (NF β fexp rnd) where
  one := ofReal (β := β) (fexp := fexp) (rnd := rnd) 1

/--
Negate the real value and round onto the grid. For a representable input, negation is exact.
-/
noncomputable instance : Neg (NF β fexp rnd) where
  neg x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (-x.val)

/-- Rounded addition: `val(a + b) = roundR (val a + val b)`. -/
noncomputable instance : Add (NF β fexp rnd) where
  add a b := ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val + b.val)

/-- Rounded subtraction: `val(a - b) = roundR (val a - val b)`. -/
noncomputable instance : Sub (NF β fexp rnd) where
  sub a b := ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val - b.val)

/-- Rounded multiplication: `val(a * b) = roundR (val a * val b)`. -/
noncomputable instance : Mul (NF β fexp rnd) where
  mul a b := ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val * b.val)

/-- Rounded division: `val(a / b) = roundR (val a / val b)`. -/
noncomputable instance : Div (NF β fexp rnd) where
  div a b := ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val / b.val)

/-- Checked rounded division. Unlike the totalized `Div` instance, this rejects a zero divisor. -/
noncomputable def checkedDiv (a b : NF β fexp rnd) : Option (NF β fexp rnd) :=
  if b.val = 0 then none else some (a / b)

omit [ValidRnd rnd] in
/-- Checked division rejects exactly the zero-divisor case. -/
@[simp] theorem checkedDiv_eq_none_iff (a b : NF β fexp rnd) :
    checkedDiv a b = none ↔ b.val = 0 := by
  simp [checkedDiv]

/-- Linear order on `NF` induced by `val`, with semantic minimum and maximum. -/
noncomputable instance : LinearOrder (NF β fexp rnd) :=
  LinearOrder.lift' val fun ⟨_⟩ ⟨_⟩ h => congrArg NF.mk h

/-- Natural exponentiation evaluated in `ℝ` and rounded once onto the target grid. -/
noncomputable def powNat (a : NF β fexp rnd) (n : Nat) : NF β fexp rnd :=
  ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val ^ n)

/-- Natural powers have unambiguous real semantics for every base. -/
noncomputable instance : Pow (NF β fexp rnd) Nat where
  pow := powNat

/--
Positive-base real exponentiation, evaluated as `exp (b * log a)` and rounded once.

The positivity proof is part of the API so negative bases and `0^0` cannot silently acquire an
arbitrary totalized value.
-/
noncomputable def positiveRealPow (a b : NF β fexp rnd) (_ha : 0 < a.val) : NF β fexp rnd :=
  ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.exp (b.val * Real.log a.val))

/--
Checked real exponentiation.

Positive bases accept every real exponent. Negative bases accept integer exponents, including
negative integer exponents. Zero uses the usual natural-power convention for nonnegative integer
exponents, maps positive noninteger exponents to zero, and rejects negative exponents. Thus the
remaining rejected case is a negative base with a noninteger exponent. Natural powers can also use
`powNat` directly.
-/
noncomputable def checkedRealPow (a b : NF β fexp rnd) : Option (NF β fexp rnd) := by
  classical
  exact
    if ha : 0 < a.val then
      some (positiveRealPow a b ha)
    else if hi : ∃ z : ℤ, b.val = z then
      let z := Classical.choose hi
      if hz : 0 ≤ z then
        some (ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val ^ z.toNat))
      else if a.val = 0 then
        none
      else
        some (ofReal (β := β) (fexp := fexp) (rnd := rnd) ((a.val ^ (-z).toNat)⁻¹))
    else if a.val = 0 then
      -- The logarithmic formula is unavailable at zero, but `0 ^ b = 0` is unambiguous for `b > 0`.
      if 0 < b.val then
        some (ofReal (β := β) (fexp := fexp) (rnd := rnd) 0)
      else
        none
    else
      none

omit [ValidRnd rnd] in
/-- On a positive base, checked exponentiation is the ordinary positive real-power formula. -/
theorem checkedRealPow_of_pos (a b : NF β fexp rnd) (ha : 0 < a.val) :
    checkedRealPow a b = some (positiveRealPow a b ha) := by
  simp [checkedRealPow, ha, positiveRealPow]

omit [ValidRnd rnd] in
/-- A positive noninteger exponent of zero uses the unambiguous real value zero. -/
theorem checkedRealPow_zero_of_pos_not_int (a b : NF β fexp rnd) (ha : a.val = 0)
    (hb : 0 < b.val) (hni : ¬ ∃ z : ℤ, b.val = z) :
    checkedRealPow a b = some (ofReal (β := β) (fexp := fexp) (rnd := rnd) 0) := by
  simp [checkedRealPow, ha, hb, hni]

/--
Evaluate each mathematical function in `ℝ` and round once. These noncomputable specifications use
Mathlib's totalized real functions; `checkedSqrt` and `checkedLog` enforce their usual real domains.
-/
noncomputable instance : MathFunctions (NF β fexp rnd) where
  exp  x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.exp x.val)
  tanh x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.tanh x.val)
  cosh x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.cosh x.val)
  sinh x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.sinh x.val)
  sqrt x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.sqrt x.val)
  abs  x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (|x.val|)
  log  x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.log x.val)
  pi      := ofReal (β := β) (fexp := fexp) (rnd := rnd) Real.pi
  cos  x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.cos x.val)
  sin  x := ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.sin x.val)

/-- Checked rounded square root; negative inputs are rejected instead of using real totalization. -/
noncomputable def checkedSqrt (x : NF β fexp rnd) : Option (NF β fexp rnd) :=
  if 0 ≤ x.val then
    some (ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.sqrt x.val))
  else
    none

omit [ValidRnd rnd] in
/-- Checked square root rejects exactly the negative inputs. -/
@[simp] theorem checkedSqrt_eq_none_iff (x : NF β fexp rnd) :
    checkedSqrt x = none ↔ ¬0 ≤ x.val := by
  simp [checkedSqrt]

/-- Checked rounded logarithm; zero and negative inputs are rejected. -/
noncomputable def checkedLog (x : NF β fexp rnd) : Option (NF β fexp rnd) :=
  if 0 < x.val then
    some (ofReal (β := β) (fexp := fexp) (rnd := rnd) (Real.log x.val))
  else
    none

omit [ValidRnd rnd] in
/-- Checked logarithm rejects exactly the nonpositive inputs. -/
@[simp] theorem checkedLog_eq_none_iff (x : NF β fexp rnd) :
    checkedLog x = none ↔ ¬0 < x.val := by
  simp [checkedLog]

end NF

end FloatLib.Floats.Formats.Flocq
