/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System
public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
public import Mathlib.Algebra.Order.Algebra

/-!
# Binary models as numerical systems

The `NumericalSystem` interface gives `Model fmt` a representation-independent semantic view.
Its ordinary semantic domain is `ℝ`; supported infinities retain their signs, and NaNs retain
the stored fraction as a payload together with their sign bit and signaling class.

`Model.toDyadic?` supplies the executable exact dyadic decoder. This real-valued view lets
generic refinement results compose with other numerical families.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-- Complete real-valued interpretation of an executable float. -/
noncomputable def toNumericalValue {fmt : FloatFormat}
    (x : Model fmt) : NumericalValue ℝ :=
  if isNaN x then
    .exceptional (.nan (some (fracField x)) (signBit x) (isSNaN x))
  else if isInf x then
    .infinity (signBit x)
  else
    .finite (toReal x)

/-- Real-valued numerical-system semantics of a binary format. -/
noncomputable abbrev numericalSystem (fmt : FloatFormat) : NumericalSystem where
  Code := Model fmt
  Scalar := ℝ
  denote := toNumericalValue

/--
Proof-facing real interpretation of an executable float.

This is a relation on the existing `Model fmt` carrier, not a second floating-point type.
`Represents x r` says that the exact bits stored by `x` have the ordinary finite meaning `r`.
-/
abbrev Represents {fmt : FloatFormat} (x : Model fmt) (r : ℝ) : Prop :=
  toNumericalValue x = .finite r

/-- The generic numerical-system relation is the direct `Model` representation relation. -/
@[simp] theorem numericalSystem_represents_iff {fmt : FloatFormat}
    (x : Model fmt) (r : ℝ) :
    (numericalSystem fmt).Represents x r ↔ Represents x r := by
  rfl

/-- Every finite executable float has its exact real interpretation as its total value. -/
theorem toNumericalValue_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    toNumericalValue x = .finite (toReal x) := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  simp [toNumericalValue, hnan, hinf]

/-- Every finite executable float denotes its real interpretation in the general interface. -/
theorem numericalSystem_denote_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    (numericalSystem fmt).denote x = .finite (toReal x) := by
  exact toNumericalValue_of_isFinite x hx

/-- The general interface represents exactly the real value used by finite arithmetic theorems. -/
theorem numericalSystem_represents_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    (numericalSystem fmt).Represents x (toReal x) :=
  numericalSystem_denote_of_isFinite x hx

/--
An executable float represents a real exactly when it is finite and its exact decoding is that
real. This is the main bridge from the single executable carrier to proof-oriented real reasoning.
-/
@[simp] theorem represents_iff {fmt : FloatFormat} (x : Model fmt) (r : ℝ) :
    Represents x r ↔ isFinite x = true ∧ toReal x = r := by
  constructor
  · intro h
    cases hnan : isNaN x
    · cases hinf : isInf x
      · have hfinite :=
          isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinf
        have hreal : toReal x = r := by
          simpa [Represents, toNumericalValue, hnan, hinf] using h
        exact ⟨hfinite, hreal⟩
      · simp [Represents, toNumericalValue, hnan, hinf] at h
    · simp [Represents, toNumericalValue, hnan] at h
  · rintro ⟨hfinite, rfl⟩
    exact numericalSystem_represents_of_isFinite x hfinite

/-- The real decoding of `x` is represented exactly when `x` is finite. -/
theorem represents_toReal_iff {fmt : FloatFormat} (x : Model fmt) :
    Represents x (toReal x) ↔ isFinite x = true := by
  simp

/-- A represented executable float is finite. -/
theorem isFinite_of_represents {fmt : FloatFormat} {x : Model fmt} {r : ℝ}
    (hx : Represents x r) :
    isFinite x = true :=
  ((represents_iff x r).mp hx).1

/-- The exact real decoding of a represented executable float is its represented value. -/
theorem toReal_eq_of_represents {fmt : FloatFormat} {x : Model fmt} {r : ℝ}
    (hx : Represents x r) :
    toReal x = r :=
  ((represents_iff x r).mp hx).2

/-- The finite real value represented by an executable bit pattern is unique. -/
theorem represents_unique {fmt : FloatFormat} {x : Model fmt} {r s : ℝ}
    (hr : Represents x r) (hs : Represents x s) :
    r = s :=
  (toReal_eq_of_represents hr).symm.trans (toReal_eq_of_represents hs)

/-- Executable negation represents the exact negative of every represented finite real value. -/
theorem neg_refines (fmt : FloatFormat) :
    Operation.Finite1 (numericalSystem fmt) (numericalSystem fmt)
      Model.neg (fun (x : ℝ) => -x) := by
  unfold Operation.Finite1 Operation.RefinesFinite1 numericalSystem
  intro x r hx
  have hx' : Represents x r := hx
  apply (represents_iff _ _).2
  refine ⟨?_, ?_⟩
  · rw [isFinite_neg]
    exact isFinite_of_represents hx'
  rw [toReal_neg x (isFinite_of_represents hx'), toReal_eq_of_represents hx']

/-- Executable addition refines one nearest-even rounding for a conventional IEEE format,
provided the result is finite. -/
theorem add_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) Model.add
      (fun (x y : ℝ) => roundAt fmt (x + y))
      (fun _ _ result => isFinite result = true) := by
  unfold Operation.Finite2If numericalSystem
  intro x y r s hx hy hout
  have hx' : Represents x r := hx
  have hy' : Represents y s := hy
  apply (represents_iff _ _).2
  refine ⟨hout, ?_⟩
  rw [toReal_add_eq_roundAt x y hfmt (isFinite_of_represents hx')
    (isFinite_of_represents hy') hout]
  rw [toReal_eq_of_represents hx', toReal_eq_of_represents hy']

/-- Executable subtraction refines one nearest-even rounding for a conventional IEEE format,
provided the result is finite. -/
theorem sub_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) Model.sub
      (fun (x y : ℝ) => roundAt fmt (x - y))
      (fun _ _ result => isFinite result = true) := by
  unfold Operation.Finite2If numericalSystem
  intro x y r s hx hy hout
  have hx' : Represents x r := hx
  have hy' : Represents y s := hy
  apply (represents_iff _ _).2
  refine ⟨hout, ?_⟩
  rw [toReal_sub_eq_roundAt x y hfmt (isFinite_of_represents hx')
    (isFinite_of_represents hy') hout]
  rw [toReal_eq_of_represents hx', toReal_eq_of_represents hy']

/-- Executable multiplication refines one nearest-even rounding for a conventional IEEE format,
provided the result is finite. -/
theorem mul_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) Model.mul
      (fun (x y : ℝ) => roundAt fmt (x * y))
      (fun _ _ result => isFinite result = true) := by
  unfold Operation.Finite2If numericalSystem
  intro x y r s hx hy hout
  have hx' : Represents x r := hx
  have hy' : Represents y s := hy
  apply (represents_iff _ _).2
  refine ⟨hout, ?_⟩
  rw [toReal_mul_eq_roundAt x y hfmt (isFinite_of_represents hx')
    (isFinite_of_represents hy') hout]
  rw [toReal_eq_of_represents hx', toReal_eq_of_represents hy']

/--
For a conventional IEEE format, executable fused multiply-add refines one nearest-even rounding
when the result remains finite.
-/
theorem fma_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite3If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) (numericalSystem fmt) Model.fma
      (fun (x y z : ℝ) => roundAt fmt (x * y + z))
      (fun _ _ _ result => isFinite result = true) := by
  unfold Operation.Finite3If numericalSystem
  intro x y z r s t hx hy hz hout
  have hx' : Represents x r := hx
  have hy' : Represents y s := hy
  have hz' : Represents z t := hz
  apply (represents_iff _ _).2
  refine ⟨hout, ?_⟩
  rw [toReal_fma_eq_roundAt x y z hfmt (isFinite_of_represents hx')
    (isFinite_of_represents hy') (isFinite_of_represents hz') hout]
  rw [toReal_eq_of_represents hx', toReal_eq_of_represents hy',
    toReal_eq_of_represents hz']

/-- A finite cross-format cast refines nearest-even rounding in its destination format. -/
theorem cast_refines (src dst : FloatFormat)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true) :
    Operation.Finite1If (numericalSystem src) (numericalSystem dst)
      (Model.cast src dst) (fun (x : ℝ) => roundAt dst x)
      (fun _ result => isFinite result = true) := by
  unfold Operation.Finite1If numericalSystem
  intro x r hx hout
  have hx' : Represents x r := hx
  apply (represents_iff _ _).2
  refine ⟨hout, ?_⟩
  rw [cast_eq_roundAt hsrc hdst x (isFinite_of_represents hx') hout]
  rw [toReal_eq_of_represents hx']

end Model
end FloatLib.Floats.Formats.BinaryInterchange
