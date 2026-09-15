/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Model.NumericalSystem
public import FloatLib.Numerics.Core.Proof
public import FloatLib.Numerics.Operation.Semantics

/-!
# Executable complex values as numerical systems

A complex code denotes a value in `ℂ` when both scalar components are finite. Its denotation is
`undefined` if either component is NaN or infinite.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecComplex

open FloatLib.Numerics

/-- Complex semantics over an arbitrary component format. -/
noncomputable def numericalSystem (fmt : FloatFormat) : NumericalSystem where
  Code := ExecComplex fmt
  Scalar := ℂ
  denote z :=
    if isFinite z then .finite (toComplex z)
    else .exceptional .undefined

/-- An executable complex value with an erased proof of its complete denotation. -/
abbrev AtValue (fmt : FloatFormat) (value : NumericalValue ℂ) :=
  (numericalSystem fmt).At value

/-- An executable complex value with an erased proof of its finite complex value. -/
abbrev At (fmt : FloatFormat) (value : ℂ) :=
  (numericalSystem fmt).AtFinite value

/-- Finite executable components denote their assembled mathematical complex value. -/
theorem numericalSystem_represents_of_isFinite {fmt : FloatFormat} (z : ExecComplex fmt)
    (hz : isFinite z = true) :
    (numericalSystem fmt).Represents z (toComplex z) := by
  simp [NumericalSystem.Represents, numericalSystem, hz]

/-- A complex code represents a value exactly when both components are finite and decode to it. -/
@[simp] theorem represents_iff {fmt : FloatFormat} (z : ExecComplex fmt) (value : ℂ) :
    (numericalSystem fmt).Represents z value ↔
      isFinite z = true ∧ toComplex z = value := by
  unfold NumericalSystem.Represents numericalSystem
  cases hfinite : isFinite z <;> simp [hfinite]

/-- Componentwise sign negation refines exact complex negation. -/
theorem neg_refines (fmt : FloatFormat) :
    Operation.Finite1 (numericalSystem fmt) (numericalSystem fmt)
      ExecComplex.neg (fun value : ℂ => -value) := by
  unfold Operation.Finite1 Operation.RefinesFinite1
  intro z value hz
  obtain ⟨hzFinite, rfl⟩ := (represents_iff z value).1 hz
  apply (represents_iff _ _).2
  refine ⟨?_, toComplex_neg z hzFinite⟩
  simpa [ExecComplex.isFinite, ExecComplex.neg] using hzFinite

/-- Conjugation refines exact mathematical complex conjugation. -/
theorem conj_refines (fmt : FloatFormat) :
    Operation.Finite1 (numericalSystem fmt) (numericalSystem fmt)
      ExecComplex.conj (starRingEnd ℂ) := by
  unfold Operation.Finite1 Operation.RefinesFinite1
  intro z value hz
  obtain ⟨hzFinite, rfl⟩ := (represents_iff z value).1 hz
  apply (represents_iff _ _).2
  refine ⟨?_, toComplex_conj z hzFinite⟩
  simpa [ExecComplex.isFinite, ExecComplex.conj] using hzFinite

/-- Complex addition refines its explicit componentwise rounded semantics. -/
theorem add_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) ExecComplex.add (roundedAdd fmt)
      (fun _ _ result => isFinite result = true) := by
  unfold Operation.Finite2If
  intro x y left right hx hy hout
  obtain ⟨hxFinite, rfl⟩ := (represents_iff x left).1 hx
  obtain ⟨hyFinite, rfl⟩ := (represents_iff y right).1 hy
  exact (represents_iff _ _).2
    ⟨hout, toComplex_add_eq_roundedAdd x y hfmt hxFinite hyFinite hout⟩

/-- Complex subtraction refines its explicit componentwise rounded semantics. -/
theorem sub_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) ExecComplex.sub (roundedSub fmt)
      (fun _ _ result => isFinite result = true) := by
  unfold Operation.Finite2If
  intro x y left right hx hy hout
  obtain ⟨hxFinite, rfl⟩ := (represents_iff x left).1 hx
  obtain ⟨hyFinite, rfl⟩ := (represents_iff y right).1 hy
  exact (represents_iff _ _).2
    ⟨hout, toComplex_sub_eq_roundedSub x y hfmt hxFinite hyFinite hout⟩

/-- Complex multiplication refines all six scalar rounding sites in `roundedMul`. -/
theorem mul_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) ExecComplex.mul (roundedMul fmt)
      (fun x y _ => MulFinite x y) := by
  unfold Operation.Finite2If
  intro x y left right hx hy hfinite
  obtain ⟨_, rfl⟩ := (represents_iff x left).1 hx
  obtain ⟨_, rfl⟩ := (represents_iff y right).1 hy
  exact (represents_iff _ _).2
    ⟨hfinite.2.2.2.2.2.2, toComplex_mul_eq_roundedMul x y hfmt hfinite⟩

/-- Ratio division refines its selected rounded expression under all scalar domain obligations. -/
theorem div_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite2If (numericalSystem fmt) (numericalSystem fmt)
      (numericalSystem fmt) ExecComplex.div (roundedDiv fmt)
      (fun x y _ => DivFinite x y) := by
  unfold Operation.Finite2If
  intro x y left right hx hy hfinite
  obtain ⟨_, rfl⟩ := (represents_iff x left).1 hx
  obtain ⟨_, rfl⟩ := (represents_iff y right).1 hy
  exact (represents_iff _ _).2
    ⟨isFinite_div x y hfinite, toComplex_div_eq_roundedDiv x y hfmt hfinite⟩

/-- Squared magnitude refines a real-valued rounded expression in the scalar numerical system. -/
theorem normSq_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite1If (numericalSystem fmt) (Model.numericalSystem fmt)
      ExecComplex.normSq (roundedNormSq fmt) (fun z _ => NormSqFinite z) := by
  unfold Operation.Finite1If
  intro z value hz hfinite
  obtain ⟨_, rfl⟩ := (represents_iff z value).1 hz
  exact (Model.represents_iff _ _).2
    ⟨hfinite.result, toReal_normSq_eq_roundedNormSq z hfmt hfinite⟩

/-- Scaled magnitude refines its real-valued expression, retaining the scalar domain conditions. -/
theorem magnitude_refines (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Operation.Finite1If (numericalSystem fmt) (Model.numericalSystem fmt)
      ExecComplex.magnitude (roundedMagnitude fmt) (fun z _ => MagnitudeFinite z) := by
  unfold Operation.Finite1If
  intro z value hz hfinite
  obtain ⟨_, rfl⟩ := (represents_iff z value).1 hz
  exact (Model.represents_iff _ _).2
    ⟨hfinite.result, toReal_magnitude_eq_roundedMagnitude z hfmt hfinite⟩

/-- Decode squared magnitude directly when the complex input represents a specified value. -/
theorem toReal_normSq_of_represents {fmt : FloatFormat} {z : ExecComplex fmt} {value : ℂ}
    (hfmt : fmt.isIEEE = true) (hz : (numericalSystem fmt).Represents z value)
    (hfinite : NormSqFinite z) :
    Model.toReal (normSq z) = roundedNormSq fmt value := by
  obtain ⟨_, rfl⟩ := (represents_iff z value).1 hz
  exact toReal_normSq_eq_roundedNormSq z hfmt hfinite

/-- Decode magnitude directly when the complex input represents a specified value. -/
theorem toReal_magnitude_of_represents {fmt : FloatFormat} {z : ExecComplex fmt} {value : ℂ}
    (hfmt : fmt.isIEEE = true) (hz : (numericalSystem fmt).Represents z value)
    (hfinite : MagnitudeFinite z) :
    Model.toReal (magnitude z) = roundedMagnitude fmt value := by
  obtain ⟨_, rfl⟩ := (represents_iff z value).1 hz
  exact toReal_magnitude_eq_roundedMagnitude z hfmt hfinite

end FloatLib.Floats.Formats.BinaryInterchange.ExecComplex
