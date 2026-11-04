/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.Flocq.Theory.Core
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof
public import FloatLib.Numerics.Exact.Dyadic.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Real interpretation of binary models

A finite bit pattern of any format denotes an exact real value, and `toRat?` reads the finite
patterns, and only those, as rationals with the same value. Arithmetic refinement comes later. It
belongs in modules that first relate each executable operation to one exact dyadic intermediate
and one rounding step.
-/

@[expose] public section

section

open FloatLib.Floats.Formats.Flocq

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Dyadic

/-- A dyadic with zero mantissa denotes zero, independently of its sign and exponent. -/
@[simp] theorem toReal_of_mantissa_zero (sign : Bool) (exponent : Int) :
    (Numerics.Dyadic.mk sign 0 exponent).toReal = 0 := by
  cases sign <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]

/-- A dyadic denotes zero if and only if its unsigned coefficient is zero. -/
theorem toReal_eq_zero_iff (d : Numerics.Dyadic) :
    d.toReal = 0 ↔ d.significand = 0 := by
  have hp := zpow_ne_zero d.exponent (by norm_num : (2 : ℝ) ≠ 0)
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hs, hp]

/-- A dyadic denotes its signed significand times the binary power of its exponent. -/
theorem toReal_mk (sign : Bool) (significand : Nat) (exponent : Int) :
    (Numerics.Dyadic.mk sign significand exponent).toReal =
      (if sign then (-1 : ℝ) else 1) * (significand : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix exponent := by
  cases sign <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, bpow,
      Numerics.binaryRadix, Numerics.Radix.toReal]

/-- Numerics.Dyadic real semantics expressed using a signed integer significand. -/
theorem toReal_eq_signedSignificand (d : Numerics.Dyadic) :
    d.toReal = (d.signedSignificand : ℝ) *
      FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix d.exponent := by
  rfl

/-- Left-shifting a signed significand multiplies its real value by the matching power of two. -/
theorem signedSignificand_shiftLeft (d : Numerics.Dyadic) (shift : Nat) :
    ((Numerics.Dyadic.mk d.negative
      (Nat.shiftLeft d.significand shift) 0).signedSignificand : ℝ) =
      (d.signedSignificand : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (Int.ofNat shift) := by
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.signedSignificand, hs, Nat.shiftLeft_eq,
      FloatLib.Floats.Formats.Flocq.bpow,
      FloatLib.Numerics.binaryRadix, Numerics.Radix.toReal]

/-- Exact dyadic addition agrees with addition in the real semantics. -/
theorem toReal_addDyadic (a b : Numerics.Dyadic) :
    (addDyadic a b).toReal = a.toReal + b.toReal := by
  have h :=
    congrArg (fun value : Rat => (value : ℝ))
      (Numerics.Dyadic.add_toRat a b)
  simpa only [addDyadic, Numerics.Dyadic.cast_toRat, Rat.cast_add] using h

/-- The exact dyadic product used by `Model.mul` agrees with real multiplication. -/
theorem toReal_mul (a b : Numerics.Dyadic) :
    (Numerics.Dyadic.mk (Bool.xor a.negative b.negative)
      (a.significand * b.significand) (a.exponent + b.exponent)).toReal =
      a.toReal * b.toReal := by
  cases ha : a.negative <;> cases hb : b.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      ha, hb, Bool.xor, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

/-- A nonzero dyadic with a clear sign denotes a positive real. -/
theorem toReal_pos_of_negative_eq_false {d : Numerics.Dyadic} (hsign : d.negative = false)
    (hsignificand : d.significand ≠ 0) : 0 < d.toReal := by
  rw [← Numerics.Dyadic.cast_toRat]
  exact_mod_cast Numerics.Dyadic.toRat_pos_of_significand_ne_zero d hsignificand hsign

/-- A dyadic with a clear sign denotes a nonnegative real. -/
theorem toReal_nonneg_of_negative_eq_false {d : Numerics.Dyadic} (hsign : d.negative = false) :
    0 ≤ d.toReal := by
  by_cases hsignificand : d.significand = 0
  · exact ((toReal_eq_zero_iff d).2 hsignificand).ge
  · exact (toReal_pos_of_negative_eq_false hsign hsignificand).le

/-- A nonzero dyadic with its sign set denotes a negative real. -/
theorem toReal_lt_zero_of_negative_eq_true {d : Numerics.Dyadic} (hsign : d.negative = true)
    (hsignificand : d.significand ≠ 0) : d.toReal < 0 := by
  have hpositive :=
    toReal_pos_of_negative_eq_false (d := { d with negative := false }) rfl hsignificand
  have hnegate : d.toReal = -({ d with negative := false } : Numerics.Dyadic).toReal := by
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsign]
  linarith

/-- A dyadic with its sign set denotes a nonpositive real. -/
theorem toReal_nonpos_of_negative_eq_true {d : Numerics.Dyadic} (hsign : d.negative = true) :
    d.toReal ≤ 0 := by
  by_cases hsignificand : d.significand = 0
  · exact ((toReal_eq_zero_iff d).2 hsignificand).le
  · exact (toReal_lt_zero_of_negative_eq_true hsign hsignificand).le

end Dyadic

/-- Real interpretation for finite values. NaN and infinity give `none`. -/
noncomputable def toReal? {fmt : FloatFormat} (x : Model fmt) : Option ℝ :=
  match toDyadic? x with
  | some d => some d.toReal
  | none => none

/-- Total real interpretation, mapping NaN and infinity to `0`. So numerical theorems must
establish finiteness or handle exceptional inputs on their own. -/
noncomputable def toReal {fmt : FloatFormat} (x : Model fmt) : ℝ :=
  match toReal? x with
  | some r => r
  | none => 0

/-- Real interpretation of Lean's unpacked logical float, with NaN and infinity mapped to zero. -/
noncomputable def unpackedToReal (x : Float.Model.UnpackedFloat) : ℝ :=
  match unpackedToDyadic? x with
  | some d => d.toReal
  | none => 0

/-- Both signed zeros of Lean's unpacked float model denote the real zero. -/
@[simp] theorem unpackedToReal_zero (sign : Float.Model.UnpackedFloat.Sign) :
    unpackedToReal (.zero sign) = 0 := by
  simp [unpackedToReal, unpackedToDyadic?]

/-- A finite unpacked model value denotes its signed integer mantissa times its dyadic scale. -/
@[simp] theorem unpackedToReal_finite
    (sign : Float.Model.UnpackedFloat.Sign) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) :
    unpackedToReal (.finite sign mantissa exponent hm) =
      (if modelSignBit sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix exponent :=
  Dyadic.toReal_mk _ _ _

/-- `toReal` is the dyadic denotation on finite values and zero on NaN and infinities. -/
lemma toReal_eq {fmt : FloatFormat} (x : Model fmt) :
    toReal x = match toDyadic? x with
      | some d => d.toReal
      | none => 0 := by
  cases h : toDyadic? x <;> simp [toReal, toReal?, h]

/-- The policy-aware zero constructor denotes zero for every encoding. -/
@[simp] theorem toReal_zero (fmt : FloatFormat) (sign : Bool) :
    toReal (zero fmt sign) = 0 := by
  rw [toReal_eq, toDyadic?_zero]
  exact Dyadic.toReal_of_mantissa_zero _ _

/-- The real interpretation erases the sign of an executable zero. -/
theorem toReal_eq_zero_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    toReal x = 0 := by
  rw [toReal_eq, toDyadic?_eq_zero_of_isZero_eq_true x hx]
  exact Dyadic.toReal_of_mantissa_zero _ _

/-- A finite nonzero value decodes to a dyadic with nonzero significand. -/
theorem significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hzero : isZero x = false) :
    d.significand ≠ 0 := by
  intro hmant
  have := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hmant
  simp [hzero] at this

/-- A value that is not finite has no dyadic decoding. -/
theorem toDyadic?_eq_none_of_isFinite_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = false) : toDyadic? x = none := by
  cases hdecode : toDyadic? x with
  | none => rfl
  | some d =>
      rw [isFinite_eq_true_of_toDyadic?_some hdecode] at hfinite
      contradiction

/-- An infinity has no dyadic decoding. -/
theorem toDyadic?_eq_none_of_isInf_eq_true {fmt : FloatFormat} {x : Model fmt}
    (hinf : isInf x = true) : toDyadic? x = none := by
  cases hdecode : toDyadic? x with
  | none => rfl
  | some d =>
      rw [isInf_eq_false_of_toDyadic?_some hdecode] at hinf
      contradiction

/-- A value without a dyadic decoding that is not an infinity is a NaN. -/
theorem isNaN_eq_true_of_toDyadic?_eq_none_of_isInf_eq_false {fmt : FloatFormat}
    {x : Model fmt} (hdecode : toDyadic? x = none) (hinf : isInf x = false) :
    isNaN x = true := by
  cases hnan : isNaN x
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite
      (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinf)
    rw [hdecode] at hd
    contradiction
  · rfl

/-- A finite value is an executable zero if and only if its real interpretation is zero. -/
theorem isZero_eq_true_iff_toReal_eq_zero {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    isZero x = true ↔ toReal x = 0 := by
  refine ⟨toReal_eq_zero_of_isZero x, fun hreal ↦ ?_⟩
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
  have hdreal : d.toReal = 0 := by simpa [toReal_eq, hd] using hreal
  exact isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd
    ((Dyadic.toReal_eq_zero_iff d).1 hdreal)

/-- Executable and logical decoding agree for formats represented by Lean's IEEE model. -/
theorem toReal_eq_unpackedToReal_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) :
    toReal x = unpackedToReal (toModel x) := by
  rw [toReal_eq, toDyadic?_ieee_eq_model fmt hfmt x]
  rfl

/-! ## Rational decoding

`toRat?` succeeds on the finite values and nowhere else, and its rational is their real value.
These facts keep the `Algebraic` namespace of the rounding proofs that first used them.
-/

namespace Algebraic

/-- A successful rational decode is the exact real value of the stored operand. -/
theorem toReal_of_toRat?_eq_some {fmt : FloatFormat}
    {value : Model fmt} {q : Rat} (hvalue : toRat? value = some q) :
    toReal value = (q : ℝ) := by
  cases hdecode : toDyadic? value with
  | none => simp [toRat?, hdecode] at hvalue
  | some exact =>
    have hq : exact.toRat = q := by simpa [toRat?, hdecode] using hvalue
    rw [toReal_eq, hdecode, ← hq, Numerics.Dyadic.cast_toRat]

/-- Rational decoding succeeds on finite operands and only on them, in every encoding. -/
theorem toRat?_isSome_eq_isFinite {fmt : FloatFormat} (value : Model fmt) :
    (toRat? value).isSome = isFinite value := by
  rw [← toDyadic?_isSome_eq_isFinite]
  simp [toRat?]

/--
A successful rational decode implies that the operand is finite. `toRat?_isSome_eq_isFinite` is
the full characterization.
-/
theorem isFinite_of_toRat?_eq_some {fmt : FloatFormat}
    {value : Model fmt} {q : Rat} (hvalue : toRat? value = some q) :
    isFinite value = true := by
  rw [← toRat?_isSome_eq_isFinite, hvalue]
  rfl

/-- A finite operand decodes to a rational, its exact real value. -/
theorem exists_toRat?_of_isFinite {fmt : FloatFormat} {value : Model fmt}
    (hvalue : isFinite value = true) :
    ∃ q : Rat, toRat? value = some q ∧ toReal value = (q : ℝ) := by
  obtain ⟨exact, hexact⟩ := exists_toDyadic?_of_isFinite hvalue
  have hq : toRat? value = some exact.toRat := by simp [toRat?, hexact]
  exact ⟨exact.toRat, hq, toReal_of_toRat?_eq_some hq⟩

/-- A finite operand whose real value is `q` decodes to `q`. -/
theorem toRat?_eq_some_of_toReal_eq {fmt : FloatFormat} {value : Model fmt} {q : Rat}
    (hfinite : isFinite value = true) (hvalue : toReal value = (q : ℝ)) :
    toRat? value = some q := by
  obtain ⟨exact, hexact, hreal⟩ := exists_toRat?_of_isFinite hfinite
  rw [hexact, Rat.cast_injective (hreal.symm.trans hvalue)]

end Algebraic

end Model
end FloatLib.Floats.Formats.BinaryInterchange

end -- noncomputable section
