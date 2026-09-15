/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Format
public import Mathlib.Algebra.Field.Rat

/-!
# Decimal datums and cohorts

A finite datum stores a sign, an integer coefficient, and a quantum exponent:
its value is `(-1)^sign * coefficient * 10^quantum`. Trailing coefficient zeros
are meaningful representation information. For example, `1 × 10^0` and
`10 × 10^-1` are different datums in the same cohort.

This representation layer implements IEEE 754-2019 §§3.3 and 3.5. It supplies
neither decimal arithmetic nor its rounding, preferred-exponent, or exception rules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- A decimal datum before selecting an interchange width.
`signaling = true` represents a signaling NaN. -/
inductive Datum where
  | finite (negative : Bool) (coefficient : Nat) (quantum : Int)
  | infinity (negative : Bool)
  | nan (negative : Bool) (signaling : Bool) (payload : Nat)
  deriving DecidableEq, Repr

namespace Datum

/-- Representability at the selected precision and quantum range.
NaN payloads have one fewer decimal digit than finite coefficients. -/
def Valid (f : Format) : Datum → Prop
  | .finite _ c q =>
      c < f.coefficientBound ∧ 0 ≤ q + f.bias ∧
        (q + f.bias).toNat < f.exponentBound
  | .infinity _ => True
  | .nan _ _ p => p < f.payloadBound

instance (f : Format) (d : Datum) : Decidable (d.Valid f) := by
  cases d <;> unfold Valid <;> infer_instance

/-- The exact rational value of a finite datum; infinities and NaNs have no rational value.
Signed zeros remain distinct datums even though both map to zero. Zero bypasses the
radix power, so its quantum does not determine the size of an intermediate integer. -/
def toRat? : Datum → Option ℚ
  | .finite s c q =>
      if c = 0 then some 0 else some ((if s then -1 else 1) * (c : ℚ) * (10 : ℚ) ^ q)
  | .infinity _ => none
  | .nan _ _ _ => none

/-- The zero shortcut preserves the usual coefficient-times-radix-power interpretation. -/
theorem toRat?_eq (d : Datum) :
    d.toRat? = match d with
      | .finite s c q => some ((if s then -1 else 1) * (c : ℚ) * (10 : ℚ) ^ q)
      | .infinity _ | .nan _ _ _ => none := by
  cases d with
  | finite s c q => by_cases hc : c = 0 <;> simp [toRat?, hc]
  | infinity s => rfl
  | nan s t p => rfl

/-- IEEE 754-2019 §§2.1 and 3.5.1 cohorts preserve the sign, including the sign of zero.
Each infinity forms a singleton cohort. NaNs have no cohort. Width-specific cohorts
restrict this relation to datums satisfying `Valid`. -/
def SameCohort : Datum → Datum → Prop
  | .finite s c q, .finite t d r =>
      s = t ∧ (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r
  | .infinity s, .infinity t => s = t
  | _, _ => False

/-- Biased exponent reconstructed by either decoder. -/
def ofBiased (f : Format) (s : Bool) (c e : Nat) : Datum :=
  .finite s c ((e : Int) - f.bias)

@[simp] theorem ofBiased_valid (f : Format) (s : Bool) (c e : Nat) :
    (ofBiased f s c e).Valid f ↔
      c < f.coefficientBound ∧ e < f.exponentBound := by
  simp [ofBiased, Valid]

theorem valid_quantum_iff (f : Format) (s : Bool) (c : Nat) (q : Int) :
    (.finite s c q : Datum).Valid f ↔
      c < f.coefficientBound ∧ f.minQuantum ≤ q ∧ q ≤ f.maxQuantum := by
  simp only [Valid, Format.minQuantum, Format.maxQuantum]
  omega

theorem sameCohort_symm {a b : Datum} (h : SameCohort a b) : SameCohort b a := by
  cases a <;> cases b <;> simp only [SameCohort] at *
  · exact ⟨h.1.symm, h.2.symm⟩
  · exact h.symm

theorem sameCohort_trans {a b c : Datum}
    (hab : SameCohort a b) (hbc : SameCohort b c) : SameCohort a c := by
  cases a <;> cases b <;> cases c <;> simp only [SameCohort] at *
  · exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  · exact hab.trans hbc

end Datum

end FloatLib.Floats.Formats.DecimalInterchange
