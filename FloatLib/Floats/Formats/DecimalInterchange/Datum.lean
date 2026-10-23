/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Format
public import FloatLib.Numerics.Exact.DecimalText.Notation
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Nat.Log

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
  deriving DecidableEq

namespace Datum

/--
Text of a datum with its coefficient and quantum: plain notation such as `1.50` or `120` when
the quantum is not positive and the leading digit is at most six places after the point,
otherwise one leading digit and an `e` exponent, such as `1.2e4` for coefficient 12 and quantum
3. Both read back as the same coefficient and quantum. Infinities print as `inf` and `-inf`, NaNs
as `nan`.
-/
def display : Datum → String
  | .finite negative coefficient quantum =>
      let record : Numerics.DecimalText.Decimal := ⟨negative, coefficient, quantum⟩
      if quantum ≤ 0 ∧ -6 ≤ (Nat.log 10 coefficient : Int) + quantum then
        String.ofList record.fixedCharacters
      else
        String.ofList record.scientificCharacters
  | .infinity negative => if negative then "-inf" else "inf"
  | .nan .. => "nan"

/-- Datums print with their coefficient and quantum, as `display` writes them. -/
instance : ToString Datum where
  toString := display

/-- `#eval` and `repr` show the same text, parenthesized when negative inside an argument. -/
instance : Repr Datum where
  reprPrec value precedence :=
    let text := display value
    if text.startsWith "-" then Repr.addAppParen text precedence else text

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

/-- The rational value of a finite datum, or `none` for infinities and NaNs.
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

/-- Cohort relation of IEEE 754-2019 §§2.1 and 3.5.1: equal value and equal sign, including the
sign of zero. Each infinity forms a singleton cohort. NaNs have no cohort. Width-specific cohorts
restrict this relation to datums satisfying `Valid`. -/
def SameCohort : Datum → Datum → Prop
  | .finite s c q, .finite t d r =>
      s = t ∧ (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r
  | .infinity s, .infinity t => s = t
  | _, _ => False

/-- Finite datum from a coefficient and a biased exponent, as either decoder rebuilds it. -/
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
