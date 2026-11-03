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

Literals keep the digits they are written with, so `(1.20 : Datum)` is coefficient 120 at
quantum `-2` and differs from `(1.2 : Datum)`. Unary minus is IEEE `negate`.
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

/--
IEEE `negate`: reverse the sign bit and keep everything else. A zero keeps its quantum and
becomes the zero of the other sign, and a NaN keeps its signaling bit and payload. Like every
sign-bit operation of IEEE 754-2019 §5.5.1, it treats NaNs as it treats numbers and signals no
exception.
-/
def negate : Datum → Datum
  | .finite s c q => .finite (!s) c q
  | .infinity s => .infinity (!s)
  | .nan s signaling payload => .nan (!s) signaling payload

/-- `-x` is `negate x`, which reverses the sign of zeros, infinities, and NaNs too. -/
instance : Neg Datum where
  neg := negate

/-- Unary minus is IEEE `negate`. -/
@[simp] theorem neg_eq_negate (d : Datum) : -d = d.negate :=
  rfl

/-- The natural literal `n` is the datum with coefficient `n` and quantum zero. -/
instance (n : Nat) : OfNat Datum n where
  ofNat := .finite false n 0

/--
A decimal literal keeps its written coefficient and quantum: `1.20` is coefficient 120 at
quantum `-2`, the datum that reading the text `1.20` gives, and `1.2e4` is coefficient 12 at
quantum 3. The literal does not expand the power of ten, so `1e1000000` is coefficient 1 at
quantum 1000000.

A literal need not fit the format as an operand of `Arithmetic.add`, `sub`, `mul`, `div`, `fma`,
`sqrt`, `powInt` or `rootN`, which read the exact value of a finite operand and round only their
result. `Arithmetic.nextUp`, `nextDown` and `remainder`, the codecs and the certified functions
need an operand that satisfies `Valid f`.
-/
instance : OfScientific Datum where
  ofScientific mantissa exponentSign decimalExponent :=
    .finite false mantissa (if exponentSign then -(decimalExponent : Int) else decimalExponent)

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

/-- A finite datum rebuilt from a coefficient and a biased exponent is valid exactly when both fit
their format bounds. -/
@[simp] theorem ofBiased_valid (f : Format) (s : Bool) (c e : Nat) :
    (ofBiased f s c e).Valid f ↔
      c < f.coefficientBound ∧ e < f.exponentBound := by
  simp [ofBiased, Valid]

/-- A finite datum is valid exactly when its coefficient fits the precision and its quantum lies
between the least and largest quantum of the format. -/
theorem valid_quantum_iff (f : Format) (s : Bool) (c : Nat) (q : Int) :
    (.finite s c q : Datum).Valid f ↔
      c < f.coefficientBound ∧ f.minQuantum ≤ q ∧ q ≤ f.maxQuantum := by
  simp only [Valid, Format.minQuantum, Format.maxQuantum]
  omega

/-- The cohort relation is symmetric. -/
theorem sameCohort_symm {a b : Datum} (h : SameCohort a b) : SameCohort b a := by
  cases a <;> cases b <;> simp only [SameCohort] at *
  · exact ⟨h.1.symm, h.2.symm⟩
  · exact h.symm

/-- The cohort relation is transitive. It is not reflexive on NaNs, which have no cohort. -/
theorem sameCohort_trans {a b c : Datum}
    (hab : SameCohort a b) (hbc : SameCohort b c) : SameCohort a c := by
  cases a <;> cases b <;> cases c <;> simp only [SameCohort] at *
  · exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  · exact hab.trans hbc

end Datum

end FloatLib.Floats.Formats.DecimalInterchange
