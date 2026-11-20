/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Format
public import FloatLib.Numerics.Exact.DecimalText.Notation
public import Mathlib.Data.Nat.Log

/-!
# Decimal datums and cohorts

A finite datum stores a sign, an integer coefficient, and a quantum exponent, and its value is
`(-1)^sign * coefficient * 10^quantum`. Trailing zeros of the coefficient carry information.
`1 × 10^0` and `10 × 10^-1` have the same value, for example, but they are different datums in the
same cohort.

This layer covers the representation side of IEEE 754-2019, §§3.3 and 3.5. Decimal arithmetic,
with its rounding, preferred-exponent, and exception rules, is not part of it.

Literals keep the digits you write, so `(1.20 : Datum)` is coefficient 120 at quantum `-2` and
differs from `(1.2 : Datum)`. Unary minus is IEEE `negate`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- A decimal datum before selecting an interchange width.
`signaling = true` represents a signaling NaN. -/
inductive Datum where
  /-- The finite number `coefficient * 10 ^ quantum`, negated when `negative` is true. -/
  | finite (negative : Bool) (coefficient : Nat) (quantum : Int)
  /-- An infinity, negative when `negative` is true. -/
  | infinity (negative : Bool)
  /-- A NaN with its sign, whether it is signaling, and its payload. -/
  | nan (negative : Bool) (signaling : Bool) (payload : Nat)

/--
Two datums are equal exactly when they are of the same kind with the same fields, and the
decision compares the fields one after the other. Lean's kernel reduces it by evaluating the
fields. A derived instance returns its answer through rewrites along the proofs that the fields
are equal, and to reduce those the kernel compares the computations of the fields as terms.
-/
instance : DecidableEq Datum := fun x y =>
  match x, y with
  | .finite s c q, .finite s' c' q' =>
      if hs : s = s' then
        if hc : c = c' then
          if hq : q = q' then isTrue (by rw [hs, hc, hq])
          else isFalse fun h => hq (Datum.finite.inj h).2.2
        else isFalse fun h => hc (Datum.finite.inj h).2.1
      else isFalse fun h => hs (Datum.finite.inj h).1
  | .infinity s, .infinity s' =>
      if hs : s = s' then isTrue (by rw [hs]) else isFalse fun h => hs (Datum.infinity.inj h)
  | .nan s t p, .nan s' t' p' =>
      if hs : s = s' then
        if ht : t = t' then
          if hp : p = p' then isTrue (by rw [hs, ht, hp])
          else isFalse fun h => hp (Datum.nan.inj h).2.2
        else isFalse fun h => ht (Datum.nan.inj h).2.1
      else isFalse fun h => hs (Datum.nan.inj h).1
  | .finite .., .infinity .. => isFalse nofun
  | .finite .., .nan .. => isFalse nofun
  | .infinity .., .finite .. => isFalse nofun
  | .infinity .., .nan .. => isFalse nofun
  | .nan .., .finite .. => isFalse nofun
  | .nan .., .infinity .. => isFalse nofun

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
A decimal literal keeps its written coefficient and quantum. `1.20` is coefficient 120 at quantum
`-2`, as when reading the text `1.20`, and `1.2e4` is coefficient 12 at quantum 3. The power of ten
is never expanded, so `1e1000000` is coefficient 1 at quantum 1000000.

`Arithmetic.add`, `sub`, `mul`, `div`, `fma`, `sqrt`, `pown` and `rootn` accept a literal that
doesn't fit the format, because they read a finite operand's exact value and round only the result.
`Arithmetic.nextUp`, `nextDown` and `remainder`, the codecs and the certified functions need
`Valid f`.
-/
instance : OfScientific Datum where
  ofScientific mantissa exponentSign logB :=
    .finite false mantissa (if exponentSign then -(logB : Int) else logB)

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

/-- A finite datum rebuilt from a coefficient and a biased exponent is valid if and only if both fit
their format bounds. -/
@[simp] theorem ofBiased_valid (f : Format) (s : Bool) (c e : Nat) :
    (ofBiased f s c e).Valid f ↔
      c < f.coefficientBound ∧ e < f.exponentBound := by
  simp [ofBiased, Valid]

/-- A finite datum is valid if and only if its coefficient fits the precision and its quantum lies
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
