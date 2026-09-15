/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Cohort
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero

/-!
# Decimal format conversion guarantees

The numerical statements concern the returned datum for every destination
descriptor. Nonoverflowing nearest conversion has at most half a decimal grid unit
of error; directed conversion encloses the input on the required side.
Representable finite inputs retain their exact value and raise no exception.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

/-- Projection preserves an explicit sign when the input is presented as a magnitude. -/
theorem project_signed_magnitude (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (hx : 0 ≤ x) (preferred : Int) :
    project f mode (if s then -x else x) preferred s =
      projectMagnitude f mode s x preferred := by
  by_cases hz : x = 0
  · cases s <;> simp [project, hz]
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    cases s <;> simp [project, hz, abs_of_pos hp, not_lt.mpr hx, hp]

/-- Finite conversion uses the supplied sign and the exact nonnegative decimal magnitude. -/
theorem convertFormat_finite (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q : Int) :
    convertFormat f mode (.finite s c q) =
      projectMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) q := by
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) _).le
  have he : Datum.finiteValue s c q =
      if s then -((c : ℚ) * (10 : ℚ) ^ q) else (c : ℚ) * (10 : ℚ) ^ q := by
    cases s <;> simp [Datum.finiteValue]
  simp only [convertFormat, he]
  exact project_signed_magnitude f mode s _ hx q

/-- Every conversion produces a valid destination datum, even from an unrestricted datum. -/
theorem convertFormat_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (convertFormat f mode x).value.Valid f := by
  cases x <;> simp only [convertFormat]
  · exact project_valid ..
  · trivial
  · exact Arithmetic.nanResult_valid ..

/-- Infinity retains its sign and raises no exception. -/
@[simp] theorem convertFormat_infinity (f : Format) (mode : RoundingMode) (s : Bool) :
    convertFormat f mode (.infinity s) = { value := .infinity s } := rfl

/-- NaN conversion preserves a fitting payload, quiets the NaN, and reports its signaling bit. -/
@[simp] theorem convertFormat_nan (f : Format) (mode : RoundingMode)
    (s signaling : Bool) (p : Nat) :
    convertFormat f mode (.nan s signaling p) =
      { value := .nan s false (if p < f.payloadBound then p else 0)
        status := { invalid := signaling } } := rfl

/-- Signed zero keeps its sign and clamps its source quantum to the destination interval. -/
@[simp] theorem convertFormat_zero (f : Format) (mode : RoundingMode) (s : Bool) (q : Int) :
    convertFormat f mode (.finite s 0 q) =
      { value := .finite s 0 (max f.minQuantum (min q f.maxQuantum)) } := by
  simpa [convertFormat, Datum.finiteValue] using project_zero f mode s q

/-- A finite input already representable in the destination retains its exact numerical value. -/
theorem convertFormat_exact (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q : Int) (h : (Datum.finite s c q).Valid f) :
    (convertFormat f mode (.finite s c q)).value.toRat? = (Datum.finite s c q).toRat? := by
  rw [convertFormat_finite]
  exact projectMagnitude_exact f mode s c q q h

/-- Changing destination width or cohort cannot raise a flag on an exactly representable input. -/
theorem convertFormat_exact_status (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q : Int) (h : (Datum.finite s c q).Valid f) :
    (convertFormat f mode (.finite s c q)).status = {} := by
  rw [convertFormat_finite]
  exact projectMagnitude_exact_status f mode s c q q h

/-- A source cohort need not itself fit the destination: any valid destination
representation of the same magnitude makes the conversion exact. -/
theorem convertFormat_exact_of_representable (f : Format) (mode : RoundingMode) (s : Bool)
    (c d : Nat) (q r : Int) (hd : (Datum.finite s d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    (convertFormat f mode (.finite s c q)).value.toRat? =
      (Datum.finite s d r).toRat? := by
  rw [convertFormat_finite, hvalue]
  exact projectMagnitude_exact f mode s d r q hd

/-- A representable exact value raises no flags even if its source coefficient or
quantum must change to fit the destination. -/
theorem convertFormat_exact_status_of_representable (f : Format) (mode : RoundingMode)
    (s : Bool) (c d : Nat) (q r : Int) (hd : (Datum.finite s d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    (convertFormat f mode (.finite s c q)).status = {} := by
  rw [convertFormat_finite, hvalue]
  exact projectMagnitude_exact_status f mode s d r q hd

/-- Exact conversion selects the quantum closest to the source quantum over the entire cohort. -/
theorem convertFormat_quantum_closest (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q : Int) (h : (Datum.finite s c q).Valid f)
    (d : Nat) (r : Int)
    (hout : (convertFormat f mode (.finite s c q)).value = .finite s d r)
    (e : Nat) (t : Int) (he : (Datum.finite s e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (e : ℚ) * (10 : ℚ) ^ t) :
    |q - r| ≤ |q - t| := by
  rw [convertFormat_finite] at hout
  exact projectMagnitude_quantum_closest f mode s c q q h d r hout e t he hvalue

/-- Across different source and destination widths, exact conversion selects a
destination cohort member whose quantum is closest to the source quantum. -/
theorem convertFormat_quantum_closest_of_representable (f : Format) (mode : RoundingMode)
    (s : Bool) (c d : Nat) (q r : Int) (hd : (Datum.finite s d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r)
    (e : Nat) (t : Int)
    (hout : (convertFormat f mode (.finite s c q)).value = .finite s e t)
    (a : Nat) (b : Int) (ha : (Datum.finite s a b).Valid f)
    (heq : (c : ℚ) * (10 : ℚ) ^ q = (a : ℚ) * (10 : ℚ) ^ b) :
    |q - t| ≤ |q - b| := by
  rw [convertFormat_finite, hvalue] at hout
  exact projectMagnitude_quantum_closest f mode s d r q hd e t hout a b ha
    (hvalue.symm.trans heq)

/-- Both nearest directions bound the actual conversion error by half the selected grid unit. -/
theorem convertFormat_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (convertFormat f mode x).status.overflow = false) :
    ∃ value, (convertFormat f mode x).value.toRat? = some value ∧
      |value - a| ≤ (10 : ℚ) ^ roundingQuantum f |a| / 2 := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  exact project_error_le_half f mode hm _ _ _ hfinite

/-- All five directions keep a nonoverflowing conversion within one selected grid unit. -/
theorem convertFormat_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (convertFormat f mode x).status.overflow = false) :
    ∃ value, (convertFormat f mode x).value.toRat? = some value ∧
      |value - a| < (10 : ℚ) ^ roundingQuantum f |a| := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  exact project_error_lt_one f mode _ _ _ hfinite

/-- Upward conversion encloses the input from above whenever it does not overflow. -/
theorem le_convertFormat_towardPositive (f : Format) (x : Datum) (a : ℚ)
    (hx : x.toRat? = some a)
    (hfinite : (convertFormat f .towardPositive x).status.overflow = false) :
    ∃ value, (convertFormat f .towardPositive x).value.toRat? = some value ∧ a ≤ value := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  exact le_project_towardPositive f _ _ _ hfinite

/-- Downward conversion encloses the input from below whenever it does not overflow. -/
theorem convertFormat_towardNegative_le (f : Format) (x : Datum) (a : ℚ)
    (hx : x.toRat? = some a)
    (hfinite : (convertFormat f .towardNegative x).status.overflow = false) :
    ∃ value, (convertFormat f .towardNegative x).value.toRat? = some value ∧ value ≤ a := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  exact project_towardNegative_le f _ _ _ hfinite

/-- Finite nonoverflowing conversion raises inexact exactly when the numerical value changes. -/
theorem convertFormat_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a)
    (hfinite : (convertFormat f mode x).status.overflow = false)
    (hv : (convertFormat f mode x).value.toRat? = some value) :
    (convertFormat f mode x).status.inexact = true ↔ value ≠ a := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  exact project_inexact_iff f mode _ value _ _ hfinite hv

/-- Decimal underflow uses the exact input magnitude and requires inexactness. -/
theorem convertFormat_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (convertFormat f mode x).status.overflow = false) :
    (convertFormat f mode x).status.underflow = true ↔
      |a| < f.minNormal ∧ (convertFormat f mode x).status.inexact = true := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  exact project_underflow_iff f mode _ _ _ hfinite

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
