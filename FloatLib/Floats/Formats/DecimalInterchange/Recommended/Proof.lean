/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Recommended.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Comparison.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Proof

/-!
# Contracts of the decimal quantum, minimum and maximum, and payload operations

For every decimal `Format`:

* `sameQuantum_quantum` and `toRat?_quantum`: the quantum of a finite datum has the quantum
  exponent `q` of the datum and the value `10 ^ q`.
* `extremum_status`: each of the eight minimum and maximum operations raises `invalid` exactly
  when an operand is a signaling NaN, and no other flag.
* `extremum_of_isNaN_eq_false` and `extremum_value_eq_or`: without a NaN operand the result is
  one of the two operands, unchanged.
* `numericValue?_selectExtremum`: the selection by value has the smaller or the larger of the
  two exact values, infinities included, and `numericValue?_abs_selectByMagnitude` the smaller or
  the larger magnitude. `numericValue?_minimum` and `numericValue?_maximum` state the first for
  the two named operations.
* `extremum_number_nan_left` and `extremum_number_nan_right`: when a number is preferred, one NaN
  operand gives the other operand, with `invalid` for a signaling NaN.
* `getPayload_setPayload` and `toRat?_of_admissiblePayload?`: the payload read from
  `setPayload f x` is the integer that an admissible `x` denotes, and `setPayload_getPayload`,
  `setPayloadSignaling_getPayload`: writing back the payload read from a NaN of the format gives
  the quiet or the signaling NaN with that payload and a clear sign.
* `setPayload_valid`: a NaN built by `setPayload` is a datum of the format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-! ## Quantum -/

/-- The quantum of a finite datum has the quantum exponent of the datum. -/
theorem sameQuantum_quantum (f : Format) (s : Bool) (c : Nat) (q : Int) :
    Datum.sameQuantum (.finite s c q) (quantum f (.finite s c q)).value = true := by
  simp [quantum, Datum.sameQuantum]

/-- The quantum of a finite datum with quantum exponent `q` is `10 ^ q`. -/
theorem toRat?_quantum (f : Format) (s : Bool) (c : Nat) (q : Int) :
    (quantum f (.finite s c q)).value.toRat? = some ((10 : ℚ) ^ q) := by
  simp [quantum, Datum.toRat?]

/-! ## Minimum and maximum -/

/-- A selection by value is one of the two operands. -/
theorem selectExtremum_eq_or (larger : Bool) (x y : Datum) :
    selectExtremum larger x y = x ∨ selectExtremum larger x y = y := by
  unfold selectExtremum
  split <;> split <;> simp

/-- A selection by magnitude is one of the two operands. -/
theorem selectByMagnitude_eq_or (larger : Bool) (x y : Datum) :
    selectByMagnitude larger x y = x ∨ selectByMagnitude larger x y = y := by
  unfold selectByMagnitude
  split
  · split <;> simp
  · split <;> simp
  · exact selectExtremum_eq_or larger x y

/--
The selection by value has the smaller (`larger := false`) or the larger (`larger := true`) of
the exact values of two data that are not NaNs, infinities included.
-/
theorem numericValue?_selectExtremum (larger : Bool) {x y : Datum} {a b : NumericValue}
    (hx : x.numericValue? = some a) (hy : y.numericValue? = some b) :
    (selectExtremum larger x y).numericValue? = some (if larger then max a b else min a b) := by
  have hcompare : x.compare y = some (compare a b) := by simp [Datum.compare, hx, hy]
  unfold selectExtremum
  rw [hcompare]
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.2 h]
    cases larger <;> simp [hx, hy, h.le]
  · subst h
    rw [compare_eq_iff_eq.2 rfl]
    dsimp only
    split <;> cases larger <;> simp [hx, hy]
  · rw [compare_gt_iff_gt.2 h]
    cases larger <;> simp [hx, hy, h.le]

/--
The selection by magnitude has the smaller (`larger := false`) or the larger
(`larger := true`) of the exact magnitudes of two data that are not NaNs.
-/
theorem numericValue?_abs_selectByMagnitude (larger : Bool) {x y : Datum} {a b : NumericValue}
    (hx : x.abs.numericValue? = some a) (hy : y.abs.numericValue? = some b) :
    (selectByMagnitude larger x y).abs.numericValue? =
      some (if larger then max a b else min a b) := by
  have hcompare : x.abs.compare y.abs = some (compare a b) := by simp [Datum.compare, hx, hy]
  unfold selectByMagnitude
  rw [hcompare]
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.2 h]
    cases larger <;> simp [hx, hy, h.le]
  · subst h
    rw [compare_eq_iff_eq.2 rfl]
    dsimp only
    rcases selectExtremum_eq_or larger x y with hsel | hsel <;> rw [hsel] <;>
      cases larger <;> simp [hx, hy]
  · rw [compare_gt_iff_gt.2 h]
    cases larger <;> simp [hx, hy, h.le]

/--
Each of the eight minimum and maximum operations raises `invalid` exactly when an operand is a
signaling NaN, and no other flag.
-/
theorem extremum_status (f : Format) (larger magnitude number : Bool) (x y : Datum) :
    (extremum f larger magnitude number x y).status =
      { invalid := x.isSignaling || y.isSignaling } := by
  cases x <;> cases y <;> cases number <;> simp [extremum, nanResult, Datum.isSignaling]

/-- Without a NaN operand the result is the selection among the operands, with no flag. -/
theorem extremum_of_isNaN_eq_false (f : Format) (larger magnitude number : Bool) {x y : Datum}
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    extremum f larger magnitude number x y =
      { value := if magnitude then selectByMagnitude larger x y
          else selectExtremum larger x y } := by
  cases x <;> cases y <;> first | rfl | simp [Datum.isNaN] at hx hy

/-- Without a NaN operand the result of a minimum or maximum is one of the operands. -/
theorem extremum_value_eq_or (f : Format) (larger magnitude number : Bool) {x y : Datum}
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    (extremum f larger magnitude number x y).value = x ∨
      (extremum f larger magnitude number x y).value = y := by
  rw [extremum_of_isNaN_eq_false f larger magnitude number hx hy]
  cases magnitude
  · exact selectExtremum_eq_or larger x y
  · exact selectByMagnitude_eq_or larger x y

/-- When a number is preferred, a NaN first operand gives the second operand. -/
theorem extremum_number_nan_left (f : Format) (larger magnitude : Bool) (s t : Bool) (p : Nat)
    {y : Datum} (hy : y.isNaN = false) :
    extremum f larger magnitude true (.nan s t p) y =
      { value := y, status := { invalid := t } } := by
  cases y <;> first | rfl | simp [Datum.isNaN] at hy

/-- When a number is preferred, a NaN second operand gives the first operand. -/
theorem extremum_number_nan_right (f : Format) (larger magnitude : Bool) (s t : Bool) (p : Nat)
    {x : Datum} (hx : x.isNaN = false) :
    extremum f larger magnitude true x (.nan s t p) =
      { value := x, status := { invalid := t } } := by
  cases x <;> first | rfl | simp [Datum.isNaN] at hx

/-- `minimum` of two data that are not NaNs has the smaller of their exact values. -/
theorem numericValue?_minimum (f : Format) {x y : Datum} {a b : NumericValue}
    (hx : x.numericValue? = some a) (hy : y.numericValue? = some b) :
    (minimum f x y).value.numericValue? = some (min a b) := by
  have hxn : x.isNaN = false := by
    cases h : x.isNaN
    · rfl
    · rw [(Datum.numericValue?_eq_none_iff x).2 h] at hx
      cases hx
  have hyn : y.isNaN = false := by
    cases h : y.isNaN
    · rfl
    · rw [(Datum.numericValue?_eq_none_iff y).2 h] at hy
      cases hy
  rw [minimum, extremum_of_isNaN_eq_false f false false false hxn hyn]
  exact numericValue?_selectExtremum false hx hy

/-- `maximum` of two data that are not NaNs has the larger of their exact values. -/
theorem numericValue?_maximum (f : Format) {x y : Datum} {a b : NumericValue}
    (hx : x.numericValue? = some a) (hy : y.numericValue? = some b) :
    (maximum f x y).value.numericValue? = some (max a b) := by
  have hxn : x.isNaN = false := by
    cases h : x.isNaN
    · rfl
    · rw [(Datum.numericValue?_eq_none_iff x).2 h] at hx
      cases hx
  have hyn : y.isNaN = false := by
    cases h : y.isNaN
    · rfl
    · rw [(Datum.numericValue?_eq_none_iff y).2 h] at hy
      cases hy
  rw [maximum, extremum_of_isNaN_eq_false f true false false hxn hyn]
  exact numericValue?_selectExtremum true hx hy

end Arithmetic

namespace Datum

/-! ## NaN payloads -/

/-- A payload that a datum names is below the payload bound of the format. -/
theorem admissiblePayload?_lt_payloadBound {f : Format} {x : Datum} {n : Nat}
    (h : x.admissiblePayload? f = some n) : n < f.payloadBound := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩
  · cases s
    · rcases q with k | k
      · simp only [admissiblePayload?] at h
        split at h
        · rename_i hlt
          cases h
          exact hlt
        · cases h
      · simp only [admissiblePayload?] at h
        split at h
        · rename_i hlt
          cases h
          exact hlt.2
        · cases h
    · cases q <;> cases h
  · cases h
  · cases h

/-- A datum that names the payload `n` denotes the integer `n`. -/
theorem toRat?_of_admissiblePayload? {f : Format} {x : Datum} {n : Nat}
    (h : x.admissiblePayload? f = some n) : x.toRat? = some (n : ℚ) := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩
  · cases s
    · rcases q with k | k
      · simp only [admissiblePayload?] at h
        split at h
        · cases h
          by_cases hc : c = 0
          · simp [toRat?, hc]
          · simp [toRat?, hc]
        · cases h
      · simp only [admissiblePayload?] at h
        split at h
        · rename_i hdiv
          cases h
          have hmul : c = 10 ^ (k + 1) * (c / 10 ^ (k + 1)) :=
            (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv.1)).symm
          have hpow : ((10 : ℚ) ^ (k + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
          by_cases hc : c = 0
          · simp [toRat?, hc]
          · simp only [toRat?, hc, ite_false, Bool.false_eq_true, one_mul, zpow_negSucc,
              Option.some.injEq]
            conv_lhs => rw [hmul]
            push_cast
            field_simp
        · cases h
    · cases q <;> cases h
  · cases h
  · cases h

/-- The payload read from `setPayload f x` is the integer that an admissible `x` names. -/
theorem getPayload_setPayload {f : Format} {x : Datum} {n : Nat}
    (h : x.admissiblePayload? f = some n) :
    (setPayload f x).getPayload = .finite false n 0 := by
  simp [setPayload, h, getPayload]

/-- `setPayload` of a datum that names no payload is `+0`. -/
theorem setPayload_of_admissiblePayload?_eq_none {f : Format} {x : Datum}
    (h : x.admissiblePayload? f = none) : setPayload f x = .finite false 0 0 := by
  simp [setPayload, h]

/-- `getPayload` of a datum that is not a NaN is `-1`. -/
theorem getPayload_of_isNaN_eq_false {x : Datum} (h : x.isNaN = false) :
    x.getPayload = .finite true 1 0 := by
  cases x <;> first | rfl | simp [isNaN] at h

/-- The result of `setPayload` is a NaN exactly when the operand names a payload. -/
theorem isNaN_setPayload (f : Format) (x : Datum) :
    (setPayload f x).isNaN = (x.admissiblePayload? f).isSome := by
  unfold setPayload
  cases x.admissiblePayload? f <;> rfl

/-- A NaN built by `setPayload` is a datum of the format. -/
theorem setPayload_valid {f : Format} {x : Datum} {n : Nat}
    (h : x.admissiblePayload? f = some n) : (setPayload f x).Valid f := by
  simpa [setPayload, h, Valid] using admissiblePayload?_lt_payloadBound h

/-- The nonnegative integer `p` with quantum exponent zero names the payload `p`. -/
theorem admissiblePayload?_finite_zero {f : Format} {p : Nat} (hp : p < f.payloadBound) :
    (Datum.finite false p 0).admissiblePayload? f = some p := by
  change (Datum.finite false p (Int.ofNat 0)).admissiblePayload? f = some p
  simp [admissiblePayload?, hp]

/--
Writing back the payload read from a NaN of the format gives the quiet NaN with that payload
and a clear sign.
-/
theorem setPayload_getPayload {f : Format} (s t : Bool) {p : Nat} (hp : p < f.payloadBound) :
    setPayload f (Datum.nan s t p).getPayload = .nan false false p := by
  simp [getPayload, setPayload, admissiblePayload?_finite_zero hp]

/--
Writing back as a signaling NaN the payload read from a NaN of the format gives the signaling
NaN with that payload and a clear sign.
-/
theorem setPayloadSignaling_getPayload {f : Format} (s t : Bool) {p : Nat}
    (hp : p < f.payloadBound) :
    setPayloadSignaling f (Datum.nan s t p).getPayload = .nan false true p := by
  simp [getPayload, setPayloadSignaling, admissiblePayload?_finite_zero hp]

end Datum
end FloatLib.Floats.Formats.DecimalInterchange
