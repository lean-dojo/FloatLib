/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Steps
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Sign.Proof

/-!
# Neighbor range, status and cohort guarantees

Normalizing the input keeps its value and exposes its smallest quantum, so in decimal32 `1.2`
becomes `1.200000`, with seven digits. Both coefficient steps return a normalized representation,
signed zero and the finite endpoints included. The only source of a flag is NaN propagation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Exact input normalization supplies the hypotheses of the grid-step proofs. -/
theorem neighbor_normalize (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hvalid : (Datum.finite s c q).Valid f) (hc : c ≠ 0) :
    ∃ d r, roundedPair f .nearest false ((c : ℚ) * (10 : ℚ) ^ q) = (d, r) ∧
      d < f.coefficientBound ∧ 0 < d ∧ f.minQuantum ≤ r ∧ r ≤ f.maxQuantum ∧
      (r = f.minQuantum ∨ f.payloadBound ≤ d) ∧
      (d : ℚ) * (10 : ℚ) ^ r = (c : ℚ) * (10 : ℚ) ^ q := by
  have hv : (Datum.finite false c q).Valid f := by
    simpa only [Datum.valid_quantum_iff] using hvalid
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have he := roundedPair_exact_value f .nearest false c q hv
  refine ⟨_, _, rfl, roundedPair_coefficient_lt f .nearest false hx, ?_,
    roundedPair_quantum_ge_min f .nearest false _, ?_,
    roundedPair_minimum_or_full f .nearest false _, he⟩
  · have hp : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) (zpow_pos (by norm_num) _)
    change 0 < (roundedPair f .nearest false ((c : ℚ) * (10 : ℚ) ^ q)).1
    by_contra h
    change ¬0 < (roundedPair f .nearest false ((c : ℚ) * (10 : ℚ) ^ q)).1 at h
    have hz : (roundedPair f .nearest false ((c : ℚ) * (10 : ℚ) ^ q)).1 = 0 :=
      by omega
    rw [hz, Nat.cast_zero, zero_mul] at he
    linarith
  · exact (roundedPair_quantum_le_of_valid f .nearest false c q hv).trans
      ((Datum.valid_quantum_iff ..).mp hv).2.2

/-- A grid step from a valid nonzero finite operand delivers a valid datum, and a finite result is
on the least grid or has a full leading digit. -/
private theorem nextUp_finite_valid_full (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hx : (Datum.finite s c q).Valid f) (hc : c ≠ 0) :
    (nextUp f (.finite s c q)).value.Valid f ∧
      ∀ t d r, (nextUp f (.finite s c q)).value = .finite t d r →
        r = f.minQuantum ∨ f.payloadBound ≤ d := by
  obtain ⟨a, b, hp, ha, hapos, hbmin, hbmax, hfull, _⟩ := neighbor_normalize f s c q hx hc
  simp only [nextUp, ite_eq_right hc, hp]
  cases s
  · exact ⟨neighborAbove_valid f a b hbmin hbmax,
      fun t d r hout => neighborAbove_full f a d b r t hfull hout⟩
  · obtain ⟨d, r, he, hv, hdfull, _⟩ := neighborBelow_spec f a b ha hapos hbmin hbmax hfull
    simp only [↓reduceIte, he, Datum.negate, Bool.not_false, Datum.finite.injEq]
    refine ⟨by simpa [Datum.valid_quantum_iff] using hv, ?_⟩
    rintro t d' r' ⟨-, rfl, rfl⟩
    exact hdfull

/-- For a valid operand, `nextUp` delivers a valid datum, including the propagated NaN, the step
from either zero to the least positive value, and the steps at both ends of the finite range. -/
theorem nextUp_valid (f : Format) (x : Datum) (hx : x.Valid f) :
    (nextUp f x).value.Valid f := by
  cases x with
  | nan s t p => exact nanResult_valid ..
  | infinity s =>
      cases s
      · trivial
      · exact Format.maxFinite_valid ..
  | finite s c q =>
      by_cases hc : c = 0
      · simp only [nextUp, hc, ↓reduceIte]
        apply (Datum.valid_quantum_iff ..).mpr
        exact ⟨f.one_lt_coefficientBound, le_rfl, f.minQuantum_le_maxQuantum⟩
      · exact (nextUp_finite_valid_full f s c q hx hc).1

/-- `nextDown` is `nextUp` of the negated operand, negated back, for every datum including NaNs. -/
theorem nextDown_value (f : Format) (x : Datum) :
    (nextDown f x).value = (nextUp f x.negate).value.negate := rfl

/-- For a valid operand, `nextDown` delivers a valid datum, including the propagated NaN and the
steps at both ends of the finite range. -/
theorem nextDown_valid (f : Format) (x : Datum) (hx : x.Valid f) :
    (nextDown f x).value.Valid f := by
  simpa [nextDown_value] using nextUp_valid f x.negate (by simpa using hx)

/-- Neighbor steps raise `invalid` for signaling NaNs and nothing else, and leave all other flags
clear. -/
theorem nextUp_status (f : Format) (x : Datum) :
    (nextUp f x).status = { invalid := x.isSNaN } := by
  cases x with
  | nan s t p => rfl
  | infinity s => cases s <;> rfl
  | finite s c q =>
      simp only [nextUp, Datum.isSNaN]
      split <;> rfl

/-- `nextDown` raises invalid if and only if the input is a signaling NaN, and leaves all other
flags clear. -/
theorem nextDown_status (f : Format) (x : Datum) :
    (nextDown f x).status = { invalid := x.isSNaN } := by
  simp only [nextDown, nextUp_status]
  cases x <;> rfl

/-- Every finite successor has a full leading digit unless it is on the smallest grid. -/
theorem nextUp_full (f : Format) (x : Datum) (hx : x.Valid f)
    (s : Bool) (c : Nat) (q : Int) (hout : (nextUp f x).value = .finite s c q) :
    q = f.minQuantum ∨ f.payloadBound ≤ c := by
  cases x with
  | nan s t p => simp [nextUp, nanResult] at hout
  | infinity s =>
      cases s
      · contradiction
      · simp only [nextUp, Format.maxFinite, Datum.finite.injEq] at hout
        obtain ⟨rfl, rfl, rfl⟩ := hout
        right
        exact f.payloadBound_le_coefficientBound_sub_one
  | finite t d r =>
      by_cases hd : d = 0
      · simp only [nextUp, hd, ↓reduceIte, Datum.finite.injEq] at hout
        exact Or.inl hout.2.2.symm
      · exact (nextUp_finite_valid_full f t d r hx hd).2 s c q hout

/-- The actual successor's quantum is minimal among all valid equal-magnitude cohorts. -/
theorem nextUp_quantum_minimal (f : Format) (x : Datum) (hx : x.Valid f)
    (s : Bool) (c : Nat) (q : Int) (hout : (nextUp f x).value = .finite s c q)
    (d : Nat) (r : Int) (hd : (Datum.finite s d r).Valid f)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  have hv := (Datum.valid_quantum_iff ..).mp hd
  exact quantum_le_of_minimum_or_full f c d q r (nextUp_full f x hx s c q hout) hv.1 hv.2.1 he

/-- A finite result of `nextDown` uses the least quantum among all valid representations of its
value. -/
theorem nextDown_quantum_minimal (f : Format) (x : Datum) (hx : x.Valid f)
    (s : Bool) (c : Nat) (q : Int) (hout : (nextDown f x).value = .finite s c q)
    (d : Nat) (r : Int) (hd : (Datum.finite s d r).Valid f)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  rw [nextDown_value, Datum.negate_eq_iff_eq_negate] at hout
  exact nextUp_quantum_minimal f x.negate (by simpa using hx) (!s) c q hout d r hd he

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
