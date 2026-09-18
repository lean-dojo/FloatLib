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

Normalization preserves the input value and exposes its smallest quantum.
Both coefficient steps return a normalized representation, including signed
zero and the finite endpoints. NaN propagation is the only source of a flag.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Exact input normalization supplies the hypotheses of the grid-step proofs. -/
theorem neighbor_normalize (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hvalid : (Datum.finite s c q).Valid f) (hc : c ≠ 0) :
    ∃ d r, roundedPair f .nearestEven false ((c : ℚ) * (10 : ℚ) ^ q) = (d, r) ∧
      d < f.coefficientBound ∧ 0 < d ∧ f.minQuantum ≤ r ∧ r ≤ f.maxQuantum ∧
      (r = f.minQuantum ∨ f.payloadBound ≤ d) ∧
      (d : ℚ) * (10 : ℚ) ^ r = (c : ℚ) * (10 : ℚ) ^ q := by
  have hv : (Datum.finite false c q).Valid f := by
    simpa only [Datum.valid_quantum_iff] using hvalid
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have he := roundedPair_exact_value f .nearestEven false c q hv
  refine ⟨_, _, rfl, roundedPair_coefficient_lt f .nearestEven false hx, ?_,
    roundedPair_quantum_ge_min f .nearestEven false _, ?_,
    roundedPair_minimum_or_full f .nearestEven false hx, he⟩
  · have hp : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) (zpow_pos (by norm_num) _)
    change 0 < (roundedPair f .nearestEven false ((c : ℚ) * (10 : ℚ) ^ q)).1
    by_contra h
    change ¬0 < (roundedPair f .nearestEven false ((c : ℚ) * (10 : ℚ) ^ q)).1 at h
    have hz : (roundedPair f .nearestEven false ((c : ℚ) * (10 : ℚ) ^ q)).1 = 0 :=
      by omega
    rw [hz, Nat.cast_zero, zero_mul] at he
    linarith
  · exact (roundedPair_quantum_le_of_valid f .nearestEven false c q hv).trans
      ((Datum.valid_quantum_iff ..).mp hv).2.2

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
      · obtain ⟨d, r, hp, hd, hdpos, hrmin, hrmax, hfull, _⟩ :=
          neighbor_normalize f s c q hx hc
        simp only [nextUp, ite_eq_right hc, hp]
        cases s
        · exact neighborAbove_valid f d r hrmin hrmax
        · obtain ⟨a, b, he, hv, _, _⟩ :=
            neighborBelow_spec f d r hd hdpos hrmin hrmax hfull
          simpa [he, Datum.negate, Datum.valid_quantum_iff] using hv

theorem nextDown_valid (f : Format) (x : Datum) (hx : x.Valid f) :
    (nextDown f x).value.Valid f := by
  have hn : x.negate.Valid f := by
    simpa [Datum.negate_eq_withSign] using hx
  simpa [nextDown, Datum.negate_eq_withSign] using nextUp_valid f x.negate hn

/-- Neighbor steps raise `invalid` exactly for signaling NaNs and leave all other flags clear. -/
theorem nextUp_status (f : Format) (x : Datum) :
    (nextUp f x).status = { invalid := x.isSignaling } := by
  cases x with
  | nan s t p => rfl
  | infinity s => cases s <;> rfl
  | finite s c q =>
      simp only [nextUp, Datum.isSignaling]
      split <;> rfl

theorem nextDown_status (f : Format) (x : Datum) :
    (nextDown f x).status = { invalid := x.isSignaling } := by
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
      · obtain ⟨a, b, hp, ha, hapos, hbmin, hbmax, hfull, _⟩ :=
          neighbor_normalize f t d r hx hd
        simp only [nextUp, ite_eq_right hd, hp] at hout
        cases t
        · exact neighborAbove_full f a c b q s hfull hout
        · obtain ⟨e, u, he, _, hefull, _⟩ :=
            neighborBelow_spec f a b ha hapos hbmin hbmax hfull
          simp only [Bool.true_eq, ↓reduceIte, he, Datum.negate,
            Bool.not_false, Datum.finite.injEq] at hout
          obtain ⟨rfl, rfl, rfl⟩ := hout
          exact hefull

/-- The actual successor's quantum is minimal among all valid equal-magnitude cohorts. -/
theorem nextUp_quantum_minimal (f : Format) (x : Datum) (hx : x.Valid f)
    (s : Bool) (c : Nat) (q : Int) (hout : (nextUp f x).value = .finite s c q)
    (d : Nat) (r : Int) (hd : (Datum.finite s d r).Valid f)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  have hv := (Datum.valid_quantum_iff ..).mp hd
  exact neighbor_quantum_minimal f c d q r (nextUp_full f x hx s c q hout) hv.1 hv.2.1 he

theorem nextDown_quantum_minimal (f : Format) (x : Datum) (hx : x.Valid f)
    (s : Bool) (c : Nat) (q : Int) (hout : (nextDown f x).value = .finite s c q)
    (d : Nat) (r : Int) (hd : (Datum.finite s d r).Valid f)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  have hn : x.negate.Valid f := by simpa [Datum.negate_eq_withSign] using hx
  have ho : (nextUp f x.negate).value = .finite (!s) c q := by
    have h := congrArg Datum.negate hout
    change (nextUp f x.negate).value.negate.negate = (Datum.finite s c q).negate at h
    rw [Datum.negate_negate] at h
    exact h
  exact nextUp_quantum_minimal f x.negate hn (!s) c q ho d r hd he

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
