/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Proof
import Mathlib.Tactic.Linarith

/-!
# Adjacency of the public decimal neighbor operations

The quantified bounds compare the delivered result with every valid finite
datum, including other cohorts and either sign of zero. The endpoint theorems
cover infinite results separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

private theorem finite_witness (x : Datum) (v : ℚ) (hv : x.toRat? = some v) :
    ∃ s c q, x = .finite s c q ∧ v = Datum.finiteValue s c q := by
  cases x with
  | finite s c q =>
      refine ⟨s, c, q, rfl, ?_⟩
      simp only [Datum.toRat?_eq] at hv
      exact (Option.some.inj hv).symm
  | infinity s => contradiction
  | nan s t p => contradiction

/-- The finite successor is strictly greater, and no valid finite value lies between them. -/
theorem nextUp_finite_adjacent (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hx : (Datum.finite s c q).Valid f) (v : ℚ)
    (hout : (nextUp f (.finite s c q)).value.toRat? = some v) :
    Datum.finiteValue s c q < v ∧
      ∀ (t : Bool) (d : Nat) (r : Int), (Datum.finite t d r).Valid f →
        Datum.finiteValue s c q < Datum.finiteValue t d r →
        v ≤ Datum.finiteValue t d r := by
  have hpq : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) _
  by_cases hc : c = 0
  · have hv : v = (10 : ℚ) ^ f.minQuantum := by
      simpa [nextUp, hc, Datum.toRat?_eq] using hout.symm
    rw [hv]
    simp only [hc, Datum.finiteValue, Nat.cast_zero, mul_zero, zero_mul]
    refine ⟨zpow_pos (by norm_num) _, ?_⟩
    intro t d r hd hlt
    have hr := ((Datum.valid_quantum_iff ..).mp hd).2.1
    have hn : 0 ≤ (d : ℚ) * (10 : ℚ) ^ r :=
      mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
    cases t
    · simpa using neighbor_integer_gap 0 d f.minQuantum r hr (by simpa using hlt)
    · simp only [↓reduceIte, neg_mul, one_mul] at hlt
      linarith
  · obtain ⟨a, b, hp, ha, hapos, hbmin, hbmax, hfull, he⟩ :=
      neighbor_normalize f s c q hx hc
    have hpb : 0 < (10 : ℚ) ^ b := zpow_pos (by norm_num) _
    have han : (0 : ℚ) ≤ a := Nat.cast_nonneg _
    have hapos' : (0 : ℚ) < a := by exact_mod_cast hapos
    simp only [nextUp, ite_eq_right hc, hp] at hout
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hout
      obtain ⟨t, d, r, hv, hvalue⟩ := finite_witness (neighborAbove f a b) v hout
      obtain ⟨rfl, hdvalue⟩ := neighborAbove_finite f a d b r t ha hv
      have hv' : v = ((a + 1 : Nat) : ℚ) * (10 : ℚ) ^ b := by
        simpa [Datum.finiteValue] using hvalue.trans (by simpa [Datum.finiteValue] using hdvalue)
      rw [hv']
      simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte, one_mul]
      constructor
      · rw [← he, Nat.cast_add, Nat.cast_one]
        nlinarith
      · intro t e u hu hlt
        have hu' := (Datum.valid_quantum_iff ..).mp hu
        have hn : 0 ≤ (e : ℚ) * (10 : ℚ) ^ u :=
          mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
        cases t
        · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hlt ⊢
          exact neighbor_gap f a e b u hfull hu'.1 hu'.2.1 (by rwa [he])
        · simp only [↓reduceIte, neg_mul, one_mul] at hlt
          nlinarith [mul_nonneg han hpb.le]
    · simp only [↓reduceIte] at hout
      obtain ⟨d, r, hv, hdvalid, hdfull, hstep⟩ :=
        neighborBelow_spec f a b ha hapos hbmin hbmax hfull
      have hv' : v = -((d : ℚ) * (10 : ℚ) ^ r) := by
        simpa [hv, Datum.negate, Datum.toRat?_eq] using hout.symm
      have hpr : 0 < (10 : ℚ) ^ r := zpow_pos (by norm_num) _
      have hdnonneg : 0 ≤ (d : ℚ) * (10 : ℚ) ^ r :=
        mul_nonneg (Nat.cast_nonneg _) hpr.le
      have hstep' : ((d : ℚ) + 1) * (10 : ℚ) ^ r = (c : ℚ) * (10 : ℚ) ^ q := by
        simpa using hstep.trans he
      rw [hv']
      simp only [Datum.finiteValue, ↓reduceIte, neg_mul, one_mul]
      constructor
      · nlinarith [hstep']
      · intro t e u hu hlt
        have hu' := (Datum.valid_quantum_iff ..).mp hu
        have hn : 0 ≤ (e : ℚ) * (10 : ℚ) ^ u :=
          mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
        cases t
        · simpa using neg_nonpos.mpr hdnonneg |>.trans hn
        · simp only [↓reduceIte, neg_mul, one_mul] at hlt ⊢
          by_contra h
          have hlt' : (d : ℚ) * (10 : ℚ) ^ r < (e : ℚ) * (10 : ℚ) ^ u := by
            linarith
          have hgap := neighbor_gap f d e r u hdfull hu'.1 hu'.2.1 hlt'
          rw [hstep, he] at hgap
          linarith

/-- Public successor adjacency expressed entirely in exact numerical values. -/
theorem nextUp_adjacent (f : Format) (x : Datum) (hx : x.Valid f)
    (a b : ℚ) (ha : x.toRat? = some a) (hb : (nextUp f x).value.toRat? = some b) :
    a < b ∧ ∀ (y : Datum) (v : ℚ), y.Valid f → y.toRat? = some v → a < v → b ≤ v := by
  obtain ⟨s, c, q, rfl, rfl⟩ := finite_witness x a ha
  have h := nextUp_finite_adjacent f s c q hx b hb
  refine ⟨h.1, ?_⟩
  intro y v hy hv hlt
  obtain ⟨t, d, r, rfl, rfl⟩ := finite_witness y v hv
  exact h.2 t d r hy hlt

/-- Negation transfers successor adjacency to the public predecessor operation. -/
theorem nextDown_adjacent (f : Format) (x : Datum) (hx : x.Valid f)
    (a b : ℚ) (ha : x.toRat? = some a) (hb : (nextDown f x).value.toRat? = some b) :
    b < a ∧ ∀ (y : Datum) (v : ℚ), y.Valid f → y.toRat? = some v → v < a → v ≤ b := by
  have hn : x.negate.Valid f := by simpa [Datum.negate_eq_withSign] using hx
  have hna : x.negate.toRat? = some (-a) := by rw [Datum.negate_toRat?, ha]; rfl
  have hnb : (nextUp f x.negate).value.toRat? = some (-b) := by
    have he := congrArg (fun z => z.map (- ·)) hb
    change (nextUp f x.negate).value.negate.toRat?.map (- ·) = _ at he
    rw [← Datum.negate_toRat?, Datum.negate_negate] at he
    exact he
  have h := nextUp_adjacent f x.negate hn (-a) (-b) hna hnb
  refine ⟨by linarith [h.1], ?_⟩
  intro y v hy hv hlt
  have hyn : y.negate.Valid f := by simpa [Datum.negate_eq_withSign] using hy
  have hyv : y.negate.toRat? = some (-v) := by rw [Datum.negate_toRat?, hv]; rfl
  have hle := h.2 y.negate (-v) hyn hyv (by linarith)
  linarith

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
