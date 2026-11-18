/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Ordered
public import FloatLib.Numerics.Quantization.Stochastic.Cell

/-!
# One stochastic grid interface for numerical systems

The grid is the existing `NumericalSystem.Representable` predicate after mapping its
finite scalars to reals. `neighbors_of_finite` constructs `Ordered.Brackets` for every
finite code type whenever the input lies between representable values.

`neighborLaw` extends the strict cell law to coincident neighbors, which occur at exact
grid inputs. Its expectation, variance, and representable support are independent of
the format. Saturating an input before applying this law changes its expectation by
exactly the clipping displacement. Exceptional encodings are excluded by `Represents`.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory

/-- A finite encoding has finitely many real finite values, including duplicate encodings. -/
theorem finite_representable (S : NumericalSystem) (f : S.Scalar → ℝ) [Finite S.Code] :
    {x | (S.mapScalar f).Representable x}.Finite := by
  have h : (Set.range (S.mapScalar f).denote).Finite := Set.finite_range _
  have hi : Function.Injective (NumericalValue.finite : ℝ → NumericalValue ℝ) :=
    fun _ _ h ↦ NumericalValue.finite.inj h
  have hf := Set.Finite.preimage hi.injOn h
  exact hf

/-- Every in-range input of a finite format has representable lower and upper neighbors. -/
theorem neighbors_of_finite (S : NumericalSystem) (f : S.Scalar → ℝ) [Finite S.Code]
    (x : ℝ) (hlo : ∃ a, (S.mapScalar f).Representable a ∧ a ≤ x)
    (hhi : ∃ b, (S.mapScalar f).Representable b ∧ x ≤ b) :
    ∃ lo hi, Ordered.Brackets (S.mapScalar f) x lo hi := by
  have hl := Set.Nonempty.isGreatest_csSup (s := {a | (S.mapScalar f).Representable a ∧ a ≤ x})
    hlo ((finite_representable S f).subset
    (by intro a ha; exact ha.1))
  have hu := Set.Nonempty.isLeast_csInf (s := {b | (S.mapScalar f).Representable b ∧ x ≤ b})
    hhi ((finite_representable S f).subset
    (by intro b hb; exact hb.1))
  obtain ⟨lo, hloRep⟩ := hl.1.1
  obtain ⟨hi, hhiRep⟩ := hu.1.1
  exact ⟨lo, hi,
    (Ordered.lowerNeighbor_iff_isGreatest (S.mapScalar f) x lo).2 ⟨_, hloRep, hl⟩,
    (Ordered.upperNeighbor_iff_isLeast (S.mapScalar f) x hi).2 ⟨_, hhiRep, hu⟩⟩

/-- Stochastic rounding also fixes an exact input whose two neighbors coincide. -/
noncomputable def neighborLaw (a b x : ℝ) (hx : x ∈ Set.Icc a b) : Measure ℝ :=
  if h : a < b then cellLaw a b x h hx else Measure.dirac x

/-- The law of one stochastic rounding between two neighbors is a probability measure. -/
instance (a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    IsProbabilityMeasure (neighborLaw a b x hx) := by
  unfold neighborLaw
  split_ifs <;> infer_instance

/-- Exact real expectation, including the degenerate grid cell. -/
theorem mean_neighborLaw (a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    ∫ y, y ∂neighborLaw a b x hx = x := by
  unfold neighborLaw
  split_ifs with h
  · exact mean_cellLaw a b x h hx
  · simp

/-- The sharp variance formula remains valid at exact grid inputs. -/
theorem variance_neighborLaw (a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    variance (fun y : ℝ ↦ y) (neighborLaw a b x hx) = (x - a) * (b - x) := by
  unfold neighborLaw
  split_ifs with h
  · exact variance_cellLaw a b x h hx
  · have hax : a = x := by linarith [hx.1, hx.2]
    have hbx : b = x := by linarith [hx.1, hx.2]
    subst a b
    simp

/-- The stochastic result stays in the format's finite real grid almost surely. -/
theorem ae_neighborLaw_representable (S : NumericalSystem) (f : S.Scalar → ℝ)
    (a b x : ℝ) (lo hi : S.Code) (h : Ordered.Brackets (S.mapScalar f) x lo hi)
    (ha : (S.mapScalar f).Represents lo a) (hb : (S.mapScalar f).Represents hi b) :
    ∀ᵐ y ∂neighborLaw a b x
      ⟨Ordered.lowerNeighbor_le h.1 ha, Ordered.le_upperNeighbor h.2 hb⟩,
      (S.mapScalar f).Representable y := by
  have hx : x ∈ Set.Icc a b :=
    ⟨Ordered.lowerNeighbor_le h.1 ha, Ordered.le_upperNeighbor h.2 hb⟩
  unfold neighborLaw
  split_ifs with hab
  · filter_upwards [ae_bernoulli_endpoints a b (upProb a b x hab hx)] with y hy
    rcases hy with rfl | rfl
    · exact ⟨lo, ha⟩
    · exact ⟨hi, hb⟩
  · have hax : a = x := by linarith [hx.1, hx.2]
    simpa [MeasureTheory.ae_dirac_eq, ← hax] using
      (show (S.mapScalar f).Representable a from ⟨lo, ha⟩)

/-- Any prior change to the input, including saturation, contributes exactly its displacement. -/
theorem neighborLaw_input_bias (a b input target : ℝ) (h : input ∈ Set.Icc a b) :
    (∫ y, y ∂neighborLaw a b input h) - target = input - target := by
  rw [mean_neighborLaw]

end FloatLib.Numerics.Quantization.Stochastic
