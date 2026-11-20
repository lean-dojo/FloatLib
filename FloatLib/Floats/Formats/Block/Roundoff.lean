/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Catalog
public import FloatLib.Floats.Formats.Block.CodedDot.Reduction
public import FloatLib.Tactic.Roundoff

/-!
# `roundoff` rules for block-scaled formats

These registrations give `roundoff` the block theory, so that a program written with
`Block.Format.reconstruct`, `Block.accumulate` or `Block.accumulateChunked` gets its bound without
a proof:

* `Format.reconstruct_mixedError`: a reconstructed element approximates its input with the
  relative error of the element format and absolute error `|σ| * η + max 0 (|x| - |σ| * M)`,
  where `σ` is the element's total scale. The rule has no premise: it holds for every level
  structure, selection rule and scale, zero included.
* `accumulate_mixedError`, `accumulateChunked_mixedError`: ordered accumulation of given terms in
  an accumulator format, and accumulation with promotion of a narrow accumulator to a wide one.

The element and accumulator formats are found by instance search. `Rounding.HasBudget E u η M`
records the budget of an element format: saturating, unclipped and native rounding of every
binary descriptor, fixed point clipped to an interval that contains zero, signed fixed point, and
the exact format.
`Rounding.HasAccumulatorBudget A u η` records a budget without saturation, for the unclipped
rounding of a binary descriptor and the exact format. A sum of products of reconstructed values
is then bounded by the existing rules for real sums and products.

`Format.quantize_mixedError` is not a rule. It states the same budget for the stored element
against its exact scaled input. A kernel on stored element words and scale words takes it as a
hypothesis about its operands, and `roundoff` then states the kernel's bound against the exact
scaled inputs (the tests do this for a dot product in the order of NVFP4's matrix product). For
the codes of the stored formats with OCP MX elements the hypothesis is the theorem
`OCP.MX.Standard.Profile.encode_mixedError`.

`Tensor.Dot_rounding` and `Tensor.DotGeneral_rounding` cover exact dot products of stored
`Block.Tensor` operands (OCP MX v1.0, §§6.1–6.2). Finite decoded operands and a finite result
give the mixed error of one final rounding, against the exact sum of the stored values.
A caller exposes this proved bound as a local contract before composing the dot with further
arithmetic. Automatic discovery of stored `Tensor.value` inputs is not yet supported.

`Tensor.Dot_binary_rounding` permits a supplied product projection and finite binary accumulator.
`Tensor.Dot_nearest_binary_rounding` and `Tensor.DotGeneral_nearest_binary_rounding` instantiate
nearest-even product projection. They retain finite products, finite partial sums and a finite
delivered result as explicit range hypotheses, and allow cancellation in the exact reference sum.

What these rules do not cover: scale selection in a finite working precision and rounding
directions other than nearest-even. A block dot product on stored binary words, with casts to
an accumulator format, uses the mixed-precision cast and product rules of `roundoff` directly.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

variable {ι γ : Type*}

/-- The error budget of an element format, for instance search: relative error `u`, absolute
error `η`, saturation at `M`. -/
class Rounding.HasBudget (E : Rounding ℝ) (u η M : outParam ℝ) : Prop where
  /-- The format has this budget. -/
  budget : E.Budget u η M
  /-- The relative error is nonnegative. -/
  relative_nonneg : 0 ≤ u
  /-- The absolute error is nonnegative. -/
  absolute_nonneg : 0 ≤ η

/-- The error budget of an accumulator format that does not saturate, for instance search. -/
class Rounding.HasAccumulatorBudget (A : Rounding ℝ) (u η : outParam ℝ) : Prop where
  /-- Every rounding is within `u * |z| + η` of its input. -/
  budget : ∀ z, |A.round z - z| ≤ u * |z| + η
  /-- The relative error is nonnegative. -/
  relative_nonneg : 0 ≤ u
  /-- The absolute error is nonnegative. -/
  absolute_nonneg : 0 ≤ η

namespace Rounding

/-- The budget of a saturating binary format: its unit roundoff, its underflow error and its
largest finite value. -/
instance (fmt : FloatFormat) :
    HasBudget (saturating fmt) (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt)
      (Model.toReal (Model.posMaxFinite fmt)) where
  budget := saturating_budget fmt
  relative_nonneg := (Model.unitRoundoffAt_pos fmt).le
  absolute_nonneg := (Model.underflowErrorAt_pos fmt).le

/-- The budget of the grid of a binary format, up to the format's largest finite value: its unit
roundoff and its underflow error. -/
instance (fmt : FloatFormat) :
    HasBudget (grid fmt) (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt)
      (Model.toReal (Model.posMaxFinite fmt)) where
  budget := grid_budget fmt _
  relative_nonneg := (Model.unitRoundoffAt_pos fmt).le
  absolute_nonneg := (Model.underflowErrorAt_pos fmt).le

/-- The budget of the rounding of a binary format: its unit roundoff, its underflow error and its
largest finite value. -/
instance (fmt : FloatFormat) :
    HasBudget (ofFormat fmt) (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt)
      (Model.toReal (Model.posMaxFinite fmt)) where
  budget := ofFormat_budget fmt
  relative_nonneg := (Model.unitRoundoffAt_pos fmt).le
  absolute_nonneg := (Model.underflowErrorAt_pos fmt).le

/-- Exact arithmetic has the zero budget. -/
instance : HasBudget (exact : Rounding ℝ) 0 0 0 where
  budget := exact_budget 0
  relative_nonneg := le_rfl
  absolute_nonneg := le_rfl

/-- The budget of fixed point clipped to `[lo, hi]`: half a step, and saturation at the smaller of
`-lo` and `hi`. -/
instance (frac : ℤ) (lo hi : ℝ) :
    HasBudget (fixed frac lo hi) 0 ((2 : ℝ) ^ (-frac - 1)) (min (-lo) hi) where
  budget := fixed_budget frac
  relative_nonneg := le_rfl
  absolute_nonneg := (zpow_pos (by norm_num) _).le

/-- The budget of signed fixed point: half a step, and saturation at its largest value. -/
instance (int frac : ℕ) :
    HasBudget (signedFixed int frac) 0 ((2 : ℝ) ^ (-(frac : ℤ) - 1))
      ((2 : ℝ) ^ ((int : ℤ) - 1) - (2 : ℝ) ^ (-(frac : ℤ))) where
  budget := signedFixed_budget int frac
  relative_nonneg := le_rfl
  absolute_nonneg := (zpow_pos (by norm_num) _).le

/-- The accumulator budget of the grid of a binary format: its unit roundoff and its underflow
error. -/
instance (fmt : FloatFormat) :
    HasAccumulatorBudget (grid fmt) (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt) where
  budget := Model.abs_roundAt_sub_le_unitRoundoffAt fmt
  relative_nonneg := (Model.unitRoundoffAt_pos fmt).le
  absolute_nonneg := (Model.underflowErrorAt_pos fmt).le

/-- An exact accumulator has the zero budget. -/
instance : HasAccumulatorBudget (exact : Rounding ℝ) 0 0 where
  budget z := by simp [exact]
  relative_nonneg := le_rfl
  absolute_nonneg := le_rfl

end Rounding

/--
`roundoff` rule for block quantization: a reconstructed element approximates its input with the
relative error of the element format, and with its absolute error and its saturation threshold
multiplied by the magnitude of the element's total scale. There is no premise.
-/
theorem Format.reconstruct_mixedError (F : Format ι γ ℝ) (x : ι → ℝ) (i : ι) {u η M : ℝ}
    [h : Rounding.HasBudget (F.element i) u η M] :
    MixedError (F.reconstruct x i) (x i) u
      (|F.scale x i| * η + max 0 (|x i| - |F.scale x i| * M)) where
  r_nonneg := h.relative_nonneg
  a_nonneg := add_nonneg (mul_nonneg (abs_nonneg _) h.absolute_nonneg) (le_max_left _ _)
  bound := by
    have := F.abs_reconstruct_sub_le_abs x i h.budget h.relative_nonneg
    linarith

/--
A stored element approximates its exact scaled input within the element budget: relative error
`u`, and absolute error `η` plus the excess of the scaled input over `M`. There is no premise.
This is the hypothesis that a kernel on stored elements and scales takes about its operands.
-/
theorem Format.quantize_mixedError (F : Format ι γ ℝ) (x : ι → ℝ) (i : ι) {u η M : ℝ}
    [h : Rounding.HasBudget (F.element i) u η M] :
    MixedError (F.quantize x i) (F.normalized x i) u
      (η + max 0 (|F.normalized x i| - M)) where
  r_nonneg := h.relative_nonneg
  a_nonneg := add_nonneg h.absolute_nonneg (le_max_left _ _)
  bound := by
    have := h.budget (F.normalized x i)
    simp only [Format.quantize]
    linarith

/-- `roundoff` rule for ordered accumulation of given terms in an accumulator format. -/
theorem accumulate_mixedError (A : Rounding ℝ) {u η : ℝ} [h : Rounding.HasAccumulatorBudget A u η]
    (terms : List ℝ) :
    MixedError (accumulate A terms) terms.sum 0
      (((1 + u) ^ terms.length - 1) * (terms.map abs).sum +
        terms.length * (1 + u) ^ terms.length * η) where
  r_nonneg := le_rfl
  a_nonneg := by
    have hpow : 1 ≤ (1 + u) ^ terms.length := one_le_pow₀ (by linarith [h.relative_nonneg])
    have habs : 0 ≤ (terms.map abs).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        exact abs_nonneg _
    have hη := h.absolute_nonneg
    have hn : (0 : ℝ) ≤ terms.length := Nat.cast_nonneg _
    have h1 : 0 ≤ ((1 + u) ^ terms.length - 1) * (terms.map abs).sum :=
      mul_nonneg (by linarith) habs
    have h2 : 0 ≤ (terms.length : ℝ) * (1 + u) ^ terms.length * η :=
      mul_nonneg (mul_nonneg hn (by linarith)) hη
    linarith
  bound := by
    have := abs_accumulate_sub_le h.relative_nonneg h.absolute_nonneg h.budget terms
    linarith

/-- The largest length of a chunk. -/
def chunkBound (chunks : List (List ℝ)) : ℕ :=
  chunks.foldr (fun chunk bound => max chunk.length bound) 0

/-- Every chunk has at most `chunkBound` terms. -/
theorem length_le_chunkBound (chunks : List (List ℝ)) :
    ∀ chunk ∈ chunks, chunk.length ≤ chunkBound chunks := by
  induction chunks with
  | nil => simp
  | cons head tail ih =>
    intro chunk hchunk
    rcases List.mem_cons.mp hchunk with rfl | hmem
    · exact le_max_left _ _
    · exact (ih chunk hmem).trans (le_max_right _ _)

/--
`roundoff` rule for accumulation with promotion: each chunk is accumulated in the narrow format
and the chunk results in the wide format. With `m` chunks of at most `k` terms the absolute error
is at most `((1 + u_W) ^ m * (1 + u_N) ^ k - 1) * ∑ |t|` plus
`m * (1 + u_W) ^ m * (k * (1 + u_N) ^ k * η_N + η_W)`.
-/
theorem accumulateChunked_mixedError (N W : Rounding ℝ) {uN ηN uW ηW : ℝ}
    [hN : Rounding.HasAccumulatorBudget N uN ηN] [hW : Rounding.HasAccumulatorBudget W uW ηW]
    (chunks : List (List ℝ)) :
    MixedError (accumulateChunked N W chunks) (chunks.map List.sum).sum 0
      (((1 + uW) ^ chunks.length * (1 + uN) ^ chunkBound chunks - 1) *
          (chunks.map fun chunk => (chunk.map abs).sum).sum +
        chunks.length * (1 + uW) ^ chunks.length *
          (chunkBound chunks * (1 + uN) ^ chunkBound chunks * ηN + ηW)) where
  r_nonneg := le_rfl
  a_nonneg := by
    have hpW : 1 ≤ (1 + uW) ^ chunks.length := one_le_pow₀ (by linarith [hW.relative_nonneg])
    have hpN : 1 ≤ (1 + uN) ^ chunkBound chunks := one_le_pow₀ (by linarith [hN.relative_nonneg])
    have hT : 0 ≤ (chunks.map fun chunk => (chunk.map abs).sum).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨chunk, -, rfl⟩ := List.mem_map.mp hx
        exact List.sum_nonneg fun y hy => by
          obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
          exact abs_nonneg _
    have hm : (0 : ℝ) ≤ chunks.length := Nat.cast_nonneg _
    have hk : (0 : ℝ) ≤ chunkBound chunks := Nat.cast_nonneg _
    have hηN := hN.absolute_nonneg
    have hηW := hW.absolute_nonneg
    have h1 : 0 ≤ ((1 + uW) ^ chunks.length * (1 + uN) ^ chunkBound chunks - 1) *
        (chunks.map fun chunk => (chunk.map abs).sum).sum :=
      mul_nonneg (by linarith [one_le_mul_of_one_le_of_one_le hpW hpN]) hT
    have h2 : 0 ≤ (chunks.length : ℝ) * (1 + uW) ^ chunks.length *
        (chunkBound chunks * (1 + uN) ^ chunkBound chunks * ηN + ηW) :=
      mul_nonneg (mul_nonneg hm (by linarith))
        (add_nonneg (mul_nonneg (mul_nonneg hk (by linarith)) hηN) hηW)
    linarith
  bound := by
    have := abs_accumulateChunked_sub_le hN.relative_nonneg hN.absolute_nonneg
      hW.relative_nonneg hW.absolute_nonneg hN.budget hW.budget chunks (chunkBound chunks)
      (length_le_chunkBound chunks)
    linarith

/-- OCP MX v1.0, §6.1: a finite exact dot incurs one rounding against its decoded operands. -/
theorem Tensor.Dot_rounding {ι γ δ : Type} {F : CodedFormat ι γ} {G : CodedFormat ι δ}
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a : Tensor F) (b : Tensor G) (order : List ι)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (OCP.MX.Dot fmt a b order) = true) :
    MixedError (Model.toReal (OCP.MX.Dot fmt a b order))
      (((order.map fun i => a.value i * b.value i).sum : ℚ) : ℝ)
      (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt) :=
  Model.mixedError_toReal_of_eq_roundAt (toReal_Dot_eq_roundAt fmt hfmt a b order ha hb hfinite)

/-- OCP MX v1.0, §6.2: exact block reduction incurs one rounding against the block sums. -/
theorem Tensor.DotGeneral_rounding {ι γ δ : Type} {F : CodedFormat ι γ} {G : CodedFormat ι δ}
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a : Tensor F) (b : Tensor G)
    (blocks : List (List ι))
    (ha : ∀ block ∈ blocks, ∀ i ∈ block, (a.decode i).isFinite = true)
    (hb : ∀ block ∈ blocks, ∀ i ∈ block, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (OCP.MX.DotGeneral fmt a b blocks) = true) :
    MixedError (Model.toReal (OCP.MX.DotGeneral fmt a b blocks))
      (((blocks.map fun block => (block.map fun i => a.value i * b.value i).sum).sum : ℚ) : ℝ)
      (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt) :=
  Model.mixedError_toReal_of_eq_roundAt
    (toReal_DotGeneral_eq_roundAt fmt hfmt a b blocks ha hb hfinite)

attribute [roundoff_rule] Format.reconstruct_mixedError accumulate_mixedError
  accumulateChunked_mixedError Tensor.Dot_rounding Tensor.DotGeneral_rounding

end FloatLib.Floats.Formats.Block
