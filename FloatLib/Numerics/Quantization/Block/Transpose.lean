/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Policy
public import Mathlib.Data.Fintype.Prod

/-!
# Block shapes and transposition

`tiles k l` groups a matrix into tiles of `k` rows and `l` columns. It is the only shape: `1 × l`
blocks along a row are `tiles 1 l`, `k × 1` blocks along a column are `tiles k 1`, and since
natural division by zero is zero, `tiles 0 0` is one group for the tensor, `tiles 1 0` one group
per row (per expert, per token) and `tiles 0 1` one group per column.

A forward pass multiplies by a quantized weight and the backward pass by its transpose. Hardware
block scaling groups along the dot-product dimension, so the two passes quantize the same matrix
along different axes. `Format.reconstruct_relabel` states when relabelling the elements commutes
with quantization: every level must select, for the relabelled data, the scale it selects for the
original data (`Level.Transports`). Selection from the largest magnitude, selection among candidate
targets and caller-supplied scales all have this property when the relabelling carries groups to
groups (`Level.transports_ofMax`, `Level.transports_ofCandidates`, `Level.transports_supplied`).

Transposition carries `tiles k l` to `tiles l k` (`tiles_swap`). So quantizing the transpose with
`l × k` tiles is the transpose of quantizing with `k × l` tiles (`reconstruct_transpose`), and for
square tiles quantizing along rows and along columns give the same decoded matrix
(`reconstruct_transpose_square`). For `1 × l` blocks with `l > 1` the transposed data would need
`l × 1` blocks, which is not the shape hardware applies to it, and the test module
`Conformance.Formats.BlockExamples` has a matrix on which the two decoded matrices differ.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

variable {ι ι' γ γ' K : Type*}

/-- Tiles of `k` rows and `l` columns of a matrix, identified by their tile coordinates. A zero
size puts the whole axis in one tile. -/
def tiles {m n : ℕ} (k l : ℕ) (p : Fin m × Fin n) : ℕ × ℕ :=
  (p.1 / k, p.2 / l)

/-- Transposition exchanges the two tile sizes. -/
theorem tiles_swap {m n : ℕ} (k l : ℕ) (p : Fin n × Fin m) :
    tiles l k p = (tiles k l (Equiv.prodComm (Fin n) (Fin m) p)).swap :=
  rfl

/--
`L'` selects for relabelled data the scales `L` selects for the original data: with elements
relabelled by `π`, the scale `L'` stores for the element `i` is the scale `L` stores for `π i`.
-/
def Level.Transports (π : ι' → ι) (L' : Level ι' γ' K) (L : Level ι γ K) : Prop :=
  ∀ (y : ι → K) (i : ι'), L'.scaleAt (fun j => y (π j)) i = L.scaleAt y (π i)

section Field

variable [Field K]

/-- Levels that transport along `π` normalize relabelled data to the relabelled normalized data. -/
theorem normalize_relabel {π : ι' → ι} {levels' : List (Level ι' γ' K)}
    {levels : List (Level ι γ K)} (h : List.Forall₂ (Level.Transports π) levels' levels)
    (x : ι → K) (i : ι') :
    normalize levels' (fun j => x (π j)) i = normalize levels x (π i) := by
  induction h generalizing x with
  | nil => rfl
  | cons hL _ ih =>
    simp only [normalize]
    rw [← ih]
    congr 1
    funext j
    rw [hL x j]

/-- Levels that transport along `π` select for relabelled data the relabelled total scales. -/
theorem total_relabel {π : ι' → ι} {levels' : List (Level ι' γ' K)}
    {levels : List (Level ι γ K)} (h : List.Forall₂ (Level.Transports π) levels' levels)
    (x : ι → K) (i : ι') :
    total levels' (fun j => x (π j)) i = total levels x (π i) := by
  induction h generalizing x with
  | nil => rfl
  | cons hL _ ih =>
    simp only [total]
    rw [hL x i, ← ih]
    congr 2
    funext j
    rw [hL x j]

/--
Relabelling commutes with quantization. If the element formats agree along `π` and every level of
`F'` transports to the corresponding level of `F`, the values `F'` reconstructs from the relabelled
data are the relabelled values `F` reconstructs. For transposition this is the absence of a
mismatch between the forward and the backward weight.
-/
theorem Format.reconstruct_relabel {π : ι' → ι} {F' : Format ι' γ' K} {F : Format ι γ K}
    (helement : ∀ i, F'.element i = F.element (π i))
    (hlevels : List.Forall₂ (Level.Transports π) F'.levels F.levels) (x : ι → K) (i : ι') :
    F'.reconstruct (fun j => x (π j)) i = F.reconstruct x (π i) := by
  simp only [Format.reconstruct, Format.decode, Format.quantize, Format.normalized, Format.scale]
  rw [normalize_relabel hlevels, total_relabel hlevels, helement]

end Field

/-- Caller-supplied scales transport when the relabelling carries each scale to its group. -/
theorem Level.transports_supplied (π : ι' → ι) (τ : γ → γ') {group : ι → γ} {group' : ι' → γ'}
    (hgroup : ∀ i, group' i = τ (group (π i))) (format : Rounding K) {s : γ → K} {s' : γ' → K}
    (hs : ∀ g, s' (τ g) = s g) :
    (Level.supplied group' format s').Transports π (Level.supplied group format s) := by
  intro y i
  simp [Level.scaleAt, Level.supplied, Level.scale, hgroup, hs]

section Max

variable [Field K] [LinearOrder K]
  [Fintype ι] [Fintype ι'] [DecidableEq γ] [DecidableEq γ']

/--
Selection from the largest magnitude transports along any bijection of the elements that carries
groups to groups.
-/
theorem Level.transports_ofMax (π : ι' ≃ ι) (τ : γ → γ') (hτ : Function.Injective τ)
    {group : ι → γ} {group' : ι' → γ'} (hgroup : ∀ i, group' i = τ (group (π i)))
    (format : Rounding K) (target zero : K) :
    (Level.ofMax group' format target zero).Transports π
      (Level.ofMax group format target zero) := by
  intro y i
  simp only [Level.scaleAt, Level.scale, Level.ofMax, hgroup,
    amax_comp_equiv π τ hτ hgroup y]

/-- The measured error of a candidate target is kept by a bijection of the elements that carries
groups to groups and element formats to element formats. -/
theorem candidateError_comp_equiv (π : ι' ≃ ι) (τ : γ → γ') (hτ : Function.Injective τ)
    {group : ι → γ} {group' : ι' → γ'} (hgroup : ∀ i, group' i = τ (group (π i)))
    (format : Rounding K) {element : ι → Rounding K} {element' : ι' → Rounding K}
    (helement : ∀ i, element' i = element (π i)) (measure : K → K) (y : ι → K) (g : γ)
    (target : K) :
    candidateError group' format element' measure (fun j => y (π j)) (τ g) target =
      candidateError group format element measure y g target := by
  unfold candidateError
  rw [amax_comp_equiv π τ hτ hgroup y]
  refine Finset.sum_equiv π (fun i => ?_) (fun i _ => by rw [helement])
  simp only [mem_members, hgroup]
  exact ⟨fun h => hτ h, fun h => congrArg τ h⟩

/--
Selection among candidate targets transports along any bijection of the elements that carries
groups to groups and element formats to element formats.
-/
theorem Level.transports_ofCandidates (π : ι' ≃ ι) (τ : γ → γ') (hτ : Function.Injective τ)
    {group : ι → γ} {group' : ι' → γ'} (hgroup : ∀ i, group' i = τ (group (π i)))
    (format : Rounding K) {element : ι → Rounding K} {element' : ι' → Rounding K}
    (helement : ∀ i, element' i = element (π i)) (measure : K → K) (targets : List K)
    (zero : K) :
    (Level.ofCandidates group' format element' measure targets zero).Transports π
      (Level.ofCandidates group format element measure targets zero) := by
  intro y i
  have herror : candidateError group' format element' measure (fun j => y (π j))
      (τ (group (π i))) = candidateError group format element measure y (group (π i)) :=
    funext fun target =>
      candidateError_comp_equiv π τ hτ hgroup format helement measure y _ target
  simp only [Level.scaleAt, Level.scale, Level.ofCandidates, hgroup, selectedTarget, herror,
    amax_comp_equiv π τ hτ hgroup y]

/--
Quantizing the transpose with `l × k` tiles is the transpose of quantizing with `k × l` tiles, for
one level that selects each tile's scale from its largest magnitude and one element format.
-/
theorem reconstruct_transpose {m n : ℕ} (element scale : Rounding K) (target zero : K)
    (k l : ℕ) (x : Fin m × Fin n → K) (i : Fin n) (j : Fin m) :
    (Format.mk (fun _ => element)
        [Level.ofMax (tiles (m := n) (n := m) l k) scale target zero]).reconstruct
        (fun p => x (p.2, p.1)) (i, j) =
      (Format.mk (fun _ => element)
        [Level.ofMax (tiles (m := m) (n := n) k l) scale target zero]).reconstruct x (j, i) :=
  Format.reconstruct_relabel (π := Equiv.prodComm (Fin n) (Fin m)) (fun _ => rfl)
    (List.Forall₂.cons
      (Level.transports_ofMax (Equiv.prodComm (Fin n) (Fin m)) Prod.swap
        Prod.swap_injective (tiles_swap k l) scale target zero) List.Forall₂.nil) x (i, j)

/--
With square tiles, quantizing a square matrix along rows and along columns give the same decoded
matrix: quantizing the transpose is the transpose of quantizing.
-/
theorem reconstruct_transpose_square {n : ℕ} (element scale : Rounding K) (target zero : K)
    (k : ℕ) (x : Fin n × Fin n → K) (i j : Fin n) :
    (Format.mk (fun _ => element)
        [Level.ofMax (tiles (m := n) (n := n) k k) scale target zero]).reconstruct
        (fun p => x (p.2, p.1)) (i, j) =
      (Format.mk (fun _ => element)
        [Level.ofMax (tiles (m := n) (n := n) k k) scale target zero]).reconstruct x (j, i) :=
  reconstruct_transpose element scale target zero k k x i j

end Max

end FloatLib.Floats.Formats.Block
