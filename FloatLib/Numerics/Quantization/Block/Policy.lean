/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Format
public import FloatLib.Numerics.Quantization.Saturating
public import Mathlib.Data.Int.Log
public import Mathlib.Data.Rat.Floor

/-!
# Scale selection

A level selects the unrounded scale of each group and stores it rounded in its own format. The
selection rules of the block formats of ML accelerators are three constructors of `Level`:

* `Level.ofMax group format target zero` scales a group so that its largest magnitude `amax` maps
  to `target`: the ideal scale is `amax / target`, and `zero` for an all-zero group. With the
  element format's largest power of two as target and a scale format that rounds down to a power
  of two (`Rounding.pow2Floor`), this is the rule of OCP MX 1.0, section 6.3. With the largest
  element magnitude as target it is NVFP4's rule (NVIDIA, arXiv:2509.25149, Appendix B): the
  outer level stores `amax / (6 * 448)` in binary32 and the block level stores `amax / 6`,
  computed from the data divided by the outer scale, in E4M3. Rounding the power of two up
  (`Rounding.pow2Ceil`) gives the variants that avoid saturation.
* `Level.ofCandidates` evaluates several targets and keeps, group by group, the first one with the
  least measured reconstruction error. Four Over Six (Cook et al., arXiv:2512.02010) is the
  target list `[6, 4]`.
* `Level.supplied` stores a scale the caller chose.

## Main results

* `abs_le_amax`, `amax_le_iff`, `exists_abs_eq_amax`: `amax` is the largest magnitude of a group
  and is attained.
* `ofMax_abs_div_scale_le`, `ofMax_le_amax_div_scale`: if the stored scale lies between `c₁` and
  `c₂` times the ideal scale, every scaled magnitude of the group is at most `target / c₁` and the
  scaled maximum is at least `target / c₂`. An exact scale has `c₁ = c₂ = 1`, a scale format with
  relative error `ε` has `1 - ε` and `1 + ε`, rounding a power of two down has `1/2` and `1`, and
  rounding it up has `1` and `2`.
* `Rounding.pow2Floor_le`, `Rounding.lt_two_mul_pow2Floor`, `Rounding.le_pow2Ceil`,
  `Rounding.pow2Ceil_lt_two_mul`: the two power-of-two roundings inside their exponent range.
* `ofCandidates_error_le`: the target `Level.ofCandidates` keeps has the least measured error
  among its candidates. It is not optimal among all scales (the test module
  `Conformance.Formats.BlockExamples` has a block where a third scale is better).
* `total_append`: the levels above a level act on its data only through the normalized data, so
  a statement about one level applies to it at any depth.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

variable {ι γ K : Type*}

section Append

variable [Field K]

/-- The total scale of a list of levels is the total scale of its outer part times the total
scale its inner part selects for the data normalized by the outer part. -/
theorem total_append (outer inner : List (Level ι γ K)) (x : ι → K) (i : ι) :
    total (outer ++ inner) x i = total outer x i * total inner (normalize outer x) i := by
  induction outer generalizing x with
  | nil => simp [total, normalize]
  | cons L Ls ih => simp only [List.cons_append, total, normalize, ih, mul_assoc]

/-- The total scale of one level is its stored scale. -/
@[simp] theorem total_singleton (L : Level ι γ K) (x : ι → K) (i : ι) :
    total [L] x i = L.scaleAt x i := by
  simp [total]

end Append

namespace Level

/-- A scale chosen by the caller for each group. The data is not read. -/
def supplied (group : ι → γ) (format : Rounding K) (s : γ → K) : Level ι γ K where
  group := group
  format := format
  ideal _ g := s g

/-- A caller-supplied scale is stored rounded in the level's format. -/
@[simp] theorem supplied_scale (group : ι → γ) (format : Rounding K) (s : γ → K) (y : ι → K)
    (g : γ) : (supplied group format s).scale y g = format.round (s g) :=
  rfl

end Level

section Max

variable [Field K] [LinearOrder K] [Fintype ι] [DecidableEq γ]

/-- The elements of a group. -/
def members (group : ι → γ) (g : γ) : Finset ι :=
  Finset.univ.filter fun i => group i = g

/-- An element is a member of the group it maps to. -/
@[simp] theorem mem_members {group : ι → γ} {g : γ} {i : ι} :
    i ∈ members group g ↔ group i = g := by
  simp [members]

/-- Largest magnitude among the elements of a group, and zero for an empty group. -/
def amax (group : ι → γ) (y : ι → K) (g : γ) : K :=
  (members group g).fold max 0 fun i => |y i|

/-- The largest magnitude of a group is at most `c` exactly when `c` is nonnegative and bounds
every magnitude of the group. -/
theorem amax_le_iff {group : ι → γ} {y : ι → K} {g : γ} {c : K} :
    amax group y g ≤ c ↔ 0 ≤ c ∧ ∀ i, group i = g → |y i| ≤ c := by
  simp [amax, Finset.fold_max_le]

/-- The largest magnitude of a group is nonnegative. -/
theorem amax_nonneg (group : ι → γ) (y : ι → K) (g : γ) : 0 ≤ amax group y g :=
  (amax_le_iff.mp le_rfl).1

/-- Every element is bounded by the largest magnitude of its group. -/
theorem abs_le_amax (group : ι → γ) (y : ι → K) (i : ι) : |y i| ≤ amax group y (group i) :=
  (amax_le_iff.mp le_rfl).2 i rfl

/-- A positive largest magnitude is attained by an element of the group. -/
theorem exists_abs_eq_amax {group : ι → γ} {y : ι → K} {g : γ} (h : 0 < amax group y g) :
    ∃ i, group i = g ∧ |y i| = amax group y g := by
  rcases (Finset.le_fold_max (s := members group g) (b := (0 : K)) (f := fun i => |y i|)
    (c := amax group y g)).mp le_rfl with h0 | ⟨i, hi, hle⟩
  · exact absurd h0 (not_le.mpr h)
  · have hg : group i = g := mem_members.mp hi
    exact ⟨i, hg, le_antisymm (hg ▸ abs_le_amax group y i) hle⟩

/-- Relabelling elements and groups by bijections that carry one group map to the other keeps the
largest magnitude of each group. -/
theorem amax_comp_equiv {ι' γ' : Type*} [Fintype ι'] [DecidableEq γ']
    (π : ι' ≃ ι) (τ : γ → γ') (hτ : Function.Injective τ)
    {group : ι → γ} {group' : ι' → γ'} (hgroup : ∀ i, group' i = τ (group (π i)))
    (y : ι → K) (g : γ) :
    amax group' (fun i => y (π i)) (τ g) = amax group y g := by
  refine le_antisymm (amax_le_iff.mpr ⟨amax_nonneg group y g, fun i hi => ?_⟩)
    (amax_le_iff.mpr ⟨amax_nonneg group' _ _, fun i hi => ?_⟩)
  · rw [hgroup] at hi
    exact hτ hi ▸ abs_le_amax group y (π i)
  · have h := abs_le_amax group' (fun i => y (π i)) (π.symm i)
    rwa [hgroup, π.apply_symm_apply, hi] at h

namespace Level

/--
Scale each group so that its largest magnitude maps to `target`: the ideal scale is the group's
largest magnitude divided by `target`, and `zero` for a group whose elements are all zero.
-/
def ofMax (group : ι → γ) (format : Rounding K) (target zero : K) : Level ι γ K where
  group := group
  format := format
  ideal y g := if amax group y g = 0 then zero else amax group y g / target

/-- The scale stored for a group that is not all zero. -/
theorem ofMax_scale {group : ι → γ} {format : Rounding K} {target zero : K} {y : ι → K} {g : γ}
    (h : 0 < amax group y g) :
    (ofMax group format target zero).scale y g = format.round (amax group y g / target) := by
  simp [scale, ofMax, h.ne']

/-- The scale stored for an all-zero group. -/
theorem ofMax_scale_of_eq_zero {group : ι → γ} {format : Rounding K} {target zero : K}
    {y : ι → K} {g : γ} (h : amax group y g = 0) :
    (ofMax group format target zero).scale y g = format.round zero := by
  simp [scale, ofMax, h]

end Level

section Candidates

/--
Error a candidate target leaves in a group: the sum over the group of `measure` applied to the
element errors when the group is scaled so that its largest magnitude maps to `target`. The
squared error and the absolute error are the measures of Four Over Six.
-/
def candidateError (group : ι → γ) (format : Rounding K) (element : ι → Rounding K)
    (measure : K → K) (y : ι → K) (g : γ) (target : K) : K :=
  ∑ i ∈ members group g,
    measure (((element i).scaled (format.round (amax group y g / target))).round (y i) - y i)

/-- The target `Level.ofCandidates` keeps for a group: the first candidate with the least measured
error. -/
def selectedTarget (group : ι → γ) (format : Rounding K) (element : ι → Rounding K)
    (measure : K → K) (targets : List K) (y : ι → K) (g : γ) : Option K :=
  targets.argmin (candidateError group format element measure y g)

/--
Choose the target of each group among `targets`: every candidate is tried, and the first one with
the least measured reconstruction error is kept. An all-zero group and an empty candidate list get
the ideal scale `zero`. The level must be the last one, since the measured error is that of the
elements rounded at the candidate scale.
-/
def Level.ofCandidates (group : ι → γ) (format : Rounding K) (element : ι → Rounding K)
    (measure : K → K) (targets : List K) (zero : K) : Level ι γ K where
  group := group
  format := format
  ideal y g :=
    if amax group y g = 0 then zero
    else match selectedTarget group format element measure targets y g with
      | some target => amax group y g / target
      | none => zero

/-- The selected target is one of the candidates. -/
theorem selectedTarget_mem {group : ι → γ} {format : Rounding K} {element : ι → Rounding K}
    {measure : K → K} {targets : List K} {y : ι → K} {g : γ} {target : K}
    (h : selectedTarget group format element measure targets y g = some target) :
    target ∈ targets :=
  List.argmin_mem (by simpa [selectedTarget] using h)

/--
The selected target has the least measured error among the candidates. This is all the selection
guarantees: a scale outside the candidate list can have a smaller error.
-/
theorem ofCandidates_error_le {group : ι → γ} {format : Rounding K} {element : ι → Rounding K}
    {measure : K → K} {targets : List K} {y : ι → K} {g : γ} {target other : K}
    (h : selectedTarget group format element measure targets y g = some target)
    (hother : other ∈ targets) :
    candidateError group format element measure y g target ≤
      candidateError group format element measure y g other :=
  List.le_of_mem_argmin hother (by simpa [selectedTarget] using h)

/-- The scale `Level.ofCandidates` stores for a group that is not all zero is the rounded ideal
scale of its selected target. -/
theorem ofCandidates_scale {group : ι → γ} {format : Rounding K} {element : ι → Rounding K}
    {measure : K → K} {targets : List K} {zero : K} {y : ι → K} {g : γ} {target : K}
    (ha : 0 < amax group y g)
    (h : selectedTarget group format element measure targets y g = some target) :
    (Level.ofCandidates group format element measure targets zero).scale y g =
      format.round (amax group y g / target) := by
  simp [Level.scale, Level.ofCandidates, ha.ne', h]

/--
With `Level.ofCandidates` as the only level, the measured error of the format's reconstruction
over a group is the candidate error of the selected target, so the selection minimizes the error
the format actually leaves, among the candidates.
-/
theorem sum_measure_reconstruct_ofCandidates {group : ι → γ} {format : Rounding K}
    {element : ι → Rounding K} {measure : K → K} {targets : List K} {zero : K} {y : ι → K}
    {g : γ} {target : K} (ha : 0 < amax group y g)
    (h : selectedTarget group format element measure targets y g = some target) :
    ∑ i ∈ members group g,
        measure ((Format.mk element
          [Level.ofCandidates group format element measure targets zero]).reconstruct y i - y i) =
      candidateError group format element measure y g target := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hg : group i = g := mem_members.mp hi
  rw [Format.reconstruct_eq, Format.scale, total_singleton, Level.scaleAt,
    show (Level.ofCandidates group format element measure targets zero).group i = group i from rfl,
    hg, ofCandidates_scale ha h]

end Candidates

end Max

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι] [DecidableEq γ]

/-- The largest magnitude of a group is the bound of its magnitudes that one of them attains. -/
theorem amax_eq {group : ι → γ} {y : ι → K} {g : γ} {c : K}
    (hle : ∀ i, group i = g → |y i| ≤ c) (hex : ∃ i, group i = g ∧ |y i| = c) :
    amax group y g = c := by
  obtain ⟨i, hi, h⟩ := hex
  refine le_antisymm (amax_le_iff.mpr ⟨h ▸ abs_nonneg _, hle⟩) ?_
  rw [← h, ← hi]
  exact abs_le_amax group y i

/-- A group has largest magnitude zero exactly when all its elements are zero. -/
theorem amax_eq_zero_iff {group : ι → γ} {y : ι → K} {g : γ} :
    amax group y g = 0 ↔ ∀ i, group i = g → y i = 0 := by
  constructor
  · intro h i hi
    have := (amax_le_iff.mp h.le).2 i hi
    exact abs_nonpos_iff.mp this
  · intro h
    refine le_antisymm (amax_le_iff.mpr ⟨le_rfl, fun i hi => ?_⟩) (amax_nonneg group y g)
    simp [h i hi]

/-- Dividing a group by a positive scale that is constant on it divides its largest magnitude. -/
theorem amax_div {group : ι → γ} {y c : ι → K} {g : γ} {c₀ : K} (hc₀ : 0 < c₀)
    (hc : ∀ i, group i = g → c i = c₀) :
    amax group (fun i => y i / c i) g = amax group y g / c₀ := by
  refine le_antisymm (amax_le_iff.mpr ⟨div_nonneg (amax_nonneg group y g) hc₀.le, ?_⟩) ?_
  · intro i hi
    rw [hc i hi, abs_div, abs_of_pos hc₀]
    exact div_le_div_of_nonneg_right (hi ▸ abs_le_amax group y i) hc₀.le
  · rw [div_le_iff₀ hc₀]
    refine amax_le_iff.mpr ⟨mul_nonneg (amax_nonneg group _ g) hc₀.le, fun i hi => ?_⟩
    have h := abs_le_amax group (fun i => y i / c i) i
    rw [hi] at h
    simp only [hc i hi, abs_div, abs_of_pos hc₀] at h
    exact (div_le_iff₀ hc₀).mp h

namespace Level

/--
An unsigned scale format stores the same scales as its signed descriptor. For a positive target
and a nonnegative scale for all-zero groups, a largest-magnitude level asks its scale format to
store nonnegative values only, so two scale formats that agree on nonnegative values (a signed
format and the unsigned format with the same exponent and significand, for example E4M3 and
UE4M3) give the same stored scales.
-/
theorem ofMax_scale_congr {group : ι → γ} {format format' : Rounding K} {target zero : K}
    (ht : 0 < target) (hz : 0 ≤ zero) (h : ∀ v, 0 ≤ v → format'.round v = format.round v)
    (y : ι → K) (g : γ) :
    (ofMax group format' target zero).scale y g = (ofMax group format target zero).scale y g := by
  simp only [scale, ofMax]
  split_ifs
  · exact h _ hz
  · exact h _ (div_nonneg (amax_nonneg group y g) ht.le)

/-- The largest magnitude of a group of rationals is the largest magnitude of their casts. -/
theorem _root_.FloatLib.Floats.Formats.Block.amax_ratCast (group : ι → γ) (y : ι → ℚ) (g : γ) :
    ((amax group y g : ℚ) : K) = amax group (fun i => (y i : K)) g := by
  unfold amax
  have h := Finset.fold_hom (op := max) (op' := max) (m := fun q : ℚ => (q : K))
    (f := fun i => |y i|) (b := 0) (s := members group g) fun a b => Rat.cast_max a b
  simp only [Rat.cast_zero, Rat.cast_abs] at h
  exact h.symm

/-- The ideal scale of a largest-magnitude level over the rationals is, after the cast, the
ideal scale of the level with the cast target and the cast scale for all-zero groups. -/
theorem ofMax_ideal_ratCast (group : ι → γ) (format : Rounding ℚ) (format' : Rounding K)
    (target zero : ℚ) (y : ι → ℚ) (g : γ) :
    (((ofMax group format target zero).ideal y g : ℚ) : K) =
      (ofMax group format' (target : K) (zero : K)).ideal (fun i => (y i : K)) g := by
  simp only [ofMax]
  rw [← amax_ratCast]
  by_cases h : amax group y g = 0
  · simp [h]
  · have h' : ((amax group y g : ℚ) : K) ≠ 0 := by exact_mod_cast h
    simp [h, h']

/--
A largest-magnitude level over the rationals and the level with the cast target, the cast scale
for all-zero groups and a scale format `format'` over `K` select the same scale for a group, when
`format'` rounds the ideal scale of that group as `format` does.
-/
theorem ofMax_scale_ratCast (group : ι → γ) (format : Rounding ℚ) (format' : Rounding K)
    (target zero : ℚ) (y : ι → ℚ) (g : γ)
    (hformat : ((format.round ((ofMax group format target zero).ideal y g) : ℚ) : K) =
      format'.round (((ofMax group format target zero).ideal y g : ℚ) : K)) :
    (((ofMax group format target zero).scale y g : ℚ) : K) =
      (ofMax group format' (target : K) (zero : K)).scale (fun i => (y i : K)) g := by
  change ((format.round ((ofMax group format target zero).ideal y g) : ℚ) : K) =
    format'.round ((ofMax group format' (target : K) (zero : K)).ideal (fun i => (y i : K)) g)
  rw [hformat, ofMax_ideal_ratCast]

end Level

/--
Saturation margin of a selected scale. If the stored scale `s` is at least `c` times the ideal
scale `a / t` of a group with largest magnitude `a`, every element of the group has scaled
magnitude at most `t / c`. With `t / c` at most the element format's largest magnitude, no
element saturates.
-/
theorem abs_div_scale_le {a t c s y : K} (ha : 0 < a) (ht : 0 < t) (hc : 0 < c)
    (hs : c * (a / t) ≤ s) (hy : |y| ≤ a) : |y / s| ≤ t / c := by
  have hpos : 0 < c * (a / t) := mul_pos hc (div_pos ha ht)
  have hs0 : 0 < s := hpos.trans_le hs
  rw [abs_div, abs_of_pos hs0, div_le_div_iff₀ hs0 hc]
  calc |y| * c ≤ a * c := mul_le_mul_of_nonneg_right hy hc.le
    _ = t * (c * (a / t)) := by field_simp
    _ ≤ t * s := mul_le_mul_of_nonneg_left hs ht.le

/--
Use of the element range by a selected scale. If the stored scale `s` is positive and at most `c`
times the ideal scale `a / t`, the group's largest magnitude is scaled to at least `t / c`.
-/
theorem le_div_scale {a t c s : K} (ht : 0 < t) (hc : 0 < c) (hs0 : 0 < s)
    (hs : s ≤ c * (a / t)) : t / c ≤ a / s := by
  rw [div_le_div_iff₀ hc hs0]
  calc t * s ≤ t * (c * (a / t)) := mul_le_mul_of_nonneg_left hs ht.le
    _ = a * c := by field_simp

/--
`Level.ofMax` with a stored scale at least `c` times the ideal one: every element of a group that
is not all zero has scaled magnitude at most `target / c`.
-/
theorem ofMax_abs_div_scale_le {group : ι → γ} {format : Rounding K} {target zero c : K}
    {y : ι → K} (i : ι) (ha : 0 < amax group y (group i)) (ht : 0 < target) (hc : 0 < c)
    (hs : c * (amax group y (group i) / target) ≤
      format.round (amax group y (group i) / target)) :
    |y i / (Level.ofMax group format target zero).scaleAt y i| ≤ target / c := by
  rw [Level.scaleAt, show (Level.ofMax group format target zero).group i = group i from rfl,
    Level.ofMax_scale ha]
  exact abs_div_scale_le ha ht hc hs (abs_le_amax group y i)

/--
`Level.ofMax` with a positive stored scale at most `c` times the ideal one: the group's largest
magnitude is scaled to at least `target / c`.
-/
theorem ofMax_le_amax_div_scale {group : ι → γ} {format : Rounding K} {target zero c : K}
    {y : ι → K} {g : γ} (ha : 0 < amax group y g) (ht : 0 < target) (hc : 0 < c)
    (hs0 : 0 < format.round (amax group y g / target))
    (hs : format.round (amax group y g / target) ≤ c * (amax group y g / target)) :
    target / c ≤ amax group y g / (Level.ofMax group format target zero).scale y g := by
  rw [Level.ofMax_scale ha]
  exact le_div_scale ht hc hs0 hs

/--
A stored scale `s` within a relative `ε` of the ideal scale lies between `1 - ε` and `1 + ε`
times the ideal scale. These are the constants `c₁` and `c₂` of the bounds in terms of the block
maximum.
-/
theorem scale_bounds_of_relative {s ideal ε : K} (h : |s - ideal| ≤ ε * ideal) :
    (1 - ε) * ideal ≤ s ∧ s ≤ (1 + ε) * ideal := by
  rw [sub_mul, add_mul, one_mul]
  obtain ⟨hupper, hlower⟩ := abs_sub_le_iff.mp h
  exact ⟨sub_le_comm.mp hlower, sub_le_iff_le_add'.mp hupper⟩

end Ordered

namespace Rounding

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/--
Round a positive value down to a power of two, with the exponent clamped to `[lo, hi]`. This is
the scale rounding of OCP MX 1.0, section 6.3, for E8M0 with `lo = -127` and `hi = 127`. Zero and
negative inputs give `2 ^ 0` clamped.
-/
def pow2Floor (lo hi : ℤ) : Rounding K where
  round x := 2 ^ Numerics.Quantization.Saturating.clamp lo hi (Int.log 2 x)

/--
Round a positive value up to a power of two, with the exponent clamped to `[lo, hi]`. Zero and
negative inputs give `2 ^ 0` clamped.
-/
def pow2Ceil (lo hi : ℤ) : Rounding K where
  round x := 2 ^ Numerics.Quantization.Saturating.clamp lo hi (Int.clog 2 x)

/-- Both power-of-two roundings store positive values. -/
theorem pow2Floor_pos (lo hi : ℤ) (x : K) : 0 < (pow2Floor lo hi : Rounding K).round x :=
  zpow_pos (by norm_num) _

/-- Both power-of-two roundings store positive values. -/
theorem pow2Ceil_pos (lo hi : ℤ) (x : K) : 0 < (pow2Ceil lo hi : Rounding K).round x :=
  zpow_pos (by norm_num) _

/-- Inside the exponent range, rounding down to a power of two does not exceed the input. -/
theorem pow2Floor_le {lo hi : ℤ} {x : K} (hx : 0 < x) (hlo : lo ≤ Int.log 2 x)
    (hhi : Int.log 2 x ≤ hi) : (pow2Floor lo hi : Rounding K).round x ≤ x := by
  have h := Int.zpow_log_le_self (b := 2) (by decide) hx
  simpa only [pow2Floor, Numerics.Quantization.Saturating.clamp_eq_self hlo hhi,
    Nat.cast_ofNat] using h

/-- Inside the exponent range, the input is below twice its rounding down to a power of two. -/
theorem lt_two_mul_pow2Floor {lo hi : ℤ} {x : K} (hlo : lo ≤ Int.log 2 x)
    (hhi : Int.log 2 x ≤ hi) : x < 2 * (pow2Floor lo hi : Rounding K).round x := by
  have h := Int.lt_zpow_succ_log_self (b := 2) (by decide) x
  rw [zpow_add_one₀ (by norm_num)] at h
  simpa only [pow2Floor, Numerics.Quantization.Saturating.clamp_eq_self hlo hhi,
    Nat.cast_ofNat, mul_comm] using h

/-- Inside the exponent range, rounding up to a power of two is at least the input. -/
theorem le_pow2Ceil {lo hi : ℤ} {x : K} (hlo : lo ≤ Int.clog 2 x) (hhi : Int.clog 2 x ≤ hi) :
    x ≤ (pow2Ceil lo hi : Rounding K).round x := by
  have h := Int.self_le_zpow_clog (b := 2) (by decide) x
  simpa only [pow2Ceil, Numerics.Quantization.Saturating.clamp_eq_self hlo hhi,
    Nat.cast_ofNat] using h

/-- Inside the exponent range, rounding up to a power of two is below twice the input. -/
theorem pow2Ceil_lt_two_mul {lo hi : ℤ} {x : K} (hx : 0 < x) (hlo : lo ≤ Int.clog 2 x)
    (hhi : Int.clog 2 x ≤ hi) : (pow2Ceil lo hi : Rounding K).round x < 2 * x := by
  have h := Int.zpow_pred_clog_lt_self (b := 2) (by decide) hx
  rw [zpow_sub_one₀ (by norm_num)] at h
  have h2 : (2 : K) ^ Int.clog 2 x < 2 * x := by
    have := mul_lt_mul_of_pos_right h (by norm_num : (0 : K) < 2)
    simpa [mul_comm] using this
  simpa only [pow2Ceil, Numerics.Quantization.Saturating.clamp_eq_self hlo hhi] using h2

/-- The binary logarithm of a rational does not change when the rational is cast to `K`. -/
theorem _root_.FloatLib.Floats.Formats.Block.log_two_ratCast (q : ℚ) :
    Int.log 2 (q : K) = Int.log 2 q := by
  rcases le_or_gt q 0 with hq | hq
  · rw [Int.log_of_right_le_zero _ hq, Int.log_of_right_le_zero _ (by exact_mod_cast hq)]
  · have hq' : (0 : K) < (q : K) := by exact_mod_cast hq
    have key : ∀ x : ℤ, x ≤ Int.log 2 (q : K) ↔ x ≤ Int.log 2 q := fun x => by
      have hcast : (((2 : ℚ) ^ x : ℚ) : K) = (2 : K) ^ x := by
        push_cast
        rfl
      rw [← Int.zpow_le_iff_le_log (by norm_num) hq', ← Int.zpow_le_iff_le_log (by norm_num) hq]
      simp only [Nat.cast_ofNat]
      rw [← hcast, Rat.cast_le]
    exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-- Rounding a rational down to a power of two gives the same value over `K`. -/
theorem pow2Floor_round_ratCast (lo hi : ℤ) (q : ℚ) :
    (((pow2Floor lo hi : Rounding ℚ).round q : ℚ) : K) =
      (pow2Floor lo hi : Rounding K).round (q : K) := by
  simp only [pow2Floor, log_two_ratCast]
  push_cast
  rfl

/-- The upper binary logarithm of a rational does not change when the rational is cast to `K`. -/
theorem _root_.FloatLib.Floats.Formats.Block.clog_two_ratCast (q : ℚ) :
    Int.clog 2 (q : K) = Int.clog 2 q := by
  rw [← Int.neg_log_inv_eq_clog, ← Int.neg_log_inv_eq_clog, ← Rat.cast_inv, log_two_ratCast]

/-- Rounding a rational up to a power of two gives the same value over `K`. -/
theorem pow2Ceil_round_ratCast (lo hi : ℤ) (q : ℚ) :
    (((pow2Ceil lo hi : Rounding ℚ).round q : ℚ) : K) =
      (pow2Ceil lo hi : Rounding K).round (q : K) := by
  simp only [pow2Ceil, clog_two_ratCast]
  push_cast
  rfl

/-- Rounding down to a power of two, evaluated: an input in `[2 ^ e, 2 ^ (e + 1))` with `e` inside
the exponent range is stored as `2 ^ e`. -/
theorem pow2Floor_round_eq {lo hi e : ℤ} {x : K} (h1 : (2 : K) ^ e ≤ x) (h2 : x < 2 ^ (e + 1))
    (hlo : lo ≤ e) (hhi : e ≤ hi) : (pow2Floor lo hi : Rounding K).round x = 2 ^ e := by
  have hx : 0 < x := (zpow_pos (by norm_num) e).trans_le h1
  have hlog : Int.log 2 x = e := by
    apply le_antisymm
    · have := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hx).mp (by simpa using h2)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by decide) hx).mp (by simpa using h1)
  simp only [pow2Floor, hlog, Numerics.Quantization.Saturating.clamp_eq_self hlo hhi]

/-- A power of two inside the exponent range is stored exactly by rounding down. -/
theorem pow2Floor_fixes {lo hi e : ℤ} (hlo : lo ≤ e) (hhi : e ≤ hi) :
    (pow2Floor lo hi : Rounding K).Fixes (2 ^ e) := by
  have h : Int.log 2 ((2 : K) ^ e) = e := by
    simpa using Int.log_zpow (R := K) (b := 2) (by decide) e
  simp only [Fixes, pow2Floor, h, Numerics.Quantization.Saturating.clamp_eq_self hlo hhi]

end Rounding

end FloatLib.Floats.Formats.Block
