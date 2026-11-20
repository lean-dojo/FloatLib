/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Catalog
public import FloatLib.Floats.Formats.Block.Codecs
public import FloatLib.Floats.Formats.OCP.MX.Standard.ErrorBounds

/-!
# Stored formats of ML accelerators and their policies

The executable storage formats and scale-selection policies of the block formats in
`Block.Catalog`. A storage format fixes the codes; the policy is passed to
`Block.CodedFormat.quantize`.

* OCP MX: `OCP.MX.Standard.format` with `OCP.MX.Standard.policy` (the rule of §6.3), and the
  variants `mxCeil` and `mxMaxCeil`, which round the scale up to a power of two.
* NVFP4: `nvfp4Stored outer block` has E2M1 elements, an E4M3 scale per block and a binary32 scale
  per outer group. `nvfp4Policy` is an exact-arithmetic interpretation of NVIDIA's description
  (arXiv:2509.25149v2, Appendix B.1–B.3), and `nvfp4Supplied` uses outer scales the caller
    calibrated.
  `nvfp4Stored_abs_value_sub_le` and `nvfp4Stored_abs_scale_sub_le`: the stored element and the
  stored block scale are nearest among the words of their formats, for every policy.
  `nvfp4Stored_abs_value_sub_le_budget` and `nvfp4Stored_value_eq_zero_iff`: the error bound and
  the flush-to-zero rule of the real format hold for the stored codes.
  `nvfp4Stored_value_eq_saturating`: each stored element is the real saturating E2M1 rounding
  of its input at the stored scale. The E4M3 scale codec is the real saturating E4M3 rounding
  as well (`OCP.MX.Standard.Profile.codec_round_eq_real`).
  `nvfp4Stored_value_eq_reconstruct`: with NVIDIA's selection and outer scales inside binary32's
  range, the stored values are those of the real format `nvfp4`, scales included.
* `mx_value_eq_reconstruct`: stored OCP MX with the standard selection has the values of the
  real format `mx`, for every profile, when the scale exponents do not exceed `127`.
  `nvfp4Stored_value_eq_reconstruct_of_lt` and `mx_value_eq_reconstruct_of_lt` discharge the two
  range premises for every tensor of magnitudes below `2 ^ 128`, so for every tensor of finite
  binary32 values.
* Four Over Six: `fourOverSixPolicy measure` tries the targets `6` and `4` for each block.
* The fixed-point combine format: `OCP.MX.Standard.format group .int8` stores S2F6 elements with
  an E8M0 scale, and `mxMaxCeil` with target `127 / 64` selects the least power-of-two scale under
  which no element saturates. `int8_value_eq_signedFixed`: each stored element is the real S2F6
  rounding `Rounding.signedFixed 2 6` of its input at the stored scale.
  `mxMaxCeil_value_eq_reconstruct`: with the scale rounded up (`mxCeil`, `mxMaxCeil`), stored MX
  of every profile has the values of the real format with the scale format `Rounding.pow2Ceil`,
  for every rational tensor. `combine_value_eq_reconstruct` is the case of the combine format.

The codecs round exact rationals. Scale arithmetic in a finite working precision, which the
reference implementations of these formats use, is not part of these definitions:
`Block.Working.Quantizer` is the quantizer on the encodings of a binary working format, and
`Block.nvfp4Working` is NVFP4 in binary32.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

variable {ι γ : Type}

/-- Round a positive ideal scale up to a power of two, with the exponent clamped to E8M0's
range. -/
def ceilPow2 (q : ℚ) : ℚ :=
  (2 : ℚ) ^ Numerics.Quantization.Saturating.clamp (-127) 127 (Int.clog 2 q)

/--
OCP MX with the scale rounded up: the largest magnitude of each block is mapped below the
element format's largest power of two `2 ^ emax`, so the scaled maximum lies in
`(2 ^ (emax - 1), 2 ^ emax]`.

Reference: The rounded-up selection is a FloatLib variant of OCP Microscaling Formats (MX)
Specification v1.0, §6.3.
-/
def mxCeil [Fintype ι] [DecidableEq γ] (group : ι → γ) (emax : ℤ) : Policy ι γ :=
  [(Selection.ofMax group (2 ^ emax) 1).map ceilPow2]

/--
The least power-of-two scale under which the largest magnitude of each block is at most `target`.
With `target` the largest element magnitude, no element saturates.
-/
def mxMaxCeil [Fintype ι] [DecidableEq γ] (group : ι → γ) (target : ℚ) : Policy ι γ :=
  [(Selection.ofMax group target 1).map ceilPow2]

/--
NVIDIA, *Pretraining Large Language Models with NVFP4*, arXiv:2509.25149v2, Appendix B.1–B.3:
E2M1 elements, one E4M3 scale per block, and one binary32 scale per outer group.
The element and block-scale codecs are those of the OCP MX profiles E2M1 and E4M3 with SAT
conversion, so an element above `6` and a scale above `448` saturate. Arbitrary groupings
extend the described sixteen-element blocks; this vendor description is not a standard.
-/
@[reducible] def nvfp4Stored (outer block : ι → γ) : CodedFormat ι γ where
  element := OCP.MX.Standard.Profile.codec .e2m1 .saturate
  levels :=
    [{ group := outer, codec := Codec.ofFormat .binary32 },
      { group := block, codec := OCP.MX.Standard.Profile.codec .e4m3 .saturate }]

/--
Each stored NVFP4 element minimizes the decoded absolute error among the sixteen E2M1 words at its
total scale, for every scale-selection policy, Four Over Six included.
-/
theorem nvfp4Stored_abs_value_sub_le (outer block : ι → γ) (policy : Policy ι γ)
    (x : ι → SignedRat) (i : ι) {other : OCP.MX.Standard.Element .e2m1} {q : ℚ}
    (hother : OCP.MX.Standard.Element.toRat? other = some q)
    (hσ : 0 < ((nvfp4Stored outer block).quantize policy x).scale i) :
    |((nvfp4Stored outer block).quantize policy x).value i - (x i).value| ≤
      |q * ((nvfp4Stored outer block).quantize policy x).scale i - (x i).value| :=
  OCP.MX.Standard.Profile.abs_value_quantize_sub_le .e2m1 (nvfp4Stored outer block) rfl policy x i
    hother hσ

/--
Error of a stored NVFP4 element, for every scale-selection policy: a quarter of the input's
magnitude, a quarter of its total scale, and its excess over six times that scale. This is the
bound `nvfp4_abs_reconstruct_sub_le` of the real format, proved for the stored codes.
-/
theorem nvfp4Stored_abs_value_sub_le_budget (outer block : ι → γ) (policy : Policy ι γ)
    (x : ι → SignedRat) (i : ι)
    (hσ : 0 < ((nvfp4Stored outer block).quantize policy x).scale i) :
    |((nvfp4Stored outer block).quantize policy x).value i - (x i).value| ≤
      1 / 4 * |(x i).value| + ((nvfp4Stored outer block).quantize policy x).scale i * (1 / 4) +
        max 0 (|(x i).value| - ((nvfp4Stored outer block).quantize policy x).scale i * 6) :=
  OCP.MX.Standard.Profile.abs_value_quantize_sub_le_budget .e2m1 (nvfp4Stored outer block) rfl
    policy x i hσ

/--
Flush to zero of stored NVFP4 elements, for every scale-selection policy: the stored value is
zero exactly when the input's magnitude is at most a quarter of its total scale.
-/
theorem nvfp4Stored_value_eq_zero_iff (outer block : ι → γ) (policy : Policy ι γ)
    (x : ι → SignedRat) (i : ι)
    (hσ : 0 < ((nvfp4Stored outer block).quantize policy x).scale i) :
    ((nvfp4Stored outer block).quantize policy x).value i = 0 ↔
      |(x i).value| ≤ 1 / 4 * ((nvfp4Stored outer block).quantize policy x).scale i :=
  OCP.MX.Standard.Profile.value_quantize_eq_zero_iff .e2m1 (nvfp4Stored outer block) rfl policy
    x i hσ

/--
Stored NVFP4 elements are the real E2M1 rounding, for every scale-selection policy: the stored
value of a position is the saturating nearest-even E2M1 rounding of the input in units of its
stored total scale. So the stored codes have the element values of the real format `nvfp4` at
the stored scales, and its element theorems apply to them.
-/
theorem nvfp4Stored_value_eq_saturating (outer block : ι → γ) (policy : Policy ι γ)
    (x : ι → SignedRat) (i : ι) :
    ((((nvfp4Stored outer block).quantize policy x).value i : ℚ) : ℝ) =
      ((Rounding.saturating .e2m1).scaled
        ((((nvfp4Stored outer block).quantize policy x).scale i : ℚ) : ℝ)).round
          (((x i).value : ℚ) : ℝ) :=
  OCP.MX.Standard.Profile.value_quantize_eq_real .e2m1 (nvfp4Stored outer block) rfl policy x i

/-- The real rounding of the INT8 profile is the signed fixed-point format S2F6, the element
format of the combine format. -/
theorem signedFixed_eq_real_int8 :
    Rounding.signedFixed 2 6 = OCP.MX.Standard.Profile.real .int8 := by
  simp only [Rounding.signedFixed, OCP.MX.Standard.Profile.real]
  congr 1 <;> norm_num

/--
Stored S2F6 elements are the real signed fixed-point rounding. In every block format whose
elements round as the INT8 codec with SAT conversion (OCP MXINT8, and the combine format with a
power-of-two scale per block of 32), the stored value of a position is the nearest-even S2F6
rounding of the input in units of its stored total scale, for every level structure and policy.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.3.4 and 6.3.
-/
theorem int8_value_eq_signedFixed (F : CodedFormat ι γ)
    (hF : F.element.rounding = (OCP.MX.Standard.Profile.codec .int8 .saturate).rounding)
    (policy : Policy ι γ) (x : ι → SignedRat) (i : ι) :
    (((F.quantize policy x).value i : ℚ) : ℝ) =
      ((Rounding.signedFixed 2 6).scaled (((F.quantize policy x).scale i : ℚ) : ℝ)).round
        (((x i).value : ℚ) : ℝ) := by
  rw [signedFixed_eq_real_int8]
  exact OCP.MX.Standard.Profile.value_quantize_eq_real .int8 F hF policy x i

/-- The block scale NVFP4 stores is at least as close to the ideal scale as any finite E4M3
word. -/
theorem nvfp4Stored_abs_scale_sub_le (y : ℚ) {other : OCP.MX.Standard.Element .e4m3} {q : ℚ}
    (hother : OCP.MX.Standard.Element.toRat? other = some q) :
    |(OCP.MX.Standard.Profile.codec .e4m3 .saturate).rounding.round y - y| ≤ |q - y| :=
  OCP.MX.Standard.Profile.abs_codec_round_sub_le .e4m3 y hother

/-- NVFP4 Appendix B.1–B.2 (arXiv:2509.25149v2), interpreted with exact scale arithmetic:
the ideal outer scale maps its group maximum to `6 * 448`; the ideal local scale maps the
outer-normalized block maximum to `6`. Storage rounds both scales. FloatLib chooses outer
scale one and local scale zero for all-zero groups, cases the description does not specify. -/
def nvfp4Policy [Fintype ι] [DecidableEq γ] (outer block : ι → γ) : Policy ι γ :=
  [Selection.ofMax outer (6 * 448) 1, Selection.ofMax block 6 0]

/-- NVFP4 Appendix B.1–B.2 (arXiv:2509.25149v2) with caller-supplied outer scales.
The local ideal scale is selected using exact rational division, without a positive floor. -/
def nvfp4Supplied [Fintype ι] [DecidableEq γ] (block : ι → γ) (outerScale : γ → ℚ) :
    Policy ι γ :=
  [Selection.supplied outerScale, Selection.ofMax block 6 0]

/-- Four Over Six: the outer scale maps the largest magnitude to `6 * 256`, and each block keeps
the target `4` when its measured error is strictly smaller than that of the target `6`. -/
def fourOverSixPolicy [Fintype ι] [DecidableEq γ] (outer block : ι → γ) (measure : ℚ → ℚ) :
    Policy ι γ :=
  [Selection.ofMax outer (6 * 256) 1,
    Selection.ofCandidates block (OCP.MX.Standard.Profile.codec .e4m3 .saturate)
      (OCP.MX.Standard.Profile.codec .e2m1 .saturate) measure [6, 4] 0]

/--
Stored NVFP4 with NVIDIA's selection is the real format `nvfp4`. For rational data whose ideal
outer scales are inside binary32's finite range, the value of every stored position is the value
the real format reconstructs: the binary32 outer scale, the E4M3 block scale and the E2M1 element
are the real roundings of the same exact inputs. So every theorem about `nvfp4` holds for the
codes of the executable quantizer.

Reference: NVIDIA, Pretraining Large Language Models with NVFP4 (2025), Appendix B.1–B.3.
-/
theorem nvfp4Stored_value_eq_reconstruct {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ)
    (x : Fin m × Fin n → SignedRat)
    (hrange : ∀ g, |((Selection.ofMax outer (6 * 448) 1 (fun j => (x j).value) g : ℚ) : ℝ)| ≤
      Model.toReal (Model.posMaxFinite .binary32))
    (i : Fin m × Fin n) :
    ((((nvfp4Stored outer block).quantize (nvfp4Policy outer block) x).value i : ℚ) : ℝ) =
      (nvfp4 outer block).reconstruct (fun j => (((x j).value : ℚ) : ℝ)) i := by
  have h6 : ((6 * 448 : ℚ) : ℝ) = 6 * 448 := by norm_num
  rw [CodedFormat.value_quantize]
  refine Format.reconstruct_ratCast ?_ i
    (OCP.MX.Standard.Profile.codec_round_eq_real .e2m1 _)
  change (∀ j, ((_ : ℚ) : ℝ) = _) ∧ (∀ j, ((_ : ℚ) : ℝ) = _) ∧ True
  refine ⟨fun j => ?_, fun j => ?_, trivial⟩
  · have h := Level.ofMax_scale_ratCast (K := ℝ) outer (Codec.ofFormat .binary32).rounding
      (Rounding.grid .binary32) (6 * 448) 1 (fun j => (x j).value) (outer j)
      (Codec.ofFormat_round_eq_grid .binary32 rfl _ (hrange (outer j)))
    rw [h6, Rat.cast_one] at h
    exact h
  · refine (Level.ofMax_scale_ratCast (K := ℝ) block
      (OCP.MX.Standard.Profile.codec .e4m3 .saturate).rounding (Rounding.saturating .e4m3)
      6 0 _ (block j) (OCP.MX.Standard.Profile.codec_round_eq_real .e4m3 _)).trans ?_
    rw [Rat.cast_zero, Rat.cast_ofNat]
    rfl

/--
Stored OCP MX with the standard selection is the real format `mx`. For rational data whose ideal
scales have a binary logarithm of at most `127`, the value of every stored position is the value
the real format reconstructs with the profile's real element rounding: the E8M0 scale and the
element are the real roundings of the same exact inputs. So every theorem about `mx` holds for
the codes of the executable quantizer, for each of the six profiles and every block size.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.4.1 and 6.3.
-/
theorem mx_value_eq_reconstruct {m n : ℕ} (profile : OCP.MX.Standard.Profile) (k : ℕ)
    (x : Fin m × Fin n → SignedRat)
    (hrange : ∀ g, Int.log 2 (Selection.ofMax (tiles 1 k) (2 ^ profile.maxPowerExponent) 1
      (fun j => (x j).value) g) ≤ 127)
    (i : Fin m × Fin n) :
    ((((OCP.MX.Standard.format (tiles 1 k) profile).quantize
        (OCP.MX.Standard.policy (tiles 1 k) profile) x).value i : ℚ) : ℝ) =
      (mx profile.real profile.maxPowerExponent k).reconstruct
        (fun j => (((x j).value : ℚ) : ℝ)) i := by
  have hpow : (((2 : ℚ) ^ profile.maxPowerExponent : ℚ) : ℝ) = 2 ^ profile.maxPowerExponent := by
    push_cast
    rfl
  rw [CodedFormat.value_quantize]
  refine Format.reconstruct_ratCast ?_ i (profile.codec_round_eq_real _)
  change (∀ j, ((_ : ℚ) : ℝ) = _) ∧ True
  refine ⟨fun j => ?_, trivial⟩
  have h := Level.ofMax_scale_ratCast (K := ℝ) (tiles 1 k) OCP.MX.E8M0.codec.rounding
    (Rounding.pow2Floor (-127) 127) (2 ^ profile.maxPowerExponent) 1 (fun j => (x j).value)
    (tiles 1 k j) (by
      have hr : Int.log 2 ((Level.ofMax (tiles 1 k) OCP.MX.E8M0.codec.rounding
          (2 ^ profile.maxPowerExponent) 1).ideal (fun j => (x j).value) (tiles 1 k j)) ≤ 127 :=
        hrange (tiles 1 k j)
      rw [OCP.MX.E8M0.codec_rounding_eq_pow2Floor hr]
      exact Rounding.pow2Floor_round_ratCast (-127) 127 _)
  rw [hpow, Rat.cast_one] at h
  exact h

/--
Stored NVFP4 with NVIDIA's selection is the real format `nvfp4` on every tensor of magnitudes
below `2 ^ 128`, which includes every tensor of finite binary32 values.

Reference: NVIDIA, Pretraining Large Language Models with NVFP4 (2025), Appendix B.1–B.3.
-/
theorem nvfp4Stored_value_eq_reconstruct_of_lt {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ)
    (x : Fin m × Fin n → SignedRat) (hx : ∀ j, |(x j).value| < 2 ^ 128) (i : Fin m × Fin n) :
    ((((nvfp4Stored outer block).quantize (nvfp4Policy outer block) x).value i : ℚ) : ℝ) =
      (nvfp4 outer block).reconstruct (fun j => (((x j).value : ℚ) : ℝ)) i := by
  refine nvfp4Stored_value_eq_reconstruct outer block x (fun g => ?_) i
  have hmax : Model.toReal (Model.posMaxFinite .binary32) = (16777215 : ℝ) * 2 ^ (104 : ℤ) :=
    Model.toReal_posMaxFinite_of_eq .binary32 (by decide) (by decide)
  have ha : amax outer (fun j => (x j).value) g ≤ 2 ^ 128 :=
    amax_le_iff.mpr ⟨by positivity, fun j _ => (hx j).le⟩
  have ha0 := amax_nonneg outer (fun j => (x j).value) g
  have hq : |Selection.ofMax outer (6 * 448) 1 (fun j => (x j).value) g| ≤
      (16777215 : ℚ) * 2 ^ (104 : ℤ) := by
    simp only [Selection.ofMax]
    split_ifs
    · norm_num
    · rw [abs_of_nonneg (div_nonneg ha0 (by norm_num))]
      calc amax outer (fun j => (x j).value) g / (6 * 448) ≤ 2 ^ 128 / (6 * 448) :=
            div_le_div_of_nonneg_right ha (by norm_num)
        _ ≤ (16777215 : ℚ) * 2 ^ (104 : ℤ) := by norm_num
  rw [hmax]
  exact_mod_cast hq

/--
Stored OCP MX with the standard selection is the real format `mx` on every tensor of magnitudes
below `2 ^ 128`, which includes every tensor of finite binary32 values, for each of the six
profiles and every block size.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§6.3.
-/
theorem mx_value_eq_reconstruct_of_lt {m n : ℕ} (profile : OCP.MX.Standard.Profile) (k : ℕ)
    (x : Fin m × Fin n → SignedRat) (hx : ∀ j, |(x j).value| < 2 ^ 128) (i : Fin m × Fin n) :
    ((((OCP.MX.Standard.format (tiles 1 k) profile).quantize
        (OCP.MX.Standard.policy (tiles 1 k) profile) x).value i : ℚ) : ℝ) =
      (mx profile.real profile.maxPowerExponent k).reconstruct
        (fun j => (((x j).value : ℚ) : ℝ)) i := by
  refine mx_value_eq_reconstruct profile k x (fun g => ?_) i
  simp only [Selection.ofMax]
  split_ifs with h0
  · simp
  · have hpos : 0 < amax (tiles 1 k) (fun j => (x j).value) g :=
      lt_of_le_of_ne (amax_nonneg _ _ _) (Ne.symm h0)
    obtain ⟨j, -, hj⟩ := exists_abs_eq_amax hpos
    have hlt : amax (tiles 1 k) (fun j => (x j).value) g < 2 ^ 128 := hj ▸ hx j
    have hemax : (1 : ℚ) ≤ 2 ^ profile.maxPowerExponent :=
      one_le_zpow₀ (by norm_num) (by cases profile <;> decide)
    have h128 : ((2 : ℕ) : ℚ) ^ (128 : ℤ) = 2 ^ 128 := by norm_num
    have hdiv : amax (tiles 1 k) (fun j => (x j).value) g / 2 ^ profile.maxPowerExponent <
        ((2 : ℕ) : ℚ) ^ (128 : ℤ) := by
      rw [h128]
      exact lt_of_le_of_lt (div_le_self hpos.le hemax) hlt
    have hlog : Int.log 2
        (amax (tiles 1 k) (fun j => (x j).value) g / 2 ^ profile.maxPowerExponent) < 128 :=
      (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num)
        (div_pos hpos (zpow_pos (by norm_num) _))).mp hdiv
    omega

/--
Stored OCP MX with the scale rounded up is a real format, for every rational tensor. For each of
the six profiles, with one power-of-two scale per block of `k` stored in E8M0 and rounded up from
the largest magnitude over `target` (`mxMaxCeil`, and `mxCeil` with `target = 2 ^ emax`), the
value of every stored position is the value reconstructed by the real format with the profile's
real element rounding and the scale format `Rounding.pow2Ceil (-127) 127`. There is no premise:
the exponent of the scale is clamped to E8M0's range before it is stored.

Reference: The rounded-up selection is a FloatLib variant of OCP Microscaling Formats (MX)
Specification v1.0, §6.3.
-/
theorem mxMaxCeil_value_eq_reconstruct {m n : ℕ} (profile : OCP.MX.Standard.Profile) (k : ℕ)
    (target : ℚ) (x : Fin m × Fin n → SignedRat) (i : Fin m × Fin n) :
    ((((OCP.MX.Standard.format (tiles 1 k) profile).quantize (mxMaxCeil (tiles 1 k) target)
        x).value i : ℚ) : ℝ) =
      (Format.mk (fun _ => profile.real)
        [Level.ofMax (tiles 1 k) (Rounding.pow2Ceil (-127) 127) (target : ℝ) 1]).reconstruct
          (fun j => (((x j).value : ℚ) : ℝ)) i := by
  rw [CodedFormat.value_quantize]
  refine Format.reconstruct_ratCast ?_ i (profile.codec_round_eq_real _)
  change (∀ j, ((_ : ℚ) : ℝ) = _) ∧ True
  refine ⟨fun j => ?_, trivial⟩
  -- The stored scale is the scale rounded up, which E8M0 holds exactly.
  have hstored : ∀ q : ℚ, OCP.MX.E8M0.codec.rounding.round (ceilPow2 q) =
      (Rounding.pow2Ceil (-127) 127 : Rounding ℚ).round q := by
    intro q
    have hlog : Int.log 2 (ceilPow2 q) = max (-127) (min 127 (Int.clog 2 q)) :=
      Int.log_zpow (by norm_num) _
    rw [OCP.MX.E8M0.codec_rounding_eq_pow2Floor (by rw [hlog]; omega)]
    exact Rounding.pow2Floor_fixes
      (Numerics.Quantization.Saturating.lower_le_clamp _ _ _)
      (Numerics.Quantization.Saturating.clamp_le_upper (by norm_num))
  change ((OCP.MX.E8M0.codec.rounding.round (ceilPow2
    ((Level.ofMax (tiles 1 k) OCP.MX.E8M0.codec.rounding target 1).ideal
      (fun j => (x j).value) (tiles 1 k j))) : ℚ) : ℝ) =
    (Rounding.pow2Ceil (-127) 127 : Rounding ℝ).round
      ((Level.ofMax (tiles 1 k) (Rounding.pow2Ceil (-127) 127) (target : ℝ) 1).ideal
        (fun j => (((x j).value : ℚ) : ℝ)) (tiles 1 k j))
  rw [hstored, Rounding.pow2Ceil_round_ratCast,
    Level.ofMax_ideal_ratCast (K := ℝ) (tiles 1 k) OCP.MX.E8M0.codec.rounding
      (Rounding.pow2Ceil (-127) 127) target 1, Rat.cast_one]

/--
The stored combine format is the real format `combine`, for every rational tensor: with S2F6
elements and the scale of each block of `k` rounded up to a power of two, the value of every
stored position is the value `combine 2 6 k (Rounding.pow2Ceil (-127) 127) target` reconstructs.
-/
theorem combine_value_eq_reconstruct {m n : ℕ} (k : ℕ) (target : ℚ)
    (x : Fin m × Fin n → SignedRat) (i : Fin m × Fin n) :
    ((((OCP.MX.Standard.format (tiles 1 k) .int8).quantize (mxMaxCeil (tiles 1 k) target)
        x).value i : ℚ) : ℝ) =
      (combine 2 6 k (Rounding.pow2Ceil (-127) 127) (target : ℝ)).reconstruct
        (fun j => (((x j).value : ℚ) : ℝ)) i := by
  have h := mxMaxCeil_value_eq_reconstruct .int8 k target x i
  rwa [← signedFixed_eq_real_int8] at h

end FloatLib.Floats.Formats.Block
