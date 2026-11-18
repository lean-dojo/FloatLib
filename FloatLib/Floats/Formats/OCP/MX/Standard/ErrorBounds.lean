/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Rounding

/-!
# Error bounds for stored OCP MX elements

`Profile.codec_budget` bounds the error by a relative term, half the least positive value,
and the input's excess over the largest positive value. It uses the checked adjacent gaps
of the finite word list, including the asymmetric INT8 range.

The budget, zero threshold and nearest-word property transfer to every coded block format
whose element rounding is the profile codec. `Profile.encode_mixedError` expresses the same
budget for the encoded binary word, supplying the operand hypothesis used by `roundoff`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics FloatLib.Floats.Formats

variable {ι γ : Type}

/-- Every listed element value of a profile is the value of a finite word. -/
private theorem Profile.exists_candidate_of_mem_values (profile : Profile) {v : ℚ}
    (h : v ∈ profile.values) : ∃ c ∈ Element.candidates profile, c.2 = v := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
  exact ⟨c, (Profile.mem_sorted profile).mp hc, rfl⟩

/--
Error budget of the element codec of every profile, on exact rationals: with SAT conversion the
stored value differs from the input by at most `unitRoundoff * abs q + zeroThreshold`, plus the
excess of `abs q` over the largest element value. For the floating profiles the relative part is
`2 ^ (-precision)`, and for INT8 the error is half a step.
-/
theorem Profile.codec_budget (profile : Profile) :
    (profile.codec .saturate).rounding.Budget profile.unitRoundoff profile.zeroThreshold
      profile.maxMagnitude := by
  intro q
  have hq := Element.quantize_quantizesWith profile .saturate (SignedRat.ofRat q)
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := id hq
  have hround : (profile.codec .saturate).rounding.round q = value :=
    Element.finiteValue_decode hvalue
  rw [hround]
  have hu : 0 ≤ profile.unitRoundoff := by cases profile <;> norm_num [Profile.unitRoundoff]
  have hη : 0 ≤ profile.zeroThreshold := by cases profile <;> norm_num [Profile.zeroThreshold]
  have hM : 0 ≤ profile.maxMagnitude := by cases profile <;> norm_num [Profile.maxMagnitude]
  have hlowest : profile.lowest ≤ -profile.maxMagnitude := by
    cases profile <;> norm_num [Profile.lowest, Profile.maxMagnitude]
  have hmax0 : (0 : ℚ) ≤ max 0 (|q| - profile.maxMagnitude) := le_max_left _ _
  have hmax1 : |q| - profile.maxMagnitude ≤ max 0 (|q| - profile.maxMagnitude) :=
    le_max_right _ _
  have hterm : 0 ≤ profile.unitRoundoff * |q| := mul_nonneg hu (abs_nonneg q)
  -- It suffices to exhibit one finite word within the budget.
  suffices h : ∃ c ∈ Element.candidates profile, |c.2 - q| ≤
      profile.unitRoundoff * |q| + profile.zeroThreshold +
        max 0 (|q| - profile.maxMagnitude) by
    obtain ⟨c, hc, hb⟩ := h
    have hnear := Element.Quantizes.error_le hq hvalue (Element.mem_candidates.mp hc)
    rw [SignedRat.value_ofRat] at hnear
    exact hnear.trans hb
  obtain ⟨hhead, hlast, hadj⟩ := profile.values_adjacent
  obtain ⟨a, l, hvals⟩ : ∃ a l, profile.values = a :: l := by
    cases hl : profile.values with
    | nil => simp [hl] at hhead
    | cons a l => exact ⟨a, l, rfl⟩
  have ha : a = profile.lowest := by simpa [hvals] using hhead
  rcases lt_or_ge profile.maxMagnitude q with hbig | hle
  · -- above the range: the largest value
    obtain ⟨c, hc, hcv⟩ := profile.exists_candidate_of_mem_values
      (List.mem_of_mem_getLast? (Option.mem_def.mpr hlast))
    refine ⟨c, hc, ?_⟩
    have habsq : |q| = q := abs_of_pos (lt_of_le_of_lt hM hbig)
    have h1 : |c.2 - q| = q - profile.maxMagnitude := by
      rw [hcv, abs_of_neg (by linarith)]
      ring
    rw [h1]
    linarith
  rcases lt_or_ge q profile.lowest with hsmall | hge
  · -- below the range: the least value
    obtain ⟨c, hc, hcv⟩ := profile.exists_candidate_of_mem_values
      (List.mem_of_mem_head? (Option.mem_def.mpr hhead))
    refine ⟨c, hc, ?_⟩
    have habsq : |q| = -q := abs_of_neg (by linarith)
    have h1 : |c.2 - q| = profile.lowest - q := by rw [hcv, abs_of_pos (by linarith)]
    rw [h1]
    linarith
  · -- inside the range: one of two adjacent values
    rw [hvals] at hlast hadj
    rcases exists_adjacent_bracket l a q _ hlast (ha ▸ hge) hle with ⟨p, hp, h1, h2⟩ | rfl
    · obtain ⟨hgap, hsign⟩ := hadj p (by simpa using hp)
      have hmem := List.of_mem_zip hp
      have hmin : min |p.1| |p.2| ≤ |q| := by
        rcases hsign with h0 | h0
        · exact (min_le_left _ _).trans (by
            rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]; exact h1)
        · exact (min_le_right _ _).trans (by
            rw [abs_of_nonpos h0, abs_of_nonpos (h2.trans h0)]; linarith)
      have hbound : (p.2 - p.1) / 2 ≤ profile.unitRoundoff * |q| + profile.zeroThreshold :=
        hgap.trans (by
          have := mul_le_mul_of_nonneg_left hmin hu
          linarith)
      rcases le_total (q - p.1) (p.2 - q) with hl | hr
      · obtain ⟨c, hc, hcv⟩ := profile.exists_candidate_of_mem_values
          (hvals ▸ hmem.1)
        refine ⟨c, hc, ?_⟩
        rw [hcv, abs_of_nonpos (by linarith)]
        linarith
      · obtain ⟨c, hc, hcv⟩ := profile.exists_candidate_of_mem_values
          (hvals ▸ List.mem_cons_of_mem _ hmem.2)
        refine ⟨c, hc, ?_⟩
        rw [hcv, abs_of_nonneg (by linarith)]
        linarith
    · obtain ⟨c, hc, hcv⟩ := profile.exists_candidate_of_mem_values
        (hvals ▸ List.mem_cons_self)
      refine ⟨c, hc, ?_⟩
      rw [hcv, sub_self, abs_zero]
      linarith

/--
The binary word a floating profile's codec stores for an input approximates the input within the
profile's budget: relative error `unitRoundoff`, and absolute error `zeroThreshold` plus the
excess of the input over the largest element value. This is the hypothesis a kernel on stored
words takes about its operands, in the form `roundoff` reads. The element code of a quantized
block tensor is the code stored for the input divided by its total scale
(`Block.CodedFormat.elements_quantize`).
-/
theorem Profile.encode_mixedError (profile : Profile) {fmt : BinaryInterchange.FloatFormat}
    (hfmt : profile.floatFormat? = some fmt) (s : SignedRat) :
    MixedError
      (BinaryInterchange.Model.toReal (BinaryInterchange.Model.ofNatBits (fmt := fmt)
        (Element.quantize profile (.finite s) .saturate).toNat))
      ((s.value : ℚ) : ℝ) ((profile.unitRoundoff : ℚ) : ℝ)
      (((profile.zeroThreshold + max 0 (|s.value| - profile.maxMagnitude) : ℚ)) : ℝ) := by
  have hvalue : Block.finiteValue
      (Element.decode (Element.quantize profile (.finite s) .saturate)) =
      (profile.codec .saturate).rounding.round s.value :=
    Block.Codec.value_encode_eq (profile.codec .saturate) s
  have hu : 0 ≤ profile.unitRoundoff := by cases profile <;> norm_num [Profile.unitRoundoff]
  have hη : 0 ≤ profile.zeroThreshold := by cases profile <;> norm_num [Profile.zeroThreshold]
  have hmax := le_max_left (0 : ℚ) (|s.value| - profile.maxMagnitude)
  rw [profile.toReal_ofNatBits hfmt, hvalue]
  refine ⟨by exact_mod_cast hu, by exact_mod_cast add_nonneg hη hmax, ?_⟩
  have h : |(profile.codec .saturate).rounding.round s.value - s.value| ≤
      profile.unitRoundoff * |s.value| +
        (profile.zeroThreshold + max 0 (|s.value| - profile.maxMagnitude)) := by
    have := profile.codec_budget s.value
    linarith
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h' ⊢
  exact h'

/--
Error of stored codes. In any block format whose elements round as a profile's codec with SAT
conversion, under a positive total scale `σ`, the stored value of a position differs from the
input by at most `unitRoundoff * abs x + σ * zeroThreshold + max 0 (abs x - σ * maxMagnitude)`.
This holds for every level structure, scale format and selection policy.
-/
theorem Profile.abs_value_quantize_sub_le_budget (profile : Profile) (F : Block.CodedFormat ι γ)
    (hF : F.element.rounding = (profile.codec .saturate).rounding)
    (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι)
    (hσ : 0 < (F.quantize selection x).scale i) :
    |(F.quantize selection x).value i - (x i).value| ≤
      profile.unitRoundoff * |(x i).value| +
        (F.quantize selection x).scale i * profile.zeroThreshold +
        max 0 (|(x i).value| - (F.quantize selection x).scale i * profile.maxMagnitude) := by
  have helement : (F.toFormat selection).element i = (profile.codec .saturate).rounding := hF
  rw [Block.CodedFormat.scale_quantize] at hσ ⊢
  rw [Block.CodedFormat.value_quantize]
  exact Block.Format.abs_reconstruct_sub_le _ _ i (helement ▸ profile.codec_budget) hσ

/--
Flush to zero of stored codes. In any block format whose elements round as a profile's codec with
SAT conversion, under a positive total scale, the stored value of a position is zero exactly when
the input's magnitude is at most the profile's zero threshold times the total scale. This holds
for every level structure, scale format and selection policy.
-/
theorem Profile.value_quantize_eq_zero_iff (profile : Profile) (F : Block.CodedFormat ι γ)
    (hF : F.element.rounding = (profile.codec .saturate).rounding)
    (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι)
    (hσ : 0 < (F.quantize selection x).scale i) :
    (F.quantize selection x).value i = 0 ↔
      |(x i).value| ≤ profile.zeroThreshold * (F.quantize selection x).scale i := by
  have helement : (F.toFormat selection).element i = (profile.codec .saturate).rounding := hF
  rw [Block.CodedFormat.scale_quantize] at hσ ⊢
  rw [Block.CodedFormat.value_quantize]
  exact Block.Format.reconstruct_eq_zero_iff_abs_le _ _ i
    (fun y => by rw [helement]; exact profile.codec_round_eq_zero_iff y) hσ

/--
With SAT conversion and a positive total scale, the stored element of any block format whose
elements round as a profile's codec minimizes the decoded absolute error among all finite element
words at that scale. This holds for every level structure, scale format and selection policy: OCP
MX with one E8M0 level, and NVFP4 with E4M3 block scales and a binary32 outer scale.
-/
theorem Profile.abs_value_quantize_sub_le (profile : Profile) (F : Block.CodedFormat ι γ)
    (hF : F.element.rounding = (profile.codec .saturate).rounding)
    (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι) {other : Element profile} {q : ℚ}
    (hother : Element.toRat? other = some q) (hσ : 0 < (F.quantize selection x).scale i) :
    |(F.quantize selection x).value i - (x i).value| ≤
      |q * (F.quantize selection x).scale i - (x i).value| := by
  have helement : (F.toFormat selection).element i = (profile.codec .saturate).rounding := hF
  rw [Block.CodedFormat.value_quantize, Block.Format.reconstruct_eq, helement]
  rw [Block.CodedFormat.scale_quantize] at hσ ⊢
  exact Block.Rounding.abs_scaled_round_sub_le_of_nearest
    (R := {q | ∃ other : Element profile, Element.toRat? other = some q})
    (fun y v ⟨w, hw⟩ => profile.abs_codec_round_sub_le y hw) hσ _ ⟨other, hother⟩

/--
OCP MX with SAT conversion and a positive selected scale: the stored element minimizes the decoded
absolute error among all finite element words at that scale, for every selection policy.
-/
theorem abs_value_quantize_sub_le (group : ι → γ) (profile : Profile)
    (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι) {other : Element profile} {q : ℚ}
    (hother : Element.toRat? other = some q)
    (hσ : 0 < ((format group profile).quantize selection x).scale i) :
    |((format group profile).quantize selection x).value i - (x i).value| ≤
      |q * ((format group profile).quantize selection x).scale i - (x i).value| :=
  profile.abs_value_quantize_sub_le (format group profile) rfl selection x i hother hσ

end FloatLib.Floats.Formats.OCP.MX.Standard
