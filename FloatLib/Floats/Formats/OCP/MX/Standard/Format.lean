/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational
public import FloatLib.Floats.Formats.Block.Binary
public import FloatLib.Floats.Formats.OCP.MX.Standard.ElementProof
public import FloatLib.Floats.Formats.OCP.MX.Standard.Compiled
public import FloatLib.Floats.Formats.OCP.MX.Standard.ScaleProof
public import FloatLib.Numerics.Quantization.Block.Coded

/-!
# OCP MX storage codecs and decoding

`Profile.codec` supplies the six standard element encodings, with saturating or native
overflow conversion. `E8M0.codec` stores floor-logarithm scales, clamping below exponent
`-127` and returning NaN above `127`. `format group profile` combines an element codec
with one scale per group; `policy` selects scales from the largest input magnitude.
Quantization, exact decoding and dot products are the general `Block.CodedFormat.quantize`,
`Block.Tensor.decode` and `OCP.MX.Dot`, and the general theorems apply. The statements
below are the ones specific to the element and scale encodings of the standard.

`Tensor.scale_eq` and the decoding lemmas describe every stored tensor, including invalid
scales and infinite elements. Finite values, nearest rounding and quantization error bounds
are developed in `Standard.Values`, `Standard.Rounding` and `Standard.ErrorBounds`.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.1–5.4 and 6.3.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Numerics FloatLib.Floats.Formats

/-- E8M0 as a scale codec with the selection rounding of OCP MX 1.0, section 6.3. -/
@[reducible] def E8M0.codec : Block.Codec where
  Code := E8M0
  decode scale :=
    match scale.exponent? with
    | some exponent => .finite (SignedRat.ofRat ((2 : ℚ) ^ exponent))
    | none => .exceptional .nan
  encode s :=
    if 127 < Int.log 2 s.value then E8M0.ofNatBits 255
    else E8M0.ofExponentSaturating (Int.log 2 s.value)
  value_encode _ := rfl

/-- An ideal scale whose exponent is above 127 is stored as the NaN scale. -/
theorem E8M0.codec_encode_exponent?_of_lt {s : SignedRat} (h : 127 < Int.log 2 s.value) :
    (E8M0.codec.encode s).exponent? = none := by
  simp only [ite_eq_left h]
  rfl

/-- An ideal scale whose exponent is at most 127 is stored with that exponent, clamped at
`-127`. -/
theorem E8M0.codec_encode_exponent?_of_le {s : SignedRat} (h : Int.log 2 s.value ≤ 127) :
    (E8M0.codec.encode s).exponent? = some (max (-127) (Int.log 2 s.value)) := by
  simp [not_lt.mpr h, min_eq_right h]

/-- Inside the exponent range, the E8M0 codec rounds an ideal scale down to a power of two, as
`Block.Rounding.pow2Floor (-127) 127` does. -/
theorem E8M0.codec_rounding_eq_pow2Floor {q : ℚ} (h : Int.log 2 q ≤ 127) :
    E8M0.codec.rounding.round q = (Block.Rounding.pow2Floor (-127) 127).round q := by
  have hexp : (E8M0.codec.encode (SignedRat.ofRat q)).exponent? =
      some (max (-127) (Int.log 2 q)) :=
    E8M0.codec_encode_exponent?_of_le (s := SignedRat.ofRat q) h
  have hcode : E8M0.codec.decode (E8M0.codec.encode (SignedRat.ofRat q)) =
      .finite (SignedRat.ofRat ((2 : ℚ) ^ max (-127) (Int.log 2 q))) := by
    change (match (E8M0.codec.encode (SignedRat.ofRat q)).exponent? with
      | some exponent => NumericalValue.finite (SignedRat.ofRat ((2 : ℚ) ^ exponent))
      | none => .exceptional .nan) = _
    rw [hexp]
  change Block.finiteValue (E8M0.codec.decode (E8M0.codec.encode (SignedRat.ofRat q))) = _
  rw [hcode]
  simp [Block.finiteValue, Block.Rounding.pow2Floor,
    Numerics.Quantization.Saturating.clamp, min_eq_right h]

namespace Standard

/-- A finite element word has the rational value `toRat?` reports. -/
theorem Element.finiteValue_decode {profile : Profile} {word : Element profile} {q : ℚ}
    (h : Element.toRat? word = some q) : Block.finiteValue (Element.decode word) = q := by
  unfold Element.toRat? at h
  cases hd : Element.decode word with
  | finite v =>
    simp only [hd, NumericalValue.finite?_finite, Option.map_some, Option.some.injEq] at h
    simp [Block.finiteValue, h]
  | infinity s => simp [hd] at h
  | exceptional e => simp [hd] at h

private theorem Element.finiteValue_quantize_zero (profile : Profile) (overflow : OverflowMode)
    (s : SignedRat) (hs : s.value = 0) :
    Block.finiteValue (Element.decode (Element.quantize profile (.finite s) overflow)) = 0 := by
  have hq := Element.quantize_quantizesWith profile overflow s
  have hround : Element.roundsOut profile s.value = false := by
    rw [hs]
    cases profile <;> simp [Element.roundsOut]
  simp only [Element.QuantizesWith, hround, Bool.false_eq_true, and_false, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := id hq
  have hzero : value = s.value :=
    Element.Quantizes.exact hq hvalue (other := 0) (by rw [hs]; exact Element.toRat?_zero profile)
  rw [Element.finiteValue_decode hvalue, hzero, hs]

/--
Element codec of a profile. `overflow := .saturate` is the SAT conversion of §5.3.1 and `.native`
the OVF conversion, which only the FP8 elements distinguish.
-/
@[reducible] def Profile.codec (profile : Profile) (overflow : OverflowMode := .saturate) :
    Block.Codec where
  Code := Element profile
  decode := Element.decode
  encode s := Element.quantize profile (.finite s) overflow
  value_encode s := by
    by_cases h : s.value = 0
    · rw [Element.finiteValue_quantize_zero profile overflow s h,
        Element.finiteValue_quantize_zero profile overflow (SignedRat.ofRat s.value) (by simp [h])]
    · rw [SignedRat.ofRat_value_of_ne_zero h]

/--
The OCP MX 1.0 storage format of a profile on the blocks of `group`: the profile's element codec
and one E8M0 scale per block. The standard's blocks have 32 elements.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.1–5.4 and 6.3.
-/
@[reducible] def format {ι γ : Type} (group : ι → γ) (profile : Profile)
    (overflow : OverflowMode := .saturate) : Block.CodedFormat ι γ where
  element := profile.codec overflow
  levels := [{ group := group, codec := E8M0.codec }]

/--
The scale selection of OCP MX 1.0, section 6.3: the largest magnitude of each block lands in the
binade of the element format's largest power of two, and an all-zero block gets `2 ^ 0`.
-/
def policy {ι γ : Type} [Fintype ι] [DecidableEq γ] (group : ι → γ) (profile : Profile) :
    Block.Policy ι γ :=
  [Block.Selection.ofMax group (2 ^ profile.maxPowerExponent) 1]

variable {ι γ : Type}

/-- Without its codes and with the standard policy, the format of a profile is one
largest-magnitude level over E8M0 and the profile's element rounding. -/
theorem toFormat_format [Fintype ι] [DecidableEq γ] (group : ι → γ) (profile : Profile)
    (overflow : OverflowMode) :
    (format group profile overflow).toFormat (policy group profile) =
      { element := fun _ => (profile.codec overflow).rounding
        levels := [Block.Level.ofMax group E8M0.codec.rounding
          (2 ^ profile.maxPowerExponent) 1] } :=
  rfl

/-- Each stored element satisfies the element contract of §5.3 at its exact scaled input. -/
theorem format_elements_quantize (group : ι → γ) (profile : Profile) (overflow : OverflowMode)
    (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι) :
    Element.QuantizesWith overflow
      (x i * SignedRat.ofRat
        (1 / ((format group profile overflow).toFormat selection).scale
          (fun j => (x j).value) i))
      (((format group profile overflow).quantize selection x).elements i) :=
  Element.quantize_quantizesWith profile overflow _

namespace Tensor

variable {group : ι → γ} {profile : Profile} {overflow : OverflowMode}

/-- The scale code of the block of a position. -/
def scaleCode (t : Block.Tensor (format group profile overflow)) (i : ι) : E8M0 :=
  t.scales.1 (group i)

/-- A position has finite scales exactly when its block's scale is not the NaN code. -/
theorem isFinite_iff (t : Block.Tensor (format group profile overflow)) (i : ι) :
    Block.ScaleCodes.isFinite (format group profile overflow).levels t.scales i = true ↔
      ∃ exponent, (scaleCode t i).exponent? = some exponent := by
  change ((E8M0.codec.decode (t.scales.1 (group i))).isFinite && true) = true ↔ _
  rw [Bool.and_true]
  change (match (t.scales.1 (group i)).exponent? with
    | some exponent => NumericalValue.finite (SignedRat.ofRat ((2 : ℚ) ^ exponent))
    | none => .exceptional .nan).isFinite = true ↔ _
  cases h : (t.scales.1 (group i)).exponent? <;> simp [scaleCode, h]

/-- The total scale of a position whose block has exponent `e` is `2 ^ e`. -/
theorem scale_eq (t : Block.Tensor (format group profile overflow)) (i : ι) {exponent : Int}
    (h : (scaleCode t i).exponent? = some exponent) : t.scale i = (2 : ℚ) ^ exponent := by
  change Block.finiteValue (match (t.scales.1 (group i)).exponent? with
    | some exponent => NumericalValue.finite (SignedRat.ofRat ((2 : ℚ) ^ exponent))
    | none => .exceptional .nan) * 1 = _
  rw [show (t.scales.1 (group i)).exponent? = some exponent from h]
  simp [Block.finiteValue]

/-- A NaN scale makes every position of its block NaN, whatever the element words. -/
theorem decode_of_nan_scale (t : Block.Tensor (format group profile overflow)) (i : ι)
    (h : (scaleCode t i).exponent? = none) : t.decode i = .exceptional .nan := by
  apply Block.Tensor.decode_of_not_isFinite
  rw [Bool.eq_false_iff, ne_eq, isFinite_iff]
  simp [h]

/-- A finite element under a finite scale decodes to the element value times `2 ^ exponent`,
with no rounding and no range limit. -/
theorem decode_finite (t : Block.Tensor (format group profile overflow)) (i : ι)
    {exponent : Int} {value : SignedRat} (h : (scaleCode t i).exponent? = some exponent)
    (hvalue : Element.decode (t.elements i) = .finite value) :
    t.decode i = .finite (value * SignedRat.ofRat ((2 : ℚ) ^ exponent)) := by
  rw [Block.Tensor.decode_finite t i ((isFinite_iff t i).mpr ⟨exponent, h⟩) hvalue,
    scale_eq t i h]

/-- An element infinity under a finite scale keeps its sign, because E8M0 scales are positive. -/
theorem decode_infinity (t : Block.Tensor (format group profile overflow)) (i : ι)
    {exponent : Int} {negative : Bool} (h : (scaleCode t i).exponent? = some exponent)
    (hvalue : Element.decode (t.elements i) = .infinity negative) :
    t.decode i = .infinity negative := by
  refine Block.Tensor.decode_infinity_of_pos t i ((isFinite_iff t i).mpr ⟨exponent, h⟩) hvalue ?_
  rw [scale_eq t i h]
  exact zpow_pos (by norm_num) _

end Tensor

end Standard

end FloatLib.Floats.Formats.OCP.MX
