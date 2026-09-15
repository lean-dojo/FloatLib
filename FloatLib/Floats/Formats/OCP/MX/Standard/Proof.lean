/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.ElementProof
public import FloatLib.Floats.Formats.OCP.MX.Standard.ScaleProof
import Init.Data.Vector.Monadic

/-!
# Exact decoding and destination quantization of standard MX blocks

Finite lane decoding is exact multiplication by the shared power of two. Saturating block
quantization minimizes each lane's absolute error among all finite words at the selected scale.
The result applies at subnormal and binade boundaries as well as outside the element range.
-/

public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics

/-- Exact rational meaning of scaling a finite lane. -/
@[simp] theorem scaleFinite_value (exponent : Int) (value : SignedRat) :
    (scaleFinite exponent value).value = value.value * (2 : Rat) ^ exponent := by
  simp [scaleFinite]

/-- A positive power-of-two scale preserves the sign, including the sign of zero. -/
@[simp] theorem scaleFinite_negative (exponent : Int) (value : SignedRat) :
    (scaleFinite exponent value).negative = value.negative := by
  have hnonneg : ¬(2 : Rat) ^ exponent < 0 := not_lt.mpr (le_of_lt (zpow_pos (by norm_num) _))
  simp [scaleFinite, hnonneg]

/-- A zero-length or otherwise malformed array cannot become a standard block. -/
theorem Block.ofArray?_eq_none_iff {profile : Profile} (scale : E8M0)
    (values : Array (Element profile)) :
    Block.ofArray? scale values = none ↔ values.size ≠ 32 := by
  simp [ofArray?]

/-- A NaN shared scale overrides every element, including finite words and infinities. -/
theorem Block.decodeLane_of_nan_scale {profile : Profile} (block : Block profile)
    (lane : Fin 32) (hscale : block.scale.exponent? = none) :
    block.decodeLane lane = .exceptional .nan := by
  simp [decodeLane, hscale]

/-- Finite lane decoding is exact multiplication, without binary32 range truncation. -/
theorem Block.decodeLane_finite {profile : Profile} (block : Block profile)
    (lane : Fin 32) {exponent : Int} {value : SignedRat}
    (hscale : block.scale.exponent? = some exponent)
    (hvalue : Element.decode block.values[lane.val] = .finite value) :
    block.decodeLane lane = .finite (scaleFinite exponent value) := by
  simp [decodeLane, hscale, hvalue]

/-- A finite shared scale preserves an element infinity and its sign. -/
theorem Block.decodeLane_infinity {profile : Profile} (block : Block profile)
    (lane : Fin 32) {exponent : Int} {negative : Bool}
    (hscale : block.scale.exponent? = some exponent)
    (hvalue : Element.decode block.values[lane.val] = .infinity negative) :
    block.decodeLane lane = .infinity negative := by
  simp [decodeLane, hscale, hvalue]

/-- A finite shared scale preserves a lane-local NaN without changing adjacent lanes. -/
theorem Block.decodeLane_exceptional {profile : Profile} (block : Block profile)
    (lane : Fin 32) {exponent : Int} {exceptional : ExceptionalValue}
    (hscale : block.scale.exponent? = some exponent)
    (hvalue : Element.decode block.values[lane.val] = .exceptional exceptional) :
    block.decodeLane lane = .exceptional exceptional := by
  simp [decodeLane, hscale, hvalue]

/-- The generic decoder retains every lane when the block has a finite vector observation. -/
theorem Block.decodeFinite_of_decode {profile : Profile} (block : Block profile)
    (values : Vector SignedRat 32) (h : block.decode = values.map NumericalValue.finite) :
    block.decodeFinite = .finite values := by
  unfold decodeFinite
  rw [h, Vector.mapM_map]
  change (match values.mapM (fun value => some value) with
    | some values => NumericalValue.finite values
    | none => .exceptional .nan) = .finite values
  have hmap : values.mapM (fun value => some value) = some values := by
    simpa only [Vector.map_id, Option.pure_def, id_eq] using
      (Vector.mapM_pure (m := Option) (xs := values) id)
  rw [hmap]

/-- Finite numerical element values remain exact after applying a shared scale. -/
theorem Block.decodeLane_value {profile : Profile} (block : Block profile)
    (lane : Fin 32) {exponent : Int} {value : Rat}
    (hscale : block.scale.exponent? = some exponent)
    (hvalue : Element.toRat? block.values[lane.val] = some value) :
    (block.decodeLane lane).finite?.map SignedRat.value =
      some (value * (2 : Rat) ^ exponent) := by
  unfold Element.toRat? at hvalue
  cases hdecode : Element.decode block.values[lane.val] with
  | finite exact =>
    simp only [hdecode, NumericalValue.finite?_finite, Option.map_some, Option.some.injEq]
      at hvalue
    simp [Block.decodeLane_finite block lane hscale hdecode, scaleFinite_value, hvalue]
  | infinity sign => simp [hdecode] at hvalue
  | exceptional value => simp [hdecode] at hvalue

/-- Both explicit element overflow modes refine their numerical contract. -/
theorem Element.quantize_quantizesWith (profile : Profile) (mode : OverflowMode)
    (input : SignedRat) :
    Element.QuantizesWith mode input (Element.quantize profile mode (.finite input)) := by
  unfold Element.quantize Element.QuantizesWith
  by_cases h : mode = .overflow ∧ Element.roundsOut profile input.value = true
  · simp [h.1, h.2]
  · have hbool : (decide (mode = .overflow) && Element.roundsOut profile input.value) = false :=
      Bool.eq_false_iff.mpr (by simpa using h)
    simp only [hbool, Bool.false_eq_true, ↓reduceIte, if_neg h]
    exact Element.quantizeFinite_quantizes profile input

/-- Automatic shared-scale conversion satisfies the standard destination relation. -/
theorem quantizeFinite_quantizes (profile : Profile) (mode : OverflowMode)
    (input : Vector SignedRat 32) :
    Quantizes profile mode input (quantizeFinite profile mode input) := by
  unfold Quantizes quantizeFinite quantizeAt
  cases hscale : (selectScale profile input).exponent? with
  | none => rfl
  | some exponent =>
    refine ⟨rfl, fun lane => ?_⟩
    simp only [Vector.getElem_map]
    exact Element.quantize_quantizesWith profile mode _

private theorem scaled_error (exponent : Int) (input value : Rat) :
    |value * (2 : Rat) ^ exponent - input| =
      |value - input * (2 : Rat) ^ (-exponent)| * (2 : Rat) ^ exponent := by
  have hpos : (0 : Rat) < 2 ^ exponent := zpow_pos (by norm_num) _
  calc
    _ = |(value - input * (2 : Rat) ^ (-exponent)) * (2 : Rat) ^ exponent| := by
      congr 1
      rw [zpow_neg, sub_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
    _ = _ := by rw [abs_mul, abs_of_pos hpos]

/--
At a finite selected scale, SAT minimizes the decoded absolute error of each lane among all
finite element encodings.
-/
theorem quantizeFinite_error_le (profile : Profile) (input : Vector SignedRat 32)
    (lane : Fin 32) {exponent : Int}
    (hscale : (selectScale profile input).exponent? = some exponent) :
    ∃ value,
      ((quantizeFinite profile .saturate input).decodeLane lane).finite?.map SignedRat.value =
        some value ∧
      ∀ (other : Element profile) (otherValue : Rat), Element.toRat? other = some otherValue →
        |value - input[lane.val].value| ≤
          |otherValue * (2 : Rat) ^ exponent - input[lane.val].value| := by
  let block := quantizeFinite profile .saturate input
  have hblock := quantizeFinite_quantizes profile .saturate input
  simp only [Quantizes, hscale] at hblock
  have hround : Element.Quantizes (scaleFinite (-exponent) input[lane.val])
      block.values[lane.val] := by
    simpa only [Element.QuantizesWith, reduceCtorEq, false_and, ↓reduceIte] using hblock.2 lane
  have hnearest := hround
  obtain ⟨value, hvalue, _⟩ := hround
  refine ⟨value * (2 : Rat) ^ exponent,
    Block.decodeLane_value block lane (hblock.1 ▸ hscale) hvalue, ?_⟩
  intro other otherValue hother
  rw [scaled_error, scaled_error]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num) _))
  simpa only [scaleFinite_value] using hnearest.error_le hvalue hother

end FloatLib.Floats.Formats.OCP.MX.Standard
