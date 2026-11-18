/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.CodedDot
public import FloatLib.Floats.Formats.P3109.Block.Proof

/-!
# P3109 formats in the general block-scaled format

`Format.codec format policy` makes a P3109 format an element or scale codec of
`Formats.Block.CodedFormat`, under any projection policy (rounding mode and saturation). So the
general quantizer, its error and flush-to-zero theorems and its dot products apply to P3109
elements and scales, and `Block.format scaleFormat format length` is the storage format of a
block of chapter 5 of the interim report.

The chapter 5 operations agree with the general format where both multiply and divide finite
values:

* `Block.convertTo_lane`: conversion to a block at a finite nonzero scale stores, in each lane,
  the code the element codec stores for the exact scaled input. This is the rule
  `CodedFormat.elements_quantize` states for the general quantizer.
* `Block.decode_lane`: under a finite scale of either sign, zero included, decoding a lane
  (§5.4.1) is `Tensor.decode`.
* `Block.dotExact_eq`: under finite scales, the exact dot product of two blocks (§5.6.2) is
  `Tensor.dotExact` over the lanes in order. Both use the closed arithmetic `Arithmetic.add` and
  `Arithmetic.mul`.

The report's rules for a zero or infinite result scale in conversion to a block (§5.4.2) and its
products with an infinite scale (§5.4.1) are not instances: the general quantizer divides by the
scale, and the general decoding gives NaN under a scale with no finite value. Stochastic rounding
with one random word per lane is an element format per position in
`Formats.Block.Format`; the stored format here has one policy for every lane.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics FloatLib.Floats Arithmetic

/-- A P3109 format as a codec: a word decodes to its exact value, and an exact value is stored by
one projection under `policy`.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§5.4.2.
-/
@[reducible] def Format.codec (format : Format) (policy : ProjectionPolicy := {}) :
    Formats.Block.Codec where
  Code := ExecFloat.P3109 format
  decode word := (Mixed.decode word).map SignedRat.ofRat
  encode s := (Destination.p3109 format).project policy (.finite s.value)
  value_encode s := by simp

namespace Block

variable {length : ℕ+}

/-- The storage format of a chapter 5 block in the general block format: `length` lanes of
`format` and one scale of `scaleFormat`. -/
@[reducible] def format (scaleFormat format : Format) (length : ℕ+)
    (policy scalePolicy : ProjectionPolicy := {}) :
    Formats.Block.CodedFormat (Fin (length : ℕ)) Unit where
  element := format.codec policy
  levels := [{ group := fun _ => (), codec := scaleFormat.codec scalePolicy }]

/-- A chapter 5 block as a stored tensor of the general block format. -/
def toTensor {scaleFormat elementFormat : Format} (policy scalePolicy : ProjectionPolicy)
    (block : Block (ExecFloat.P3109 scaleFormat) (ExecFloat.P3109 elementFormat) length) :
    Formats.Block.Tensor (format scaleFormat elementFormat length policy scalePolicy) where
  scales := (fun _ => block.scale, ())
  elements lane := block.values[lane.val]

variable {Scale ScaleExact : Type} [ExecFloat.ExactDecoder Scale ScaleExact]
  [ExecFloat.ExactMap ScaleExact Rat]

/--
Conversion to a block (§5.5.2) at a finite nonzero scale `σ`, with one rounding mode for the
block: each lane stores the code the element codec stores for the exact scaled input `x / σ`.
-/
theorem convertTo_lane (elementFormat : Format) (policy : ProjectionPolicy)
    (values : Vector Rat length) (scale : Scale) {σ : ℚ}
    (hσ : Mixed.decode scale = .finite σ) (hσ0 : σ ≠ 0) (lane : Fin (length : ℕ)) :
    (ConvertToBlock (Destination.p3109 elementFormat) ⟨.scalar policy.rounding, policy.saturation⟩
        values scale).values[lane.val] =
      (elementFormat.codec policy).encode (SignedRat.ofRat (values[lane.val] / σ)) := by
  have hvalue : Mixed.decode values[lane.val] = NumericalValue.finite values[lane.val] := rfl
  simp only [ConvertToBlock, project, Vector.getElem_ofFn, Vector.getElem_map, hσ, hvalue,
    normalize_finite _ _ hσ0, SignedRat.value_ofRat]
  rfl

/-- The exceptional class of a decoded word is the report's NaN. -/
private theorem exceptional_eq_nan {Source SourceExact : Type}
    [ExecFloat.ExactDecoder Source SourceExact] [ExecFloat.ExactMap SourceExact Rat]
    {word : Source} {kind : ExceptionalValue} (h : Mixed.decode word = .exceptional kind) :
    kind = .nan := by
  unfold Mixed.decode at h
  generalize (ExecFloat.ExactDecoder.decodeTo word : NumericalValue Rat) = value at h
  cases value <;> simp_all [canonical, nan]

/--
Decoding (§5.4.1) under a finite scale is the exact decoding of the general block format: a
finite element times the scale, an element infinity with the sign of the product or NaN under
the scale zero, and NaN kept.
-/
theorem decode_lane {scaleFormat elementFormat : Format} (policy scalePolicy : ProjectionPolicy)
    (block : Block (ExecFloat.P3109 scaleFormat) (ExecFloat.P3109 elementFormat) length)
    {σ : ℚ} (hσ : Mixed.decode block.scale = .finite σ) (lane : Fin (length : ℕ)) :
    (decode block)[lane.val] =
      ((toTensor policy scalePolicy block).decode lane).map SignedRat.value := by
  have hfinite : Formats.Block.ScaleCodes.isFinite
      (format scaleFormat elementFormat length policy scalePolicy).levels
      (toTensor policy scalePolicy block).scales lane = true := by
    change (((Mixed.decode block.scale).map SignedRat.ofRat).isFinite && true) = true
    rw [hσ]
    rfl
  have hscale : (toTensor policy scalePolicy block).scale lane = σ := by
    change Formats.Block.finiteValue ((Mixed.decode block.scale).map SignedRat.ofRat) * 1 = σ
    rw [hσ]
    simp [Formats.Block.finiteValue]
  have helement : (format scaleFormat elementFormat length policy scalePolicy).element.decode
      ((toTensor policy scalePolicy block).elements lane) =
      (Mixed.decode block.values[lane.val]).map SignedRat.ofRat := rfl
  simp only [decode, Vector.getElem_map, hσ]
  cases hvalue : Mixed.decode block.values[lane.val] with
  | finite value =>
    rw [hvalue] at helement
    rw [Formats.Block.Tensor.decode_finite _ lane hfinite helement, hscale]
    simp only [Arithmetic.Multiply, NumericalValue.map_finite, SignedRat.value_mul,
      SignedRat.value_ofRat]
    rw [_root_.mul_comm]
  | infinity negative =>
    rw [hvalue] at helement
    rw [Formats.Block.Tensor.decode_infinity _ lane hfinite helement, hscale]
    by_cases hzero : σ = 0
    · simp [Arithmetic.Multiply, Arithmetic.nan, hzero]
    · simp [Arithmetic.Multiply, hzero]
  | exceptional kind =>
    rw [hvalue] at helement
    rw [Formats.Block.Tensor.decode_exceptional _ lane hfinite helement,
      exceptional_eq_nan hvalue]
    rfl

/--
Under finite scales, the exact dot product of two chapter 5 blocks (§5.6.2), which may have
different scale and element formats, is the exact dot product of the general block format over
the lanes in increasing order.
-/
theorem dotExact_eq {leftScale leftElement rightScale rightElement : Format}
    (policy scalePolicy : ProjectionPolicy)
    (left : Block (ExecFloat.P3109 leftScale) (ExecFloat.P3109 leftElement) length)
    (right : Block (ExecFloat.P3109 rightScale) (ExecFloat.P3109 rightElement) length)
    {σ τ : ℚ} (hσ : Mixed.decode left.scale = .finite σ)
    (hτ : Mixed.decode right.scale = .finite τ) :
    dotExact left right =
      Formats.Block.Tensor.dotExact (toTensor policy scalePolicy left)
        (toTensor policy scalePolicy right) (List.finRange (length : ℕ)) := by
  unfold dotExact sumExact Formats.Block.Tensor.dotExact Formats.Block.Extended.sum
  dsimp only
  congr 1
  rw [Vector.toList_ofFn, List.ofFn_eq_map]
  refine List.map_congr_left fun lane _ => ?_
  rw [decode_lane policy scalePolicy left hσ lane, decode_lane policy scalePolicy right hτ lane]

end Block

end FloatLib.Floats.Formats.P3109
