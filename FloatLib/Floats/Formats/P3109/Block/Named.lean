/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109
import Mathlib.Tactic.FinCases

/-!
# The named scaled and block operations of P3109 chapter 5

P3109 Interim Report v4.1 (14 September 2026), §§5.7 and 5.8, an unapproved draft. Chapter 5
names one scaled operation and one block operation for each operation of chapter 4. FloatLib
defines each name as an instance of one generic operation (`Mixed.scaledUnary`, `Block.unary` and
their siblings). This module checks the names against that table.

* `scaled`, `block` and `scaled_roots`: every named exact operation is evaluated by Lean's kernel
  on rational operands with independent scales, into the destination that keeps the exact result
  (the root operations into Binary8p4se).
* `scaled_functions`, `block_functions`, `scaled_angles` and `block_angles`: every named
  elementary function decodes to the reference value of its function at the scaled operand,
  normalized by the result scale, for every P3109 descriptor, policy, scale type and operand.
  These are the generic theorems `Mixed.decode_scaledUnaryFunction`,
  `Block.decode_unaryFunction_lane`, `Mixed.decode_scaledAngleFunction` and
  `Block.decode_angleFunction_lane` at each name.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Block.Named

open FloatLib.Numerics FloatLib.Floats FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.P3109 FloatLib.Floats.Formats.P3109.Arithmetic

/-- Blocks of two lanes. -/
abbrev Two : ℕ+ := ⟨2, by decide⟩

/-- The vector of two lanes. -/
abbrev pair {α : Type} (first second : α) : Vector α Two := ⟨#[first, second], rfl⟩

/-- The destination that keeps the exact result. -/
abbrev exact : Destination (NumericalValue Rat) := ⟨fun _ value => value⟩

/-- A block of two rational lanes with a rational scale. -/
abbrev source (scale first second : Rat) : Block Rat Rat Two := ⟨scale, pair first second⟩

/-- The block with scale `2` and lanes `1 / 2` and `-3 / 2`: the values `1` and `-3`. -/
abbrev left : Block Rat Rat Two := source 2 (1 / 2) (-3 / 2)

/-- The block with scale `3` and lanes `2 / 3` and `-1 / 3`: the values `2` and `-1`. -/
abbrev right : Block Rat Rat Two := source 3 (2 / 3) (-1 / 3)

/-- P3109 interim report v4.1, §5.8: the named exact scaled operations at the operands `2 * (-3
    / 2) = -3` and
`3 * (-1 / 3) = -1`, and the three ternary ones at `2 * (1 / 2)`, `3 * (2 / 3)`, `4 * (1 / 4)`
and at `-3`, `-2`, `2`. -/
theorem scaled :
    [Mixed.ScaledConvert exact (2 : Rat) (-3 / 2 : Rat),
      Mixed.ScaledAbs exact (2 : Rat) (-3 / 2 : Rat),
      Mixed.ScaledNegate exact (2 : Rat) (-3 / 2 : Rat),
      Mixed.ScaledRecip exact (2 : Rat) (-3 / 2 : Rat),
      Mixed.ScaledCopySign exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledAdd exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledSubtract exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMultiply exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledDivide exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMinimum exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMaximum exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMinimumNumber exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMaximumNumber exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMinimumMagnitude exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMaximumMagnitude exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMinimumMagnitudeNumber exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMaximumMagnitudeNumber exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMinimumFinite exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledMaximumFinite exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-1 / 3 : Rat),
      Mixed.ScaledFMA exact (2 : Rat) (1 / 2 : Rat) (3 : Rat) (2 / 3 : Rat) (4 : Rat) (1 / 4 : Rat),
      Mixed.ScaledFAA exact (2 : Rat) (1 / 2 : Rat) (3 : Rat) (2 / 3 : Rat) (4 : Rat) (1 / 4 : Rat),
      Mixed.ScaledClamp exact (2 : Rat) (-3 / 2 : Rat) (3 : Rat) (-2 / 3 : Rat) (4 : Rat) (1 / 2 :
        Rat)] =
      [.finite (-3), .finite 3, .finite 3, .finite (-1 / 3), .finite (-3), .finite (-4),
        .finite (-2), .finite 3, .finite 3, .finite (-3), .finite (-1), .finite (-3), .finite (-1),
        .finite (-1), .finite (-3), .finite (-1), .finite (-3), .finite (-3), .finite (-1),
        .finite 3, .finite 4, .finite (-2)] := by
  decide +kernel

/-- P3109 interim report v4.1, §5.8 with §§4.10.9 to 4.10.11: the three named scaled root
    operations into
Binary8p4se: `sqrt (4 * 1) = 2`, `1 / sqrt (4 * 1) = 1 / 2` and `hypot (1 * 3) (1 * 4) = 5`. -/
theorem scaled_roots :
    [Mixed.decode (Mixed.ScaledSqrt .binary8p4se (4 : Rat) (1 : Rat)),
      Mixed.decode (Mixed.ScaledRSqrt .binary8p4se (4 : Rat) (1 : Rat)),
      Mixed.decode (Mixed.ScaledHypot .binary8p4se (1 : Rat) (3 : Rat) (1 : Rat) (4 : Rat))] =
      [.finite 2, .finite (1 / 2), .finite 5] := by
  decide +kernel

/-- P3109 interim report v4.1, §5.7: the named exact block operations on the blocks with the
    values `(1, -3)`
and `(2, -1)`, with the result scale `2`. -/
theorem block :
    [(BlockConvert exact {} left (2 : Rat)).values, (BlockAbs exact {} left (2 : Rat)).values,
      (BlockNegate exact {} left (2 : Rat)).values, (BlockRecip exact {} left (2 : Rat)).values,
      (BlockCopySign exact {} left right (2 : Rat)).values,
      (BlockAdd exact {} left right (2 : Rat)).values,
      (BlockSubtract exact {} left right (2 : Rat)).values,
      (BlockMultiply exact {} left right (2 : Rat)).values,
      (BlockDivide exact {} left right (2 : Rat)).values,
      (BlockMinimum exact {} left right (2 : Rat)).values,
      (BlockMaximum exact {} left right (2 : Rat)).values,
      (BlockMinimumNumber exact {} left right (2 : Rat)).values,
      (BlockMaximumNumber exact {} left right (2 : Rat)).values,
      (BlockMinimumMagnitude exact {} left right (2 : Rat)).values,
      (BlockMaximumMagnitude exact {} left right (2 : Rat)).values,
      (BlockMinimumMagnitudeNumber exact {} left right (2 : Rat)).values,
      (BlockMaximumMagnitudeNumber exact {} left right (2 : Rat)).values,
      (BlockMinimumFinite exact {} left right (2 : Rat)).values,
      (BlockMaximumFinite exact {} left right (2 : Rat)).values,
      (BlockFMA exact {} left right (source 1 1 1) (2 : Rat)).values,
      (BlockFAA exact {} left right (source 1 1 1) (2 : Rat)).values,
      (BlockClamp exact {} left (source 1 (-2) (-2)) (source 1 2 2) (2 : Rat)).values] =
      [pair (.finite (1 / 2)) (.finite (-3 / 2)), pair (.finite (1 / 2)) (.finite (3 / 2)),
        pair (.finite (-1 / 2)) (.finite (3 / 2)), pair (.finite (1 / 2)) (.finite (-1 / 6)),
        pair (.finite (1 / 2)) (.finite (-3 / 2)), pair (.finite (3 / 2)) (.finite (-2)),
        pair (.finite (-1 / 2)) (.finite (-1)), pair (.finite 1) (.finite (3 / 2)),
        pair (.finite (1 / 4)) (.finite (3 / 2)), pair (.finite (1 / 2)) (.finite (-3 / 2)),
        pair (.finite 1) (.finite (-1 / 2)), pair (.finite (1 / 2)) (.finite (-3 / 2)),
        pair (.finite 1) (.finite (-1 / 2)), pair (.finite (1 / 2)) (.finite (-1 / 2)),
        pair (.finite 1) (.finite (-3 / 2)), pair (.finite (1 / 2)) (.finite (-1 / 2)),
        pair (.finite 1) (.finite (-3 / 2)), pair (.finite (1 / 2)) (.finite (-3 / 2)),
        pair (.finite 1) (.finite (-1 / 2)), pair (.finite (3 / 2)) (.finite 2),
        pair (.finite 2) (.finite (-3 / 2)), pair (.finite (1 / 2)) (.finite (-1))] := by
  decide +kernel

section Functions

variable {length : ℕ+}
  {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact : Type}
  {ResultScale ResultScaleExact : Type}
  [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
  [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
  [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
  [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
  [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]

/-- P3109 interim report v4.1, §5.8: each named scaled elementary function decodes to the
    reference value of
its function at the product of the scale and the operand, for every descriptor, rounding mode,
saturation mode, scale and operand. -/
theorem scaled_functions (format : Format) (scale : Scale) (value : Source)
    (mode : RoundingMode) (saturation : SaturationMode) :
    ∀ entry ∈ ([
      (Mixed.ScaledLog format scale value mode saturation, Functions.Unary.log),
      (Mixed.ScaledLog2 format scale value mode saturation, Functions.Unary.log2),
      (Mixed.ScaledLogOnePlus format scale value mode saturation, Functions.Unary.logOnePlus),
      (Mixed.ScaledExp format scale value mode saturation, Functions.Unary.exp),
      (Mixed.ScaledExp2 format scale value mode saturation, Functions.Unary.exp2),
      (Mixed.ScaledExpMinusOne format scale value mode saturation, Functions.Unary.expMinusOne),
      (Mixed.ScaledSin format scale value mode saturation, Functions.Unary.sin),
      (Mixed.ScaledCos format scale value mode saturation, Functions.Unary.cos),
      (Mixed.ScaledTan format scale value mode saturation, Functions.Unary.tan),
      (Mixed.ScaledArcSin format scale value mode saturation, Functions.Unary.arcSin),
      (Mixed.ScaledArcCos format scale value mode saturation, Functions.Unary.arcCos),
      (Mixed.ScaledArcTan format scale value mode saturation, Functions.Unary.arcTan),
      (Mixed.ScaledSinh format scale value mode saturation, Functions.Unary.sinh),
      (Mixed.ScaledCosh format scale value mode saturation, Functions.Unary.cosh),
      (Mixed.ScaledTanh format scale value mode saturation, Functions.Unary.tanh),
      (Mixed.ScaledArcSinh format scale value mode saturation, Functions.Unary.arcSinh),
      (Mixed.ScaledArcCosh format scale value mode saturation, Functions.Unary.arcCosh),
      (Mixed.ScaledArcTanh format scale value mode saturation, Functions.Unary.arcTanh),
      (Mixed.ScaledSinPi format scale value mode saturation, Functions.Unary.sinPi),
      (Mixed.ScaledCosPi format scale value mode saturation, Functions.Unary.cosPi),
      (Mixed.ScaledTanPi format scale value mode saturation, Functions.Unary.tanPi),
      (Mixed.ScaledArcSinPi format scale value mode saturation, Functions.Unary.arcSinPi),
      (Mixed.ScaledArcCosPi format scale value mode saturation, Functions.Unary.arcCosPi),
      (Mixed.ScaledArcTanPi format scale value mode saturation, Functions.Unary.arcTanPi),
      (Mixed.ScaledSoftplus format scale value mode saturation, Functions.Unary.softplus)] :
        List (ExecFloat.P3109 format × Functions.Unary)),
      Format.SameDatum (ExecFloat.P3109.decode entry.1)
        (Functions.referenceValue format { rounding := mode, saturation }
          (FunctionBlock.normalize (.finite 1) (Functions.unary entry.2
            (Arithmetic.Multiply (Mixed.decode scale) (Mixed.decode value))))) := by
  intro entry h
  fin_cases h <;> exact Mixed.decode_scaledUnaryFunction format _ scale value mode saturation

/-- P3109 interim report v4.1, §5.7: each lane of each named block elementary function decodes
    to the reference
value of its function at the lane, normalized by the result scale, for every descriptor, block
policy, block and result scale. -/
theorem block_functions (format : Format) (policy : BlockPolicy length)
    (block : Block Scale Source length) (resultScale : ResultScale)
    (lane : Fin (length : Nat)) :
    ∀ entry ∈ ([
      ((BlockLog format policy block resultScale).values[lane.val], Functions.Unary.log),
      ((BlockLog2 format policy block resultScale).values[lane.val], Functions.Unary.log2),
      ((BlockLogOnePlus format policy block resultScale).values[lane.val],
        Functions.Unary.logOnePlus),
      ((BlockExp format policy block resultScale).values[lane.val], Functions.Unary.exp),
      ((BlockExp2 format policy block resultScale).values[lane.val], Functions.Unary.exp2),
      ((BlockExpMinusOne format policy block resultScale).values[lane.val],
        Functions.Unary.expMinusOne),
      ((BlockSin format policy block resultScale).values[lane.val], Functions.Unary.sin),
      ((BlockCos format policy block resultScale).values[lane.val], Functions.Unary.cos),
      ((BlockTan format policy block resultScale).values[lane.val], Functions.Unary.tan),
      ((BlockArcSin format policy block resultScale).values[lane.val], Functions.Unary.arcSin),
      ((BlockArcCos format policy block resultScale).values[lane.val], Functions.Unary.arcCos),
      ((BlockArcTan format policy block resultScale).values[lane.val], Functions.Unary.arcTan),
      ((BlockSinh format policy block resultScale).values[lane.val], Functions.Unary.sinh),
      ((BlockCosh format policy block resultScale).values[lane.val], Functions.Unary.cosh),
      ((BlockTanh format policy block resultScale).values[lane.val], Functions.Unary.tanh),
      ((BlockArcSinh format policy block resultScale).values[lane.val], Functions.Unary.arcSinh),
      ((BlockArcCosh format policy block resultScale).values[lane.val], Functions.Unary.arcCosh),
      ((BlockArcTanh format policy block resultScale).values[lane.val], Functions.Unary.arcTanh),
      ((BlockSinPi format policy block resultScale).values[lane.val], Functions.Unary.sinPi),
      ((BlockCosPi format policy block resultScale).values[lane.val], Functions.Unary.cosPi),
      ((BlockTanPi format policy block resultScale).values[lane.val], Functions.Unary.tanPi),
      ((BlockArcSinPi format policy block resultScale).values[lane.val], Functions.Unary.arcSinPi),
      ((BlockArcCosPi format policy block resultScale).values[lane.val], Functions.Unary.arcCosPi),
      ((BlockArcTanPi format policy block resultScale).values[lane.val], Functions.Unary.arcTanPi),
      ((BlockSoftplus format policy block resultScale).values[lane.val], Functions.Unary.softplus)]
        :
        List (ExecFloat.P3109 format × Functions.Unary)),
      Format.SameDatum (ExecFloat.P3109.decode entry.1)
        (Functions.referenceValue format (policy.at lane)
          (FunctionBlock.normalize (Mixed.decode resultScale)
            (Functions.unary entry.2 (Block.decode block)[lane.val]))) := by
  intro entry h
  fin_cases h <;> exact Block.decode_unaryFunction_lane format policy _ block resultScale lane

/-- P3109 interim report v4.1, §5.8: the two named scaled two-argument arc tangents decode to
    the reference
value of the arc tangent of the two scaled operands, in radians and in half turns. -/
theorem scaled_angles (format : Format) (yScale : Scale) (y : Source) (xScale : RightScale)
    (x : Right) (mode : RoundingMode) (saturation : SaturationMode) :
    ∀ entry ∈ ([(Mixed.ScaledArcTan2 format yScale y xScale x mode saturation, false),
      (Mixed.ScaledArcTan2Pi format yScale y xScale x mode saturation, true)] :
        List (ExecFloat.P3109 format × Bool)),
      Format.SameDatum (ExecFloat.P3109.decode entry.1)
        (Functions.referenceValue format { rounding := mode, saturation }
          (FunctionBlock.normalize (.finite 1) (Functions.arcTan2 entry.2
            (Arithmetic.Multiply (Mixed.decode yScale) (Mixed.decode y))
            (Arithmetic.Multiply (Mixed.decode xScale) (Mixed.decode x))))) := by
  intro entry h
  fin_cases h <;>
    exact Mixed.decode_scaledAngleFunction format _ yScale y xScale x mode saturation

/-- P3109 interim report v4.1, §5.7: each lane of the two named block two-argument arc tangents
    decodes to the
reference value of the arc tangent of the two lanes, normalized by the result scale. -/
theorem block_angles (format : Format) (policy : BlockPolicy length)
    (y : Block Scale Source length) (x : Block RightScale Right length)
    (resultScale : ResultScale) (lane : Fin (length : Nat)) :
    ∀ entry ∈ ([((BlockArcTan2 format policy y x resultScale).values[lane.val], false),
      ((BlockArcTan2Pi format policy y x resultScale).values[lane.val], true)] :
        List (ExecFloat.P3109 format × Bool)),
      Format.SameDatum (ExecFloat.P3109.decode entry.1)
        (Functions.referenceValue format (policy.at lane)
          (FunctionBlock.normalize (Mixed.decode resultScale)
            (Functions.arcTan2 entry.2 (Block.decode y)[lane.val]
              (Block.decode x)[lane.val]))) := by
  intro entry h
  fin_cases h <;> exact Block.decode_angleFunction_lane format policy _ y x resultScale lane

end Functions

end FloatLib.Floats.Formats.P3109.Block.Named
