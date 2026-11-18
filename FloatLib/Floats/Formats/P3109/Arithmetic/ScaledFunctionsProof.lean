/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.ReferencePaths

public import FloatLib.Floats.Formats.P3109.Arithmetic.ScaledFunctions
public import FloatLib.Floats.Formats.P3109.Block.Functions.Proof
public import FloatLib.Numerics.Executable.Conversion.Proof

/-!
# P3109 scaled function certificates

P3109 interim report v4.1 §5.8 (unapproved draft): every elementary scaled operation
is the sole lane of its block operation with exact result scale one.
The source scales and elements have independent exact decoding types.
-/

public section

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

open FloatLib.Numerics FloatLib.Floats.ExecFloat

variable {Scale ScaleExact Source SourceExact : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]

/-- Every scaled unary function refines the one-lane §5.8 real-function reference. -/
theorem decode_scaledUnaryFunction (format : Format) (operation : Functions.Unary)
    (scale : Scale) (value : Source) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode (scaledUnaryFunction format operation scale value mode saturation))
      (Functions.referenceValue format { rounding := mode, saturation }
        (FunctionBlock.normalize (.finite 1)
          (Functions.unary operation (Arithmetic.Multiply (decode scale) (decode value))))) := by
  simpa [scaledUnaryFunction, Block.decode, BlockPolicy.at, decode, canonical] using
    Block.decode_unaryFunction_lane format (length := 1) ⟨.scalar mode, saturation⟩
      operation ⟨scale, #v[value]⟩ (1 : Rat) ⟨0, by decide⟩

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- Both scaled inverse-tangent forms refine the §5.8 one-lane reference for all source types. -/
theorem decode_scaledAngleFunction (format : Format) (piScaled : Bool)
    (yScale : Scale) (y : Source) (xScale : RightScale) (x : Right)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (scaledAngleFunction format piScaled yScale y xScale x mode saturation))
      (Functions.referenceValue format { rounding := mode, saturation }
        (FunctionBlock.normalize (.finite 1)
          (Functions.arcTan2 piScaled
            (Arithmetic.Multiply (decode yScale) (decode y))
            (Arithmetic.Multiply (decode xScale) (decode x))))) := by
  simpa [scaledAngleFunction, Block.decode, BlockPolicy.at, decode, canonical] using
    Block.decode_angleFunction_lane format (length := 1) ⟨.scalar mode, saturation⟩
      piScaled ⟨yScale, #v[y]⟩ ⟨xScale, #v[x]⟩ (1 : Rat) ⟨0, by decide⟩

end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

/-!
# P3109 block and scaled function execution paths

The reference certificates and kernel defining equations cover all named
§§5.7–5.8 elementary functions at arbitrary descriptors and positive block
lengths. They retain exact normalization and every supplied stochastic word.
No direct encoding speedup is claimed by these registrations.
-/

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Floats.ExecFloat

reference_paths Block.BlockLog
reference_paths Block.BlockLog2
reference_paths Block.BlockLogOnePlus
reference_paths Block.BlockExp
reference_paths Block.BlockExp2
reference_paths Block.BlockExpMinusOne
reference_paths Block.BlockSin
reference_paths Block.BlockCos
reference_paths Block.BlockTan
reference_paths Block.BlockArcSin
reference_paths Block.BlockArcCos
reference_paths Block.BlockArcTan
reference_paths Block.BlockSinh
reference_paths Block.BlockCosh
reference_paths Block.BlockTanh
reference_paths Block.BlockArcSinh
reference_paths Block.BlockArcCosh
reference_paths Block.BlockArcTanh
reference_paths Block.BlockSinPi
reference_paths Block.BlockCosPi
reference_paths Block.BlockTanPi
reference_paths Block.BlockArcSinPi
reference_paths Block.BlockArcCosPi
reference_paths Block.BlockArcTanPi
reference_paths Block.BlockSoftplus
reference_paths Block.BlockArcTan2
reference_paths Block.BlockArcTan2Pi

reference_paths Arithmetic.Mixed.ScaledLog
reference_paths Arithmetic.Mixed.ScaledLog2
reference_paths Arithmetic.Mixed.ScaledLogOnePlus
reference_paths Arithmetic.Mixed.ScaledExp
reference_paths Arithmetic.Mixed.ScaledExp2
reference_paths Arithmetic.Mixed.ScaledExpMinusOne
reference_paths Arithmetic.Mixed.ScaledSin
reference_paths Arithmetic.Mixed.ScaledCos
reference_paths Arithmetic.Mixed.ScaledTan
reference_paths Arithmetic.Mixed.ScaledArcSin
reference_paths Arithmetic.Mixed.ScaledArcCos
reference_paths Arithmetic.Mixed.ScaledArcTan
reference_paths Arithmetic.Mixed.ScaledSinh
reference_paths Arithmetic.Mixed.ScaledCosh
reference_paths Arithmetic.Mixed.ScaledTanh
reference_paths Arithmetic.Mixed.ScaledArcSinh
reference_paths Arithmetic.Mixed.ScaledArcCosh
reference_paths Arithmetic.Mixed.ScaledArcTanh
reference_paths Arithmetic.Mixed.ScaledSinPi
reference_paths Arithmetic.Mixed.ScaledCosPi
reference_paths Arithmetic.Mixed.ScaledTanPi
reference_paths Arithmetic.Mixed.ScaledArcSinPi
reference_paths Arithmetic.Mixed.ScaledArcCosPi
reference_paths Arithmetic.Mixed.ScaledArcTanPi
reference_paths Arithmetic.Mixed.ScaledSoftplus
reference_paths Arithmetic.Mixed.ScaledArcTan2
reference_paths Arithmetic.Mixed.ScaledArcTan2Pi

attribute [kernel_optimize]
  Block.projectFunctions.eq_def Block.unaryFunction.eq_def Block.angleFunction.eq_def
  Arithmetic.Mixed.scaledUnaryFunction.eq_def Arithmetic.Mixed.scaledAngleFunction.eq_def

end FloatLib.Floats.Formats.P3109
