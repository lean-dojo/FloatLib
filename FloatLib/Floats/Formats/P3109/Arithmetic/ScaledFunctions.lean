/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Functions.Operations
public meta import FloatLib.Tactic.P3109ScaledFunctions

/-!
# P3109 scaled elementary functions

P3109 interim report v4.1 §5.8 (unapproved draft) defines each scaled function as a
one-lane block function at exact result scale one. The scalar policy
retains its supplied random word; no intermediate source conversion occurs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

open FloatLib.Numerics FloatLib.Floats.ExecFloat

variable {Scale ScaleExact Source SourceExact : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]

/-- P3109 interim report v4.1, §5.8: the sole lane of an elementary block operation at result
    scale one. -/
def scaledUnaryFunction (format : Format) (operation : Functions.Unary)
    (scale : Scale) (value : Source) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109 format :=
  (Block.unaryFunction format (length := 1) ⟨.scalar mode, saturation⟩ operation
    ⟨scale, #v[value]⟩ (1 : Rat)).values[0]

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- P3109 interim report v4.1, §5.8: the one-lane inverse-tangent block operation at exact
    result scale one. -/
def scaledAngleFunction (format : Format) (piScaled : Bool)
    (yScale : Scale) (y : Source) (xScale : RightScale) (x : Right)
    (mode : RoundingMode) (saturation : SaturationMode) : ExecFloat.P3109 format :=
  (Block.angleFunction format (length := 1) ⟨.scalar mode, saturation⟩ piScaled
    ⟨yScale, #v[y]⟩ ⟨xScale, #v[x]⟩ (1 : Rat)).values[0]


scaled_function ScaledLog := Functions.Unary.log
scaled_function ScaledLog2 := Functions.Unary.log2
scaled_function ScaledLogOnePlus := Functions.Unary.logOnePlus
scaled_function ScaledExp := Functions.Unary.exp
scaled_function ScaledExp2 := Functions.Unary.exp2
scaled_function ScaledExpMinusOne := Functions.Unary.expMinusOne
scaled_function ScaledSin := Functions.Unary.sin
scaled_function ScaledCos := Functions.Unary.cos
scaled_function ScaledTan := Functions.Unary.tan
scaled_function ScaledArcSin := Functions.Unary.arcSin
scaled_function ScaledArcCos := Functions.Unary.arcCos
scaled_function ScaledArcTan := Functions.Unary.arcTan
scaled_function ScaledSinh := Functions.Unary.sinh
scaled_function ScaledCosh := Functions.Unary.cosh
scaled_function ScaledTanh := Functions.Unary.tanh
scaled_function ScaledArcSinh := Functions.Unary.arcSinh
scaled_function ScaledArcCosh := Functions.Unary.arcCosh
scaled_function ScaledArcTanh := Functions.Unary.arcTanh
scaled_function ScaledSinPi := Functions.Unary.sinPi
scaled_function ScaledCosPi := Functions.Unary.cosPi
scaled_function ScaledTanPi := Functions.Unary.tanPi
scaled_function ScaledArcSinPi := Functions.Unary.arcSinPi
scaled_function ScaledArcCosPi := Functions.Unary.arcCosPi
scaled_function ScaledArcTanPi := Functions.Unary.arcTanPi
scaled_function ScaledSoftplus := Functions.Unary.softplus


scaled_angle ScaledArcTan2 := false
scaled_angle ScaledArcTan2Pi := true

end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed
