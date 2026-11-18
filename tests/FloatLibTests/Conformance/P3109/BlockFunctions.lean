/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.ScaledFunctionsProof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLib.Tactic.FloatDecide

/-! P3109 interim report v4.1, §§5.4, 5.7–5.8: all-descriptor proof clients and closed normalization
regressions. -/

public section

namespace FloatLibTests.Conformance.P3109.BlockFunctions

open FloatLib.Numerics FloatLib.Floats
open Formats.P3109

local macro "check_unary " blockName:ident scaledName:ident " via " operation:term : command =>
  `(section
    variable {length : ℕ+} {Scale ScaleExact Source SourceExact ResultScale ResultScaleExact : Type}
    variable [ExecFloat.ExactDecoder Scale ScaleExact] [ExecFloat.ExactMap ScaleExact Rat]
    variable [ExecFloat.ExactDecoder Source SourceExact] [ExecFloat.ExactMap SourceExact Rat]
    variable [ExecFloat.ExactDecoder ResultScale ResultScaleExact]
      [ExecFloat.ExactMap ResultScaleExact Rat]
    example (format : Format) (policy : BlockPolicy length) (block : Block Scale Source length)
        (resultScale : ResultScale) (lane : Fin (length : Nat)) :
        Format.SameDatum (ExecFloat.P3109.decode
          ($blockName format policy block resultScale).values[lane.val])
          (Functions.referenceValue format (policy.at lane)
            (FunctionBlock.normalize (Arithmetic.Mixed.decode resultScale)
              (Functions.unary $operation (Block.decode block)[lane.val]))) :=
      Block.decode_unaryFunction_lane format policy $operation block resultScale lane
    example (format : Format) (scale : Scale) (value : Source)
        (mode : RoundingMode) (saturation : SaturationMode) :
        Format.SameDatum (ExecFloat.P3109.decode ($scaledName format scale value mode saturation))
          (Functions.referenceValue format { rounding := mode, saturation }
            (FunctionBlock.normalize (.finite 1) (Functions.unary $operation
              (Arithmetic.Multiply (Arithmetic.Mixed.decode scale)
                  (Arithmetic.Mixed.decode value))))) :=
      Arithmetic.Mixed.decode_scaledUnaryFunction format $operation scale value mode saturation
    end)

check_unary Block.BlockLog Arithmetic.Mixed.ScaledLog via Functions.Unary.log
check_unary Block.BlockLog2 Arithmetic.Mixed.ScaledLog2 via Functions.Unary.log2
check_unary Block.BlockLogOnePlus Arithmetic.Mixed.ScaledLogOnePlus via Functions.Unary.logOnePlus
check_unary Block.BlockExp Arithmetic.Mixed.ScaledExp via Functions.Unary.exp
check_unary Block.BlockExp2 Arithmetic.Mixed.ScaledExp2 via Functions.Unary.exp2
check_unary Block.BlockExpMinusOne Arithmetic.Mixed.ScaledExpMinusOne via
    Functions.Unary.expMinusOne
check_unary Block.BlockSin Arithmetic.Mixed.ScaledSin via Functions.Unary.sin
check_unary Block.BlockCos Arithmetic.Mixed.ScaledCos via Functions.Unary.cos
check_unary Block.BlockTan Arithmetic.Mixed.ScaledTan via Functions.Unary.tan
check_unary Block.BlockArcSin Arithmetic.Mixed.ScaledArcSin via Functions.Unary.arcSin
check_unary Block.BlockArcCos Arithmetic.Mixed.ScaledArcCos via Functions.Unary.arcCos
check_unary Block.BlockArcTan Arithmetic.Mixed.ScaledArcTan via Functions.Unary.arcTan
check_unary Block.BlockSinh Arithmetic.Mixed.ScaledSinh via Functions.Unary.sinh
check_unary Block.BlockCosh Arithmetic.Mixed.ScaledCosh via Functions.Unary.cosh
check_unary Block.BlockTanh Arithmetic.Mixed.ScaledTanh via Functions.Unary.tanh
check_unary Block.BlockArcSinh Arithmetic.Mixed.ScaledArcSinh via Functions.Unary.arcSinh
check_unary Block.BlockArcCosh Arithmetic.Mixed.ScaledArcCosh via Functions.Unary.arcCosh
check_unary Block.BlockArcTanh Arithmetic.Mixed.ScaledArcTanh via Functions.Unary.arcTanh
check_unary Block.BlockSinPi Arithmetic.Mixed.ScaledSinPi via Functions.Unary.sinPi
check_unary Block.BlockCosPi Arithmetic.Mixed.ScaledCosPi via Functions.Unary.cosPi
check_unary Block.BlockTanPi Arithmetic.Mixed.ScaledTanPi via Functions.Unary.tanPi
check_unary Block.BlockArcSinPi Arithmetic.Mixed.ScaledArcSinPi via Functions.Unary.arcSinPi
check_unary Block.BlockArcCosPi Arithmetic.Mixed.ScaledArcCosPi via Functions.Unary.arcCosPi
check_unary Block.BlockArcTanPi Arithmetic.Mixed.ScaledArcTanPi via Functions.Unary.arcTanPi
check_unary Block.BlockSoftplus Arithmetic.Mixed.ScaledSoftplus via Functions.Unary.softplus

local macro "check_angle " blockName:ident scaledName:ident " via " piScaled:term : command =>
  `(section
    variable {length : ℕ+}
    variable {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right
        RightExact : Type}
    variable {ResultScale ResultScaleExact : Type}
    variable [ExecFloat.ExactDecoder Scale ScaleExact] [ExecFloat.ExactMap ScaleExact Rat]
    variable [ExecFloat.ExactDecoder Source SourceExact] [ExecFloat.ExactMap SourceExact Rat]
    variable [ExecFloat.ExactDecoder RightScale RightScaleExact]
      [ExecFloat.ExactMap RightScaleExact Rat]
    variable [ExecFloat.ExactDecoder Right RightExact] [ExecFloat.ExactMap RightExact Rat]
    variable [ExecFloat.ExactDecoder ResultScale ResultScaleExact]
      [ExecFloat.ExactMap ResultScaleExact Rat]
    example (format : Format) (policy : BlockPolicy length) (y : Block Scale Source length)
        (x : Block RightScale Right length) (resultScale : ResultScale)
        (lane : Fin (length : Nat)) :
        Format.SameDatum (ExecFloat.P3109.decode
          ($blockName format policy y x resultScale).values[lane.val])
          (Functions.referenceValue format (policy.at lane)
            (FunctionBlock.normalize (Arithmetic.Mixed.decode resultScale)
              (Functions.arcTan2 $piScaled (Block.decode y)[lane.val]
                (Block.decode x)[lane.val]))) :=
      Block.decode_angleFunction_lane format policy $piScaled y x resultScale lane
    example (format : Format) (yScale : Scale) (y : Source) (xScale : RightScale) (x : Right)
        (mode : RoundingMode) (saturation : SaturationMode) :
        Format.SameDatum
          (ExecFloat.P3109.decode ($scaledName format yScale y xScale x mode saturation))
          (Functions.referenceValue format { rounding := mode, saturation }
            (FunctionBlock.normalize (.finite 1) (Functions.arcTan2 $piScaled
              (Arithmetic.Multiply (Arithmetic.Mixed.decode yScale) (Arithmetic.Mixed.decode y))
              (Arithmetic.Multiply (Arithmetic.Mixed.decode xScale)
                  (Arithmetic.Mixed.decode x))))) :=
      Arithmetic.Mixed.decode_scaledAngleFunction format $piScaled yScale y xScale x mode saturation
    end)

check_angle Block.BlockArcTan2 Arithmetic.Mixed.ScaledArcTan2 via false
check_angle Block.BlockArcTan2Pi Arithmetic.Mixed.ScaledArcTan2Pi via true

example (expression : FunctionExpr) :
    (FunctionBlock.signWitness expression : ℝ) =
      if expression.toReal = 0 then 0 else if expression.toReal < 0 then -1 else 1 :=
  FunctionBlock.signWitness_eq_real expression

example (scale : Rat) (expression : FunctionExpr) (hscale : scale ≠ 0) :
    (FunctionBlock.normalize (.finite scale) (.finite expression)).map FunctionExpr.toReal =
      .finite (expression.toReal / (scale : ℝ)) :=
  FunctionBlock.normalize_finite_real scale expression hscale

example (scale : NumericalValue Rat) (category : ExceptionalValue) :
    FunctionBlock.normalize scale (.exceptional category) = .exceptional .nan :=
  FunctionBlock.normalize_exceptional scale category

example (category : ExceptionalValue) (value : NumericalValue FunctionExpr) :
    FunctionBlock.normalize (.exceptional category) value = .exceptional .nan :=
  FunctionBlock.normalize_exceptional_scale category value

example (value : NumericalValue FunctionExpr)
    (hvalue : ∀ category, value ≠ .exceptional category) :
    FunctionBlock.normalize (.finite 0) value = .finite (.rational 0) :=
  FunctionBlock.normalize_zero value hvalue

example (negative : Bool) (expression : FunctionExpr) :
    (FunctionBlock.normalize (.infinity negative) (.finite expression)).map FunctionExpr.toReal =
      .finite ((if negative then (-1 : ℝ) else 1) *
        (if expression.toReal = 0 then 0 else if expression.toReal < 0 then -1 else 1)) :=
  FunctionBlock.normalize_infinite_finite_real negative expression

example :
    (Block.BlockLog2 Format.binary8p3se {} (⟨(2 : Rat), #v[(1 / 2 : Rat), 1]⟩ :
      Block Rat Rat 2) (1 : Rat)).values[1].toNatBits =
      (ExecFloat.P3109.ofRat 1 : ExecFloat.P3109 Format.binary8p3se).toNatBits := by
  float_decide

example :
    (Arithmetic.Mixed.ScaledSinPi Format.binary8p3se (2 : Rat) (1 / 4 : Rat)).toNatBits =
      (ExecFloat.P3109.ofRat 1 : ExecFloat.P3109 Format.binary8p3se).toNatBits := by
  float_decide

end FloatLibTests.Conformance.P3109.BlockFunctions
