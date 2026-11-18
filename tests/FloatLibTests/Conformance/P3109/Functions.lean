/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Functions.Proof
public import FloatLib.Floats.Formats.P3109.Functions.Domain
public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLib.Tactic.FloatDecide

/-!
# P3109 function proof clients and exact boundary regressions

P3109 interim report v4.1 §§4.10.9–4.10.13 and §§4.10.15–4.10.16, unapproved draft.
The proof clients quantify over independent descriptors and all policies.
Closed kernel cases exercise exact function values and exceptional branches.
-/

@[expose] public section

namespace FloatLibTests.Conformance.P3109.Functions

open FloatLib.Numerics FloatLib.Floats
open Formats.P3109 ExecFloat.P3109

local macro "check_unary " operation:ident " via " selection:term
    " using " proof:ident : command =>
  `(example {format : Format} (input : ExecFloat.P3109 format)
        (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
        Format.SameDatum (decode ($operation input target mode saturation))
          (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
            (Formats.P3109.Functions.unary $selection input.toClosedRat)) :=
      $proof input target mode saturation)

check_unary Log via Formats.P3109.Functions.Unary.log using decode_Log
check_unary Log2 via Formats.P3109.Functions.Unary.log2 using decode_Log2
check_unary LogOnePlus via Formats.P3109.Functions.Unary.logOnePlus using decode_LogOnePlus
check_unary Exp via Formats.P3109.Functions.Unary.exp using decode_Exp
check_unary Exp2 via Formats.P3109.Functions.Unary.exp2 using decode_Exp2
check_unary ExpMinusOne via Formats.P3109.Functions.Unary.expMinusOne using decode_ExpMinusOne
check_unary Sin via Formats.P3109.Functions.Unary.sin using decode_Sin
check_unary Cos via Formats.P3109.Functions.Unary.cos using decode_Cos
check_unary Tan via Formats.P3109.Functions.Unary.tan using decode_Tan
check_unary ArcSin via Formats.P3109.Functions.Unary.arcSin using decode_ArcSin
check_unary ArcCos via Formats.P3109.Functions.Unary.arcCos using decode_ArcCos
check_unary ArcTan via Formats.P3109.Functions.Unary.arcTan using decode_ArcTan
check_unary Sinh via Formats.P3109.Functions.Unary.sinh using decode_Sinh
check_unary Cosh via Formats.P3109.Functions.Unary.cosh using decode_Cosh
check_unary Tanh via Formats.P3109.Functions.Unary.tanh using decode_Tanh
check_unary ArcSinh via Formats.P3109.Functions.Unary.arcSinh using decode_ArcSinh
check_unary ArcCosh via Formats.P3109.Functions.Unary.arcCosh using decode_ArcCosh
check_unary ArcTanh via Formats.P3109.Functions.Unary.arcTanh using decode_ArcTanh
check_unary SinPi via Formats.P3109.Functions.Unary.sinPi using decode_SinPi
check_unary CosPi via Formats.P3109.Functions.Unary.cosPi using decode_CosPi
check_unary TanPi via Formats.P3109.Functions.Unary.tanPi using decode_TanPi
check_unary ArcSinPi via Formats.P3109.Functions.Unary.arcSinPi using decode_ArcSinPi
check_unary ArcCosPi via Formats.P3109.Functions.Unary.arcCosPi using decode_ArcCosPi
check_unary ArcTanPi via Formats.P3109.Functions.Unary.arcTanPi using decode_ArcTanPi
check_unary Softplus via Formats.P3109.Functions.Unary.softplus using decode_Softplus

example {yFormat xFormat : Format}
    (y : ExecFloat.P3109 yFormat) (x : ExecFloat.P3109 xFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (ArcTan2 y x target mode saturation))
      (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
        (Formats.P3109.Functions.arcTan2 false y.toClosedRat x.toClosedRat)) :=
  decode_ArcTan2 y x target mode saturation

example {yFormat xFormat : Format}
    (y : ExecFloat.P3109 yFormat) (x : ExecFloat.P3109 xFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (ArcTan2Pi y x target mode saturation))
      (Formats.P3109.Functions.referenceValue target { rounding := mode, saturation }
        (Formats.P3109.Functions.arcTan2 true y.toClosedRat x.toClosedRat)) :=
  decode_ArcTan2Pi y x target mode saturation

example (format : Format) (target : ℝ) (hzero : 0 ≤ target)
    (hinterior : ComparisonRounding.referenceLower format target < format.maxFiniteBits + 1) :
    ((format.decodePositiveFinite (ComparisonRounding.referenceLower format target)).toRat : ℝ) ≤
      target ∧ target <
      ((format.decodePositiveFinite
        (ComparisonRounding.referenceLower format target + 1)).toRat : ℝ) :=
  ComparisonRounding.referenceLower_bracket format target hzero hinterior

example (argument : Rat) (h : Real.cos ((argument : ℝ) * Real.pi) = 0) :
    Formats.P3109.Functions.finiteUnary .tanPi argument =
      .infinity (decide (Real.sin ((argument : ℝ) * Real.pi) < 0)) :=
  Formats.P3109.Functions.finiteUnary_tanPi_of_cos_eq_zero argument h

example (argument : Rat) (h : Real.cos ((argument : ℝ) * Real.pi) ≠ 0) :
    Formats.P3109.Functions.finiteUnary .tanPi argument = .finite (.tanPi argument) :=
  Formats.P3109.Functions.finiteUnary_tanPi_of_cos_ne_zero argument h

example (piScaled : Bool) (multiple : Rat) :
    (Formats.P3109.Functions.angle piScaled multiple).toReal =
      if piScaled then (multiple : ℝ) else (multiple : ℝ) * Real.pi :=
  Formats.P3109.Functions.toReal_angle piScaled multiple

example (baseTwo : Bool) :
    Formats.P3109.Functions.logarithm baseTwo 0 = .infinity true :=
  Formats.P3109.Functions.logarithm_zero baseTwo

example (baseTwo : Bool) (x : Rat) (h : x < 0) :
    Formats.P3109.Functions.logarithm baseTwo x = .exceptional (.nan) :=
  Formats.P3109.Functions.logarithm_of_neg baseTwo x h

example (negative : Bool) :
    Formats.P3109.Functions.finiteUnary .arcTanh (if negative then -1 else 1) =
      .infinity negative :=
  Formats.P3109.Functions.finiteUnary_arcTanh_endpoint negative

example (operation : Formats.P3109.Functions.Unary) (category : ExceptionalValue) :
    Formats.P3109.Functions.unary operation (.exceptional category) = .exceptional (.nan) :=
  Formats.P3109.Functions.unary_exceptional operation category

example (scaled : Bool) :
    Formats.P3109.Functions.arcTan2 scaled (.finite 0) (.finite 0) = .exceptional (.nan) :=
  Formats.P3109.Functions.arcTan2_origin scaled

example (scaled yNegative xNegative : Bool) :
    Formats.P3109.Functions.arcTan2 scaled (.infinity yNegative) (.infinity xNegative) =
      .exceptional (.nan) :=
  Formats.P3109.Functions.arcTan2_infinities scaled yNegative xNegative

private abbrev F := Format.binary8p4se

example :
    (Exp (0 : ExecFloat.P3109 F)).toNatBits = (1 : ExecFloat.P3109 F).toNatBits ∧
    (ExpMinusOne (0 : ExecFloat.P3109 F)).toNatBits = 0 ∧
    (Log (1 : ExecFloat.P3109 F)).toNatBits = 0 ∧
    (Log2 (2 : ExecFloat.P3109 F)).toNatBits = (1 : ExecFloat.P3109 F).toNatBits := by
  float_decide

example :
    (TanPi (ofRat (1 / 2) : ExecFloat.P3109 F)).toNatBits = 127 ∧
    (TanPi (ofRat (-1 / 2) : ExecFloat.P3109 F)).toNatBits = 255 ∧
    (ArcTanh (1 : ExecFloat.P3109 F)).toNatBits = 127 ∧
    (ArcTan2 (0 : ExecFloat.P3109 F) (0 : ExecFloat.P3109 F)).toNatBits = 128 := by
  float_decide

example :
    (SinPi (1 : ExecFloat.P3109 F)).toNatBits = 0 ∧
    (CosPi (0 : ExecFloat.P3109 F)).toNatBits = (1 : ExecFloat.P3109 F).toNatBits ∧
    (ArcTan2Pi (1 : ExecFloat.P3109 F) (1 : ExecFloat.P3109 F)).toNatBits =
      (ofRat (1 / 4) : ExecFloat.P3109 F).toNatBits := by
  float_decide

end FloatLibTests.Conformance.P3109.Functions
