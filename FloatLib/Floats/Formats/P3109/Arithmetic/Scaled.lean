/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.CompilerOptimize
public import FloatLib.Tactic.KernelOptimize

public import FloatLib.Floats.Formats.P3109.Block.Operations
public meta import FloatLib.Tactic.P3109Scaled

/-!
# P3109 scaled operations

The unapproved P3109 interim report v4.1 (14 September 2026), §5.8, defines
`ScaledOp` as its one-lane block operation with output scale one. Input scales
and elements have independent exact decoders. Exact closed operations use the
same three arity schemas as mixed arithmetic. Roots use the block root evaluator
at length one, preserving its domain and exceptional-scale rules.

The generic projection equations concern any closed operation. The correspondence
with explicit division by result scale one additionally requires a canonical
result; that premise excludes extra exceptional metadata absent from P3109.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

open FloatLib.Numerics FloatLib.Floats.ExecFloat

variable {Scale ScaleExact Source SourceExact Result : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]

/-- P3109 interim report v4.1, §5.8: apply an exact unary operation to a scaled operand, then
    project once. -/
@[inline] def scaledUnary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat) (scale : Scale) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation }
    (operation (Arithmetic.Multiply (decode scale) (decode value)))

variable {RightScale RightScaleExact Right RightExact ThirdScale ThirdScaleExact
  Third ThirdExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
variable [ExactDecoder ThirdScale ThirdScaleExact] [ExactMap ThirdScaleExact Rat]
variable [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]

/-- P3109 interim report v4.1, §5.8: retain all three exact scaled operands until the sole
    output projection. -/
@[inline] def scaledTernary (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (scale : Scale) (value : Source) (rightScale : RightScale) (right : Right)
    (thirdScale : ThirdScale) (third : Third)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
  destination.project { rounding := mode, saturation }
    (operation (Arithmetic.Multiply (decode scale) (decode value))
      (Arithmetic.Multiply (decode rightScale) (decode right))
      (Arithmetic.Multiply (decode thirdScale) (decode third)))

/-- Every scaled unary instance refines the descriptor's one final report projection (§5.8). -/
theorem decode_scaledUnary (format : Format)
    (operation : NumericalValue Rat → NumericalValue Rat) (scale : Scale) (value : Source)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (scaledUnary (Destination.p3109 format) operation scale value mode saturation))
      (format.projectRatValue { rounding := mode, saturation }
        (operation (Arithmetic.Multiply (decode scale) (decode value)))) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- Every scaled ternary instance refines the descriptor's one final report projection (§5.8). -/
theorem decode_scaledTernary (format : Format)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (scale : Scale) (value : Source) (rightScale : RightScale) (right : Right)
    (thirdScale : ThirdScale) (third : Third)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode (scaledTernary (Destination.p3109 format) operation
        scale value rightScale right thirdScale third mode saturation))
      (format.projectRatValue { rounding := mode, saturation }
        (operation (Arithmetic.Multiply (decode scale) (decode value))
          (Arithmetic.Multiply (decode rightScale) (decode right))
          (Arithmetic.Multiply (decode thirdScale) (decode third)))) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- Canonical unary results equal explicit normalization at result scale one (§5.8). -/
theorem scaledUnary_eq_project_div_one (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat)
    (hcanonical : ∀ value, canonical (operation value) = operation value)
    (scale : Scale) (value : Source) (mode : RoundingMode) (saturation : SaturationMode) :
    scaledUnary destination operation scale value mode saturation =
      destination.project { rounding := mode, saturation }
        (Arithmetic.Divide (operation (Arithmetic.Multiply (decode scale) (decode value)))
          (.finite 1)) := by
  rw [div_one, hcanonical]
  rfl

/-- Canonical ternary results equal explicit normalization at result scale one (§5.8). -/
theorem scaledTernary_eq_project_div_one (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (hcanonical : ∀ x y z, canonical (operation x y z) = operation x y z)
    (scale : Scale) (value : Source) (rightScale : RightScale) (right : Right)
    (thirdScale : ThirdScale) (third : Third)
    (mode : RoundingMode) (saturation : SaturationMode) :
    scaledTernary destination operation scale value rightScale right thirdScale third
        mode saturation =
      destination.project { rounding := mode, saturation }
        (Arithmetic.Divide
          (operation (Arithmetic.Multiply (decode scale) (decode value))
            (Arithmetic.Multiply (decode rightScale) (decode right))
            (Arithmetic.Multiply (decode thirdScale) (decode third))) (.finite 1)) := by
  rw [div_one, hcanonical]
  rfl


/-- P3109 interim report v4.1, §5.8: project one exact scaled datum into the chosen destination. -/
scaled_unary ScaledConvert := id
/-- P3109 interim report v4.1, §5.8 with §4.10.1: project the absolute value of one exact scaled
    datum. -/
scaled_unary ScaledAbs := Arithmetic.Abs
/-- P3109 interim report v4.1, §5.8 with §4.10.1: project the negation of one exact scaled datum. -/
scaled_unary ScaledNegate := Arithmetic.Negate
/-- P3109 interim report v4.1, §5.8 with §4.10.8: reciprocal of one exact scaled datum, with
    zero mapped to NaN. -/
scaled_unary ScaledRecip := Arithmetic.Recip

/-- P3109 interim report v4.1, §5.8 with §4.10.2: copy the sign between exact scaled data. -/
scaled_binary ScaledCopySign := Arithmetic.CopySign
/-- P3109 interim report v4.1, §5.8 with §4.10.5: divide exact scaled operands before projection. -/
scaled_binary ScaledDivide := Arithmetic.Divide
/-- P3109 interim report v4.1, §5.8 with §4.11: minimum of exact scaled operands, propagating
    NaN. -/
scaled_binary ScaledMinimum := Arithmetic.Minimum
/-- P3109 interim report v4.1, §5.8 with §4.11: maximum of exact scaled operands, propagating
    NaN. -/
scaled_binary ScaledMaximum := Arithmetic.Maximum
/-- P3109 interim report v4.1, §5.8 with §4.11: minimum of exact scaled operands, preferring
    non-NaN. -/
scaled_binary ScaledMinimumNumber := Arithmetic.MinimumNumber
/-- P3109 interim report v4.1, §5.8 with §4.11: maximum of exact scaled operands, preferring
    non-NaN. -/
scaled_binary ScaledMaximumNumber := Arithmetic.MaximumNumber
/-- P3109 interim report v4.1, §5.8 with §4.11: minimum by magnitude of exact scaled operands. -/
scaled_binary ScaledMinimumMagnitude := Arithmetic.MinimumMagnitude
/-- P3109 interim report v4.1, §5.8 with §4.11: maximum by magnitude of exact scaled operands. -/
scaled_binary ScaledMaximumMagnitude := Arithmetic.MaximumMagnitude
/-- P3109 interim report v4.1, §5.8 with §4.11: minimum by magnitude of exact scaled operands,
    preferring non-NaN. -/
scaled_binary ScaledMinimumMagnitudeNumber := Arithmetic.MinimumMagnitudeNumber
/-- P3109 interim report v4.1, §5.8 with §4.11: maximum by magnitude of exact scaled operands,
    preferring non-NaN. -/
scaled_binary ScaledMaximumMagnitudeNumber := Arithmetic.MaximumMagnitudeNumber
/-- P3109 interim report v4.1, §5.8 with §4.11: minimum of exact scaled operands, preferring
    finite values. -/
scaled_binary ScaledMinimumFinite := Arithmetic.MinimumFinite
/-- P3109 interim report v4.1, §5.8 with §4.11: maximum of exact scaled operands, preferring
    finite values. -/
scaled_binary ScaledMaximumFinite := Arithmetic.MaximumFinite

/-- P3109 interim report v4.1, §5.8 with §4.10.6: fused scaled multiply-add with one final
    projection. -/
scaled_ternary ScaledFMA := Arithmetic.FMA
/-- P3109 interim report v4.1, §5.8 with §4.10.7: fused scaled add-add with one final projection. -/
scaled_ternary ScaledFAA := Arithmetic.FAA
/-- P3109 interim report v4.1, §5.8 with §4.11: clamp exact scaled data before projection. -/
scaled_ternary ScaledClamp := Arithmetic.Clamp

/-- P3109 interim report v4.1, §5.8 with §4.10.8: the one-lane block square root at exact result
    scale one. -/
def ScaledSqrt (format : Format) (scale : Scale) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 format :=
  (Block.BlockSqrt format (length := 1) ⟨.scalar mode, saturation⟩
    ⟨scale, #v[value]⟩ (1 : Rat)).values[0]

/-- P3109 interim report v4.1, §5.8 with §4.10.8: the one-lane reciprocal block root at result
    scale one. -/
def ScaledRSqrt (format : Format) (scale : Scale) (value : Source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 format :=
  (Block.BlockRSqrt format (length := 1) ⟨.scalar mode, saturation⟩
    ⟨scale, #v[value]⟩ (1 : Rat)).values[0]

/-- P3109 interim report v4.1, §5.8 with §4.10.14: the one-lane block hypotenuse at exact result
    scale one. -/
def ScaledHypot (format : Format) (scale : Scale) (value : Source)
    (rightScale : RightScale) (right : Right)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 format :=
  (Block.BlockHypot format (length := 1) ⟨.scalar mode, saturation⟩
    ⟨scale, #v[value]⟩ ⟨rightScale, #v[right]⟩ (1 : Rat)).values[0]

end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

/-!
# Reference execution paths for P3109 block operations

Each named operation of P3109 interim report v4.1 (unapproved, 14 September 2026), §§5.5–5.8,
has a compiled certificate for its complete polymorphic function. The certificate
executes the specification itself, so its equality is reflexive and covers all
source types, descriptors, block lengths, projection policies and destinations.

For kernel evaluation the named operations and shared arity schemas are
registered for unfolding. Unfolding is definitional equality; registration checks
the entire definition's trust surface. These are reference paths, with no claimed
speedup. The candidate estimate is descriptive planner metadata, not a timing.
-/

namespace FloatLib.Floats.Formats.P3109

attribute [compiler_optimize reference] Block.ConvertFromBlock
attribute [compiler_optimize reference] Block.ConvertToBlock
attribute [compiler_optimize reference] Block.ConvertToBlockMaxAbsFinite
attribute [compiler_optimize reference] Block.BlockReduceAdd
attribute [compiler_optimize reference] Block.BlockReduceMultiply
attribute [compiler_optimize reference] Block.BlockDotProduct
attribute [compiler_optimize reference] Block.BlockConvert
attribute [compiler_optimize reference] Block.BlockAbs
attribute [compiler_optimize reference] Block.BlockNegate
attribute [compiler_optimize reference] Block.BlockRecip
attribute [compiler_optimize reference] Block.BlockSqrt
attribute [compiler_optimize reference] Block.BlockRSqrt
attribute [compiler_optimize reference] Block.BlockHypot
attribute [compiler_optimize reference] Block.BlockCopySign
attribute [compiler_optimize reference] Block.BlockAdd
attribute [compiler_optimize reference] Block.BlockSubtract
attribute [compiler_optimize reference] Block.BlockMultiply
attribute [compiler_optimize reference] Block.BlockDivide
attribute [compiler_optimize reference] Block.BlockMinimum
attribute [compiler_optimize reference] Block.BlockMaximum
attribute [compiler_optimize reference] Block.BlockMinimumNumber
attribute [compiler_optimize reference] Block.BlockMaximumNumber
attribute [compiler_optimize reference] Block.BlockMinimumMagnitude
attribute [compiler_optimize reference] Block.BlockMaximumMagnitude
attribute [compiler_optimize reference] Block.BlockMinimumMagnitudeNumber
attribute [compiler_optimize reference] Block.BlockMaximumMagnitudeNumber
attribute [compiler_optimize reference] Block.BlockMinimumFinite
attribute [compiler_optimize reference] Block.BlockMaximumFinite
attribute [compiler_optimize reference] Block.BlockFMA
attribute [compiler_optimize reference] Block.BlockFAA
attribute [compiler_optimize reference] Block.BlockClamp

attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledConvert
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledAbs
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledNegate
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledRecip
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledSqrt
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledRSqrt
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledHypot
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledCopySign
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledAdd
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledSubtract
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMultiply
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledDivide
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMinimum
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMaximum
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMinimumNumber
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMaximumNumber
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMinimumMagnitude
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMaximumMagnitude
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMinimumMagnitudeNumber
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMaximumMagnitudeNumber
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMinimumFinite
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledMaximumFinite
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledFMA
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledFAA
attribute [compiler_optimize reference] Arithmetic.Mixed.ScaledClamp

attribute [kernel_optimize unfold]
  Block.ConvertFromBlock Block.ConvertToBlock Block.ConvertToBlockMaxAbsFinite
  Block.BlockReduceAdd Block.BlockReduceMultiply Block.BlockDotProduct
  Block.BlockConvert Block.BlockAbs Block.BlockNegate Block.BlockRecip
  Block.BlockSqrt Block.BlockRSqrt Block.BlockHypot Block.BlockCopySign
  Block.BlockAdd Block.BlockSubtract Block.BlockMultiply Block.BlockDivide
  Block.BlockMinimum Block.BlockMaximum Block.BlockMinimumNumber Block.BlockMaximumNumber
  Block.BlockMinimumMagnitude Block.BlockMaximumMagnitude
  Block.BlockMinimumMagnitudeNumber Block.BlockMaximumMagnitudeNumber
  Block.BlockMinimumFinite Block.BlockMaximumFinite Block.BlockFMA Block.BlockFAA Block.BlockClamp
  Block.unary Block.binary Block.ternary Block.project Block.projectRoots
  Arithmetic.Mixed.ScaledConvert Arithmetic.Mixed.ScaledAbs Arithmetic.Mixed.ScaledNegate
  Arithmetic.Mixed.ScaledRecip Arithmetic.Mixed.ScaledSqrt Arithmetic.Mixed.ScaledRSqrt
  Arithmetic.Mixed.ScaledHypot Arithmetic.Mixed.ScaledCopySign
  Arithmetic.Mixed.ScaledAdd Arithmetic.Mixed.ScaledSubtract Arithmetic.Mixed.ScaledMultiply
  Arithmetic.Mixed.ScaledDivide Arithmetic.Mixed.ScaledMinimum Arithmetic.Mixed.ScaledMaximum
  Arithmetic.Mixed.ScaledMinimumNumber Arithmetic.Mixed.ScaledMaximumNumber
  Arithmetic.Mixed.ScaledMinimumMagnitude Arithmetic.Mixed.ScaledMaximumMagnitude
  Arithmetic.Mixed.ScaledMinimumMagnitudeNumber Arithmetic.Mixed.ScaledMaximumMagnitudeNumber
  Arithmetic.Mixed.ScaledMinimumFinite Arithmetic.Mixed.ScaledMaximumFinite
  Arithmetic.Mixed.ScaledFMA Arithmetic.Mixed.ScaledFAA Arithmetic.Mixed.ScaledClamp
  Arithmetic.Mixed.scaledUnary Arithmetic.Mixed.scaledBinary Arithmetic.Mixed.scaledTernary

end FloatLib.Floats.Formats.P3109
