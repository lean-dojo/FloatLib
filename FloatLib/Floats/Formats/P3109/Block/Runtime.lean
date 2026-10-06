/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Runtime
public import Mathlib.Data.PNat.Basic

/-!
# P3109 scaled blocks

Chapter 5 of the unapproved P3109 interim report 4.0.3 defines a nonempty sequence with
one independently typed scale. Decoding multiplies exact closed rational observations;
projection normalizes each exact result before one destination projection. Zero and infinite
result scales use the special rules of §5.4.2 rather than ordinary division.

The policies retain one saturation mode and one rounding mode across a block. Stochastic
modes accept one intrinsically bounded random word per lane, all with the same bit width.
Reductions accumulate exact closed values in lane order and round only the final result.
The generic elementwise operations cover exact rational closed operations; transcendental
functions require a separate evaluator and are not installed by this module.

Reference: §§5.3–5.8 of
<https://github.com/P3109/Public/tree/34f5964d9bb2382b2665d15467fc3517b990b308>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat
open Arithmetic

/-- A nonempty block with independently typed scale and scalar elements. -/
structure Block (Scale Element : Type) (length : ℕ+) where
  /-- Shared scale, decoded through its own exact source interface. -/
  scale : Scale
  /-- Precisely the declared number of scalar element codes. -/
  values : Vector Element length

/-- A shared scalar rounding rule or explicit same-width stochastic words for every lane. -/
inductive BlockRounding (length : ℕ+) where
  | scalar (mode : RoundingMode)
  | stochasticA (width : Nat) (words : Vector (BitVec width) length)
  | stochasticB (width : Nat) (words : Vector (BitVec width) length)
  | stochasticC (width : Nat) (words : Vector (BitVec width) length)

/-- Projection attributes shared by a block, with explicit lane-specific random words. -/
structure BlockPolicy (length : ℕ+) where
  /-- Scalar rule or the report's sequence of stochastic random words. -/
  rounding : BlockRounding length := .scalar .nearestTiesToEven
  /-- One saturation rule, shared by every element projection. -/
  saturation : SaturationMode := .none

/-- Specialize the shared rounding attributes to one lane as prescribed by §5.3. -/
def BlockPolicy.at {length : ℕ+} (policy : BlockPolicy length)
    (lane : Fin (length : Nat)) : ProjectionPolicy :=
  { saturation := policy.saturation
    rounding := match policy.rounding with
      | .scalar mode => mode
      | .stochasticA width words => .stochasticA ⟨width, words[lane.val]⟩
      | .stochasticB width words => .stochasticB ⟨width, words[lane.val]⟩
      | .stochasticC width words => .stochasticC ⟨width, words[lane.val]⟩ }

namespace Block

variable {length : ℕ+}
variable {Scale ScaleExact Source SourceExact Result : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]

/-- Exact §5.4.1 decoding, including the closed rules for nonfinite scale or element codes. -/
def decode (block : Block Scale Source length) : Vector (NumericalValue Rat) length :=
  let scale := Mixed.decode block.scale
  block.values.map fun value => Arithmetic.mul scale (Mixed.decode value)

/-- Closed signum, with zero mapped to zero and either infinity to its sign. -/
def signum : NumericalValue Rat → NumericalValue Rat
  | .exceptional _ => Arithmetic.nan
  | .infinity negative => .finite (if negative then -1 else 1)
  | .finite value => .finite (if value = 0 then 0 else if value < 0 then -1 else 1)

/--
Exact §5.4.2 result normalization. NaN takes precedence over zero or infinite scales;
zero scales map other inputs to zero, and infinite scales map them to signed unit or zero.
-/
def normalize : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => Arithmetic.nan
  | .infinity negative, value => if negative then Arithmetic.neg (signum value) else signum value
  | .finite scale, value =>
      if scale = 0 then .finite 0 else Arithmetic.div value (.finite scale)

/-- Normalize exact lane results at the supplied scale, then project each lane once. -/
def project (destination : Destination Result) (policy : BlockPolicy length) (scale : Scale)
    (values : Vector (NumericalValue Rat) length) : Vector Result length :=
  let exactScale := Mixed.decode scale
  Vector.ofFn fun lane : Fin (length : Nat) =>
    destination.project (policy.at lane) (normalize exactScale values[lane.val])

/-- §5.5.1 conversion out of a block, with independent scalar destination and lane attributes. -/
def convertFrom (destination : Destination Result) (policy : BlockPolicy length)
    (block : Block Scale Source length) : Vector Result length :=
  let values := decode block
  Vector.ofFn fun lane : Fin (length : Nat) =>
    destination.project (policy.at lane) values[lane.val]

/-- §5.5.2 conversion to a block whose result scale is an explicit operand. -/
def convertTo (destination : Destination Result) (policy : BlockPolicy length)
    (values : Vector Source length) (scale : Scale) : Block Scale Result length :=
  ⟨scale, project destination policy scale (values.map Mixed.decode)⟩

/-- Maximum finite absolute value; all-NaN and all-infinite blocks follow closed extrema rules. -/
def maxAbsFinite (values : Vector (NumericalValue Rat) length) : NumericalValue Rat :=
  values.toList.foldl (fun largest value =>
    Arithmetic.maximumFinite largest (Arithmetic.abs value)) Arithmetic.nan

/-- §5.5.3 select a scale by projecting the maximum finite magnitude, then normalize every lane. -/
def convertToMaxAbsFinite (scaleDestination : Destination Scale)
    (destination : Destination Result) (scalePolicy : ProjectionPolicy)
    (policy : BlockPolicy length) (values : Vector Source length) : Block Scale Result length :=
  let exact := values.map Mixed.decode
  let scale := scaleDestination.project scalePolicy (maxAbsFinite exact)
  ⟨scale, project destination policy scale exact⟩

/-- Ordered exact closed sum, with a zero identity and no intermediate projections. -/
def sumExact (values : Vector (NumericalValue Rat) length) : NumericalValue Rat :=
  values.toList.foldl Arithmetic.add (.finite 0)

/-- Ordered exact closed product, with a one identity and no intermediate projections. -/
def productExact (values : Vector (NumericalValue Rat) length) : NumericalValue Rat :=
  values.toList.foldl Arithmetic.mul (.finite 1)

/-- §5.6.1 sum every decoded lane and project the complete sum once. -/
def reduceAdd (destination : Destination Result) (policy : ProjectionPolicy)
    (block : Block Scale Source length) : Result :=
  destination.project policy (sumExact (decode block))

/-- §5.6.1 multiply every decoded lane and project the complete product once. -/
def reduceMultiply (destination : Destination Result) (policy : ProjectionPolicy)
    (block : Block Scale Source length) : Result :=
  destination.project policy (productExact (decode block))

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- Exact §5.6.2 dot product of independently scaled blocks, including closed exceptional rules. -/
def dotExact (left : Block Scale Source length) (right : Block RightScale Right length) :
    NumericalValue Rat :=
  let leftValues := decode left
  let rightValues := decode right
  sumExact (Vector.ofFn fun lane : Fin (length : Nat) =>
    Arithmetic.mul leftValues[lane.val] rightValues[lane.val])

/-- Project a complete block dot product once; no lane product or partial sum is rounded. -/
def dotProduct (destination : Destination Result) (policy : ProjectionPolicy)
    (left : Block Scale Source length) (right : Block RightScale Right length) : Result :=
  destination.project policy (dotExact left right)

/-- §5.7 unary elementwise operation, followed by normalization at an explicit result scale. -/
def unary (destination : Destination Result) (policy : BlockPolicy length)
    (operation : NumericalValue Rat → NumericalValue Rat)
    (block : Block Scale Source length) (resultScale : RightScale) :
    Block RightScale Result length :=
  ⟨resultScale, project destination policy resultScale ((decode block).map operation)⟩

variable {ResultScale ResultScaleExact : Type}
variable [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]

/-- §5.7 binary elementwise operation on independent source scales and element formats. -/
def binary (destination : Destination Result) (policy : BlockPolicy length)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : Block Scale Source length) (right : Block RightScale Right length)
    (resultScale : ResultScale) : Block ResultScale Result length :=
  let leftValues := decode left
  let rightValues := decode right
  ⟨resultScale, project destination policy resultScale
    (Vector.ofFn fun lane : Fin (length : Nat) =>
      operation leftValues[lane.val] rightValues[lane.val])⟩

variable {ThirdScale ThirdScaleExact Third ThirdExact : Type}
variable [ExactDecoder ThirdScale ThirdScaleExact] [ExactMap ThirdScaleExact Rat]
variable [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]

/-- §5.7 ternary elementwise operation, retaining the full exact expression until projection. -/
def ternary (destination : Destination Result) (policy : BlockPolicy length)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : Block Scale Source length) (right : Block RightScale Right length)
    (third : Block ThirdScale Third length) (resultScale : ResultScale) :
    Block ResultScale Result length :=
  let leftValues := decode left
  let rightValues := decode right
  let thirdValues := decode third
  ⟨resultScale, project destination policy resultScale
    (Vector.ofFn fun lane : Fin (length : Nat) =>
      operation leftValues[lane.val] rightValues[lane.val] thirdValues[lane.val])⟩

end Block
end FloatLib.Floats.Formats.P3109
