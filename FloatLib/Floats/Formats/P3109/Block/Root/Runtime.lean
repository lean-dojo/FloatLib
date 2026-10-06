/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime

/-!
# P3109 block square roots and norms

Normalize the exact root at the result scale before rounding. A finite nonzero scale `s`
turns `sqrt(q) / s` into the signed root of `q / s²`. Exact square comparisons then perform
one destination rounding, including negative scales and lane-specific stochastic words.
The zero, infinite, and NaN scale rules are the same rules as ordinary block projection.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics FloatLib.Floats.ExecFloat Arithmetic

/-- An exact signed root of a closed rational radicand, before destination rounding. -/
structure BlockRoot where
  /-- Sign of the result after normalization at a possibly negative scale. -/
  negative : Bool := false
  /-- Squared magnitude; negative finite radicands are rejected by square-root rounding. -/
  radicand : NumericalValue Rat
  deriving DecidableEq, Repr

namespace BlockRoot

/-- Normalize an exact square root under the special scale rules of §5.4.2. -/
def normalize (scale radicand : NumericalValue Rat) : BlockRoot :=
  match scale, radicand with
  | .exceptional _, _ | _, .exceptional _ | _, .infinity true => ⟨false, Arithmetic.nan⟩
  | _, .finite value =>
      if value < 0 then ⟨false, Arithmetic.nan⟩
      else match scale with
        | .exceptional _ => ⟨false, Arithmetic.nan⟩
        | .infinity negative => ⟨negative, .finite (if value = 0 then 0 else 1)⟩
        | .finite scale =>
            if scale = 0 then ⟨false, .finite 0⟩
            else ⟨decide (scale < 0), .finite (value / (scale * scale))⟩
  | .infinity negative, .infinity false => ⟨negative, .finite 1⟩
  | .finite scale, .infinity false =>
      if scale = 0 then ⟨false, .finite 0⟩
      else ⟨decide (scale < 0), .infinity false⟩

/-- Directed rounding of a negative root reverses the direction on its positive magnitude. -/
def magnitudeMode (negative : Bool) : RoundingMode → RoundingMode
  | .towardPositive => if negative then .towardNegative else .towardPositive
  | .towardNegative => if negative then .towardPositive else .towardNegative
  | mode => mode

/-- Apply a root's sign after magnitude rounding, retaining the closed exceptional rules. -/
def applySign (negative : Bool) : NumericalValue Numerics.Dyadic →
    NumericalValue Numerics.Dyadic
  | .finite value => .finite (if negative then value.neg else value)
  | .infinity sign => .infinity (negative != sign)
  | .exceptional _ => .exceptional .nan

/-- One exact square-comparison precision rounding of the normalized signed root. -/
def rounded (format : Format) (mode : RoundingMode) (root : BlockRoot) :
    NumericalValue Numerics.Dyadic :=
  applySign root.negative
    (Arithmetic.sqrtRounded format (magnitudeMode root.negative mode) root.radicand)

/-- Saturation follows signed precision rounding and uses the original requested direction. -/
def value (format : Format) (policy : ProjectionPolicy) (root : BlockRoot) :
    NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding (rounded format policy.rounding root)

/-- Encode a normalized root after its single precision rounding and saturation. -/
def project (format : Format) (policy : ProjectionPolicy) (root : BlockRoot) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofCode (BitVec.ofNat format.bitWidth
    (Format.Internal.encodeDatumNat format (value format policy root)))

end BlockRoot

namespace Block

variable {length : ℕ+}
variable {Scale ScaleExact Source SourceExact ResultScale ResultScaleExact : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
variable [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]

/-- Project exact root radicands at a shared result scale, with independent lane rounding words. -/
def projectRoots (format : Format) (policy : BlockPolicy length) (scale : ResultScale)
    (radicands : Vector (NumericalValue Rat) length) :
    Block ResultScale (ExecFloat.P3109 format) length :=
  let exactScale := Mixed.decode scale
  ⟨scale, Vector.ofFn fun lane : Fin (length : Nat) =>
    BlockRoot.project format (policy.at lane)
      (BlockRoot.normalize exactScale radicands[lane.val])⟩

/-- Elementwise square root, normalized before the single final destination rounding. -/
def sqrt (format : Format) (policy : BlockPolicy length)
    (block : Block Scale Source length) (resultScale : ResultScale) :
    Block ResultScale (ExecFloat.P3109 format) length :=
  projectRoots format policy resultScale (decode block)

/-- Elementwise reciprocal square root with the report's nonpositive-domain rule. -/
def rsqrt (format : Format) (policy : BlockPolicy length)
    (block : Block Scale Source length) (resultScale : ResultScale) :
    Block ResultScale (ExecFloat.P3109 format) length :=
  projectRoots format policy resultScale ((decode block).map Arithmetic.rsqrtRadicand)

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- Elementwise hypotenuse of independently scaled sources, retaining the exact sum of squares. -/
def hypot (format : Format) (policy : BlockPolicy length)
    (left : Block Scale Source length) (right : Block RightScale Right length)
    (resultScale : ResultScale) : Block ResultScale (ExecFloat.P3109 format) length :=
  let leftValues := decode left
  let rightValues := decode right
  projectRoots format policy resultScale
    (Vector.ofFn fun lane : Fin (length : Nat) =>
      Arithmetic.hypotRadicand leftValues[lane.val] rightValues[lane.val])

end Block
end FloatLib.Floats.Formats.P3109
