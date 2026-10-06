/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.Proof

/-!
# Semantics of P3109 blocks

Lane projection refines the report's exact normalization followed by destination projection.
The special scale laws include NaN precedence and zero and infinite result scales. Finite
reductions retain the complete rational sum or product without intermediate rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics FloatLib.Floats.ExecFloat Arithmetic

variable {length : ℕ+}

/-- Explicit stochastic words are specialized independently at each lane. -/
@[simp] theorem BlockPolicy.at_stochasticA (width : Nat)
    (words : Vector (BitVec width) length) (saturation : SaturationMode)
    (lane : Fin (length : Nat)) :
    (BlockPolicy.at ⟨.stochasticA width words, saturation⟩ lane).rounding =
      .stochasticA ⟨width, words[lane.val]⟩ := rfl

namespace Block

/-- Finite nonzero result scales use ordinary exact division. -/
@[simp] theorem normalize_finite (scale value : Rat) (hscale : scale ≠ 0) :
    normalize (.finite scale) (.finite value) = .finite (value / scale) := by
  simp [normalize, hscale, Arithmetic.div]

/-- NaN inputs take precedence even when the result scale is zero. -/
@[simp] theorem normalize_exceptional (scale : NumericalValue Rat) (kind : ExceptionalValue) :
    normalize scale (.exceptional kind) = Arithmetic.nan := by
  cases scale <;> rfl

/-- A non-NaN input normalized at a zero scale becomes zero, including either infinity. -/
theorem normalize_zero (value : NumericalValue Rat)
    (hvalue : ∀ kind, value ≠ .exceptional kind) :
    normalize (.finite 0) value = .finite 0 := by
  cases value <;> simp_all [normalize]

/-- Infinite scales reduce a finite input to its sign and the scale's sign. -/
@[simp] theorem normalize_infinite_finite (negative : Bool) (value : Rat) :
    normalize (.infinity negative) (.finite value) =
      .finite ((if negative then (-1 : Rat) else 1) *
        (if value = 0 then 0 else if value < 0 then -1 else 1)) := by
  cases negative <;> by_cases hzero : value = 0 <;> by_cases hneg : value < 0 <;>
    simp [normalize, signum, Arithmetic.neg, hzero, hneg]

private theorem foldl_add_finite (values : List Rat) (initial : Rat) :
    (values.map NumericalValue.finite).foldl Arithmetic.add (.finite initial) =
      .finite (values.foldl (· + ·) initial) := by
  induction values generalizing initial with
  | nil => rfl
  | cons head tail ih => simp [Arithmetic.add, ih]

private theorem foldl_mul_finite (values : List Rat) (initial : Rat) :
    (values.map NumericalValue.finite).foldl Arithmetic.mul (.finite initial) =
      .finite (values.foldl (· * ·) initial) := by
  induction values generalizing initial with
  | nil => rfl
  | cons head tail ih => simp [Arithmetic.mul, ih]

/-- Finite sum reduction is the exact rational sum with zero identity. -/
@[simp] theorem sumExact_finite (values : Vector Rat length) :
    sumExact (values.map NumericalValue.finite) =
      .finite (values.toList.foldl (· + ·) 0) := by
  unfold sumExact
  rw [Vector.toList_map]
  exact foldl_add_finite values.toList 0

/-- Finite product reduction is the exact rational product with one identity. -/
@[simp] theorem productExact_finite (values : Vector Rat length) :
    productExact (values.map NumericalValue.finite) =
      .finite (values.toList.foldl (· * ·) 1) := by
  unfold productExact
  rw [Vector.toList_map]
  exact foldl_mul_finite values.toList 1

variable {Scale ScaleExact Source SourceExact : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]

/-- Decoding a finite lane multiplies the exact source scale and element. -/
theorem decode_lane_finite (block : Block Scale Source length) (lane : Fin (length : Nat))
    (scale value : Rat) (hscale : Mixed.decode block.scale = .finite scale)
    (hvalue : Mixed.decode block.values[lane.val] = .finite value) :
    (decode block)[lane.val] = .finite (scale * value) := by
  simp [decode, hscale, hvalue, Arithmetic.mul]

/-- Every P3109 destination lane refines the exact normalized report projection. -/
theorem decode_project_lane (format : Format) (policy : BlockPolicy length) (scale : Scale)
    (values : Vector (NumericalValue Rat) length) (lane : Fin (length : Nat)) :
    Format.SameDatum
      (ExecFloat.P3109.decode (project (Destination.p3109 format) policy scale values)[lane.val])
      (format.projectRatValue (policy.at lane)
        (normalize (Mixed.decode scale) values[lane.val])) := by
  simp only [project, Vector.getElem_ofFn]
  exact ExecFloat.P3109.decode_projectRat _ _

/-- Conversion out projects the decoded scaled datum of each lane once. -/
theorem decode_convertFrom_lane (format : Format) (policy : BlockPolicy length)
    (block : Block Scale Source length) (lane : Fin (length : Nat)) :
    Format.SameDatum
      (ExecFloat.P3109.decode (convertFrom (Destination.p3109 format) policy block)[lane.val])
      (format.projectRatValue (policy.at lane) (decode block)[lane.val]) := by
  simp only [convertFrom, Vector.getElem_ofFn]
  exact ExecFloat.P3109.decode_projectRat _ _

/-- Conversion to a block copies the explicit result scale without rounding it. -/
@[simp] theorem convertTo_scale {Result : Type} (destination : Destination Result)
    (policy : BlockPolicy length) (values : Vector Source length) (scale : Scale) :
    (convertTo destination policy values scale).scale = scale := rfl

/-- P3109 sum reduction refines one projection of the complete exact sum. -/
theorem decode_reduceAdd (format : Format) (policy : ProjectionPolicy)
    (block : Block Scale Source length) :
    Format.SameDatum
      (ExecFloat.P3109.decode (reduceAdd (Destination.p3109 format) policy block))
      (format.projectRatValue policy (sumExact (decode block))) :=
  ExecFloat.P3109.decode_projectRat _ _

/-- P3109 product reduction refines one projection of the complete exact product. -/
theorem decode_reduceMultiply (format : Format) (policy : ProjectionPolicy)
    (block : Block Scale Source length) :
    Format.SameDatum
      (ExecFloat.P3109.decode (reduceMultiply (Destination.p3109 format) policy block))
      (format.projectRatValue policy (productExact (decode block))) :=
  ExecFloat.P3109.decode_projectRat _ _

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- Finite block dots retain the rational sum of all products with independently decoded scales. -/
theorem dotExact_finite (left : Block Scale Source length) (right : Block RightScale Right length)
    (x y : Vector Rat length) (hx : decode left = x.map NumericalValue.finite)
    (hy : decode right = y.map NumericalValue.finite) :
    dotExact left right = .finite
      ((Vector.ofFn fun lane : Fin (length : Nat) => x[lane.val] * y[lane.val]).toList.foldl
        (· + ·) 0) := by
  unfold dotExact
  rw [hx, hy]
  dsimp only
  have heq : (Vector.ofFn fun lane : Fin (length : Nat) =>
      Arithmetic.mul (x.map NumericalValue.finite)[lane.val]
        (y.map NumericalValue.finite)[lane.val]) =
      (Vector.ofFn fun lane : Fin (length : Nat) => x[lane.val] * y[lane.val]).map
        NumericalValue.finite := by
    ext lane hlane
    simp [Arithmetic.mul]
  rw [heq, sumExact_finite]

/-- Independently scaled block dots refine one projection of the complete exact dot. -/
theorem decode_dotProduct (format : Format) (policy : ProjectionPolicy)
    (left : Block Scale Source length) (right : Block RightScale Right length) :
    Format.SameDatum
      (ExecFloat.P3109.decode (dotProduct (Destination.p3109 format) policy left right))
      (format.projectRatValue policy (dotExact left right)) :=
  ExecFloat.P3109.decode_projectRat _ _

end Block
end FloatLib.Floats.Formats.P3109
