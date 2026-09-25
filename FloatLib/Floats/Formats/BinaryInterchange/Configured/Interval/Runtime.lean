/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Activations
public import FloatLib.Numerics.Enclosure.Interval.Basic

/-!
# Intervals with configured binary endpoints

`ExecFloat.Binary.Interval` stores endpoints in the same carrier as configured scalar values.
All operations delegate to `Model.Interval`; packing and decoding change representation, not
rounding or exceptional-value behavior. The format, storage plan, and codec are unrestricted.

Arithmetic uses outward rounding and the model's whole-range fallback for unordered bounds.
`Valid` requires finite endpoints; `ValidExtended` also permits infinities. The real-enclosure
theorems and lossless-conversion proofs are in `Configured.Interval.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

/-- A closed interval stored in the configured endpoint carrier. -/
abbrev Interval {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type} :=
  Numerics.Interval (FloatLib.Floats.ExecFloat (Configured.Family format code plan))

namespace Interval

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code
local notation "Bounds" => Interval (format := format) (plan := plan) (code := code)

/-- Decode both endpoints without changing their complete encodings. -/
@[inline] def toModel (I : Bounds) : Model.Interval format :=
  ⟨Binary.toModel I.lo, Binary.toModel I.hi⟩

/-- Pack both model endpoints into the configured carrier. -/
@[inline] def ofModel (I : Model.Interval format) : Bounds :=
  ⟨Binary.ofModel I.lo, Binary.ofModel I.hi⟩

/-- Numerical membership; a NaN value or endpoint is unordered. -/
def mem (I : Bounds) (x : Value) : Prop :=
  Binary.toModel x ∈ I.toModel

/-- Membership of a configured scalar in configured bounds. -/
instance : Membership (ExecFloat (Configured.Family format code plan)) Bounds where
  mem := Interval.mem

/-- Both endpoints are finite and ordered. -/
abbrev Valid (I : Bounds) : Prop := Model.Interval.Valid I.toModel

/-- Both endpoints are non-NaN and ordered; infinities are permitted. -/
abbrev ValidExtended (I : Bounds) : Prop := Model.Interval.ValidExtended I.toModel

/-- Degenerate interval, preserving even a signed zero or NaN encoding. -/
@[inline] def point (x : Value) : Bounds := ofModel (Model.Interval.point (Binary.toModel x))

/-- Complete numerical range: infinities where supported, maximal finite endpoints otherwise. -/
@[inline] def whole : Bounds := ofModel (Model.Interval.whole format)

/-- Executable numerical comparison; unordered comparisons return `false`. -/
@[inline] def leB (x y : Value) : Bool := Model.Interval.leB (Binary.toModel x) (Binary.toModel y)

/-- Keep ordered bounds, falling back to `whole` for NaNs or reversed endpoints. -/
@[inline] def ofBounds (lo hi : Value) : Bounds :=
  ofModel (Model.Interval.ofBounds (Binary.toModel lo) (Binary.toModel hi))

/-- Test whether the numerical endpoint range contains zero. -/
@[inline] def containsZero (I : Bounds) : Bool := Model.Interval.containsZero I.toModel

/-- Endpoint hull, inheriting the model's IEEE NaN propagation. -/
@[inline] def hull (I J : Bounds) : Bounds :=
  ofModel (Model.Interval.hull I.toModel J.toModel)

/-- Outward-rounded sum, with the model's conservative fallback for indeterminate bounds. -/
@[inline] def add (I J : Bounds) : Bounds := ofModel (Model.Interval.add I.toModel J.toModel)

/-- Outward-rounded difference. -/
@[inline] def sub (I J : Bounds) : Bounds := ofModel (Model.Interval.sub I.toModel J.toModel)

/-- Outward-rounded four-corner product enclosure. -/
@[inline] def mul (I J : Bounds) : Bounds := ofModel (Model.Interval.mul I.toModel J.toModel)

/-- Outward-rounded quotient; a denominator containing zero returns the whole range. -/
@[inline] def div (I J : Bounds) : Bounds := ofModel (Model.Interval.div I.toModel J.toModel)

/-- Negate and exchange the endpoints. -/
@[inline] def neg (I : Bounds) : Bounds := ofModel (Model.Interval.neg I.toModel)

/-- Reciprocal enclosure; an interval containing zero returns the whole range. -/
@[inline] def inv (I : Bounds) : Bounds := ofModel (Model.Interval.inv I.toModel)

/-- Endpoint-grid image enclosure for `max x 0`. -/
@[inline] def relu (I : Bounds) : Bounds := ofModel (Model.Interval.relu I.toModel)

/-- Absolute-value enclosure, handling intervals crossing zero. -/
@[inline] def abs (I : Bounds) : Bounds := ofModel (Model.Interval.abs I.toModel)

/-- Directed square-root endpoints; real soundness additionally needs nonnegative input bounds. -/
@[inline] def sqrt (I : Bounds) : Bounds := ofModel (Model.Interval.sqrt I.toModel)

end Interval
end FloatLib.Floats.ExecFloat.Binary
