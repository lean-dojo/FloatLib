/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.Codebook.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Codebook.Catalog.Proof
public import FloatLib.Floats.Formats.Codebook.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Configured catalog-codebook operations

Named codebooks expose only the arithmetic justified by their complete denotation. The bipolar
table has total negation and multiplication; the ternary table uses checked operations because
one word is reserved.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Codebook.Catalog

namespace bipolar1

/-- Configured one-bit `{-1, +1}` lookup encoding. -/
abbrev Value := ExecFloat.Codebook Formats.Codebook.Catalog.bipolar1

/-- Construct the bipolar value negative one without exposing its stored bit. -/
@[inline] def negativeOne : Value :=
  ofCode (BitVec.ofNat 1 0)

/-- Construct the bipolar value positive one without exposing its stored bit. -/
@[inline] def positiveOne : Value :=
  ofCode (BitVec.ofNat 1 1)

/-- The named negative bipolar value has exact integer meaning `-1`. -/
@[simp, grind =] theorem decode_negativeOne :
    ExecFloat.Codebook.decode negativeOne = .finite (-1) :=
  Formats.Codebook.Catalog.bipolar1_denote_zero

/-- The named positive bipolar value has exact integer meaning `1`. -/
@[simp, grind =] theorem decode_positiveOne :
    ExecFloat.Codebook.decode positiveOne = .finite 1 :=
  Formats.Codebook.Catalog.bipolar1_denote_one

/-- Exact additive inverse of a configured bipolar value. -/
@[inline] def neg (value : Value) : Value :=
  ofCode (Formats.Codebook.Catalog.bipolar1.neg value.toCode)

/-- Exact multiplication of configured bipolar values. -/
@[inline] def mul (left right : Value) : Value :=
  ofCode (Formats.Codebook.Catalog.bipolar1.mul left.toCode right.toCode)

instance : Neg Value where
  neg := neg

namespace Plan

/-- Planner estimate for exact one-bit bipolar multiplication. -/
def mulEstimate : Backend.Candidate where
  name := "one-bit bipolar multiplication"
  kind := .custom "direct codebook bit kernel" 0
  storage := .byte
  steadyCost := 1

/-- Certified bipolar multiplication candidate used by common `ExecFloat` dispatch. -/
def mulCertified : Backend.Certified bipolar1.mul :=
  Backend.Certified.reference mulEstimate bipolar1.mul

end Plan

/-- The proved bipolar multiplication kernel participates in common `ExecFloat` dispatch. -/
@[always_inline] instance
    [planning : Backend.PolicyFor
      (Codebook.Family Formats.Codebook.Catalog.bipolar1)] :
    ExecFloat.Mul (Codebook.Family Formats.Codebook.Catalog.bipolar1) :=
  ExecFloat.Capability.ofDirectKernel
    .mul bipolar1.mul Plan.mulCertified bipolar1.mul rfl

end bipolar1

namespace ternary2

/-- Configured two-bit `{0, +1, -1, reserved}` lookup encoding. -/
abbrev Value := ExecFloat.Codebook Formats.Codebook.Catalog.ternary2

/-- Construct the ternary codebook's zero without exposing its stored word. -/
@[inline] def zero : Value :=
  ofCode (BitVec.ofNat 2 0)

/-- Construct the ternary codebook's positive one without exposing its stored word. -/
@[inline] def positiveOne : Value :=
  ofCode (BitVec.ofNat 2 1)

/-- Construct the ternary codebook's negative one without exposing its stored word. -/
@[inline] def negativeOne : Value :=
  ofCode (BitVec.ofNat 2 2)

/-- Construct the ternary codebook's reserved exceptional value. -/
@[inline] def reserved : Value :=
  ofCode (BitVec.ofNat 2 3)

/-- The named ternary zero has exact integer meaning `0`. -/
@[simp, grind =] theorem decode_zero :
    ExecFloat.Codebook.decode zero = .finite 0 :=
  Formats.Codebook.Catalog.ternary2_denote_zero

/-- The named positive ternary value has exact integer meaning `1`. -/
@[simp, grind =] theorem decode_positiveOne :
    ExecFloat.Codebook.decode positiveOne = .finite 1 :=
  Formats.Codebook.Catalog.ternary2_denote_positive

/-- The named negative ternary value has exact integer meaning `-1`. -/
@[simp, grind =] theorem decode_negativeOne :
    ExecFloat.Codebook.decode negativeOne = .finite (-1) :=
  Formats.Codebook.Catalog.ternary2_denote_negative

/-- The named reserved ternary value denotes the catalog's exceptional observation. -/
@[simp, grind =] theorem decode_reserved :
    ExecFloat.Codebook.decode reserved = .exceptional (.reserved (some 3)) :=
  Formats.Codebook.Catalog.ternary2_denote_reserved

/-- Exact negation, returning `none` for the reserved word. -/
@[inline] def neg? (value : Value) : Option Value :=
  (Formats.Codebook.Catalog.ternary2.neg? value.toCode).map ofCode

/-- Exact multiplication, returning `none` if either operand is the reserved word. -/
@[inline] def mul? (left right : Value) : Option Value :=
  (Formats.Codebook.Catalog.ternary2.mul? left.toCode right.toCode).map ofCode

end ternary2
end FloatLib.Floats.ExecFloat.Codebook.Catalog
