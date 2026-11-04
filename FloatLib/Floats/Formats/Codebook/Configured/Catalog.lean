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
import FloatLib.Floats.Formats.Codebook.Arithmetic.Proof

/-!
# Configured catalog-codebook operations

A named codebook gets only the arithmetic its complete denotation justifies. Every bipolar word is
`-1` or `+1`, so negation and multiplication are total there. The ternary table has a reserved
word, which makes its operations checked: they can reject an operand. On configured values, the
`decode_*` theorems give the exact integer meaning of each operation, building on the table-level
refinements in `Codebook.Arithmetic.Proof`.
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

/-- Exact additive inverse of a configured bipolar value `value` (`decode_neg`). -/
@[inline] def neg (value : Value) : Value :=
  ofCode (Formats.Codebook.Catalog.bipolar1.neg value.toCode)

/-- Exact product of configured bipolar values `left` and `right` (`decode_mul`). -/
@[inline] def mul (left right : Value) : Value :=
  ofCode (Formats.Codebook.Catalog.bipolar1.mul left.toCode right.toCode)

/-- Configured bipolar negation negates the exact integer meaning. -/
theorem decode_neg {value : Value} {x : ℤ} (h : ExecFloat.Codebook.decode value = .finite x) :
    ExecFloat.Codebook.decode (neg value) = .finite (-x) :=
  Formats.Codebook.Catalog.bipolar1.neg_refines value.toCode x h

/-- Configured bipolar multiplication multiplies the exact integer meanings. -/
theorem decode_mul {left right : Value} {x y : ℤ}
    (hx : ExecFloat.Codebook.decode left = .finite x)
    (hy : ExecFloat.Codebook.decode right = .finite y) :
    ExecFloat.Codebook.decode (mul left right) = .finite (x * y) :=
  Formats.Codebook.Catalog.bipolar1.mul_refines left.toCode right.toCode x y hx hy

instance : Neg Value where
  neg := neg

namespace Plan

/-- Planner estimate for exact one-bit bipolar multiplication. -/
def mulEstimate : Backend.Candidate where
  name := "one-bit bipolar multiplication"
  kind := .custom "direct codebook bit kernel" 0
  storage := .byte
  steadyCost := 1

/-- Bipolar multiplication candidate for common `ExecFloat` dispatch. Its reference is the kernel
`bipolar1.mul` itself, so the certificate records only that the planner runs that kernel. The
kernel's semantic correctness is `decode_mul`. -/
def mulCertified : Backend.Certified bipolar1.mul :=
  Backend.Certified.reference mulEstimate bipolar1.mul

end Plan

/-- Bipolar multiplication joins common `ExecFloat` dispatch with the kernel `bipolar1.mul` as both
implementation and specification. `decode_mul` gives its exact integer meaning. -/
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

/-- Exact negation of `value`, returning `none` for the reserved word (`decode_neg?`,
`neg?_reserved`). -/
@[inline] def neg? (value : Value) : Option Value :=
  (Formats.Codebook.Catalog.ternary2.neg? value.toCode).map ofCode

/-- Exact product of `left` and `right`, returning `none` if either operand is the reserved word
(`decode_mul?`, `mul?_reserved_left`, `mul?_reserved_right`). -/
@[inline] def mul? (left right : Value) : Option Value :=
  (Formats.Codebook.Catalog.ternary2.mul? left.toCode right.toCode).map ofCode

/-- Checked ternary negation succeeds on every finite value and negates its integer meaning. -/
theorem decode_neg? {value : Value} {x : ℤ} (h : ExecFloat.Codebook.decode value = .finite x) :
    (neg? value).map ExecFloat.Codebook.decode = some (.finite (-x)) := by
  rw [neg?, Option.map_map]
  exact Formats.Codebook.Catalog.ternary2.neg_refines value.toCode x h

/-- Checked ternary multiplication succeeds on finite values and multiplies their integer
meanings. -/
theorem decode_mul? {left right : Value} {x y : ℤ}
    (hx : ExecFloat.Codebook.decode left = .finite x)
    (hy : ExecFloat.Codebook.decode right = .finite y) :
    (mul? left right).map ExecFloat.Codebook.decode = some (.finite (x * y)) := by
  rw [mul?, Option.map_map]
  exact Formats.Codebook.Catalog.ternary2.mul_refines left.toCode right.toCode x y hx hy

/-- Checked ternary negation fails on the reserved word. -/
@[simp] theorem neg?_reserved : neg? reserved = none := by
  simp [neg?, Formats.Codebook.Catalog.ternary2.neg?, reserved, ofCode, toCode]

/-- A reserved left operand makes checked ternary multiplication fail, also against zero. -/
@[simp] theorem mul?_reserved_left (value : Value) : mul? reserved value = none := by
  simp [mul?, reserved, ofCode, toCode]

/-- A reserved right operand makes checked ternary multiplication fail, also against zero. -/
@[simp] theorem mul?_reserved_right (value : Value) : mul? value reserved = none := by
  simp [mul?, reserved, ofCode, toCode]

end ternary2
end FloatLib.Floats.ExecFloat.Codebook.Catalog
