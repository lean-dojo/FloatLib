/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# Parameterized binary `ExecFloat` types

The public configured binary type identifies a format by its numerical parameters and storage
plan. Numerical parameters select the descriptor and storage plan, and operation backends are
registered in `Configured.NativeDispatch` and `Configured.Plan.Instances`.

Tooling and serialization code can use these types without importing the complete value API.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat
namespace Binary

/--
The validated binary descriptor selected by `ExecFloat.Binary`.

It exposes the exponent and fraction widths, derived storage width, exponent bias, and
exceptional-value encoding of a configured type without requiring users to inspect the carrier
implementation.
-/
abbrev descriptor
    (exponentBits fractionBits : Nat)
    (encoding : FloatFormat.Encoding := .ieee)
    (bias : Nat := encoding.defaultBias exponentBits)
    (exponentBits_ge_two : 2 ≤ exponentBits := by
      first
      | decide
      | fail "ExecFloat.Binary requires exponentBits ≥ 2")
    (fractionBits_pos : 0 < fractionBits := by
      first
      | decide
      | fail "ExecFloat.Binary requires fractionBits ≥ 1")
    (bias_pos : 0 < bias := by
      first
      | decide
      | fail "ExecFloat.Binary requires a positive exponent bias")
    (bias_le_maxFinite : bias ≤ encoding.maxFiniteExponent exponentBits := by
      first
      | decide
      | fail
          "ExecFloat.Binary requires bias ≤ encoding.maxFiniteExponent exponentBits") :
    FloatFormat :=
  -- Expose the fields so rebuilding an arbitrary descriptor reduces back to that descriptor.
  -- Generic configured methods can then infer its codec without unfolding `FloatFormat.custom`.
  { expWidth := exponentBits
    expWidth_ge_two := exponentBits_ge_two
    fracWidth := fractionBits
    fracWidth_pos := fractionBits_pos
    exponentBias := bias
    encoding := encoding
    exponentBias_pos := bias_pos
    exponentBias_le_maxFinite := bias_le_maxFinite }

/--
Infer a configured receiver's descriptor before comparing its individual fields.

This keeps field notation independent of unrelated codecs in scope. The `id` wrappers allow
proof fields to be compared by proof irrelevance when Lean checks the hint.
-/
unif_hint descriptorEta
    (format source : FloatFormat) (exponentBits fractionBits : Nat)
    (encoding : FloatFormat.Encoding) (bias : Nat)
    (exponentBits_ge_two : 2 ≤ exponentBits) (fractionBits_pos : 0 < fractionBits)
    (bias_pos : 0 < bias)
    (bias_le_maxFinite : bias ≤ encoding.maxFiniteExponent exponentBits) where
  format =?= source
  source =?= FloatFormat.mk exponentBits (id exponentBits_ge_two)
    fractionBits (id fractionBits_pos) bias encoding (id bias_pos) (id bias_le_maxFinite) ⊢
  ExecFloat.Binary.descriptor format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite =?= source

/--
The default eight-exponent-bit, twenty-three-fraction-bit configuration is the IEEE 754 binary32
interchange descriptor.
-/
@[simp, grind =] theorem descriptor_binary32 :
    descriptor (exponentBits := 8) (fractionBits := 23) = FloatFormat.binary32 := by
  rfl

/--
The default eleven-exponent-bit, fifty-two-fraction-bit configuration is the IEEE 754 binary64
interchange descriptor.
-/
@[simp, grind =] theorem descriptor_binary64 :
    descriptor (exponentBits := 11) (fractionBits := 52) = FloatFormat.binary64 := by
  rfl

/--
The encoded-format family underlying `ExecFloat.Binary`.

Most users only need the value type `ExecFloat.Binary`. Generic code that inspects capabilities
or storage plans can use this corresponding `EncodedFormat` parameter.
-/
abbrev Family
    (exponentBits fractionBits : Nat)
    (encoding : FloatFormat.Encoding := .ieee)
    (bias : Nat := encoding.defaultBias exponentBits)
    (exponentBits_ge_two : 2 ≤ exponentBits := by
      first
      | decide
      | fail "ExecFloat.Binary requires exponentBits ≥ 2")
    (fractionBits_pos : 0 < fractionBits := by
      first
      | decide
      | fail "ExecFloat.Binary requires fractionBits ≥ 1")
    (bias_pos : 0 < bias := by
      first
      | decide
      | fail "ExecFloat.Binary requires a positive exponent bias")
    (bias_le_maxFinite : bias ≤ encoding.maxFiniteExponent exponentBits := by
      first
      | decide
      | fail
          "ExecFloat.Binary requires bias ≤ encoding.maxFiniteExponent exponentBits") :=
  let format :=
    Binary.descriptor exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite
  let plan :=
    Configured.StoragePlan.forKnownWidth format
      (1 + exponentBits + fractionBits) (by rfl)
  Configured.Family format (Configured.Code plan) plan

/--
The limb-stored family of a binary format wider than 128 bits.

The descriptor is the one `Binary.Family` selects, and only the storage carrier differs. Values are
`Model.WideLimb.Value` arrays of 32-bit limbs. Eligible descriptors offer the wide-limb kernels
for all six arithmetic operations to the planner. Comparison and conversion rebuild the
exact-width proof model from the limbs first.
-/
abbrev LimbFamily
    (exponentBits fractionBits : Nat)
    (encoding : FloatFormat.Encoding := .ieee)
    (bias : Nat := encoding.defaultBias exponentBits)
    (width_gt : 128 < 1 + exponentBits + fractionBits := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires more than 128 encoded bits")
    (exponentBits_ge_two : 2 ≤ exponentBits := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires exponentBits ≥ 2")
    (fractionBits_pos : 0 < fractionBits := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires fractionBits ≥ 1")
    (bias_pos : 0 < bias := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires a positive exponent bias")
    (bias_le_maxFinite : bias ≤ encoding.maxFiniteExponent exponentBits := by
      first
      | decide
      | fail
          "ExecFloat.BinaryLimbs requires bias ≤ encoding.maxFiniteExponent exponentBits") :=
  let format :=
    Binary.descriptor exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite
  let plan :=
    Configured.StoragePlan.limbsForKnownWidth format
      (1 + exponentBits + fractionBits) (by rfl) width_gt
  Configured.Family format (Configured.Code plan) plan

end Binary

/--
An executable binary format selected by its numerical parameters.

The stored width is derived as `1 + exponentBits + fractionBits`, so no separate width parameter
can disagree with the layout. Storage and operation implementations are selected statically
from the resulting format. The optional `plan` and `code` parameters let generic code use the
same interface with another certified carrier.
-/
abbrev Binary
    (exponentBits fractionBits : Nat)
    (encoding : FloatFormat.Encoding := .ieee)
    (bias : Nat := encoding.defaultBias exponentBits)
    (exponentBits_ge_two : 2 ≤ exponentBits := by
      first
      | decide
      | fail "ExecFloat.Binary requires exponentBits ≥ 2")
    (fractionBits_pos : 0 < fractionBits := by
      first
      | decide
      | fail "ExecFloat.Binary requires fractionBits ≥ 1")
    (bias_pos : 0 < bias := by
      first
      | decide
      | fail "ExecFloat.Binary requires a positive exponent bias")
    (bias_le_maxFinite : bias ≤ encoding.maxFiniteExponent exponentBits := by
      first
      | decide
      | fail
          "ExecFloat.Binary requires bias ≤ encoding.maxFiniteExponent exponentBits")
    (plan : Configured.StoragePlan (Binary.descriptor exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite) :=
      Configured.StoragePlan.forKnownWidth _ (1 + exponentBits + fractionBits) rfl)
    (code : Type := Configured.Code plan) :=
  FloatLib.Floats.ExecFloat <|
    Configured.Family (Binary.descriptor exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite) code plan

/--
An executable binary format wider than 128 bits stored as an array of 32-bit limbs.

This is the opt-in counterpart of `ExecFloat.Binary` for wide formats: same descriptor, same
literals and reference semantics. For eligible descriptors, the planner can select the kernels
of `ExecFloat/Backends/WideLimb` to run the six arithmetic operations on the stored limbs.
`ExecFloat.Binary` keeps the exact-width proof model, avoiding limb conversion for comparison and
conversion.
-/
abbrev BinaryLimbs
    (exponentBits fractionBits : Nat)
    (encoding : FloatFormat.Encoding := .ieee)
    (bias : Nat := encoding.defaultBias exponentBits)
    (width_gt : 128 < 1 + exponentBits + fractionBits := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires more than 128 encoded bits")
    (exponentBits_ge_two : 2 ≤ exponentBits := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires exponentBits ≥ 2")
    (fractionBits_pos : 0 < fractionBits := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires fractionBits ≥ 1")
    (bias_pos : 0 < bias := by
      first
      | decide
      | fail "ExecFloat.BinaryLimbs requires a positive exponent bias")
    (bias_le_maxFinite : bias ≤ encoding.maxFiniteExponent exponentBits := by
      first
      | decide
      | fail
          "ExecFloat.BinaryLimbs requires bias ≤ encoding.maxFiniteExponent exponentBits") :=
  Binary exponentBits fractionBits encoding bias
    exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite
    (plan := Configured.StoragePlan.limbsForKnownWidth
      (Binary.descriptor exponentBits fractionBits encoding bias
        exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite)
      (1 + exponentBits + fractionBits) rfl width_gt)

end ExecFloat

/-! ## Standard formats -/

/-- IEEE 754-2019 binary16, half precision: 5 exponent bits and 10 fraction bits. -/
abbrev Binary16 := ExecFloat.Binary (exponentBits := 5) (fractionBits := 10)

/--
Bfloat16, the brain floating-point format of TPUs and `torch.bfloat16`: the 8-bit exponent of
binary32 and 7 fraction bits.
-/
abbrev BFloat16 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 7)

/-- IEEE 754-2019 binary32, single precision: 8 exponent bits and 23 fraction bits. -/
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/-- IEEE 754-2019 binary64, double precision: 11 exponent bits and 52 fraction bits. -/
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

/-- IEEE 754-2019 binary128, quadruple precision: 15 exponent bits and 112 fraction bits. -/
abbrev Binary128 := ExecFloat.Binary (exponentBits := 15) (fractionBits := 112)

/--
IEEE 754-2019 binary256, octuple precision: 19 exponent bits and 236 fraction bits.

`ExecFloat.BinaryLimbs (exponentBits := 19) (fractionBits := 236)` is the same format stored as
32-bit limbs, which runs the wide-limb arithmetic kernels on them.
-/
abbrev Binary256 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 236)

end FloatLib.Floats
