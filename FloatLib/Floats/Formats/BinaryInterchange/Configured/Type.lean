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
plan. Numerical parameters select the descriptor and storage plan; operation backends are
registered separately in `Configured.NativeDispatch` and `Configured.Plan.Instances`.

Tooling and serialization code can use these types without importing the complete value API.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat
namespace Binary

/--
The validated binary descriptor selected by `ExecFloat.Binary`.

This is the user-facing inspection point for a configured type. It exposes the exponent and
fraction widths, derived storage width, exponent bias, and exceptional-value encoding without
requiring users to inspect the carrier implementation.
-/
abbrev format
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
  FloatFormat.custom exponentBits fractionBits bias encoding
    exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite

/--
The default eight-exponent-bit, twenty-three-fraction-bit configuration is exactly the IEEE
754 binary32 interchange descriptor.
-/
@[simp, grind =] theorem format_binary32 :
    format (exponentBits := 8) (fractionBits := 23) = FloatFormat.binary32 := by
  rfl

/--
The default eleven-exponent-bit, fifty-two-fraction-bit configuration is exactly the IEEE
754 binary64 interchange descriptor.
-/
@[simp, grind =] theorem format_binary64 :
    format (exponentBits := 11) (fractionBits := 52) = FloatFormat.binary64 := by
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
    Binary.format exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite
  let plan :=
    Configured.StoragePlan.forKnownWidth format
      (1 + exponentBits + fractionBits) (by rfl)
  Configured.Family format (Configured.Code plan) plan

/--
The limb-stored family of a binary format wider than 128 bits.

The descriptor is the one `Binary.Family` selects; only the storage carrier differs. Values are
`Model.WideLimb.Value` arrays of 32-bit limbs. Eligible descriptors offer direct limb addition,
subtraction, multiplication, and fused multiply-add to the planner. Division, square root,
comparison, and conversion rebuild the exact-width proof model from the limbs first.
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
    Binary.format exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite
  let plan :=
    Configured.StoragePlan.limbsForKnownWidth format
      (1 + exponentBits + fractionBits) (by rfl) width_gt
  Configured.Family format (Configured.Code plan) plan

end Binary

/--
An executable binary format wider than 128 bits stored as an array of 32-bit limbs.

This is the opt-in counterpart of `ExecFloat.Binary` for wide formats: same descriptor, same
literals and reference semantics. For eligible descriptors, the planner can select the kernels
of `ExecFloat/Backends/WideLimb` to run addition, subtraction, multiplication, and fused
multiply-add
directly on the stored limbs. `ExecFloat.Binary` keeps the exact-width proof model, avoiding limb
conversion for division, square root, comparison, and conversion.
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
  FloatLib.Floats.ExecFloat <|
    Binary.LimbFamily exponentBits fractionBits encoding bias width_gt
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite

/--
An executable binary format selected directly by its numerical parameters.

The stored width is derived as `1 + exponentBits + fractionBits`; it is not a separate parameter
that can disagree with the layout. Storage and operation implementations are selected statically
from the resulting format.
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
          "ExecFloat.Binary requires bias ≤ encoding.maxFiniteExponent exponentBits") :=
  FloatLib.Floats.ExecFloat <|
    Binary.Family exponentBits fractionBits encoding bias
      exponentBits_ge_two fractionBits_pos bias_pos bias_le_maxFinite

end ExecFloat
end FloatLib.Floats
