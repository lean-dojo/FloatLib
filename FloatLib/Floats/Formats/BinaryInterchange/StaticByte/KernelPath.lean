/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value -- shake: keep
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Proof

/-!
# Kernel view of one-byte values

A static-byte family stores each value in one `UInt8`. The instance `natView` reads that byte as
a natural number and stores one back with primitive projections and constructors, which makes
the kernel operations of `KernelPath.Value` and their rewrite theorems available for every
static-byte family (E4M3, E5M2 and every other format of at most eight bits).

Lean's kernel then computes on the encodings and never builds the families' exhaustive byte
tables.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath (NatView)

universe u

/-- A bound below the format width fits a byte. -/
theorem lt_byte_of_lt {F : Type u} [Family F] {n : Nat}
    (hn : n < 2 ^ (Family.format (F := F)).bitWidth) : n < 2 ^ 8 :=
  Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (Family.width_le_eight (F := F)))

/--
Structural equality of the stored byte: distinct encodings of zero are unequal and a NaN equals
itself. It is what a kernel decision about two static-byte values compares.
-/
instance (F : Type u) [Family F] : DecidableEq (FormatCode F) :=
  fun left right =>
    if h : left.1 = right.1 then isTrue (Subtype.ext h)
    else isFalse fun equality => h (congrArg Subtype.val equality)

/-- Every static-byte family has the natural-number view of its byte. -/
instance natView (F : Type u) [Family F] : NatView F (Family.format (F := F)) where
  toNat := fun (c : Code F) => kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0) 0
  ofNat := fun n hn => (⟨⟨⟨⟨n, lt_byte_of_lt (F := F) hn⟩⟩⟩, hn⟩ : Code F)
  toModel := codeToModel
  ofModel := modelToCode
  toNat_eq := fun c => (Model.toNatBits_ofNatBits_of_lt _ c.2).symm
  toNat_ofNat := fun _ _ => rfl
  ofModel_toModel := modelToCode_codeToModel

/-- A scientific literal of a one-byte type is the kernel literal. -/
@[kernel_optimize] theorem ofScientific_eq (F : Type u) [Family F] (mantissa : Nat)
    (exponentSign : Bool) (exponent : Nat) :
    (OfScientific.ofScientific mantissa exponentSign exponent : FloatLib.Floats.ExecFloat F) =
      KernelPath.Value.ofScientific mantissa exponentSign exponent := by
  rw [KernelPath.Value.ofScientific_eq_lift]
  rfl

/-- A natural-number literal of a one-byte type is the kernel literal. -/
@[kernel_optimize] theorem ofNat_eq (F : Type u) [Family F] (value : Nat) :
    (OfNat.ofNat value : FloatLib.Floats.ExecFloat F) = KernelPath.Value.ofNatural value := by
  rw [KernelPath.Value.ofNatural_eq_lift]
  rfl

/-- The negation of a one-byte value is the kernel negation. -/
@[kernel_optimize] theorem neg_eq {F : Type u} [Family F] (value : FloatLib.Floats.ExecFloat F) :
    -value = KernelPath.Value.neg value := by
  rw [KernelPath.Value.neg_eq_lift]
  rfl

/-- The comparison of one-byte values is the model comparison of the decoded values. -/
instance modelComparison (F : Type u) [Family F] :
    KernelPath.Value.ModelComparison F (Family.format (F := F)) :=
  ⟨fun _ _ => rfl⟩

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
