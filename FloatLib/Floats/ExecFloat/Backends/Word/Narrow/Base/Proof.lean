/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Correctness of native binary32 storage operations

The `UInt32` storage conversions are mutual inverses, and native sign-bit negation agrees with
the generic binary32 model. Runtime clients can import `Base.Runtime` without these proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Word negation is the model sign flip. -/
@[simp] theorem negate_eq (x : Value) :
    negate x = Model.neg x := by
  cases x
  rfl

/-- Repacking the stored word returns the value. -/
@[simp] theorem ofUInt32_toUInt32 (x : Value) :
    ofUInt32 (toUInt32 x) = x := by
  cases x
  rfl

/-- Unpacking a freshly packed word returns the word. -/
@[simp] theorem toUInt32_ofUInt32 (bits : UInt32) :
    toUInt32 (ofUInt32 bits) = bits :=
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
