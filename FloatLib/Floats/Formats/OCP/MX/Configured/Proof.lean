/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Runtime

/-!
# Representation theorems for configured OCP MX values

Complete E8M0 bytes and joint MX block codes round-trip through their configured wrappers.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.OCP.MX

open FloatLib.Floats.Formats.BinaryInterchange

universe u

namespace E8M0

/-- Unwrapping a freshly wrapped E8M0 code returns the original code. -/
@[simp, grind =] theorem toCode_ofCode (code : Formats.OCP.MX.E8M0) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the code of an E8M0 value returns the original value. -/
@[simp, grind =] theorem ofCode_toCode (value : ExecFloat.OCP.MX.E8M0) :
    ofCode (toCode value) = value :=
  ExecFloat.ofRaw_raw value

/-- Reconstructing an E8M0 scale from its complete byte preserves the value. -/
@[simp, grind =] theorem ofNatBits_toNatBits
    (value : ExecFloat.OCP.MX.E8M0) :
    ofNatBits (toNatBits value) = value := by
  rw [ofNatBits, toNatBits, Formats.OCP.MX.E8M0.ofNatBits_toNatBits]
  exact ofCode_toCode value

/-- An in-range byte is unchanged by E8M0 encoding and decoding. -/
@[simp, grind =] theorem toNatBits_ofNatBits_of_lt
    (bits : Nat) (bits_lt : bits < 2 ^ 8) :
    toNatBits (ofNatBits bits) = bits := by
  simp [ofNatBits, toNatBits,
    Formats.OCP.MX.E8M0.toNatBits_ofNatBits_of_lt bits bits_lt]

end E8M0

namespace Block

variable {format : FloatFormat}

/-- Unwrapping a freshly wrapped MX block returns the original code. -/
@[simp, grind =] theorem toCode_ofCode (code : Formats.OCP.MX.BlockCode format) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the code of an MX block returns the original value. -/
@[simp, grind =] theorem ofCode_toCode
    (value : ExecFloat.OCP.MX.Block format) :
    ofCode (toCode value) = value :=
  ExecFloat.ofRaw_raw value

/-- `ofComponents` preserves the supplied shared scale. -/
@[simp, grind =] theorem scale_ofComponents
    (scaleValue : ExecFloat.OCP.MX.E8M0) (elementValues : Array (Model format)) :
    scale (ofComponents scaleValue elementValues) = scaleValue := by
  exact E8M0.ofCode_toCode scaleValue

/-- `ofComponents` preserves the supplied binary element words. -/
@[simp, grind =] theorem values_ofComponents
    (scaleValue : ExecFloat.OCP.MX.E8M0) (elementValues : Array (Model format)) :
    values (ofComponents scaleValue elementValues) = elementValues :=
  rfl

/-- Building from nominal elements stores exactly their corresponding proof-model values. -/
@[simp, grind =] theorem values_ofElements
    {F : Type u} [StaticByte.Family F]
    (scaleValue : ExecFloat.OCP.MX.E8M0)
    (elementValues : Array (FloatLib.Floats.ExecFloat F)) :
    values (ofElements scaleValue elementValues) =
      elementValues.map fun value => StaticByte.toModel (F := F) value :=
  rfl

end Block
end FloatLib.Floats.ExecFloat.OCP.MX
