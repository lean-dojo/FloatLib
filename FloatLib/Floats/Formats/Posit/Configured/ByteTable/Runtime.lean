/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Certified
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Runtime

/-!
# Runtime support for byte-sized posit tables

Byte-sized posit tables share a finite encoding and direct execution on their carrier. Certified
table construction and correctness proofs are separate so consumers can depend on the smallest
appropriate layer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.ByteTable

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

variable {format : Format}

/-- The exact posit model as a proved finite byte encoding. -/
def encoding (format : Format) (width_le : format.bits ≤ 8) :
    TinyTable.Encoding (Model format) where
  radix := format.modulus
  radix_pos := Nat.two_pow_pos format.bits
  radix_le_byte := by
    simpa only [Format.modulus, show 256 = 2 ^ 8 by decide] using
      (Nat.pow_le_pow_right (by decide : 0 < 2) width_le)
  decode code := Model.ofNatBits code.val
  encode value := ⟨value.toNatBits, Model.toNatBits_lt_modulus value⟩
  decode_encode value := Model.ofNatBits_toNatBits value
  encode_decode code := by
    apply Fin.ext
    exact Model.toNatBits_ofNatBits_of_lt code.val code.isLt

/-! ## Direct configured-carrier execution -/

/-- Execute a certified binary table on the public byte carrier. -/
@[always_inline, inline] def runBinary
    {modelSpec : Model format → Model format → Model format}
    (width_le : format.bits ≤ 8)
    (kernel : TinyTable.CertifiedBinary (encoding format width_le) modelSpec)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le)) (.byte width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.byte width_le)) (.byte width_le)) :=
  FloatLib.Floats.ExecFloat.applyBinary kernel.run left right

/-- Execute a certified unary table on the public byte carrier. -/
@[always_inline, inline] def runUnary
    {modelSpec : Model format → Model format}
    (width_le : format.bits ≤ 8)
    (kernel : TinyTable.CertifiedUnary (encoding format width_le) modelSpec)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le)) (.byte width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.byte width_le)) (.byte width_le)) :=
  FloatLib.Floats.ExecFloat.applyUnary kernel.run value

/-- Execute a certified ternary table on the public byte carrier. -/
@[always_inline, inline] def runTernary
    {modelSpec : Model format → Model format → Model format → Model format}
    (width_le : format.bits ≤ 8)
    (kernel : TinyTable.CertifiedTernary (encoding format width_le) modelSpec)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le)) (.byte width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.byte width_le)) (.byte width_le)) :=
  FloatLib.Floats.ExecFloat.applyTernary kernel.run left right addend

end FloatLib.Floats.Formats.Posit.Configured.ByteTable
