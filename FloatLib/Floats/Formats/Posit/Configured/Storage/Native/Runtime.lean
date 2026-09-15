/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Native.Core

/-!
# Native-word runtime access for configured posits

These wrappers expose the direct word view and certified packing operation used by fixed-word
posit kernels.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

namespace NativeCode

variable {format : Format} {plan : StoragePlan format}

/-- Zero-extend through the native storage capability. -/
@[always_inline, inline] def word [NativeCode format plan]
    (code : Code plan) : UInt64 :=
  NativeCode.toUInt64 code

/-- Pack a certified in-range result through the built-in carrier capability. -/
@[always_inline, inline] def pack [NativeCode format plan]
    (bits : Nat) (hbits : bits < format.modulus) : Code plan :=
  NativeCode.ofNat bits hbits

end NativeCode

end FloatLib.Floats.Formats.Posit.Configured
