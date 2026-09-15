/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Native.Runtime

/-!
# Correctness of native-word posit packing

The capability law immediately identifies direct native packing with exact model construction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

namespace NativeCode

variable {format : Format} {plan : StoragePlan format}

/-- Direct native-word packing decodes to the supplied complete posit encoding. -/
@[simp, grind =] theorem toModel_pack [NativeCode format plan]
    (bits : Nat) (hbits : bits < format.modulus) :
    Code.toModel (pack (plan := plan) bits hbits) =
      Model.ofNatBits (format := format) bits :=
  NativeCode.toModel_ofNat bits hbits

end NativeCode

end FloatLib.Floats.Formats.Posit.Configured
