/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Core

/-!
# Configured posit-family runtime conversion

A configured posit `ExecFloat` value and its exact-width proof model are two forms of one number,
and the storage codec converts between them. Nothing about the carrier or storage plan is decided
at runtime, since both are fixed in the value's type.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

namespace Family

variable {format : Format} {plan : StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Decode a configured executable posit into the exact-width model. -/
@[always_inline, inline] def toModel
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) : Model format :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode (plan := plan) value

/-- Pack an exact-width model value into configured posit storage. -/
@[always_inline, inline] def ofModel
    (value : Model format) : FloatLib.Floats.ExecFloat (Family format code plan) :=
  FloatLib.Floats.ExecFloat.ModelCodec.encode
    (F := Family format code plan) (plan := plan) value

end Family

end FloatLib.Floats.Formats.Posit.Configured
