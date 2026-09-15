/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Core
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Configured binary-family runtime conversion

The storage codec converts between a configured `ExecFloat` value and its binary proof model.
The selected codec and its storage plan remain type-static.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Numerics
namespace Family

variable {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Decode a configured executable value into the proof model. -/
@[always_inline, inline] def toModel
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) : Model format :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode (plan := plan) value

/-- Pack a proof-model value into configured runtime storage. -/
@[always_inline, inline] def ofModel
    (value : Model format) : FloatLib.Floats.ExecFloat (Family format code plan) :=
  FloatLib.Floats.ExecFloat.ModelCodec.encode
    (F := Family format code plan) (plan := plan) value

end Family

end FloatLib.Floats.Formats.BinaryInterchange.Configured
