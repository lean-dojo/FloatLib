/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Fundamental configured posit constants

Zero and NaR are representation-level constants needed by arithmetic, standard functions,
conformance proofs, and the public API. They live below those layers so every client uses the same
definitions without creating an import cycle.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Construct the unique posit zero. -/
@[inline] def zero :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  Configured.Family.ofModel (Model.zero format)

/-- Construct the unique posit Not-a-Real value. -/
@[inline] def nar :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  Configured.Family.ofModel (Model.nar format)

end ExecFloat.Posit
end FloatLib.Floats
