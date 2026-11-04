/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Proof

/-!
# Configured posit conversion instances

Every configured posit gets the `quantizer` instance for exact-rational conversion and a default
quantizer. What happens to an infinity or an exceptional value is up to the policies in the
conversion `Context`, and the default maps both to `NaR`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit
namespace Conversion

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Exact-rational quantization for every configured posit, with special values set by context. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) Rat where
  Context := Context
  run := run
  spec := spec
  correct := implements_run

/-- Context-free conversion uses the Posit Standard (2022), §6.5 infinity and NaN mapping to `NaR`. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) Rat where
  defaultContext := Context.default

end Conversion
end ExecFloat.Posit
end FloatLib.Floats
