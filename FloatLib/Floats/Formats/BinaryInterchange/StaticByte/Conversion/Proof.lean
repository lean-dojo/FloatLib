/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Static-byte exact conversion proofs

Exact conversion satisfies reduction equations for finite, infinite, and exceptional
observations, and its installed exact decoder agrees with the public runtime function.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte
namespace Conversion

open FloatLib.Numerics

universe u

variable {F : Type u} [Family F]

/-- Finite observations are handled by the shared exact rational binary quantizer. -/
@[simp, grind =] theorem run_finite
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context) (exact : SignedRat) :
    run (F := F) context (.finite exact) = quantizeFinite context exact :=
  rfl

/-- Infinity observations dispatch to the infinity quantizer. -/
@[simp, grind =] theorem run_infinity
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context) (negative : Bool) :
    run (F := F) context (.infinity negative) = quantizeInfinity context negative :=
  rfl

/-- Exceptional observations dispatch to the exceptional-value quantizer. -/
@[simp, grind =] theorem run_exceptional
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context)
    (exceptional : ExceptionalValue) :
    run (F := F) context (.exceptional exceptional) =
      quantizeExceptional context exceptional :=
  rfl

/-- The static-byte converter inherits the shared nearest-value and complete-outcome clauses. -/
theorem implements_run :
    Quantization.Spec.Implements (spec (F := F)) (run (F := F)) :=
  FloatLib.Floats.ExecFloat.Binary.Conversion.implements_runWith pack

/-- The installed exact decoder is the public static-byte decoder. -/
@[simp, grind =] theorem exactDecoder_run (value : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value = decode value :=
  rfl

end Conversion
end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
