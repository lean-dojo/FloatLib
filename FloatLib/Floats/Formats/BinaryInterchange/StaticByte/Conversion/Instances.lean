/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion.Proof
public import FloatLib.Floats.ExecFloat.Comparison

/-!
# Ordinary interfaces and exact conversion for static-byte formats

Every nominal static-byte family uses the same descriptor-level rules for literals, negation,
comparison, and display. With those instances defined here, standards packages need not repeat
adapters around the binary proof model.

Natural and decimal literals are rounded once from exact rationals and never pass through a host
floating-point value. This module also installs the exact decoder, the policy-aware quantizer, and
the default quantization context shared by these families.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

open FloatLib.Numerics

universe u

variable {F : Type u} [Family F]

/-- Print the mathematical binary value rather than the compact byte carrier. -/
instance :
    FloatLib.Floats.ExecFloat.FormatDisplay F where
  format code := Model.format (codeToModel code)

/--
Compare through the exact-width binary model.

NaNs are unordered, signed zeros compare equal, and finite-only descriptors inherit the same
descriptor-generic rule without a format-specific comparison implementation.
-/
instance :
    FloatLib.Floats.ExecFloat.Comparison F where
  compare left right := Model.compare (toModel left) (toModel right)

/-- Round a natural literal once, to nearest with ties to even, in the destination descriptor. -/
instance (value : Nat) :
    OfNat (FloatLib.Floats.ExecFloat F) value where
  ofNat :=
    ofModel <| Model.ofRat (Family.format (F := F)) (value : Rat)

/-- Round a decimal or scientific literal once from its exact rational value. -/
instance :
    OfScientific (FloatLib.Floats.ExecFloat F) where
  ofScientific mantissa exponentSign decimalExponent :=
    ofModel <|
      Model.ofRat (Family.format (F := F)) <|
        (OfScientific.ofScientific mantissa exponentSign decimalExponent : Rat)

/-- Negate the proof-model value and repack it into the same direct byte carrier. -/
instance :
    Neg (FloatLib.Floats.ExecFloat F) where
  neg value := ofModel <| Model.neg (toModel value)

namespace Conversion

/-- Every nominal static-byte binary destination uses the shared binary conversion policy. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer (FloatLib.Floats.ExecFloat F) SignedRat where
  Context := FloatLib.Floats.ExecFloat.Binary.Conversion.Context
  run := run
  spec := spec
  correct := implements_run
  addExact := FloatLib.Floats.ExecFloat.Binary.Conversion.addExact
  subExact := FloatLib.Floats.ExecFloat.Binary.Conversion.subExact

/-- Context-free conversion uses the canonical binary conversion context. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer (FloatLib.Floats.ExecFloat F) SignedRat where
  defaultContext := FloatLib.Floats.ExecFloat.Binary.Conversion.Context.default

/-- Conversions into a static-byte destination take an `IEEERoundingMode`, nearest by default. -/
instance roundingModes :
    FloatLib.Floats.ExecFloat.RoundingModes (FloatLib.Floats.ExecFloat F)
      Model.IEEERoundingMode where
  default := .nearest

/--
A conversion's `(mode := m)` selects the canonical binary context rounding in direction `m`, and
`.nearest` the canonical context itself.
-/
@[inline] instance modeContext (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.ModeContext (FloatLib.Floats.ExecFloat F) SignedRat mode where
  context :=
    match mode with
    | .nearest => FloatLib.Floats.ExecFloat.Binary.Conversion.Context.default
    | mode => FloatLib.Floats.ExecFloat.Binary.Conversion.Context.withRounding mode

/-- The context a static-byte conversion's `(mode := m)` selects is `Context.withRounding m`. -/
@[simp] theorem context_modeContext (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.ModeContext.context :
        FloatLib.Floats.ExecFloat.ContextFor (FloatLib.Floats.ExecFloat F) mode) =
      FloatLib.Floats.ExecFloat.Binary.Conversion.Context.withRounding mode := by
  cases mode <;> rfl

end Conversion
end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
