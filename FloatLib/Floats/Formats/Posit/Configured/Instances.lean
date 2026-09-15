/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Formatting
public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.ExecFloat.Comparison
public import FloatLib.Floats.Formats.Posit.Comparison

/-!
# Comparison, display, and literal instances for configured posits

Numerical literals are rounded once from exact rationals. Display and comparison operate on the
exact-width model independently of the selected packed carrier.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Configured posits print their mathematical value rather than their packed carrier. -/
instance :
    FloatLib.Floats.ExecFloat.FormatDisplay (Configured.Family format code plan) where
  format raw := Model.display (codec.toModel raw)

/--
Configured posit comparison follows the standard's total signed-word order.

NaR compares below every real posit because the standard compares complete words as signed
two's-complement integers; this does not give NaR a real or infinite numerical meaning.
-/
instance configuredComparison :
    FloatLib.Floats.ExecFloat.Comparison (Configured.Family format code plan) where
  compare left right :=
    some (cmp (toModel left) (toModel right))

end ExecFloat.Posit

namespace Formats.Posit

/-- Natural literals are rounded once from their exact value into the destination posit. -/
instance {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] (value : Nat) :
    OfNat (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) value where
  ofNat :=
    Configured.Family.ofModel <| Model.roundRat format (value : Rat)

/-- Decimal literals are rounded once from an exact rational, never through a host float. -/
instance {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    OfScientific (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  ofScientific mantissa exponentSign decimalExponent :=
    Configured.Family.ofModel <|
      Model.roundRat format <|
        (OfScientific.ofScientific mantissa exponentSign decimalExponent : Rat)

/-- Posit negation is whole-word two's complement and fixes zero and NaR. -/
instance {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    Neg (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  neg value :=
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary
      (Model := Model format) (plan := plan) Model.neg value

end Formats.Posit
end FloatLib.Floats
