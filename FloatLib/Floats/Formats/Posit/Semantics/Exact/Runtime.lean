/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Decode
public import FloatLib.Numerics.Core.Value

/-!
# Executable exact rational semantics of posits

This is the executable meaning of a posit word. Every ordinary word denotes an exact rational,
and the unique NaR word denotes `ExceptionalValue.notAReal`, with no partial rational value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

open FloatLib.Numerics

namespace Model.ExactValue

/-- Forget tapered field metadata into the common exact rational value domain. -/
@[inline] def forget {format : Format} :
    Model.ExactValue format → NumericalValue Rat
  | .zero => .finite 0
  | .finite fields => .finite fields.toRat
  | .nar => .exceptional .notAReal

/-- Recover the exact rational value of an ordinary decoded value. NaR returns `none`. -/
@[inline] def toRat? {format : Format} :
    Model.ExactValue format → Option Rat
  | .zero => some 0
  | .finite fields => some fields.toRat
  | .nar => none

end Model.ExactValue

namespace Model

variable {format : Format}

/-- Complete exact rational semantics of every posit word. -/
@[inline] def decode (value : Model format) : NumericalValue Rat :=
  value.decodeExact.forget

/-- Exact rational represented by an ordinary word. The result is `none` on NaR alone. -/
@[inline] def toRat? (value : Model format) : Option Rat :=
  value.decodeExact.toRat?

end Model
end FloatLib.Floats.Formats.Posit
