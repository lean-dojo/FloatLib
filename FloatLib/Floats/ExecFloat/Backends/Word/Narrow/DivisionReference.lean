/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Exact-rational reference division for native binary32 words

The exact-rational reference divider specifies the result against which the direct binary32 word
divider is refined. It decodes finite binary32 operands, handles finite division by zero
according to IEEE binary32, and delegates nonzero quotients to the exact rational rounder.

The optimized one-word divider and its proof live in `Narrow.Division.Runtime` and
`Narrow.Division.Proof`. Keeping the reference
operation independent prevents division-only clients from depending on the much larger
addition/FMA implementation core.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Finite binary32 division through the generic exact-rational rounder. -/
@[inline] def divFinite? (x y : Value) : Option Value :=
  match toDyadic? (toUInt32 x), toDyadic? (toUInt32 y) with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then
          some (ofUInt32 0x7fc00000)
        else
          some (ofUInt32 (if sign then 0xff800000 else 0x7f800000))
      else if dx.significand == 0 then
        some (ofUInt32 (if sign then 0x80000000 else 0))
      else
        some <|
          ofUInt32 <|
            roundRatScaled sign dx.significand dy.significand
              (dx.exponent - dy.exponent)
  | _, _ => none

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
