/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Text

/-!
# Kernel rules for the conversions to and from character sequences

IEEE 754-2019 §5.12 names `convertToDecimalCharacter`, `convertFromDecimalCharacter`,
`convertToHexCharacter` and `convertFromHexCharacter`. On a configured binary value they are
`ExecFloat.Binary.format` and `ExecFloat.Binary.parse`. The rules of this module give
`float_decide` both on encodings and lists of characters, for every format descriptor, storage
plan, style and rounding direction:

* `format_eq`: the text of a configured value is `String.ofList` of
  `KernelPath.formatCharacters` on its encoding.
* `parse_eq`: the value read from a string is `KernelPath.parseCharacters` on its characters,
  stored by `KernelPath.ofNat`.
* The rules of `Numerics.Kernel.Text` remove the string between the two
  (`String.length_ofList`, `String.toList_ofList`, `ofList_eq_iff`): the length of a formatted
  value is the length of a list, a formatted value is compared with a string as a list of
  characters, and a formatted value that is read back never becomes a string.

Text that does not scan as it stands (spaces around a number, an error) is read by the
reference parser on the string. Lean's kernel evaluates its string functions in a file that is
not a `module`, and does not see their definitions in a `module`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

variable {format : FloatFormat}

/--
The text of a configured value in a style and a rounding direction is the list of characters
that the kernel form writes for its encoding.
-/
@[kernel_optimize] theorem format_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan))
    (style : Model.TextStyle) (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.format value style mode false =
      String.ofList (KernelPath.formatCharacters format style mode (toNat value)) := by
  rw [KernelPath.toNat_eq, ofList_formatCharacters, ← toModel_eq_natView]
  rfl

/--
The value read from a string in a rounding direction, without limits, is the kernel form on the
characters of the string, stored as an encoding. Errors are the errors of the reference.
-/
@[kernel_optimize] theorem parse_eq {plan : StoragePlan format} (text : String)
    (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.Binary.parse text mode none false :
        Except Model.ParseError (FloatLib.Floats.ExecFloat (Family format (Code plan) plan))) =
      (KernelPath.parseCharacters format mode text.toList).map KernelPath.ofNat := by
  rw [parseCharacters_eq]
  change (Model.parse format text mode).map FloatLib.Floats.ExecFloat.Binary.ofModel = _
  cases Model.parse format text mode with
  | error error => rfl
  | ok value => exact congrArg Except.ok (ofModel_eq_ofNat value)

end FloatLib.Floats.Formats.BinaryInterchange.Configured
