/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting

/-! # External character output for configured binary values

This module writes configured binary values as text, and storage selection affects neither the
characters nor the exception indicators. The descriptor model supplies the shortest, exact,
significant-digit, fixed, scientific and hexadecimal algorithms.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {fmt : FloatFormat} {plan : Configured.StoragePlan fmt} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model fmt) code]

local notation "Value" =>
  ExecFloat.Binary fmt.expWidth fmt.fracWidth fmt.encoding fmt.exponentBias
    fmt.expWidth_ge_two fmt.fracWidth_pos fmt.exponentBias_pos
    fmt.exponentBias_le_maxFinite plan code

/--
Write a configured value as text, as `Model.format`: by default the shortest decimal that reads
back as `value` (what `toString` and `#eval` show), otherwise in `style`, as in
`x.format (style := .fixed (places := 3))`. For the display, `mode` is the direction the text is
read back in. The styles that round, `.significant`, `.fixed`, `.scientific` and
`.hex (.significant n)`, round the printed digits in `mode`, and `.exact` and the exact `.hex`
ignore it. With `status := true` the result also carries the inexact indicator.
-/
@[inline] def format (value : Value) (style : Model.TextStyle := .shortest)
    (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => Model.TextOutcome
    | false => String :=
  Model.format (toModel value) style mode status

/-- Text and its status are independent of the storage representation. -/
@[simp] theorem format_ofModel (value : Model fmt) (style : Model.TextStyle)
    (mode : Model.IEEERoundingMode) (status : Bool) :
    format (ofModel (plan := plan) (code := code) value) style mode status =
      Model.format value style mode status := by
  simp [format]

end FloatLib.Floats.ExecFloat.Binary
