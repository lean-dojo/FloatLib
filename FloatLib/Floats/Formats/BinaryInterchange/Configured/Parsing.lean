/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Character input for configured binary values

Configured binary values use the descriptor model's exact character parser. A successful parse
changes only the storage representation; the decoded numerical value is unchanged.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Parse exact decimal or radix-two text and round it once into the configured binary format.

Malformed text and unsupported special values return `Model.ParseError`.
-/
def parse (rounding : Model.IEEERoundingMode) (input : String) :
    Except Model.ParseError
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  (Model.parse format rounding input).map ofModel

/-- Nearest-even character input for a configured binary value. -/
def parseNearest (input : String) :
    Except Model.ParseError
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  parse .nearestEven input

/-- Character input with the configured result and all five IEEE exception indicators. -/
def parseWithStatus (rounding : Model.IEEERoundingMode) (input : String) :
    Except Model.ParseError (IEEEOutcome (format := format) (plan := plan) (code := code)) :=
  (Model.parseWithStatus format rounding input).map IEEEOutcome.ofModel

/-- Decoding configured text conversion preserves the complete model outcome. -/
theorem map_toModel_parseWithStatus (rounding : Model.IEEERoundingMode) (input : String) :
    (parseWithStatus (format := format) (plan := plan) (code := code) rounding input).map
      IEEEOutcome.toModel = Model.parseWithStatus format rounding input := by
  cases h : Model.parseWithStatus format rounding input <;>
    simp [parseWithStatus, h, Except.map]

/-- Decoding configured parse success gives exactly the descriptor-model parse result. -/
theorem map_toModel_parse (rounding : Model.IEEERoundingMode) (input : String) :
    (parse (format := format) (plan := plan) (code := code) rounding input).map toModel =
      Model.parse format rounding input := by
  cases hparse : Model.parse format rounding input with
  | error parseError =>
      unfold parse
      rw [hparse]
      rfl
  | ok value =>
      unfold parse
      rw [hparse]
      change
        Except.ok
            (toModel (ofModel (plan := plan) (code := code) value)) =
          Except.ok value
      rw [toModel_ofModel]

end FloatLib.Floats.ExecFloat.Binary
