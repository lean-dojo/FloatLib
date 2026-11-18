/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public meta import FloatLib.Tactic.IEEENames
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# IeeeConfiguredFunctions generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals
open Model.Transcendentals.CorrectlyRounded (Function)

set_option hygiene false in
/--
`configured_binary name` declares the configured form of the function `name` of two operands
of `Model.Transcendentals.CorrectlyRounded`.
-/
macro (name := configuredBinary) doc:docComment "configured_binary " name:ident : command => do
  let model := Lean.mkIdent (`Model.Transcendentals.CorrectlyRounded ++ name.getId)
  `($doc:docComment
    @[inline] def $name (left right : (ExecFloat.Binary format.expWidth format.fracWidth
      format.encoding format.exponentBias
          format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
          format.exponentBias_le_maxFinite plan code)) (mode : Model.IEEERoundingMode := .nearest) :
        IEEEOutcome (format := format) (plan := plan) (code := code) :=
      IEEEOutcome.ofModel
        ($model (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) mode))


end FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded
