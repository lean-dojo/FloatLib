/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info.Command
public import FloatLib.Floats.ExecFloat.Info.Profile
public import FloatLib.Floats.ExecFloat.Info.Inspection
public import FloatLib.Floats.ExecFloat.Info.Render

/-!
# Format inspection

`#float_info` reports a numerical type's format, backends, and available theorems.
`#float_info!` includes theorem names and hypotheses; `#float_help` lists the command options.

`Info.Profile` defines report data and checks theorem references. `Info.Inspection` discovers
capabilities and backend metadata, `Info.Render` formats the report, and `Info.Command` defines
the syntax. Format families register renderers in their own `Info` modules.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Inspection

/--
Attach conversion capabilities discovered for a value type, validate the declarations relevant
to the report mode, and render the profile. Format modules supply representation and semantics.
-/
meta def renderProfile
    (profile : FormatProfile) (valueType : Lean.Expr)
    (operations : CoreOperationCoverage) : Lean.Meta.MetaM String := do
  let profile ← withConversions profile valueType
  profile.validateDeclarations
  FloatLib.Floats.ExecFloat.renderFormatInfo profile operations

/-- Render a profile using the universal operations actually installed for an `ExecFloat` family. -/
meta def renderExecProfile
    (profile : FormatProfile) (valueType family : Lean.Expr) :
    Lean.Meta.MetaM String := do
  renderProfile profile valueType (← coreOperations family)

end FloatLib.Floats.ExecFloat.Inspection
