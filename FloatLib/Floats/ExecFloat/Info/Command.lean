/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.ExecFloat.Info.Inspection

/-!
# Format inspection commands

Syntax and elaboration for `#float_help`, `#float_info`, and `#float_info!`. Each format package
registers a renderer for its configured types. The final rule reports an unsupported type when
no renderer recognizes it.

Commands inspect elaborated types at compile time. Adding a format renderer requires no change
to arithmetic execution.
-/

@[expose] public section

/--
Print a concise guide to configuring numerical types, inspecting their semantics, and finding
the family-specific constructors exported by the currently imported FloatLib package.
-/
syntax (name := floatHelpCmd) "#float_help" : command

namespace FloatLib.Floats.ExecFloat.FloatHelp.Command

open Lean Elab Command

/--
The stable, family-independent part of the interactive help text.

The guide introduces the shared `ExecFloat` carrier and operation notation. Format packages
register their own `#float_info` renderers.
-/
private meta def helpText : String :=
  String.intercalate "\n"
    [ "FloatLib executable-number help"
    , ""
    , "1. Configure a type, usually with a short project-local abbreviation:"
    , "     abbrev F32 := ExecFloat.Binary"
    , "       (exponentBits := 8) (fractionBits := 23)"
    , "     abbrev P32 := ExecFloat.Posit (bits := 32)"
    , ""
    , "2. Inspect the format and its proved surface:"
    , "     #float_info F32"
    , "   Focus on checked type-level range, roundoff, and exactness contracts:"
    , "     #float_info [errors] F32"
    , "   Include theorem declarations and full hypotheses:"
    , "     #float_info! [errors] F32"
    , "   Request the complete theorem and backend audit only when needed:"
    , "     #float_info! F32"
    , ""
    , "3. Use ordinary literals and arithmetic:"
    , "     def x : F32 := 1.5"
    , "     def y : F32 := x + 2.25"
    , ""
    , "4. Name the destination of every cross-format operation:"
    , "     abbrev F64 := ExecFloat.Binary"
    , "       (exponentBits := 11) (fractionBits := 52)"
    , "     #eval x.cast (target := F64)"
    , "     #eval ExecFloat.addAs (result := F64) x (1 : P32)"
    , "     #eval ExecFloat.convert (target := F64) (3 / 2 : Rat)"
    , "   These calls return `ConversionOutcome`, preserving status or an explicit failure."
    , ""
    , "Core configurable and family entry points:"
    , "  ExecFloat.Binary                  parameterized binary interchange"
    , "  ExecFloat.Posit                   current-standard posit by total width"
    , "  ExecFloat.FixedPoint              exact fixed point"
    , "  ExecFloat.BoundedFixedPoint       bounded fixed point"
    , "  ExecFloat.Logarithmic             exact logarithmic numbers"
    , "  ExecFloat.Codebook                finite lookup encodings"
    , "  ExecFloat.P3109 format            IEEE P3109 representation and projection"
    , "  ExecFloat.SharedScale             generic shared-scale blocks"
    , "  ExecFloat Formats.OCP...          standard-backed OCP scalar packages"
    , "  ExecFloat.OCP.MX.E8M0             OCP exponent-only block scale"
    , "  ExecFloat.OCP.MX.Block            OCP jointly stored MX blocks"
    , "  BinaryInterchange.ExecComplex fmt two-component rounded complex arithmetic"
    , "  BinaryInterchange.Model.Interval fmt  outward-rounded closed intervals"
    , "  BinaryInterchange.Model fmt       expert descriptor-indexed binary proof carrier"
    , "  Posit.Model fmt                   expert descriptor-indexed posit proof carrier"
    , ""
    , "Different configurations are distinct Lean types, but executable numerical families use"
    , "the same `ExecFloat` operations. The active planning policy selects a certified backend"
    , "for each operation; `#float_info` reports that selection."
    , "Each family exposes only values its encoding actually has. IEEE binary formats, for example,"
    , "have infinities and NaNs, while a finite-only format does not."
    , "Use raw-word constructors only for serialization, interoperability, or validation data."
    , ""
    , "#float_info reports representation, exceptional values, rounding, selected execution"
    , "strategy, universal and specialized operations, proof coverage, and current proof limits."
    , "#float_info [errors] reports only explicitly registered type-level numerical theorems;"
    , "it does not analyze compound expressions, guess input ranges, or invent an unproved bound."
    , "#float_info! also reports checked theorem names, hypotheses, planner costs, and the complete"
    , "proof boundary. Neither command infers semantics from a type alias or storage width."
    , ""
    , "Inspection scope:"
    , "  #float_info is for stored or executable numerical carriers. Operation outcomes, proof"
    , "  witnesses, backend certificates, descriptor records, and rounding contexts are supporting"
    , "  infrastructure rather than numerical formats, so they intentionally have no renderer."
    ]

elab_rules : command
  | `(#float_help) => logInfo helpText

end FloatLib.Floats.ExecFloat.FloatHelp.Command

/--
Print the format, value classes, execution strategy, proof-backed operation coverage, semantic
theorem groups, and documented proof limits for an executable numerical type.
-/
syntax (name := floatInfoCmd) "#float_info " term : command

/-- Focus the report on checked range, roundoff, and exactness contracts. -/
syntax (name := floatInfoErrorsCmd) "#float_info" "[" "errors" "]" term : command

/-- Enable the complete theorem, backend-planning, and trust-boundary audit report. -/
syntax (name := floatInfoDetailedCmd) "#float_info! " term : command

/-- Show the detailed theorem inventory for numerical-analysis contracts only. -/
syntax (name := floatInfoErrorsDetailedCmd) "#float_info!" "[" "errors" "]" term : command

macro_rules
  | `(#float_info [errors] $type:term) =>
      `(set_option floatlib.floatInfo.errors true in #float_info $type)
  | `(#float_info! [errors] $type:term) =>
      `(set_option floatlib.floatInfo.errors true in
        set_option floatlib.floatInfo.full true in
        #float_info $type)
  | `(#float_info! $type:term) =>
      `(set_option floatlib.floatInfo.full true in #float_info $type)

namespace FloatLib.Floats.ExecFloat.FloatInfo.Command

open Lean Elab Command Meta

/--
Elaborate and fully instantiate the numerical type supplied to `#float_info`.

Every family renderer uses this same command boundary before inspecting its carrier shape.
-/
meta def elaborateType (type : Syntax) : TermElabM Expr := do
  let typeExpr ← Term.elabType type
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars typeExpr

/--
Run one family renderer against a fully elaborated type without mutating the environment.

This keeps every `#float_info` extension on the same command-elaboration boundary.
-/
meta def withElaboratedType
    (type : Syntax) (render : Expr → TermElabM Unit) : CommandElabM Unit :=
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_float_info do
    render (← elaborateType type)

/--
Run a `#float_info` renderer only when the supplied type uses one exact `ExecFloat` family.

A family mismatch raises `unsupportedSyntax`, which lets Lean try the next registered format
renderer. The callback receives the user-facing value type, the recovered family, and the checked
family arguments. Format modules supply their own report data.
-/
meta def withExecFamilyApplication
    (type : Syntax) (familyName : Name) (arity : Nat)
    (render : Expr → Expr → Array Expr → TermElabM Unit) : CommandElabM Unit :=
  withElaboratedType type fun typeExpr => do
    let some (family, arguments) ←
        FloatLib.Floats.ExecFloat.Inspection.execFamilyApplication?
          familyName arity typeExpr
      | throwUnsupportedSyntax
    render typeExpr family arguments

/--
Report an unsupported type after every imported representation family has declined it.

Family-specific rules use `throwUnsupportedSyntax` when their exact carrier shape does not match,
so future numerical families can add renderers without modifying this module.
-/
elab_rules : command
  | `(#float_info%$tk $_type:term) =>
      throwErrorAt tk "`#float_info` has no renderer for this numerical type"

end FloatLib.Floats.ExecFloat.FloatInfo.Command
