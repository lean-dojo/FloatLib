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
Print a short guide to configuring numerical types, inspecting their semantics, and finding the
family entry points.
-/
syntax (name := floatHelpCmd) "#float_help" : command

namespace FloatLib.Floats.ExecFloat.FloatHelp.Command

open Lean Elab Command

/--
Help text printed by `#float_help`, the same whatever formats are imported.

It introduces the shared `ExecFloat` carrier, the operation notation, and the family entry points.
Format packages register their own `#float_info` renderers.
-/
private meta def helpText : String :=
  String.intercalate "\n"
    [ "FloatLib executable-number help"
    , ""
    , "1. Pick a type. The standard formats have names after `open FloatLib.Floats`:"
    , "     Binary16  BFloat16  Binary32  Binary64  Binary128  Binary256"
    , "     Posit8  Posit16  Posit32  Posit64     quires Quire8 to Quire64"
    , "     E4M3FN  E5M2  E4M3FNUZ  E5M2FNUZ      E2M1  E2M3  E3M2 (OCP FP8, ONNX, OCP MX)"
    , "   Any other format is selected by its parameters:"
    , "     ExecFloat.Binary (exponentBits := 5) (fractionBits := 2)"
    , "     ExecFloat.Posit (bits := 12)"
    , ""
    , "2. Inspect the format and its proved surface:"
    , "     #float_info Binary32"
    , "   Focus on checked type-level range, roundoff, and exactness contracts:"
    , "     #float_info [errors] Binary32"
    , "   Include theorem declarations and full hypotheses:"
    , "     #float_info! [errors] Binary32"
    , "   Request the complete theorem and backend audit only when needed:"
    , "     #float_info! Binary32"
    , ""
    , "3. Use ordinary literals and arithmetic:"
    , "     def x : Binary32 := 1.5"
    , "     def y : Binary32 := x + 2.25"
    , "   Choose a rounding direction, or ask for the IEEE flags and ternary value:"
    , "     open FloatLib.Rounding"
    , "     #eval ExecFloat.Binary.sqrt x (mode := up) (status := true)"
    , "   Round a rational once, read an integer, or use a format constant:"
    , "     #eval (ExecFloat.Binary.ofRat (1 / 3) (mode := up) : Binary32)"
    , "     #eval x.toInt? (mode := nearest)"
    , "     #eval (ExecFloat.Binary.epsilon : Binary32)"
    , "   `#eval y` prints the shortest decimal that reads back as `y`; `format` writes the rest:"
    , "     #eval ExecFloat.Binary.format y (style := .scientific 3)"
    , ""
    , "4. Name the destination of every cross-format operation:"
    , "     #eval x.cast (target := Binary64)"
    , "     #eval ExecFloat.addAs (target := Binary64) x (1 : Posit32)"
    , "     #eval ExecFloat.convert (target := Binary64) (3 / 2 : Rat)"
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

/-- Print the full report: theorems, backend planning, and the trust boundary. -/
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

Every family renderer reaches it through `withElaboratedType`.
-/
meta def elaborateType (type : Syntax) : TermElabM Expr := do
  let typeExpr ← Term.elabType type
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars typeExpr

/--
Run one family renderer on a fully elaborated type without modifying the environment.

Every `#float_info` extension goes through this one command-elaboration boundary.
-/
meta def withElaboratedType
    (type : Syntax) (render : Expr → TermElabM Unit) : CommandElabM Unit :=
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_float_info do
    render (← elaborateType type)

/--
Run a `#float_info` renderer when the supplied type is an `ExecFloat` family built by
`familyName` with `arity` arguments.

A mismatch raises `unsupportedSyntax`, so Lean tries the next registered format renderer. The
callback receives the value type, the recovered family, and the family arguments.
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

Family-specific rules call `throwUnsupportedSyntax` when their carrier shape does not match, so a
new numerical family can add a renderer without modifying this module.
-/
elab_rules : command
  | `(#float_info%$tk $_type:term) =>
      throwErrorAt tk "`#float_info` has no renderer for this numerical type"

end FloatLib.Floats.ExecFloat.FloatInfo.Command
