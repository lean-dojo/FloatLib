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
registers a renderer for its configured types. The final rule runs when no imported renderer
recognizes the type: it names the module whose report covers the type, or says what
`#float_info` reports on.

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
The family entry points that `#float_help` lists: each name as it reads after
`open FloatLib.Floats`, the arguments it takes, and what it is. This generic module imports no
family, so the names are text; a conformance test checks that each one resolves. Every entry has a
`#float_info` report except the one whose description says it has none.
-/
meta def entryPoints : List (String × String × String) :=
  [ ("ExecFloat.Binary", "", "parameterized binary interchange")
  , ("ExecFloat.BinaryLimbs", "", "binary interchange wider than 128 bits, stored in 32-bit limbs")
  , ("ExecFloat.Posit", "", "current-standard posit by total width")
  , ("ExecFloat.FixedPoint", "", "exact fixed point")
  , ("ExecFloat.BoundedFixedPoint", "", "bounded fixed point")
  , ("ExecFloat.Logarithmic", "", "exact logarithmic numbers")
  , ("ExecFloat.Codebook", "", "finite lookup encodings")
  , ("ExecFloat.P3109", " format", "IEEE P3109 representation and projection")
  , ("ExecFloat.SharedScale", "", "generic shared-scale blocks")
  , ("ExecFloat.OCP.MX.E8M0", "", "OCP exponent-only block scale")
  , ("ExecFloat.OCP.MX.Block", "", "OCP jointly stored MX blocks")
  , ("ExecFloat.Binary.Interval", "",
      "outward-rounded closed binary intervals; no #float_info report")
  , ("Formats.BinaryInterchange.ExecComplex", " fmt", "two-component rounded complex arithmetic")
  , ("Formats.BinaryInterchange.Model", " fmt", "descriptor-indexed binary proof model")
  , ("Formats.BinaryInterchange.Model.Interval", " fmt",
      "closed intervals of binary proof-model values")
  , ("Formats.Posit.Model", " fmt", "descriptor-indexed posit proof model")
  ]

/-- The entry points as aligned help lines. -/
private meta def entryPointLines : List String :=
  let call (entry : String × String × String) := entry.1 ++ entry.2.1
  let width := entryPoints.foldl (fun width entry => max width (call entry).length) 0
  entryPoints.map fun entry =>
    "  " ++ call entry ++ "".pushn ' ' (width + 2 - (call entry).length) ++ entry.2.2

/--
Help text printed by `#float_help`, the same whatever formats are imported.

It introduces the shared `ExecFloat` carrier, the operation notation, and the family entry points.
Format packages register their own `#float_info` renderers.
-/
private meta def helpText : String :=
  String.intercalate "\n" <|
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
    , "2. Inspect the format and its theorems:"
    , "     #float_info Binary32"
    , "   Focus on checked type-level range, roundoff, and exactness contracts:"
    , "     #float_info [errors] Binary32"
    , "   List every theorem behind those contracts, with its scope:"
    , "     #float_info! [errors] Binary32"
    , "   Request the complete theorem and backend audit only when needed:"
    , "     #float_info! Binary32"
    , "   Hover a theorem name in a report to see its statement."
    , ""
    , "3. Use ordinary literals and arithmetic:"
    , "     def x : Binary32 := 1.5"
    , "     def y : Binary32 := x + 2.25"
    , "   Choose a rounding direction, or ask for the IEEE flags and ternary value:"
    , "     #eval ExecFloat.Binary.sqrt x (mode := .up) (status := true)"
    , "   Round a rational once, read an integer, or use a format constant:"
    , "     #eval (ExecFloat.Binary.ofRat (1 / 3) (mode := .up) : Binary32)"
    , "     #eval x.toInt? (mode := .nearest)"
    , "     #eval (ExecFloat.Binary.epsilon : Binary32)"
    , "   `#eval y` prints the shortest decimal that reads back as `y`; `format` writes the rest:"
    , "     #eval y.format (style := .scientific (places := 3))"
    , ""
    , "4. Name the destination of every cross-format operation:"
    , "     #eval x.cast (target := Binary64)"
    , "     #eval ExecFloat.Mixed.add (target := Binary64) x (1 : Posit32)"
    , "     #eval ExecFloat.convert (target := Binary64) (3 / 2 : Rat)"
    , "   These calls return `ConversionOutcome`, preserving status or an explicit failure."
    , ""
    , "Family entry points, named as after `open FloatLib.Floats`:"
    ] ++ entryPointLines ++
    [ ""
    , "Different configurations are distinct Lean types, but executable numerical families use"
    , "the same `ExecFloat` operations. The active planning policy selects a certified backend"
    , "for each operation; `#float_info` reports the policy and that selection."
    , "Each family exposes only values its encoding actually has. IEEE binary formats, for example,"
    , "have infinities and NaNs, while a finite-only format does not."
    , "Use raw-word constructors only for serialization, interoperability, or validation data."
    , ""
    , "#float_info reports representation, exceptional values, rounding, conversions, execution,"
    , "operations, theorems, and what the report does not claim. For most configured types it"
    , "lists the theorems about the type's own values first, then those about its proof model or"
    , "code. #float_info [errors] reports only registered type-level range, roundoff, and"
    , "exactness theorems; it does not bound compound expressions or guess input ranges."
    , "#float_info! adds every theorem name with its scope and the planner's costs."
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

Every `#float_info` extension goes through this one command-elaboration boundary. The type's
syntax is the reference while the renderer runs, so a report can name the type as written.
-/
meta def withElaboratedType
    (type : Syntax) (render : Expr → TermElabM Unit) : CommandElabM Unit :=
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_float_info <| withRef type do
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
The modules that register the `#float_info` reports for a family, keyed by the family's
namespace. This generic module imports no family, so the names are not checked here; a conformance
test checks that every module exists.
-/
meta def reportModules : List (Name × Name) :=
  [ (`FloatLib.Floats.Formats.BinaryInterchange, `FloatLib.Floats.Formats.BinaryInterchange)
  , (`FloatLib.Floats.Formats.Posit, `FloatLib.Floats.Formats.Posit)
  , (`FloatLib.Floats.Formats.FixedPoint, `FloatLib.Floats.Formats.FixedPoint)
  , (`FloatLib.Floats.Formats.Logarithmic, `FloatLib.Floats.Formats.Logarithmic)
  , (`FloatLib.Floats.Formats.Codebook, `FloatLib.Floats.Formats.Codebook)
  , (`FloatLib.Floats.Formats.Block, `FloatLib.Floats.Formats.Block)
  , (`FloatLib.Floats.Formats.OCP.MX, `FloatLib.Floats.Formats.OCP.MX)
  , (`FloatLib.Floats.Formats.P3109, `FloatLib.Floats.Formats.P3109)
  , (`Float, `FloatLib.Floats.Formats.IEEE754)
  , (`Float32, `FloatLib.Floats.Formats.IEEE754)
  ]

/--
The head constant that names a type's family: the family of an `ExecFloat` type, otherwise the
type's own head after unfolding the caller's abbreviations.
-/
private meta def familyHead? (type : Expr) : MetaM (Option Name) := do
  if let some family ← FloatLib.Floats.ExecFloat.Inspection.execFamily? type then
    return (← whnfR family).getAppFn.constName?
  return (← whnfR type).getAppFn.constName?

/--
Explain why no report was printed, after every imported family renderer has declined the type.

Family-specific rules call `throwUnsupportedSyntax` when their carrier shape does not match, so a
new numerical family can add a renderer without modifying this module. A type in a FloatLib
family whose report module is not imported, such as `Binary32` without
`FloatLib.Floats.Formats.BinaryInterchange`, is told which module to import, and an `ExecFloat`
type of an unknown family is told that `import FloatLib` brings every family's report. Any other
type, including one whose report module is already imported but has no report for it, is told what
`#float_info` reports on.
-/
elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType type fun typeExpr => do
        -- A type that failed to elaborate has already been reported.
        if typeExpr.hasSyntheticSorry then throwAbortTerm
        let subject ← FloatLib.Floats.ExecFloat.Inspection.subjectText
        let environment ← getEnv
        let imported (module : Name) : Bool := (environment.getModuleIdx? module).isSome
        let family? := (← familyHead? typeExpr).bind fun head =>
          reportModules.find? fun (namespace_, _) => namespace_.isPrefixOf head
        let isExecFloat := (← FloatLib.Floats.ExecFloat.Inspection.execFamily? typeExpr).isSome
        match family? with
        | some (_, module) =>
            unless imported module do
              throwErrorAt tk "no `#float_info` report is imported for {subject}; add \
                `import {module}` or `import FloatLib`"
        | none =>
            if isExecFloat && !imported `FloatLib then
              throwErrorAt tk "no `#float_info` report is imported for the ExecFloat type \
                {subject}; `import FloatLib` imports the report of every FloatLib family"
        throwErrorAt tk "`#float_info` has no report for {subject}. It reports FloatLib's \
          numerical types: ExecFloat types such as `Binary32` and `Posit32`, the proof models \
          `Formats.BinaryInterchange.Model fmt` and `Formats.Posit.Model fmt`, the intervals \
          `Formats.BinaryInterchange.Model.Interval fmt`, Lean's `Float` and `Float32`, and the \
          complex, quire, and block types that `#float_help` lists"

end FloatLib.Floats.ExecFloat.FloatInfo.Command
