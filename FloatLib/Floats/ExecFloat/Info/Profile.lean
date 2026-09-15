/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata
public meta import Lean.Data.Options
public import Lean.Exception
public meta import Lean.Elab.Command
public meta import FloatLib.Floats.ExecFloat.Carrier -- shake: keep

/-!
# Proof-aware format-report profiles

A numerical family describes its representation, value classes, rounding, execution strategy,
theorem groups, and proof limits with one `FormatProfile`, which supplies the data for
`#float_info`.

Rendering and metaprogramming inspection live in separate modules. Keeping the schema independent
lets family packages construct and validate reports without depending on the command UI.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

open FloatLib.Numerics

/-- Whether `#float_info` should print the complete proof and backend audit. -/
meta register_option floatlib.floatInfo.full : Bool := {
  defValue := false
  descr := "show theorem declarations, hypotheses, planner costs, and complete proof boundaries"
}

/-- Whether `#float_info` should focus on checked range, roundoff, and exactness guarantees. -/
meta register_option floatlib.floatInfo.errors : Bool := {
  defValue := false
  descr := "show only theorem-backed numerical range and error guarantees"
}

/-- One labeled fact in a user-facing format report. -/
meta structure InfoEntry where
  /-- Short name shown on the left of the report. -/
  label : String
  /-- Human-readable value or explanation. -/
  value : String

/-- Render a Boolean report field without exposing Lean's constructor names. -/
meta def yesNo (value : Bool) : String :=
  if value then "yes" else "no"

/-- The numerical role played by a theorem group in range or roundoff analysis. -/
meta inductive NumericalAnalysisKind where
  /-- An enclosure or a representable-output-range guarantee. -/
  | range
  /-- A theorem identifying the exact quantity and rounding rule used by an operation. -/
  | rounding
  /-- An absolute roundoff or approximation bound. -/
  | absoluteError
  /-- A relative roundoff or approximation bound. -/
  | relativeError
  /-- A zero-error or exact-representation result under the stated hypotheses. -/
  | exactness

/--
The concise numerical statement attached to a checked theorem surface.

The statement summarizes the theorem for numerical users; the theorem declaration list and
`scope` remain the authoritative Lean interface.
-/
meta structure NumericalGuarantee where
  /-- Kinds of numerical analysis supported by the theorem group. -/
  kinds : List NumericalAnalysisKind
  /-- Human-readable statement of the checked guarantee. -/
  statement : String

/--
Whether a checked theorem group can be instantiated for the configured numerical type.

Input-specific premises such as finiteness or a nonzero divisor remain listed in `scope`.
This status records only descriptor-level applicability.
-/
meta inductive TheoremApplicability where
  /-- The configured descriptor satisfies the theorem group's format requirements. -/
  | verifiedForType
  /-- The descriptor is supported, but another descriptor or relation must be chosen. -/
  | conditional (condition : String)
  /-- A descriptor-level premise of the theorem group is false for this type. -/
  | unavailable (reason : String)

/--
A group of checked declarations that gives mathematical meaning to an executable specification.

`applicability` records whether the configured type satisfies the group's descriptor-level
premises. `scope` records remaining input or relation hypotheses. Declaration names are an index
into the Lean API, not a replacement for checking the exact theorem statements.
-/
meta structure TheoremSurface where
  /-- Mathematical topic covered by the declarations. -/
  topic : String
  /--
  Principal public theorems. Every name is checked before the report is printed and must resolve
  to a theorem.
  -/
  declarations : List Lean.Name
  /--
  Definitions such as executable specifications or named constructors that the surface
  deliberately lists alongside its theorems. They are checked for existence only.
  -/
  definitions : List Lean.Name := []
  /-- Whether this group is available for the configured descriptor. -/
  applicability : TheoremApplicability
  /-- Conditions under which the declarations apply. -/
  scope : String
  /--
  Optional range, roundoff, or exactness meaning exposed by `#float_info [errors]`.

  An empty field omits the group from numerical-analysis reports; it does not assert that the
  declarations have no numerical consequences. The renderer does not infer bounds from names.
  -/
  numericalGuarantee? : Option NumericalGuarantee := none

/-- Family-defined descriptive information for one encoded numerical format. -/
meta structure FormatProfile where
  /-- Representation and semantics family, such as binary interchange or a codebook. -/
  family : String
  /-- Standards identity or an explicit statement that the format is nonstandard. -/
  standard : String
  /-- Namespace prefix omitted from declaration names in this family's rendered report. -/
  declarationPrefix : String
  /-- Representation parameters that determine the encoded type. -/
  representation : List InfoEntry
  /-- Finite and exceptional value classes represented by the encoding. -/
  values : List InfoEntry
  /-- Rounding and literal-conversion behavior. -/
  rounding : List InfoEntry
  /--
  Installed explicit-conversion capabilities.

  Family elaborators populate this field by synthesizing the same `ExactDecoder`, `Quantizer`,
  and `DefaultQuantizer` instances used by execution. An empty list is retained for third-party
  profiles that have not opted into capability inspection yet.
  -/
  conversions : List InfoEntry := []
  /-- Runtime carrier and backend-selection behavior. -/
  execution : List InfoEntry
  /--
  Executable operations that belong to this carrier but not to the universal scalar
  `ExecFloat` interface.

  Examples include outward-rounded interval arithmetic, posit-quire accumulation, and explicit
  bounded-fixed-point overflow policies. Keeping these operations separate prevents a report from
  either hiding useful family APIs or falsely advertising them as scalar `ExecFloat` capabilities.
  -/
  specializedOperations : List InfoEntry := []
  /-- Principal semantic theorem surfaces available for this family. -/
  theoremSurfaces : List TheoremSurface
  /-- Claims deliberately outside the reported proof boundary. -/
  nonclaims : List String

/--
Proof-backed availability of the universal executable operations.

The operation enum defines the supported operation list. The family-specific `#float_info`
elaborator synthesizes the actual proof-carrying capability for each entry, so this report does
not maintain a second capability hierarchy that could drift from execution.
-/
meta abbrev CoreOperationCoverage :=
  List (Backend.Operation × Bool)

/-- Empty universal-operation coverage for a family that does not use the `ExecFloat` API. -/
meta def CoreOperationCoverage.none : CoreOperationCoverage :=
  Backend.Operation.all.map fun operation => (operation, false)

/-- Fail unless every listed theorem surface name is an existing theorem. -/
meta def TheoremSurface.validateTheorems (surface : TheoremSurface) : Lean.Meta.MetaM Unit := do
  let environment ← Lean.getEnv
  for declaration in surface.declarations do
    match environment.find? declaration with
    | some (.thmInfo _) => pure ()
    | some _ =>
      throwError
        "internal `#float_info` profile error: `{declaration}` is listed as a theorem surface of \
        `{surface.topic}` but is not a theorem; list definitions under `definitions`"
    | none =>
      throwError
        "internal `#float_info` profile error: theorem `{declaration}` listed under \
        `{surface.topic}` does not exist"

/-- Fail unless every listed definition of a theorem surface exists in the environment. -/
meta def TheoremSurface.validateDefinitions (surface : TheoremSurface) :
    Lean.Meta.MetaM Unit := do
  let environment ← Lean.getEnv
  for definition in surface.definitions do
    unless environment.contains definition do
      throwError
        "internal `#float_info` profile error: definition `{definition}` listed under \
        `{surface.topic}` does not exist"

/--
Refuse to render a profile whose theorem surfaces are inconsistent with the environment.

Every rendered name under `declarations` must be an existing theorem, and every rendered name
under `definitions` must exist. Errors-only mode checks names only in groups with a numerical
guarantee. In every mode, all numerical guarantees must name at least one kind and one theorem.
-/
meta def FormatProfile.validateDeclarations
    (profile : FormatProfile) : Lean.Meta.MetaM Unit := do
  let errorsOnly := floatlib.floatInfo.errors.get (← Lean.getOptions)
  for surface in profile.theoremSurfaces do
    if let some guarantee := surface.numericalGuarantee? then
      if guarantee.kinds.isEmpty then
        throwError
          "internal `#float_info` profile error: numerical guarantee `{surface.topic}` has no kind"
      if surface.declarations.isEmpty then
        throwError
          "internal `#float_info` profile error: numerical guarantee `{surface.topic}` has no declarations"
  let surfaces :=
    if errorsOnly then
      profile.theoremSurfaces.filter fun surface => surface.numericalGuarantee?.isSome
    else
      profile.theoremSurfaces
  for surface in surfaces do
    surface.validateTheorems
    surface.validateDefinitions

/--
Unfold project-local type abbreviations until a registered family constructor is exposed.

The target is tested before every unfolding step. This is essential for transparent, zero-cost
carrier definitions: the inspector may unfold `abbrev MyNumber := Family.Code ...`, but must stop
at `Family.Code` rather than normalize onward to its raw `BitVec` or integer representation.
-/
meta partial def unfoldUntilApp?
    (target : Lean.Name) (arity : Nat) (type : Lean.Expr) :
    Lean.Meta.MetaM (Option Lean.Expr) := do
  let type ← Lean.instantiateMVars type
  if type.isAppOfArity target arity then
    return some type
  let some unfolded ←
      Lean.Meta.withTransparency .all <| Lean.Meta.unfoldDefinition? type
    | return none
  if unfolded == type then
    return none
  unfoldUntilApp? target arity unfolded

/--
Unfold project-local abbreviations until `target` is visible, then return its arguments.

Format inspectors normally need the constructor parameters rather than the application itself.
Keeping that extraction here gives every inspector the same stopping point and arity check.
-/
meta def unfoldUntilAppArgs?
    (target : Lean.Name) (arity : Nat) (type : Lean.Expr) :
    Lean.Meta.MetaM (Option (Array Lean.Expr)) := do
  let some application ← unfoldUntilApp? target arity type
    | return none
  return some application.getAppArgs

end FloatLib.Floats.ExecFloat
