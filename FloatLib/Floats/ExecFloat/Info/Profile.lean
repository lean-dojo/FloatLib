/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public meta import Lean.Data.Options
public import Lean.Exception
public meta import Lean.Elab.Command
public meta import Lean.OriginalConstKind
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
  descr := "show every theorem name with its scope, the planner's costs, and every claim the \
    report does not make"
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
premises. `scope` summarizes the remaining input or relation hypotheses. Declaration names are an
index into the Lean API, rendered so that hovering one shows its exact statement.
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

  Numerical-analysis reports include only groups with an explicit guarantee in this field.
  The renderer uses that supplied guarantee rather than inferring bounds from declaration names.
  -/
  numericalGuarantee? : Option NumericalGuarantee := none

/--
Theorem groups about values of another type, which the inspected type's values reach through
`embedding`. An executable carrier states few theorems directly: `Binary32` relates its values to
the proof model `Model format` with `ExecFloat.Binary.toModel`, a configured fixed-point value to
its code with `toCode`; the theorems about that type then apply through the embedding.
-/
meta structure RelatedTheorems where
  /-- The type constructor the groups are about, such as `Formats.BinaryInterchange.Model`. -/
  type : Lean.Name
  /-- The function taking a value of the inspected type to a value of `type`. -/
  embedding : Lean.Name
  /-- The theorem groups, each stated about values of `type`. -/
  surfaces : List TheoremSurface

/-- Family-defined descriptive information for one encoded numerical format. -/
meta structure FormatProfile where
  /-- Representation and semantics family, such as binary interchange or a codebook. -/
  family : String
  /-- Standards identity or an explicit statement that the format is nonstandard. -/
  standard : String
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
  /--
  Principal theorem groups. When `relatedTheorems` is not empty, each of these groups is stated
  about values of the inspected type, and the report's heading says so. Otherwise the heading is
  just "Theorems", and each group's topic and scope say what its theorems are about.
  -/
  theoremSurfaces : List TheoremSurface
  /--
  Theorem groups about the types that the inspected type's values reach, such as its proof model
  or its code, each under a heading that names the type and the embedding. They apply to the
  inspected type's values only through the embedding and the theorems relating the two, which
  `theoremSurfaces` lists. A profile lists them only when every group in `theoremSurfaces` is
  about the inspected type's own values.
  -/
  relatedTheorems : List RelatedTheorems := []
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

/-- The names that `names` gives for each installed operation, in operation order. -/
meta def CoreOperationCoverage.installed (coverage : CoreOperationCoverage)
    (names : Backend.Operation → List Lean.Name) : List Lean.Name :=
  coverage.foldr (fun (operation, available) rest =>
    if available then names operation ++ rest else rest) []

/--
The `ExecFloat` refinement equations of the installed operations as one theorem group, or none
when no operation is installed. The notation forms, which rewrite `x + y`, `x - y`, `x * y`, and
`x / y`, come before the forms for the named operations.
-/
meta def refinementEquations (coverage : CoreOperationCoverage) : List TheoremSurface :=
  let operators := coverage.installed fun
    | .add => [``FloatLib.Floats.ExecFloat.Proof.add_notation_eq_spec]
    | .sub => [``FloatLib.Floats.ExecFloat.Proof.sub_notation_eq_spec]
    | .mul => [``FloatLib.Floats.ExecFloat.Proof.mul_notation_eq_spec]
    | .div => [``FloatLib.Floats.ExecFloat.Proof.div_notation_eq_spec]
    | .sqrt | .fma => []
  let named := coverage.installed fun
    | .add => [``FloatLib.Floats.ExecFloat.Proof.add_eq_spec]
    | .sub => [``FloatLib.Floats.ExecFloat.Proof.sub_eq_spec]
    | .mul => [``FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]
    | .div => [``FloatLib.Floats.ExecFloat.Proof.div_eq_spec]
    | .sqrt => [``FloatLib.Floats.ExecFloat.Proof.sqrt_eq_spec]
    | .fma => [``FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]
  if named.isEmpty then []
  else
    [ { topic := "arithmetic equals its reference operation"
        declarations := operators ++ named
        definitions := coverage.installed fun
          | .add => [``FloatLib.Floats.ExecFloat.Spec.add]
          | .sub => [``FloatLib.Floats.ExecFloat.Spec.sub]
          | .mul => [``FloatLib.Floats.ExecFloat.Spec.mul]
          | .div => [``FloatLib.Floats.ExecFloat.Spec.div]
          | .sqrt => [``FloatLib.Floats.ExecFloat.Spec.sqrt]
          | .fma => [``FloatLib.Floats.ExecFloat.Spec.fma]
        applicability := .verifiedForType
        scope :=
          "every operand, exceptional values included; each is an equation of stored values, " ++
          "so every result, exceptional or not, is the reference result. The " ++
          "`*_notation_eq_spec` forms rewrite `x + y`, `x - y`, `x * y`, and `x / y`; the " ++
          "others rewrite `ExecFloat.add` and its siblings" } ]

/-- Fail unless every listed theorem surface name is an existing theorem. -/
meta def TheoremSurface.validateTheorems (surface : TheoremSurface) : Lean.Meta.MetaM Unit := do
  let environment ← Lean.getEnv
  for declaration in surface.declarations do
    -- Module exports may hide theorem bodies, so check the original declaration kind.
    match Lean.getOriginalConstKind? environment declaration with
    | some .thm => pure ()
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
under `definitions` must exist, as must each related type and its embedding. Errors-only mode
checks names only in groups with a numerical guarantee. In every mode, all numerical guarantees
must name at least one kind and one theorem.
-/
meta def FormatProfile.validateDeclarations
    (profile : FormatProfile) : Lean.Meta.MetaM Unit := do
  let errorsOnly := floatlib.floatInfo.errors.get (← Lean.getOptions)
  for related in profile.relatedTheorems do
    for name in [related.type, related.embedding] do
      unless (← Lean.getEnv).contains name do
        throwError
          "internal `#float_info` profile error: related-theorems name `{name}` does not exist"
  let allSurfaces :=
    profile.theoremSurfaces ++ profile.relatedTheorems.flatMap (·.surfaces)
  for surface in allSurfaces do
    if let some guarantee := surface.numericalGuarantee? then
      if guarantee.kinds.isEmpty then
        throwError
          "internal `#float_info` profile error: numerical guarantee `{surface.topic}` has no kind"
      if surface.declarations.isEmpty then
        throwError
          "internal `#float_info` profile error: numerical guarantee `{surface.topic}` has no declarations"
  let surfaces :=
    if errorsOnly then
      allSurfaces.filter fun surface => surface.numericalGuarantee?.isSome
    else
      allSurfaces
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
