/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info.Profile
public meta import FloatLib.Floats.ExecFloat.Info.Profile
public import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata

/-!
# Formatting inspection reports

Compact and detailed reports from `FormatProfile` data and discovered operation capabilities.
Family profiles supply theorem references and hypothesis summaries; declaration validation checks
that the referenced names exist with the required kind. Both report styles use the same data.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

namespace Internal

/-- Render one section of labeled report entries. -/
meta def renderEntries (title : String) (entries : List InfoEntry) : String :=
  title ++ ":\n" ++
    String.intercalate "\n" (entries.map fun entry => s!"  {entry.label}: {entry.value}")

/-- Render a bounded section and direct users to the detailed report for the remainder. -/
meta def renderEntriesCompact
    (title : String) (entries : List InfoEntry) (limit : Nat) : String :=
  let shown := entries.take limit
  let remaining := entries.length - shown.length
  let lines := shown.map fun entry => s!"  {entry.label}: {entry.value}"
  let lines :=
    if remaining = 0 then
      lines
    else
      lines ++ [s!"  ... {remaining} more (use `#float_info!`)"]
  title ++ ":\n" ++ String.intercalate "\n" lines

/-- Render one proof-backed capability status. -/
meta def renderCapability (name : String) (available : Bool) : String :=
  let result :=
    if available then
      "proof-backed: execution is proved equal to the format's reference definition"
    else
      "not provided"
  s!"  {name}: {result}"

/-- Render proof-backed coverage of the universal arithmetic operations. -/
meta def renderCoreOperations (coverage : CoreOperationCoverage) : String :=
  "Core executable operations:\n" ++ String.intercalate "\n"
    (coverage.map fun (operation, available) =>
      renderCapability operation.label available)

/-- Render executable APIs that intentionally live outside the universal scalar interface. -/
meta def renderSpecializedOperations (operations : List InfoEntry) : String :=
  renderEntries "Specialized executable operations" operations

/-- Render descriptor-level theorem applicability. -/
meta def renderApplicability : TheoremApplicability → String
  | .verifiedForType => "verified for this configured type"
  | .conditional condition => "conditional: " ++ condition
  | .unavailable reason => "not available for this configured type: " ++ reason

/-- Render descriptor-level applicability in a compact report heading. -/
private meta def renderApplicabilityStatus : TheoremApplicability → String
  | .verifiedForType => "verified"
  | .conditional _ => "conditional"
  | .unavailable _ => "not available"

/-- Omit a family namespace prefix while retaining enough of a declaration name to find it. -/
private meta def displayDeclarationName
    (declarationPrefix : String) (declaration : Lean.Name) : String :=
  let fullName := declaration.toString
  if fullName.startsWith declarationPrefix then
    (fullName.drop declarationPrefix.length).toString
  else
    fullName

/-- Render one semantic theorem group, its applicability, and its remaining scope. -/
meta def renderTheoremSurface
    (declarationPrefix : String) (surface : TheoremSurface) : String :=
  let definitions :=
    if surface.definitions.isEmpty then
      ""
    else
      "    listed definitions:\n" ++
        String.intercalate "\n"
          (surface.definitions.map fun definition =>
            "      - " ++ displayDeclarationName declarationPrefix definition) ++
        "\n"
  "  " ++ surface.topic ++ "\n" ++
    "    applicability: " ++ renderApplicability surface.applicability ++ "\n" ++
    "    checked declarations:\n" ++
      String.intercalate "\n"
        (surface.declarations.map fun declaration =>
          "      - " ++ displayDeclarationName declarationPrefix declaration) ++
      "\n" ++
    definitions ++
    "    scope: " ++ surface.scope

/-- Render all semantic theorem groups in a profile. -/
meta def renderTheoremSurfaces
    (declarationPrefix : String) (surfaces : List TheoremSurface) : String :=
  "Semantic theorem surfaces:\n" ++
    String.intercalate "\n" (surfaces.map (renderTheoremSurface declarationPrefix))

/-- Render the explicit limits of the report's proof boundary. -/
meta def renderNonclaims (nonclaims : List String) : String :=
  "Not claimed by this report:\n" ++
    String.intercalate "\n" (nonclaims.map fun claim => "  - " ++ claim)

/-- Render a numerical-analysis category in ordinary numerical language. -/
meta def renderNumericalAnalysisKind : NumericalAnalysisKind → String
  | .range => "range"
  | .rounding => "rounding"
  | .absoluteError => "absolute error"
  | .relativeError => "relative error"
  | .exactness => "exactness"

/-- Render one checked range, roundoff, or exactness contract. -/
meta def renderNumericalGuarantee
    (declarationPrefix : String)
    (surface : TheoremSurface)
    (guarantee : NumericalGuarantee) : String :=
  let kinds :=
    String.intercalate ", " (guarantee.kinds.map renderNumericalAnalysisKind)
  let declarations :=
    String.intercalate "\n" <|
      surface.declarations.map fun declaration =>
        "      - " ++ displayDeclarationName declarationPrefix declaration
  "  [" ++ kinds ++ "] " ++ surface.topic ++ "\n" ++
    "    guarantee: " ++ guarantee.statement ++ "\n" ++
    "    applicability: " ++ renderApplicability surface.applicability ++ "\n" ++
    "    checked declarations:\n" ++ declarations ++ "\n" ++
    "    hypotheses: " ++ surface.scope

/-- Render one numerical contract without the declaration inventory or full hypothesis text. -/
meta def renderNumericalGuaranteeCompact
    (surface : TheoremSurface) (guarantee : NumericalGuarantee) : String :=
  let kinds :=
    String.intercalate ", " (guarantee.kinds.map renderNumericalAnalysisKind)
  let status := renderApplicabilityStatus surface.applicability
  "  [" ++ status ++ "; " ++ kinds ++ "] " ++ surface.topic ++ "\n" ++
    "    " ++ guarantee.statement

/--
Render only numerical-analysis contracts explicitly registered by a format profile.

This mode reports type-level theorem surfaces. An expression-level bound additionally needs ranges
for its inputs and a theorem that composes the operations in the expression.
-/
meta def renderNumericalAnalysis (profile : FormatProfile) (detailed : Bool) : String :=
  let guarantees :=
    profile.theoremSurfaces.filterMap fun surface =>
      surface.numericalGuarantee?.map fun guarantee => (surface, guarantee)
  let body :=
    if guarantees.isEmpty then
      "No checked range, roundoff, or exactness contract is registered for this carrier."
    else if detailed then
      "Checked numerical guarantees:\n" ++
        String.intercalate "\n"
          (guarantees.map fun (surface, guarantee) =>
            renderNumericalGuarantee profile.declarationPrefix surface guarantee)
    else
      "Checked numerical guarantees:\n" ++
        String.intercalate "\n"
          (guarantees.map fun (surface, guarantee) =>
            renderNumericalGuaranteeCompact surface guarantee)
  let moreDetail :=
    if detailed || guarantees.isEmpty then
      []
    else
      ["More detail: `#float_info! [errors] YourType`"]
  String.intercalate "\n\n" <|
    [ "Float range and error information: " ++ profile.family ++
        "\n  standard: " ++ profile.standard
    , body
    , "Command scope:\n" ++
        "  This report exposes type-level contracts; detailed mode includes full hypotheses.\n" ++
        "  A compound-expression range needs input ranges; no such ranges are invented here."
    ] ++ moreDetail

/-- Render the complete proof and backend audit report. -/
meta def renderFormatInfoDetailed
    (profile : FormatProfile) (coreOperations : CoreOperationCoverage) : String :=
  let specialized :=
    if profile.specializedOperations.isEmpty then
      []
    else
      [renderSpecializedOperations profile.specializedOperations]
  String.intercalate "\n\n"
    ([ "Float information\n  family: " ++ profile.family ++
        "\n  standard: " ++ profile.standard
    , renderEntries "Representation" profile.representation
    , renderEntries "Representable values" profile.values
    , renderEntries "Rounding" profile.rounding
    , renderEntries "Conversions" profile.conversions
    , renderEntries "Execution" profile.execution
    , renderCoreOperations coreOperations
    ] ++ specialized ++
    [ renderTheoremSurfaces profile.declarationPrefix profile.theoremSurfaces
    , renderNonclaims profile.nonclaims
    ])

/-- Render one theorem group as a concise proof-coverage statement. -/
meta def renderTheoremSurfaceCompact (surface : TheoremSurface) : String :=
  let status := renderApplicabilityStatus surface.applicability
  s!"  [{status}] {surface.topic}"

/-- Render the proof topics without flooding the InfoView with declaration inventories. -/
meta def renderTheoremSurfacesCompact
    (surfaces : List TheoremSurface) (limit : Nat := 4) : String :=
  let shown := surfaces.take limit
  let remaining := surfaces.length - shown.length
  let lines := shown.map renderTheoremSurfaceCompact
  let lines :=
    if remaining = 0 then
      lines
    else
      lines ++ [s!"  ... {remaining} more proof topics (use `#float_info!`)"]
  "Proof coverage:\n" ++ String.intercalate "\n" lines

/-- Render compact proof-backed coverage of the universal arithmetic interface. -/
meta def renderArithmeticCompact
    (coverage : CoreOperationCoverage) (specializedOperations : List InfoEntry) : String :=
  let available := coverage.filterMap fun (operation, supported) =>
    if supported then some operation.label else none
  let unavailable := coverage.filterMap fun (operation, supported) =>
    if supported then none else some operation.label
  let availableLine :=
    if available.isEmpty then
      "  proof-backed: none"
    else
      "  proof-backed: " ++ String.intercalate ", " available
  let unavailableLine :=
    if unavailable.isEmpty then
      []
    else
      ["  universal unavailable: " ++ String.intercalate ", " unavailable]
  let specializedLimit := 4
  let shownSpecialized := specializedOperations.take specializedLimit
  let specializedLines :=
    shownSpecialized.map fun operation =>
      s!"  specialized {operation.label}: {operation.value}"
  let remainingSpecialized := specializedOperations.length - shownSpecialized.length
  let specializedLines :=
    if remainingSpecialized = 0 then
      specializedLines
    else
      specializedLines ++
        [s!"  ... {remainingSpecialized} more specialized operations (use `#float_info!`)"]
  "Arithmetic:\n" ++
    String.intercalate "\n" (availableLine :: unavailableLine ++ specializedLines)

/-- Add one selected operation to the group using the same backend description. -/
private meta def insertBackendGroup
    (groups : List (List String × String)) (operation backend : String) :
    List (List String × String) :=
  match groups with
  | [] => [([operation], backend)]
  | (operations, existingBackend) :: rest =>
      if existingBackend = backend then
        (operations ++ [operation], existingBackend) :: rest
      else
        (operations, existingBackend) :: insertBackendGroup rest operation backend

/--
Group operations that selected the same backend.

This turns six repetitive planner rows into statements such as
`add, sub, mul, div, sqrt, fma = fixed-format specialization`.
-/
private meta def renderSelectedBackends (entries : List InfoEntry) : Option String :=
  let selected := entries.filter fun entry => entry.label.startsWith "selected "
  if selected.isEmpty then
    none
  else
    let groups :=
      selected.foldl
        (fun groups entry =>
          let operation := (entry.label.drop "selected ".length).toString
          insertBackendGroup groups operation entry.value)
        []
    let rendered := groups.map fun (operations, backend) =>
      String.intercalate ", " operations ++ " = " ++ backend
    some ("  backends: " ++ String.intercalate "; " rendered)

/-- Render only execution facts useful to a caller choosing or profiling a format. -/
meta def renderExecutionCompact (entries : List InfoEntry) : String :=
  let familyFacts :=
    entries.filter fun entry =>
      !entry.label.startsWith "selected " && !entry.label.endsWith " decision"
  let factLines :=
    (familyFacts.take 2).map fun entry => s!"  {entry.label}: {entry.value}"
  let lines :=
    match renderSelectedBackends entries with
    | some backends => factLines ++ [backends]
    | none => factLines
  "Execution:\n" ++ String.intercalate "\n" lines

/-- Render the normal, user-facing numerical-format summary. -/
meta def renderFormatInfoCompact
    (profile : FormatProfile) (coreOperations : CoreOperationCoverage) : String :=
  String.intercalate "\n\n"
    [ "Float information: " ++ profile.family ++
        "\n  standard: " ++ profile.standard
    , renderEntriesCompact "Format" profile.representation 6
    , renderEntriesCompact "Values" profile.values 4
    , renderEntriesCompact "Rounding" profile.rounding 2
    , renderEntriesCompact "Conversions" profile.conversions 5
    , renderExecutionCompact profile.execution
    , renderArithmeticCompact coreOperations profile.specializedOperations
    , renderTheoremSurfacesCompact profile.theoremSurfaces
    , renderEntriesCompact "Proof boundary"
        (profile.nonclaims.map fun claim => ⟨"not claimed", claim⟩) 1
    , "More detail: `#float_info!`"
    ]

end Internal

/--
Render a numerical-format report according to the command option.

Normal `#float_info` is intentionally concise. `#float_info!` enables the complete theorem and
backend audit without maintaining a second family-specific inspector.
-/
meta def renderFormatInfo
    (profile : FormatProfile) (coreOperations : CoreOperationCoverage) : Lean.CoreM String := do
  let options ← Lean.getOptions
  let errors := floatlib.floatInfo.errors.get options
  let detailed := floatlib.floatInfo.full.get options
  pure <|
    if errors then
      Internal.renderNumericalAnalysis profile detailed
    else if detailed then
      Internal.renderFormatInfoDetailed profile coreOperations
    else
      Internal.renderFormatInfoCompact profile coreOperations

end FloatLib.Floats.ExecFloat
