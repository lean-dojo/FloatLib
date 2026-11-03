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

Compact and detailed reports from `FormatProfile` data and discovered operation capabilities. Both
styles name the inspected type and use the same sections: Format, Values, Rounding, Conversions,
Execution, Arithmetic, the theorems, and Not claimed. A profile that lists related theorems splits
the theorems into those about the type's own values and those about each type its values reach,
such as its proof model; any other profile lists them under one heading. Theorem and definition
names are rendered as constants, so they print relative to the caller's open namespaces and show
their statements on hover. Family profiles supply the theorem references and a summary of their
scope; declaration validation checks that the referenced names exist with the required kind.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

open Lean (MessageData Name)

namespace Internal

/-- Join report lines with newlines. -/
meta def joinLines (lines : List MessageData) : MessageData :=
  MessageData.joinSep lines "\n"

/-- The report header: the inspected type as the command received it, its family and standard. -/
meta def renderHeader (title subject : String) (profile : FormatProfile) : MessageData :=
  joinLines
    [ m!"{title}: {subject}"
    , m!"  family: {profile.family}"
    , m!"  standard: {profile.standard}" ]

/-- Render one labeled entry, indented under its section title. -/
meta def renderEntry (entry : InfoEntry) : MessageData :=
  m!"  {entry.label}: {entry.value}"

/-- Render one section of labeled report entries. -/
meta def renderEntries (title : String) (entries : List InfoEntry) : MessageData :=
  joinLines (m!"{title}:" :: entries.map renderEntry)

/-- The line that points from a bounded list to the detailed report. -/
private meta def moreLine (remaining : Nat) (what : String := "more") : List MessageData :=
  if remaining = 0 then [] else [m!"  ... {remaining} {what} (use `#float_info!`)"]

/-- Render a bounded section and direct users to the detailed report for the remainder. -/
meta def renderEntriesCompact
    (title : String) (entries : List InfoEntry) (limit : Nat) : MessageData :=
  let shown := entries.take limit
  joinLines (m!"{title}:" :: shown.map renderEntry ++ moreLine (entries.length - shown.length))

/--
Render proof-backed coverage of the universal operations and then the family's specialized
operations. A compact report shows at most `limit?` of the specialized ones.
-/
meta def renderArithmetic (coverage : CoreOperationCoverage)
    (specializedOperations : List InfoEntry) (limit? : Option Nat) : MessageData :=
  let available := coverage.filterMap fun (operation, supported) =>
    if supported then some operation.label else none
  let unavailable := coverage.filterMap fun (operation, supported) =>
    if supported then none else some operation.label
  let availableLine :=
    if available.isEmpty then m!"  universal ExecFloat operations: none"
    else m!"  proof-backed: {String.intercalate ", " available}"
  let unavailableLine :=
    if available.isEmpty || unavailable.isEmpty then []
    else [m!"  not provided: {String.intercalate ", " unavailable}"]
  let meaning :=
    if limit?.isNone && !available.isEmpty then
      [m!"  proof-backed means each run is proved equal to the format's reference operation"]
    else []
  let shown := match limit? with
    | some limit => specializedOperations.take limit
    | none => specializedOperations
  joinLines <|
    m!"Arithmetic:" :: availableLine :: unavailableLine ++ meaning ++ shown.map renderEntry ++
      moreLine (specializedOperations.length - shown.length) "more specialized operations"

/-- Render descriptor-level theorem applicability. -/
meta def renderApplicability : TheoremApplicability → String
  | .verifiedForType => "verified for this type"
  | .conditional condition => "conditional: " ++ condition
  | .unavailable reason => "not available for this type: " ++ reason

/-- Render descriptor-level applicability in a compact report heading. -/
private meta def renderApplicabilityStatus : TheoremApplicability → String
  | .verifiedForType => "verified"
  | .conditional _ => "conditional"
  | .unavailable _ => "not available"

/-- Render a list of names, one per line under a label, or nothing when the list is empty. -/
private meta def renderNameList (label : String) (names : List Name) : List MessageData :=
  if names.isEmpty then []
  else m!"    {label}:" :: names.map fun name => m!"      {MessageData.ofConstName name}"

/-- Render a group's leading theorem, the name a compact report shows. -/
private meta def leadingTheorem (surface : TheoremSurface) : MessageData :=
  match surface.declarations with
  | [] => m!""
  | [first] => m!": {MessageData.ofConstName first}"
  | first :: rest => m!": {MessageData.ofConstName first} and {rest.length} more"

/-- Render one theorem group, its applicability, its names, and its remaining scope. -/
meta def renderTheoremSurface (surface : TheoremSurface) : MessageData :=
  joinLines <|
    [ m!"  {surface.topic}"
    , m!"    applicability: {renderApplicability surface.applicability}" ] ++
    renderNameList "theorems" surface.declarations ++
    renderNameList "definitions" surface.definitions ++
    [ m!"    scope: {surface.scope}" ]

/-- Render one theorem group as its status, topic, and leading theorem. -/
meta def renderTheoremSurfaceCompact (surface : TheoremSurface) : MessageData :=
  m!"  [{renderApplicabilityStatus surface.applicability}] {surface.topic}{leadingTheorem surface}"

/--
The report's theorem sections, each a heading that starts with `lead` and its groups. The
profile's own groups come first; their heading names the inspected type only when the profile
lists related theorems, which declares that those groups are about the type's own values. Each
related type follows under a heading that names it and its embedding. Sections without groups are
left out.
-/
private meta def theoremSections (lead subject : String) (profile : FormatProfile) :
    List (MessageData × List TheoremSurface) :=
  let own :=
    if profile.relatedTheorems.isEmpty then m!"{lead}" else m!"{lead} about {subject} values"
  let related := profile.relatedTheorems.map fun related =>
    (m!"{lead} about {MessageData.ofConstName related.type} values, reached with \
      {MessageData.ofConstName related.embedding}", related.surfaces)
  ((own, profile.theoremSurfaces) :: related).filter fun (_, surfaces) => !surfaces.isEmpty

/-- Render every theorem section, with each group's applicability, names, and scope. -/
meta def renderTheorems (subject : String) (profile : FormatProfile) : List MessageData :=
  (theoremSections "Theorems" subject profile).map fun (title, surfaces) =>
    joinLines (m!"{title}:" :: surfaces.map renderTheoremSurface)

/-- Render the theorem sections compactly, with at most `limit` groups per section. -/
meta def renderTheoremsCompact (subject : String) (profile : FormatProfile) (limit : Nat := 5) :
    List MessageData :=
  (theoremSections "Theorems" subject profile).map fun (title, surfaces) =>
    let shown := surfaces.take limit
    joinLines <|
      m!"{title}:" :: shown.map renderTheoremSurfaceCompact ++
        moreLine (surfaces.length - shown.length)

/-- Render the explicit limits of the report's proof boundary, at most `limit?` of them. -/
meta def renderNonclaims (nonclaims : List String) (limit? : Option Nat) : MessageData :=
  let shown := match limit? with
    | some limit => nonclaims.take limit
    | none => nonclaims
  joinLines <|
    m!"Not claimed:" :: shown.map (fun claim => m!"  - {claim}") ++
      moreLine (nonclaims.length - shown.length)

/-- Render a numerical-analysis category in ordinary numerical language. -/
meta def renderNumericalAnalysisKind : NumericalAnalysisKind → String
  | .range => "range"
  | .rounding => "rounding"
  | .absoluteError => "absolute error"
  | .relativeError => "relative error"
  | .exactness => "exactness"

/-- Render one checked range, roundoff, or exactness contract with its theorems and scope. -/
meta def renderNumericalGuarantee
    (surface : TheoremSurface) (guarantee : NumericalGuarantee) : MessageData :=
  let kinds := String.intercalate ", " (guarantee.kinds.map renderNumericalAnalysisKind)
  joinLines <|
    [ m!"  [{kinds}] {surface.topic}"
    , m!"    guarantee: {guarantee.statement}"
    , m!"    applicability: {renderApplicability surface.applicability}" ] ++
    renderNameList "theorems" surface.declarations ++
    [ m!"    scope: {surface.scope}" ]

/-- Render one numerical contract as its status, kinds, topic, leading theorem, and statement. -/
meta def renderNumericalGuaranteeCompact
    (surface : TheoremSurface) (guarantee : NumericalGuarantee) : MessageData :=
  let kinds := String.intercalate ", " (guarantee.kinds.map renderNumericalAnalysisKind)
  let status := renderApplicabilityStatus surface.applicability
  joinLines
    [ m!"  [{status}; {kinds}] {surface.topic}{leadingTheorem surface}"
    , m!"    {guarantee.statement}" ]

/--
Render only numerical-analysis contracts explicitly registered by a format profile.

This mode reports type-level theorem groups. An expression-level bound additionally needs ranges
for its inputs and a theorem that composes the operations in the expression.
-/
meta def renderNumericalAnalysis (subject : String) (profile : FormatProfile) (detailed : Bool) :
    MessageData :=
  let sections := (theoremSections "Checked guarantees" subject profile).filterMap
    fun (title, surfaces) =>
      let guarantees := surfaces.filterMap fun surface =>
        surface.numericalGuarantee?.map fun guarantee => (surface, guarantee)
      if guarantees.isEmpty then none
      else
        some <| joinLines <| m!"{title}:" :: guarantees.map fun (surface, guarantee) =>
          if detailed then renderNumericalGuarantee surface guarantee
          else renderNumericalGuaranteeCompact surface guarantee
  let body :=
    if sections.isEmpty then
      [m!"No checked range, roundoff, or exactness contract is registered for this type."]
    else sections
  let moreDetail :=
    if detailed || sections.isEmpty then []
    else [m!"More detail: `#float_info! [errors] {subject}`; hover a theorem name for its statement."]
  MessageData.joinSep
    ([renderHeader "Float range and error information" subject profile] ++ body ++
      [m!"Scope: these are type-level contracts. A bound for a compound expression also needs \
        ranges for its inputs, which this report does not supply."] ++ moreDetail)
    "\n\n"

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
private meta def renderSelectedBackends (entries : List InfoEntry) : Option MessageData :=
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
    some m!"  backends: {String.intercalate "; " rendered}"

/--
Render the execution facts a caller choosing or profiling a format needs: the planning policy, two
family facts, and the selected backends.
-/
meta def renderExecutionCompact (entries : List InfoEntry) : MessageData :=
  let policy := entries.filter (·.label == "planning policy")
  let familyFacts :=
    entries.filter fun entry =>
      entry.label != "planning policy" && !entry.label.startsWith "selected " &&
        !entry.label.endsWith " decision"
  let backends := (renderSelectedBackends entries).toList
  joinLines <|
    m!"Execution:" :: policy.map renderEntry ++ (familyFacts.take 2).map renderEntry ++ backends

/-- Render the complete proof and backend audit report. -/
meta def renderFormatInfoDetailed (subject : String)
    (profile : FormatProfile) (coreOperations : CoreOperationCoverage) : MessageData :=
  MessageData.joinSep
    ([ renderHeader "Float information" subject profile
     , renderEntries "Format" profile.representation
     , renderEntries "Values" profile.values
     , renderEntries "Rounding" profile.rounding
     , renderEntries "Conversions" profile.conversions
     , renderEntries "Execution" profile.execution
     , renderArithmetic coreOperations profile.specializedOperations none
     ] ++ renderTheorems subject profile ++
     [ renderNonclaims profile.nonclaims none ])
    "\n\n"

/-- Render the normal, user-facing numerical-format summary. -/
meta def renderFormatInfoCompact (subject : String)
    (profile : FormatProfile) (coreOperations : CoreOperationCoverage) : MessageData :=
  MessageData.joinSep
    ([ renderHeader "Float information" subject profile
     , renderEntriesCompact "Format" profile.representation 6
     , renderEntriesCompact "Values" profile.values 4
     , renderEntriesCompact "Rounding" profile.rounding 3
     , renderEntriesCompact "Conversions" profile.conversions 5
     , renderExecutionCompact profile.execution
     , renderArithmetic coreOperations profile.specializedOperations (some 4)
     ] ++ renderTheoremsCompact subject profile ++
     [ renderNonclaims profile.nonclaims (some 1)
     , m!"More detail: `#float_info! {subject}`; hover a theorem name for its statement." ])
    "\n\n"

end Internal

/--
Render a numerical-format report according to the command option. `subject` names the inspected
type in the header and the theorem sections.

Normal `#float_info` is intentionally concise. `#float_info!` enables the complete theorem and
backend audit without maintaining a second family-specific inspector.
-/
meta def renderFormatInfo (subject : String)
    (profile : FormatProfile) (coreOperations : CoreOperationCoverage) :
    Lean.CoreM MessageData := do
  let options ← Lean.getOptions
  let errors := floatlib.floatInfo.errors.get options
  let detailed := floatlib.floatInfo.full.get options
  pure <|
    if errors then
      Internal.renderNumericalAnalysis subject profile detailed
    else if detailed then
      Internal.renderFormatInfoDetailed subject profile coreOperations
    else
      Internal.renderFormatInfoCompact subject profile coreOperations

end FloatLib.Floats.ExecFloat
