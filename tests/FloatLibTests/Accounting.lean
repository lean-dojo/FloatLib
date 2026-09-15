/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Init

/-!
# Test results

Count failed checks and assemble their reports. `ReportSection.ofRows` derives the printed
counters and the exit-status total from the same rows.
-/

@[expose] public section

namespace FloatLibTests.Accounting

universe u v w x y z

/-- Convert one Boolean check into a zero-or-one failure count. -/
@[inline] def failureCount (passes : Bool) : Nat :=
  if passes then 0 else 1

/-- Count failed Boolean checks from any container that supports `for`. -/
@[inline] def countFailures {ρ : Type u} [ForIn Id ρ Bool] (checks : ρ) : Nat := Id.run do
  let mut failures := 0
  for check in checks do
    failures := failures + failureCount check
  return failures

/-- Count values that fail a predicate, independently of their container. -/
@[inline] def countWhereFailures {ρ : Type u} {α : Type v} [ForIn Id ρ α]
    (values : ρ) (passes : α → Bool) : Nat := Id.run do
  let mut failures := 0
  for value in values do
    failures := failures + failureCount (passes value)
  return failures

/-- Count failed checks over the Cartesian product of two containers. -/
@[inline] def countPairFailures
    {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    [ForIn Id ρ α] [ForIn Id σ β]
    (left : ρ) (right : σ) (passes : α → β → Bool) : Nat := Id.run do
  let mut failures := 0
  for x in left do
    for y in right do
      failures := failures + failureCount (passes x y)
  return failures

/-- Count failed checks over the Cartesian product of three containers. -/
@[inline] def countTripleFailures
    {ρ : Type u} {σ : Type v} {τ : Type w}
    {α : Type x} {β : Type y} {γ : Type z}
    [ForIn Id ρ α] [ForIn Id σ β] [ForIn Id τ γ]
    (first : ρ) (second : σ) (third : τ)
    (passes : α → β → γ → Bool) : Nat := Id.run do
  let mut failures := 0
  for x in first do
    for y in second do
      for z in third do
        failures := failures + failureCount (passes x y z)
  return failures

/-- Sum named failure counters from any ordered container supported by `for`. -/
@[inline] def namedFailureTotal {ρ : Type u} [ForIn Id ρ (String × Nat)]
    (rows : ρ) : Nat := Id.run do
  let mut total := 0
  for row in rows do
    total := total + row.2
  return total

/-- Render named failure counters followed by their aggregate `TOTAL` row. -/
def renderFailureReport {ρ : Type u} [ForIn Id ρ (String × Nat)]
    (rows : ρ) : String := Id.run do
  let mut total := 0
  let mut lines : Array String := #[]
  for row in rows do
    total := total + row.2
    lines := lines.push s!"{row.1}: {row.2}"
  lines := lines.push s!"TOTAL: {total}"
  return String.intercalate "\n" lines.toList

/-- A named report with the failure count used to set the process status. -/
structure ReportSection where
  title : String
  body : String
  failures : Nat

/-- Build a report whose printed counters and failure total come from the same rows. -/
def ReportSection.ofRows {ρ : Type u} [ForIn Id ρ (String × Nat)]
    (title : String) (rows : ρ) : ReportSection where
  title
  body := renderFailureReport rows
  failures := namedFailureTotal rows

/-- Sum the failure counts carried by a collection of report sections. -/
@[inline] def sectionFailureTotal {ρ : Type u} [ForIn Id ρ ReportSection]
    (sections : ρ) : Nat := Id.run do
  let mut total := 0
  for entry in sections do
    total := total + entry.failures
  return total

/-- Render titled validation sections and append the aggregate failure count. -/
def renderSectionedReport {ρ : Type u} [ForIn Id ρ ReportSection]
    (sections : ρ) : String := Id.run do
  let mut total := 0
  let mut blocks : Array String := #[]
  for entry in sections do
    total := total + entry.failures
    blocks := blocks.push s!"== {entry.title} ==\n{entry.body}"
  blocks := blocks.push s!"== aggregate ==\nTOTAL: {total}"
  return String.intercalate "\n\n" blocks.toList

/-- Return a successful process code exactly when a validation suite has no failures. -/
@[inline] def exitCode (failures : Nat) : UInt32 :=
  if failures = 0 then 0 else 1

/-- Print the reports and return a nonzero status if any section has failures. -/
def runSectionedReport {ρ : Type u} [ForIn Id ρ ReportSection]
    (sections : ρ) : IO UInt32 := do
  IO.println <| renderSectionedReport sections
  pure <| exitCode (sectionFailureTotal sections)

end FloatLibTests.Accounting
