/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Scoring

/-!
# Backend-selection reports

Inspectable explanations of deterministic selector decisions. Reports are intended for
development tools and calibration; executable arithmetic does not construct them.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

/-- Why one candidate appears in a selector decision report. -/
inductive AssessmentStatus where
  | selected
  | rejectedResidentMemory (required limit : Nat)
  | rejectedTemporaryMemory (required limit : Nat)
  | notPreferred
  deriving DecidableEq, Repr

/-- Disposition of one candidate in a selector report. -/
structure Assessment where
  /-- Candidate whose disposition is reported. -/
  candidate : Candidate
  /-- Reason the candidate was selected or rejected. -/
  status : AssessmentStatus
  deriving DecidableEq, Repr

/--
Explain the candidate at position `index` of a candidate list whose selected member is at
position `selectedIndex`.

Candidates are identified by position rather than by comparing estimates, so identical estimates
do not create multiple selected assessments. The selected index takes precedence over memory
limits: the mandatory baseline may be selected even when it exceeds either cap. Memory rejection
describes only unselected candidates.
-/
def Candidate.assess
    (policy : Policy) (selectedIndex index : Nat) (candidate : Candidate) : Assessment :=
  let status :=
    if index = selectedIndex then
      .selected
    else if policy.maxResidentBytes < candidate.residentBytes then
      .rejectedResidentMemory candidate.residentBytes policy.maxResidentBytes
    else if policy.maxTemporaryBytes < candidate.temporaryBytes then
      .rejectedTemporaryMemory candidate.temporaryBytes policy.maxTemporaryBytes
    else
      .notPreferred
  {
    candidate
    status
  }

/-- The selected candidate is reported as selected, regardless of the policy's memory limits. -/
@[simp] theorem Candidate.assess_selected
    (policy : Policy) (index : Nat) (candidate : Candidate) :
    (candidate.assess policy index index).status = .selected := by
  simp [Candidate.assess]

/--
Run the selection fold while tracking the position of the incumbent in `candidates.toList`.

Alternatives occupy positions `0` through `alternatives.length - 1` and the baseline occupies
position `alternatives.length`, matching `CandidateSet.toList`.
-/
def selectCandidateIndexed
    (policy : Policy) (candidates : CandidateSet Candidate) : Candidate × Nat :=
  candidates.alternatives.zipIdx.foldl
    (fun incumbent candidate =>
      if candidate.1.admissible policy && candidate.1.better policy incumbent.1 then
        candidate
      else
        incumbent)
    (candidates.baseline, candidates.alternatives.length)

/-- Position in `candidates.toList` of the candidate returned by `selectCandidate`. -/
def selectedIndex (policy : Policy) (candidates : CandidateSet Candidate) : Nat :=
  (selectCandidateIndexed policy candidates).2

private theorem foldl_indexed_fst (policy : Policy) (alternatives : List Candidate)
    (incumbent : Candidate × Nat) (start : Nat) :
    ((alternatives.zipIdx start).foldl
      (fun incumbent candidate =>
        if candidate.1.admissible policy && candidate.1.better policy incumbent.1 then
          candidate
        else
          incumbent)
      incumbent).1 =
      alternatives.foldl (consider policy) incumbent.1 := by
  induction alternatives generalizing incumbent start with
  | nil => rfl
  | cons candidate alternatives ih =>
      simp only [List.zipIdx_cons, List.foldl_cons]
      rw [ih]
      simp only [consider]
      split <;> rfl

/-- The tracked fold selects the same candidate as `selectCandidate`. -/
@[simp] theorem selectCandidateIndexed_fst
    (policy : Policy) (candidates : CandidateSet Candidate) :
    (selectCandidateIndexed policy candidates).1 = selectCandidate policy candidates :=
  foldl_indexed_fst policy candidates.alternatives _ 0

/-- Inspectable explanation of one static selection calculation. -/
structure SelectionReport where
  /-- Policy under which all estimates were evaluated. -/
  policy : Policy
  /-- Candidate chosen from the mandatory baseline and admissible alternatives. -/
  selected : Candidate
  /-- Assessment of every alternative followed by the mandatory baseline. -/
  assessments : List Assessment
  deriving DecidableEq, Repr

/--
Compute the same result as `selectCandidate` together with every accepted or rejected alternative.

This is for inspection and calibration; arithmetic projects the stored `Certified` implementation
and never constructs a report on the hot path.
-/
def selectionReport
    (policy : Policy) (candidates : CandidateSet Candidate) : SelectionReport :=
  let (selected, selectedIndex) := selectCandidateIndexed policy candidates
  {
    policy
    selected
    assessments :=
      candidates.toList.zipIdx.map fun (candidate, index) =>
        Candidate.assess policy selectedIndex index candidate
  }

/-- The reported winner is the candidate chosen by `selectCandidate`. -/
@[simp] theorem selectionReport_selected
    (policy : Policy) (candidates : CandidateSet Candidate) :
    (selectionReport policy candidates).selected = selectCandidate policy candidates :=
  selectCandidateIndexed_fst policy candidates

end FloatLib.Floats.ExecFloat.Backend
