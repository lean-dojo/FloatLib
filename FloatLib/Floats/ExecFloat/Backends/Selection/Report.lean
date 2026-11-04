/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Scoring

/-!
# Backend-selection reports

These are inspectable explanations of the deterministic selector's decisions. They're meant for
development tools and calibration, and executable arithmetic never builds them.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

/--
Why one candidate appears in a selector decision report.

The memory statuses say that an unselected candidate exceeds a cap. The selector skips every
alternative above a cap, but it never tests the mandatory baseline against the caps, so for an
unselected baseline these statuses name a cap it exceeds and not the reason it lost.
-/
inductive AssessmentStatus where
  /-- The selector returned this candidate. -/
  | selected
  /--
  The candidate is unselected and needs `required` resident bytes, above the policy's `limit`.
  -/
  | rejectedResidentMemory (required limit : Nat)
  /--
  The candidate is unselected, fits the resident cap, and needs `required` temporary bytes, above
  the policy's `limit`.
  -/
  | rejectedTemporaryMemory (required limit : Nat)
  /-- The candidate is unselected and fits both caps: it lost on score or tie-break. -/
  | notPreferred
  deriving DecidableEq, Repr

/-- Disposition of one candidate in a selector report. -/
structure Assessment where
  /-- Candidate whose disposition is reported. -/
  candidate : Candidate
  /-- Whether the candidate was selected, and for an unselected one the first memory cap it
  exceeds, if any (see `Candidate.assess`). -/
  status : AssessmentStatus
  deriving DecidableEq, Repr

/--
Explain the candidate at position `index` of a candidate list whose selected member is at position
`selectedIndex`, under `policy`.

Candidates are identified by position, so identical estimates don't create several selected
assessments. The selected index takes precedence over memory limits, which means the mandatory
baseline may be selected even when it exceeds either cap. Memory rejection describes only unselected
candidates and records that the candidate exceeds that cap
(`Candidate.assess_eq_rejectedResidentMemory_iff`,
`Candidate.assess_eq_rejectedTemporaryMemory_iff`). For an alternative, that's why the selector
skipped it (`Candidate.admissible_eq_false_of_assess_rejected`). The selector never applies the caps
to the baseline (`selectCandidate`), so an unselected baseline above a cap lost on score or
tie-break, even though its status names the cap.
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
The resident-memory rejection is reported exactly for an unselected candidate above the resident
cap, and it records the candidate's resident bytes and the cap.
-/
theorem Candidate.assess_eq_rejectedResidentMemory_iff
    (policy : Policy) (selectedIndex index : Nat) (candidate : Candidate)
    (required limit : Nat) :
    (candidate.assess policy selectedIndex index).status =
        .rejectedResidentMemory required limit ↔
      index ≠ selectedIndex ∧ policy.maxResidentBytes < candidate.residentBytes ∧
        required = candidate.residentBytes ∧ limit = policy.maxResidentBytes := by
  unfold Candidate.assess
  by_cases hindex : index = selectedIndex
  · simp [hindex]
  · by_cases hresident : policy.maxResidentBytes < candidate.residentBytes
    · simp [hindex, hresident, eq_comm]
    · by_cases htemporary : policy.maxTemporaryBytes < candidate.temporaryBytes <;>
        simp [hindex, hresident, htemporary]

/--
The temporary-memory rejection is reported exactly for an unselected candidate within the
resident cap and above the temporary cap, and it records the candidate's temporary bytes and the
cap.
-/
theorem Candidate.assess_eq_rejectedTemporaryMemory_iff
    (policy : Policy) (selectedIndex index : Nat) (candidate : Candidate)
    (required limit : Nat) :
    (candidate.assess policy selectedIndex index).status =
        .rejectedTemporaryMemory required limit ↔
      index ≠ selectedIndex ∧ candidate.residentBytes ≤ policy.maxResidentBytes ∧
        policy.maxTemporaryBytes < candidate.temporaryBytes ∧
        required = candidate.temporaryBytes ∧ limit = policy.maxTemporaryBytes := by
  unfold Candidate.assess
  by_cases hindex : index = selectedIndex
  · simp [hindex]
  · by_cases hresident : policy.maxResidentBytes < candidate.residentBytes
    · simp [hindex, hresident, Nat.not_le.mpr hresident]
    · by_cases htemporary : policy.maxTemporaryBytes < candidate.temporaryBytes
      · simp [hindex, hresident, htemporary, Nat.le_of_not_lt hresident, eq_comm]
      · simp [hindex, hresident, htemporary]

/--
A candidate reported as rejected for memory is not admissible, so `consider` never lets it
replace an incumbent. For an alternative this is why the selector skipped it.
-/
theorem Candidate.admissible_eq_false_of_assess_rejected
    (policy : Policy) (selectedIndex index : Nat) (candidate : Candidate)
    (required limit : Nat)
    (hrejected :
      (candidate.assess policy selectedIndex index).status =
          .rejectedResidentMemory required limit ∨
        (candidate.assess policy selectedIndex index).status =
          .rejectedTemporaryMemory required limit) :
    candidate.admissible policy = false := by
  rcases hrejected with hresident | htemporary
  · obtain ⟨-, hover, -⟩ :=
      (Candidate.assess_eq_rejectedResidentMemory_iff policy selectedIndex index candidate
        required limit).mp hresident
    simp [Candidate.admissible, Nat.not_le.mpr hover]
  · obtain ⟨-, -, hover, -⟩ :=
      (Candidate.assess_eq_rejectedTemporaryMemory_iff policy selectedIndex index candidate
        required limit).mp htemporary
    simp [Candidate.admissible, Nat.not_le.mpr hover]

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

private theorem foldl_indexed_mem (policy : Policy) (entries : List (Candidate × Nat))
    (incumbent : Candidate × Nat) :
    entries.foldl
        (fun incumbent candidate =>
          if candidate.1.admissible policy && candidate.1.better policy incumbent.1 then
            candidate
          else
            incumbent)
        incumbent ∈ incumbent :: entries := by
  induction entries generalizing incumbent with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons]
      split
      · exact List.mem_cons_of_mem _ (ih entry)
      · rcases List.mem_cons.mp (ih incumbent) with hincumbent | hentries
        · rw [hincumbent]
          simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hentries)

/--
`selectedIndex` is a position of `candidates.toList`, and the candidate there is the one
`selectCandidate` returns.
-/
theorem getElem?_toList_selectedIndex
    (policy : Policy) (candidates : CandidateSet Candidate) :
    candidates.toList[selectedIndex policy candidates]? =
      some (selectCandidate policy candidates) := by
  rw [← selectCandidateIndexed_fst]
  have hmem : selectCandidateIndexed policy candidates ∈
      (candidates.baseline, candidates.alternatives.length) ::
        candidates.alternatives.zipIdx :=
    foldl_indexed_mem policy _ _
  unfold selectedIndex CandidateSet.toList
  rcases List.mem_cons.mp hmem with hbaseline | halternative
  · rw [hbaseline]
    exact List.getElem?_concat_length
  · have hget := List.mem_zipIdx_iff_getElem?.mp halternative
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hget
    rw [List.getElem?_append_left hlt]
    exact hget

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
Compute the same result as `selectCandidate` under `policy`, together with an assessment of every
candidate in `candidates`: the alternatives in order, then the baseline.

It's meant for inspection and calibration. Arithmetic projects the stored `Certified` implementation
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

private theorem selectionReport_assessments
    (policy : Policy) (candidates : CandidateSet Candidate) :
    (selectionReport policy candidates).assessments =
      candidates.toList.zipIdx.map fun (candidate, index) =>
        Candidate.assess policy (selectedIndex policy candidates) index candidate :=
  rfl

/-- The report assesses every alternative in order, followed by the mandatory baseline. -/
theorem selectionReport_map_candidate
    (policy : Policy) (candidates : CandidateSet Candidate) :
    (selectionReport policy candidates).assessments.map Assessment.candidate =
      candidates.toList := by
  rw [selectionReport_assessments, List.map_map]
  exact List.zipIdx_map_fst 0 candidates.toList

private theorem filter_zipIdx_snd_eq {α : Type} (list : List α) (start index : Nat) (value : α)
    (h : list[index]? = some value) :
    (list.zipIdx start).filter (fun entry => entry.2 = start + index) =
      [(value, start + index)] := by
  induction list generalizing start index with
  | nil => simp at h
  | cons head tail ih =>
      rw [List.zipIdx_cons, List.filter_cons]
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [Nat.add_zero, decide_true, ite_true, List.cons.injEq, true_and]
          rw [List.filter_eq_nil_iff]
          intro entry hentry
          have := List.le_snd_of_mem_zipIdx hentry
          simp only [decide_eq_true_eq]
          omega
      | succ index =>
          have hne : ¬start = start + (index + 1) := by omega
          simp only [hne, decide_false, Bool.false_eq_true, ite_false]
          rw [show start + (index + 1) = start + 1 + index by omega]
          exact ih (start + 1) index (by simpa using h)

/--
Exactly one assessment has status `.selected`, and its candidate is the one `selectCandidate`
returns. Status is decided by position, so a candidate whose estimate equals the winner's is not
also reported as selected.
-/
theorem selectionReport_filter_selected
    (policy : Policy) (candidates : CandidateSet Candidate) :
    (selectionReport policy candidates).assessments.filter (·.status = .selected) =
      [{ candidate := selectCandidate policy candidates, status := .selected }] := by
  rw [selectionReport_assessments, List.filter_map]
  have hstatus :
      ((fun assessment : Assessment => decide (assessment.status = .selected)) ∘
          fun (candidate, index) =>
            Candidate.assess policy (selectedIndex policy candidates) index candidate) =
        fun entry : Candidate × Nat => decide (entry.2 = 0 + selectedIndex policy candidates) := by
    funext ⟨candidate, index⟩
    simp only [Function.comp_apply, Candidate.assess, Nat.zero_add]
    by_cases hindex : index = selectedIndex policy candidates
    · simp [hindex]
    · simp only [hindex, ite_false, decide_false]
      repeat' split
      all_goals simp
  rw [hstatus, filter_zipIdx_snd_eq _ 0 _ _ (getElem?_toList_selectedIndex policy candidates)]
  simp [Candidate.assess]

end FloatLib.Floats.ExecFloat.Backend
