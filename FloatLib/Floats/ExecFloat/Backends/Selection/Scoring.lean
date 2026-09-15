/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Policy
public import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata

/-!
# Deterministic backend scoring

The selector combines a warm-call estimate with setup and resident-memory costs over an expected
number of calls. Optional candidates must satisfy the memory ceilings before cost comparison;
the mandatory baseline remains available regardless of its estimate. A fixed tie-break order
makes selection deterministic for a given ordered candidate set.

These values are a transparent planning model, not benchmark measurements and not correctness
evidence. Families calibrate relative costs for their candidates; users can inspect the resulting
break-even point and replace the policy without changing the specification proved by those
candidates.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

/-- Number of policy-sized memory blocks needed to cover `bytes`. -/
@[inline] def Policy.memoryBlocks (policy : Policy) (bytes : Nat) : Nat :=
  if policy.memoryBlockBytes = 0 then
    bytes
  else
    (bytes + policy.memoryBlockBytes - 1) / policy.memoryBlockBytes

/-- No bytes occupy no memory blocks under any policy. -/
theorem Policy.memoryBlocks_zero (policy : Policy) : policy.memoryBlocks 0 = 0 := by
  unfold Policy.memoryBlocks
  split
  · rfl
  · exact Nat.div_eq_of_lt (by omega)

/-- Estimated cost of one call after initialization. -/
@[inline] def Candidate.warmCost (policy : Policy) (candidate : Candidate) : Nat :=
  candidate.steadyCost + candidate.marshallingCost +
    policy.allocationPenalty * candidate.allocations +
    policy.temporaryBlockPenalty * policy.memoryBlocks candidate.temporaryBytes

/-- Estimated one-time setup and persistent-memory cost. -/
@[inline] def Candidate.coldCost (policy : Policy) (candidate : Candidate) : Nat :=
  candidate.setupCost +
    policy.allocationPenalty * candidate.setupAllocations +
    policy.residentBlockPenalty * policy.memoryBlocks candidate.residentBytes

/-- Workload-weighted total score minimized by the selector. -/
@[inline] def Candidate.score (policy : Policy) (candidate : Candidate) : Nat :=
  policy.expectedCalls * candidate.warmCost policy + candidate.coldCost policy

/--
Smallest estimated call count at which `candidate` catches a slower-warm `incumbent`.

The result is absent when `candidate` has no warm-call advantage. A result of zero means the
candidate also has no additional cold cost.
-/
def Candidate.breakEvenCalls
    (policy : Policy) (candidate incumbent : Candidate) : Option Nat :=
  let candidateWarm := candidate.warmCost policy
  let incumbentWarm := incumbent.warmCost policy
  if candidateWarm < incumbentWarm then
    let advantage := incumbentWarm - candidateWarm
    let extraCold := candidate.coldCost policy - incumbent.coldCost policy
    some ((extraCold + advantage - 1) / advantage)
  else
    none

/-- Whether a candidate satisfies the selector's hard resource constraints. -/
@[inline] def Candidate.admissible (policy : Policy) (candidate : Candidate) : Bool :=
  candidate.residentBytes ≤ policy.maxResidentBytes &&
    candidate.temporaryBytes ≤ policy.maxTemporaryBytes

/--
Resolve an equal total score using lower hot-path and memory overhead.

The final kernel-class rank gives deterministic results across algorithm families. If every key is
equal, the incumbent wins, so a family can deliberately order otherwise identical implementations.
-/
@[inline] def Candidate.preferOnEqualScore
    (policy : Policy) (candidate incumbent : Candidate) : Bool :=
  if candidate.warmCost policy != incumbent.warmCost policy then
    candidate.warmCost policy < incumbent.warmCost policy
  else if candidate.marshallingCost != incumbent.marshallingCost then
    candidate.marshallingCost < incumbent.marshallingCost
  else if candidate.allocations != incumbent.allocations then
    candidate.allocations < incumbent.allocations
  else if candidate.temporaryBytes != incumbent.temporaryBytes then
    candidate.temporaryBytes < incumbent.temporaryBytes
  else if candidate.residentBytes != incumbent.residentBytes then
    candidate.residentBytes < incumbent.residentBytes
  else if candidate.coldCost policy != incumbent.coldCost policy then
    candidate.coldCost policy < incumbent.coldCost policy
  else
    candidate.kind.rank < incumbent.kind.rank

/-- Prefer the workload-weighted score, then the deterministic equal-score ordering. -/
@[inline] def Candidate.better
    (policy : Policy) (candidate incumbent : Candidate) : Bool :=
  candidate.score policy < incumbent.score policy ||
    (candidate.score policy == incumbent.score policy &&
      candidate.preferOnEqualScore policy incumbent)

/--
A candidate with a strictly cheaper warm call and no larger cold cost is `better` than the
incumbent under every policy.

For a positive expected call count the score is strictly lower. For a zero expected call count
the scores are the cold costs; either the cold cost is strictly lower or the equal-score tie
break, whose first key is the warm cost, decides in the candidate's favor.
-/
theorem Candidate.better_of_warmCost_lt_of_coldCost_le
    (policy : Policy) {candidate incumbent : Candidate}
    (hwarm : candidate.warmCost policy < incumbent.warmCost policy)
    (hcold : candidate.coldCost policy ≤ incumbent.coldCost policy) :
    candidate.better policy incumbent = true := by
  unfold Candidate.better
  have hle : candidate.score policy ≤ incumbent.score policy := by
    unfold Candidate.score
    have := Nat.mul_le_mul_left policy.expectedCalls (Nat.le_of_lt hwarm)
    omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · simp [hlt]
  · have hne : candidate.warmCost policy ≠ incumbent.warmCost policy := Nat.ne_of_lt hwarm
    simp [heq, Candidate.preferOnEqualScore, hne, hwarm]

/--
An incumbent with a strictly more expensive warm call and no smaller cold cost is never
`better` than the candidate, under every policy.
-/
theorem Candidate.not_better_of_warmCost_lt_of_coldCost_le
    (policy : Policy) {candidate incumbent : Candidate}
    (hwarm : candidate.warmCost policy < incumbent.warmCost policy)
    (hcold : candidate.coldCost policy ≤ incumbent.coldCost policy) :
    incumbent.better policy candidate = false := by
  unfold Candidate.better
  have hle : candidate.score policy ≤ incumbent.score policy := by
    unfold Candidate.score
    have := Nat.mul_le_mul_left policy.expectedCalls (Nat.le_of_lt hwarm)
    omega
  have hnlt : ¬ incumbent.score policy < candidate.score policy := Nat.not_lt.mpr hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · simp [hnlt, Nat.ne_of_gt hlt]
  · have hne : incumbent.warmCost policy ≠ candidate.warmCost policy := Nat.ne_of_gt hwarm
    simp [heq, Candidate.preferOnEqualScore, hne, Nat.not_lt.mpr (Nat.le_of_lt hwarm)]

/-- Compare one admissible candidate with the current incumbent. -/
@[inline] def consider
    (policy : Policy) (incumbent candidate : Candidate) : Candidate :=
  if candidate.admissible policy && candidate.better policy incumbent then
    candidate
  else
    incumbent

/--
Choose among the mandatory baseline and the admissible alternatives using score and tie-breaks.

The baseline seeds the fold without an admissibility check, so selection remains total even if
all estimates exceed the policy's resource limits. Capability construction can retain the selected
certificate for subsequent arithmetic calls.
-/
@[inline] def selectCandidate
    (policy : Policy) (candidates : CandidateSet Candidate) : Candidate :=
  candidates.alternatives.foldl (consider policy) candidates.baseline

/-- Kernel class selected from a family-supplied certified candidate set. -/
@[inline] def select
    (policy : Policy) (candidates : CandidateSet Candidate) : KernelClass :=
  (selectCandidate policy candidates).kind

/-- A candidate above the hard memory ceiling cannot replace the incumbent. -/
theorem consider_rejects_excess_residency
    (policy : Policy) (incumbent candidate : Candidate)
    (hbytes : policy.maxResidentBytes < candidate.residentBytes) :
    consider policy incumbent candidate = incumbent := by
  simp [consider, Candidate.admissible, Nat.not_le.mpr hbytes]

/-- A candidate above the hard temporary-memory ceiling cannot replace the incumbent. -/
theorem consider_rejects_excess_temporary_memory
    (policy : Policy) (incumbent candidate : Candidate)
    (hbytes : policy.maxTemporaryBytes < candidate.temporaryBytes) :
    consider policy incumbent candidate = incumbent := by
  simp [consider, Candidate.admissible, Nat.not_le.mpr hbytes]

/-- With no optional candidate, selection returns the mandatory baseline. -/
@[simp] theorem selectCandidate_only_baseline (policy : Policy) (baseline : Candidate) :
    selectCandidate policy { baseline := baseline } = baseline := by
  rfl

end FloatLib.Floats.ExecFloat.Backend
