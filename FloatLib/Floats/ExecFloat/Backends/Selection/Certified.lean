/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Scoring

/-!
# Certified backend selection

`Certified spec` packages an executable kernel with both an engineering estimate and an equation
showing that it implements `spec`. The operation type is abstract, so the same mechanism handles
unary, binary, ternary, stateful, and family-specific kernels.

Selection is a deterministic fold over already certified alternatives and a mandatory exact
baseline. The cost heuristic decides only which implementation to run; it never participates in
the arithmetic proof. Erasing proofs yields the same estimate selected by inspection tools, so the
reported plan cannot silently diverge from execution.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

universe u

/--
Executable kernel bundled with a static estimate and a refinement certificate.

The operation type `α` may be unary, binary, ternary, stateful, or family-specific. This keeps
the planning mechanism independent of floating-point layout and of the six core arithmetic
operations.
-/
structure Certified {α : Type u} (spec : α) where
  /-- Static cost and resource estimate attached to the executable kernel. -/
  estimate : Candidate
  /-- Executable implementation offered to the selector. -/
  run : α
  /-- The executable kernel equals the supplied specification. -/
  run_eq_spec : run = spec

namespace Certified

/--
Use the specification itself as the complete executable baseline.

The baseline runs `spec` directly. Specialized candidates can refine the same specification and
compete with the supplied estimate.
-/
def reference {α : Type u} (estimate : Candidate) (spec : α) : Certified spec where
  estimate
  run := spec
  run_eq_spec := rfl

/-- Construct a certified nullary result from an ordinary equality. -/
def nullary {α : Type u} (estimate : Candidate) (spec run : α)
    (run_eq_spec : run = spec) : Certified spec where
  estimate
  run
  run_eq_spec

/-- Construct a certified unary kernel from its pointwise refinement theorem. -/
def unary {α β : Type u} (estimate : Candidate) (spec run : α → β)
    (run_eq_spec : ∀ value, run value = spec value) : Certified spec where
  estimate
  run
  run_eq_spec := funext run_eq_spec

/-- Construct a certified binary kernel from its pointwise refinement theorem. -/
def binary {α β γ : Type u} (estimate : Candidate) (spec : α → β → γ)
    (run : α → β → γ) (run_eq_spec : ∀ left right, run left right = spec left right) :
    Certified spec where
  estimate
  run
  run_eq_spec := by
    funext left right
    exact run_eq_spec left right

/-- Construct a certified ternary kernel from its pointwise refinement theorem. -/
def ternary {α β γ δ : Type u} (estimate : Candidate) (spec : α → β → γ → δ)
    (run : α → β → γ → δ)
    (run_eq_spec : ∀ left right addend, run left right addend = spec left right addend) :
    Certified spec where
  estimate
  run
  run_eq_spec := by
    funext left right addend
    exact run_eq_spec left right addend

/--
Retain a certified kernel exactly when its structural eligibility test succeeds.

The caller supplies the eligibility decision; the constructor is independent of operation arity,
format family, and cost model.
-/
@[inline] def ifEligible {α : Type u} {spec : α}
    (eligible : Bool) (candidate : Certified spec) : Option (Certified spec) :=
  if eligible then some candidate else none

end Certified

/--
Build a candidate portfolio whose mandatory baseline executes the specification itself.

This is the uniform shape used by exact executable specifications: specialized alternatives are
considered in the supplied order, and the reference operation remains the final total baseline.
-/
@[inline] def CandidateSet.withReference {α : Type u}
    (estimate : Candidate) (spec : α)
    (alternatives : List (Certified spec) := []) :
    CandidateSet (Certified spec) where
  alternatives
  baseline := Certified.reference estimate spec

/-- Erase executable functions and proofs, retaining the inspectable cost model. -/
def CandidateSet.estimates {α : Type u} {spec : α}
    (candidates : CandidateSet (Certified spec)) : CandidateSet Candidate :=
  candidates.map Certified.estimate

/-- Compare one certified candidate while retaining its executable refinement theorem. -/
@[inline] def considerCertified {α : Type u} {spec : α}
    (policy : Policy) (incumbent candidate : Certified spec) : Certified spec :=
  if candidate.estimate.admissible policy &&
      candidate.estimate.better policy incumbent.estimate then
    candidate
  else
    incumbent

/--
Erasing a certified comparison to its estimate gives the metadata-only comparison.

Keeping this correspondence explicit prevents inspection tools from reporting a different plan
from the executable dispatcher.
-/
@[simp] theorem considerCertified_estimate {α : Type u} {spec : α}
    (policy : Policy) (incumbent : Certified spec)
    (candidate : Certified spec) :
    (considerCertified policy incumbent candidate).estimate =
      consider policy incumbent.estimate candidate.estimate := by
  simp only [considerCertified, consider]
  split <;> rfl

/--
Select an executable certified kernel by the same fold as metadata-only selection.

No correctness proof is reconstructed from the heuristic: whichever branch is selected already
contains its own refinement theorem.
-/
@[inline] def selectCertified {α : Type u} {spec : α}
    (policy : Policy) (candidates : CandidateSet (Certified spec)) : Certified spec :=
  candidates.alternatives.foldl (considerCertified policy) candidates.baseline

/-- Erasing a certified candidate fold gives the corresponding estimate fold. -/
private theorem foldl_considerCertified_estimate {α : Type u} {spec : α}
    (policy : Policy) (incumbent : Certified spec)
    (candidates : List (Certified spec)) :
    (candidates.foldl (considerCertified policy) incumbent).estimate =
      (candidates.map Certified.estimate).foldl
        (consider policy) incumbent.estimate := by
  induction candidates generalizing incumbent with
  | nil => rfl
  | cons candidate candidates ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, considerCertified_estimate]

/-- Executable selection and metadata-only selection choose the same estimate. -/
theorem selectCertified_estimate {α : Type u} {spec : α}
    (policy : Policy) (candidates : CandidateSet (Certified spec)) :
    (selectCertified policy candidates).estimate =
      selectCandidate policy candidates.estimates := by
  simp only [selectCertified, selectCandidate, CandidateSet.estimates]
  exact foldl_considerCertified_estimate
    policy candidates.baseline candidates.alternatives

/-- Selection cannot invalidate refinement because every eligible branch is certified. -/
theorem selectCertified_run_eq_spec {α : Type u} {spec : α}
    (policy : Policy) (candidates : CandidateSet (Certified spec)) :
    (selectCertified policy candidates).run = spec :=
  (selectCertified policy candidates).run_eq_spec

/--
A direct entry point equal to the specification agrees with the selected certified kernel.

The operation type is arbitrary: no format, arity, or typeclass policy is required. Returning an
equality lets callers keep a named executable entry point without constructing a capability
through a helper that might retain a runtime record or an indirect call.
-/
theorem firstOrder_eq_selected {α : Type u} {spec : α}
    (policy : Policy) (candidates : CandidateSet (Certified spec))
    (execute : α) (execute_eq_spec : execute = spec) :
    execute = (selectCertified policy candidates).run :=
  execute_eq_spec.trans (selectCertified_run_eq_spec policy candidates).symm

/-- A fold that never finds a better candidate returns its incumbent. -/
theorem foldl_considerCertified_eq_of_not_better {α : Type u} {spec : α}
    (policy : Policy) (incumbent : Certified spec) (rest : List (Certified spec))
    (hrest : ∀ other ∈ rest, other.estimate.better policy incumbent.estimate = false) :
    rest.foldl (considerCertified policy) incumbent = incumbent := by
  induction rest with
  | nil => rfl
  | cons other rest ih =>
      rw [List.foldl_cons]
      have hstep : considerCertified policy incumbent other = incumbent := by
        simp [considerCertified, hrest other (List.mem_cons_self ..)]
      rw [hstep]
      exact ih fun other' hother' => hrest other' (List.mem_cons_of_mem _ hother')

/--
An admissible head alternative that beats the baseline and is beaten by no later alternative is
the selected certificate, under the given policy.

This is the lemma a statically specialized capability uses to name the planner's winner directly
while remaining provably consistent with the advertised candidate set.
-/
theorem selectCertified_cons_of_dominant {α : Type u} {spec : α}
    (policy : Policy) (dominant : Certified spec) (rest : List (Certified spec))
    (baseline : Certified spec)
    (hadmissible : dominant.estimate.admissible policy = true)
    (hbaseline : dominant.estimate.better policy baseline.estimate = true)
    (hrest : ∀ other ∈ rest, other.estimate.better policy dominant.estimate = false) :
    selectCertified policy { alternatives := dominant :: rest, baseline } = dominant := by
  unfold selectCertified
  simp only [List.foldl_cons]
  have hhead : considerCertified policy baseline dominant = dominant := by
    simp [considerCertified, hadmissible, hbaseline]
  rw [hhead]
  exact foldl_considerCertified_eq_of_not_better policy dominant rest hrest

end FloatLib.Floats.ExecFloat.Backend
