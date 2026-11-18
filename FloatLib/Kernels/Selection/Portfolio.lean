/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Batteries.Tactic.Lint.Misc
public import FloatLib.Kernels.Selection.Certified

/-!
# Certified backend portfolios

A portfolio records ranked certified alternatives and a total baseline. The selection
lemmas identify the result when a designated alternative or the baseline wins.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

universe u

/--
`Tagged spec bound alternatives`: `alternatives` are the candidates tagged `@[compiler_optimize]`
in scope whose specification matches `spec` and whose rank is below `bound`, by decreasing rank.
A capability asks for `Tagged spec Tagged.top alternatives` to obtain all of them.
-/
class Tagged {α : Type u} (spec : α) (bound : Nat)
    (alternatives : outParam (List (Certified spec))) : Prop

namespace Tagged

/-- A bound above the rank of every tagged candidate. -/
abbrev top : Nat := 1152921504606846976

/-- No candidate: the end of every collection. -/
instance (priority := 0) nil {α : Type u} (spec : α) (bound : Nat) : Tagged spec bound [] :=
  ⟨⟩

end Tagged

/--
`NoAlternative alternatives`: the collected list is empty. Instance search proves it for `[]`
and for a concatenation of empty lists. A tagged candidate that declines a class of formats
states that as an instance (`NoAlternative (candidate format plan)` for those formats), so that
a family can tell where its own alternatives do not apply.
-/
class NoAlternative {α : Type u} {spec : α} (alternatives : List (Certified spec)) : Prop where
  /-- The list has no element. -/
  eq_nil : alternatives = []

/-- The empty list has no alternative. -/
instance NoAlternative.nil {α : Type u} {spec : α} :
    NoAlternative ([] : List (Certified spec)) :=
  ⟨rfl⟩

/-- A concatenation of two lists without alternatives has none. -/
instance NoAlternative.append {α : Type u} {spec : α} (first second : List (Certified spec))
    [empty : NoAlternative first] [rest : NoAlternative second] :
    NoAlternative (first.append second) :=
  ⟨by rw [empty.eq_nil, rest.eq_nil]; rfl⟩

/--
What instance search knows about a collection of tagged alternatives: that it is empty
(`closed`), or nothing (`opened`).
-/
inductive Closure where
  /-- No tagged alternative applies. -/
  | closed
  /-- Tagged alternatives may apply. -/
  | opened

/--
`HasClosure alternatives closure`: instance search classifies a collection, and always succeeds.
The class is `closed` when it proves the collection empty (`NoAlternative`) and `opened`
otherwise. It never fails, so that the search does not go back to a smaller collection.
-/
class HasClosure {α : Type u} {spec : α} (alternatives : List (Certified spec))
    (closure : outParam Closure) : Prop

-- `NoAlternative` is the condition under which instance search takes this instance.
/-- A collection that instance search proves empty is closed. -/
@[nolint unusedArguments]
instance (priority := 1000) HasClosure.closed {α : Type u} {spec : α}
    (alternatives : List (Certified spec)) [NoAlternative alternatives] :
    HasClosure alternatives .closed :=
  ⟨⟩

/-- Any other collection is open. -/
instance (priority := 10) HasClosure.opened {α : Type u} {spec : α}
    (alternatives : List (Certified spec)) : HasClosure alternatives .opened :=
  ⟨⟩

/--
`Collected spec closure`: the class of the complete collection of the candidates tagged for
`spec`. A family with a static form uses its static kernel where the class is `closed` and the
planner's choice among that kernel and the tagged candidates where it is `opened`
(`Capability.Static`).
-/
class Collected {α : Type u} (spec : α) (closure : outParam Closure) : Prop

-- The two instance arguments compute `closure` during instance search.
/-- The class of what `Tagged` collects for `spec`. -/
@[nolint unusedArguments]
instance Collected.of {α : Type u} (spec : α) {alternatives : List (Certified spec)}
    {closure : Closure} [Tagged spec Tagged.top alternatives] [HasClosure alternatives closure] :
    Collected spec closure :=
  ⟨⟩

/--
The alternatives tagged `@[compiler_optimize]` for `spec`, as instance search collects them where
the portfolio is asked for. A family's capability takes `[portfolio : Portfolio spec]` and hands
it to `Capability.ofTagged`.
-/
class Portfolio {α : Type u} (spec : α) where
  /-- The tagged candidates in scope whose specification matches `spec`. -/
  alternatives : List (Certified spec)
  /-- The alternatives are the collection of instance search. -/
  tagged : Tagged spec Tagged.top alternatives

/-- The portfolio of a specification is whatever `Tagged` collects for it. -/
@[always_inline, instance_reducible] instance Portfolio.collected {α : Type u} (spec : α)
    {alternatives : List (Certified spec)} [tagged : Tagged spec Tagged.top alternatives] :
    Portfolio spec where
  alternatives := alternatives
  tagged := tagged

/-! ## Selection with a designated last alternative -/

variable {α : Type u} {spec : α}

/--
Whether `candidate`, considered after `alternatives`, wins the selection: it is admissible and
better than the estimate selected from the baseline and the alternatives. The test reads
estimates only.
-/
@[inline] def winsAfter (policy : Policy) (alternatives : List Candidate) (baseline : Candidate)
    (candidate : Candidate) : Bool :=
  candidate.admissible policy &&
    candidate.better policy (selectCandidate policy { alternatives, baseline })

/--
A last alternative that wins after the others is the selected certificate: the planner returns
that candidate itself, so calling its kernel directly runs the selected implementation.
-/
theorem selectCertified_of_winsAfter (policy : Policy) (alternatives : List (Certified spec))
    (baseline last : Certified spec)
    (wins : winsAfter policy (alternatives.map Certified.estimate) baseline.estimate
      last.estimate = true) :
    selectCertified policy { alternatives := alternatives ++ [last], baseline } = last := by
  unfold selectCertified
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold winsAfter selectCandidate at wins
  rw [← foldl_considerCertified_estimate] at wins
  simp only [considerCertified, wins, ↓reduceIte]

/--
Whether the baseline stays selected: no alternative is admissible and better than it. The test
reads estimates only.
-/
@[inline] def baselineWins (policy : Policy) (alternatives : List Candidate)
    (baseline : Candidate) : Bool :=
  alternatives.all fun candidate =>
    !(candidate.admissible policy && candidate.better policy baseline)

/-- When no alternative beats the baseline, the planner returns the baseline itself. -/
theorem selectCertified_of_baselineWins (policy : Policy) (alternatives : List (Certified spec))
    (baseline : Certified spec)
    (wins : baselineWins policy (alternatives.map Certified.estimate) baseline.estimate = true) :
    selectCertified policy { alternatives, baseline } = baseline := by
  unfold selectCertified
  unfold baselineWins at wins
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, Bool.not_eq_true'] at wins
  change alternatives.foldl (considerCertified policy) baseline = baseline
  induction alternatives with
  | nil => rfl
  | cons candidate rest ih =>
      rw [List.foldl_cons]
      have hstep : considerCertified policy baseline candidate = baseline := by
        simp [considerCertified, wins candidate List.mem_cons_self]
      rw [hstep]
      exact ih fun other hother => wins other (List.mem_cons_of_mem _ hother)

end FloatLib.Floats.ExecFloat.Backend
