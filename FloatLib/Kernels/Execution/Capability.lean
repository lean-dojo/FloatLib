/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Carrier
public import FloatLib.Tactic.CompilerOptimize

/-!
# Executable arithmetic capabilities

A capability bundles an operation's specification, its certified implementations, and their cost
estimates. The selector starts from a mandatory baseline and uses the estimates to consider
alternatives within the resource limits. The named operations in `Kernels.Execution.Operations`
use this indexed contract.

A family builds its capabilities from the backends tagged `@[compiler_optimize]`:
`Capability.ofTagged` selects among a baseline, the family's own alternatives and every tagged
alternative that instance search collects, and `Capability.Static` keeps a statically fixed
kernel for the formats that no tagged alternative covers.

`Capability.run_eq_spec` is an equality of Lean definitions. The binary software kernels use proved
refinements and `@[csimp]` replacements, so their compiled correctness also depends on the compiler.
The binary32/binary64 `NativeFPU.Unchecked` host functions aren't capabilities at all, because they
have no packed-word equality theorem of the kind `Backend.Certified` requires.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

section

variable (F : Type u) [EncodedFormat F]
    [planning : Backend.PolicyFor F]

/--
Function type of each arithmetic operation over one encoded format.

Indexing by `Backend.Operation` keeps addition, subtraction, multiplication, division, square
root, and FMA distinct capabilities even when two of them share a Lean function type.
-/
abbrev OperationSignature : Backend.Operation → Type _
  | .add | .sub | .mul | .div => ExecFloat F → ExecFloat F → ExecFloat F
  | .sqrt => ExecFloat F → ExecFloat F
  | .fma => ExecFloat F → ExecFloat F → ExecFloat F → ExecFloat F

/--
Semantics, certified kernels, and static selection for one arithmetic operation.

The operation index keeps the instances of different operations apart without six structurally
identical planner records.
-/
class Capability (operation : Backend.Operation) where
  /-- Reference operation for `F`. -/
  spec : OperationSignature F operation
  /-- Certified kernels offered by this capability for the operation on `F`. -/
  candidates : Backend.CandidateSet (Backend.Certified spec)
  /--
  Lazy, memoized automatic selection, for capabilities that do not store a winner.

  The first projection runs the planner and later projections reuse the selected certificate.
  Static built-in formats skip even this projection by supplying `implementation`.
  -/
  selection : Thunk (Backend.Certified spec) :=
    Thunk.mk fun _ => Backend.selectCertified planning.policy candidates
  /--
  Certified implementation whose `run` public arithmetic computes.

  The default reads the memoized automatic selection. A statically specialized package may store
  the planner's known winner, so Lean can erase both planning and closure dispatch from the
  generated hot path.
  -/
  implementation : Backend.Certified spec :=
    selection.get
  /--
  The stored certificate is the planner's winner over `candidates` under the policy in scope.

  A static package that stores the winner for code generation must prove that the planner selects
  that same certificate. Inspection tools such as `#float_info` report `implementation`. The
  equation holds in Lean's logic and says nothing about the generated machine code.
  -/
  implementation_is_selected :
    implementation = Backend.selectCertified planning.policy candidates := by
    rfl
  /--
  First-order executable entry point that public arithmetic runs.

  The default projects the selected certificate. A static format may name the proved kernel
  itself, which lets Lean erase the certificate and typeclass dictionaries from monomorphic calls
  without changing the selection metadata or the correctness boundary.
  -/
  execute : OperationSignature F operation :=
    implementation.run
  /--
  The entry point `execute` is propositionally equal to the selected certificate's `run`.

  When a package supplies `execute := implementation.run`, or names the certificate's kernel and
  proves this field by `rfl`, the compiled code of `execute` is that kernel. Code named here must
  not acquire an unproved compiler replacement, because the equation is about the logical kernel
  and says nothing about such a substitute.
  -/
  execute_eq_implementation :
    execute = implementation.run := by
    rfl

/-- Addition capability for one format. -/
abbrev Add := Capability F .add

/-- Subtraction capability for one format. -/
abbrev Sub := Capability F .sub

/-- Multiplication capability for one format. -/
abbrev Mul := Capability F .mul

/-- Division capability for one format. -/
abbrev Div := Capability F .div

/-- Square-root capability for one format. -/
abbrev Sqrt := Capability F .sqrt

/-- Fused multiply-add capability for one format. -/
abbrev Fma := Capability F .fma

end

namespace Capability

variable {F : Type u} [EncodedFormat F]

/--
Choose among three entry points of one operation without building a closure: `direct` when
`useDirect` holds, otherwise `baseline` when `useBaseline` holds, otherwise the kernel of the
memoized selection. Each case of the operation gives a function of the operation's own arity, so
that a caller applies the chosen kernel to its operands directly.
-/
@[always_inline, inline] def guarded (operation : Backend.Operation)
    (useDirect useBaseline : Bool)
    (direct baseline : OperationSignature F operation)
    (selected : Thunk (OperationSignature F operation)) : OperationSignature F operation :=
  match operation, direct, baseline, selected with
  | .add, direct, baseline, selected | .sub, direct, baseline, selected
  | .mul, direct, baseline, selected | .div, direct, baseline, selected =>
      fun left right =>
        if useDirect then direct left right
        else if useBaseline then baseline left right
        else selected.get left right
  | .sqrt, direct, baseline, selected =>
      fun value =>
        if useDirect then direct value
        else if useBaseline then baseline value
        else selected.get value
  | .fma, direct, baseline, selected =>
      fun left right addend =>
        if useDirect then direct left right addend
        else if useBaseline then baseline left right addend
        else selected.get left right addend

/-- `guarded` is the choice among its three entry points. -/
theorem guarded_eq (operation : Backend.Operation) (useDirect useBaseline : Bool)
    (direct baseline : OperationSignature F operation)
    (selected : Thunk (OperationSignature F operation)) :
    guarded operation useDirect useBaseline direct baseline selected =
      if useDirect then direct else if useBaseline then baseline else selected.get := by
  cases operation <;> simp only [guarded] <;> (repeat' split) <;> rfl

end Capability

variable {F : Type u} [EncodedFormat F]
    [planning : Backend.PolicyFor F]

namespace Capability

/--
Build a static capability from the family's own candidate set and a first-order dispatcher equal
to `spec`. A family declares the result as its `Static` capability, and the tagged alternatives
are added
where they apply.

The candidates stay authoritative for inspection and certification. A separate `execute` lets a
format run the selected behavior without keeping a certificate projection in monomorphic
generated code.
-/
@[always_inline, instance_reducible] def ofCandidates
    (operation : Backend.Operation)
    (spec : OperationSignature F operation)
    (candidates : Backend.CandidateSet (Backend.Certified spec))
    (execute : OperationSignature F operation)
    (execute_eq_spec : execute = spec) :
    Capability F operation where
  spec := spec
  candidates := candidates
  implementation := Backend.selectCertified planning.policy candidates
  execute := execute
  execute_eq_implementation :=
    Backend.firstOrder_eq_selected planning.policy candidates execute execute_eq_spec

/--
Build a static singleton capability from one certified kernel and an entry point equal to its
`run`. A family declares the result as its `Static` capability, and the tagged alternatives are
added
where they apply.

Formats whose planner has one implementation use this package. The singleton still takes part in
inspection and selection proofs, and `execute` stays a first-order format kernel.
-/
@[always_inline, instance_reducible] def ofDirectKernel
    (operation : Backend.Operation)
    (spec : OperationSignature F operation)
    (certified : Backend.Certified spec)
    (execute : OperationSignature F operation)
    (execute_eq_certified : execute = certified.run) :
    Capability F operation where
  spec := spec
  candidates := Backend.CandidateSet.singleton certified
  implementation := certified
  execute := execute
  execute_eq_implementation := execute_eq_certified

/--
Build a static singleton capability whose entry point is the certificate's stored kernel
`certified.run`. A family declares the result as its `Static` capability, and the tagged
alternatives are added
where they apply.

Statically selected backends use it, so operation-specific planners do not repeat the same
certificate projection and `rfl` proof.
-/
@[always_inline, instance_reducible] def ofCertified
    (operation : Backend.Operation)
    {spec : OperationSignature F operation}
    (certified : Backend.Certified spec) :
    Capability F operation :=
  ofDirectKernel operation spec certified certified.run rfl

/--
Whether the direct kernel of a capability runs: it is enabled, there is a direct candidate, and
that candidate wins after every other alternative. The test reads estimates only. It is kept
out of the arithmetic body, so that the compiler computes it once for a closed format and
policy.
-/
@[noinline] def directSelected {α : Type u} {spec : α} (policy : Backend.Policy)
    (alternatives : List (Backend.Certified spec)) (baseline : Backend.Certified spec)
    (direct : Option (Backend.Certified spec)) (enabled : Bool) : Bool :=
  enabled && direct.any fun certified =>
    Backend.winsAfter policy (alternatives.map Backend.Certified.estimate)
      baseline.estimate certified.estimate

/--
Whether the baseline kernel of a capability runs: no alternative and no direct candidate beats
it. The test reads estimates only and is kept out of the arithmetic body.
-/
@[noinline] def baselineSelected {α : Type u} {spec : α} (policy : Backend.Policy)
    (alternatives : List (Backend.Certified spec)) (baseline : Backend.Certified spec)
    (direct : Option (Backend.Certified spec)) : Bool :=
  Backend.baselineWins policy
    ((alternatives ++ direct.toList).map Backend.Certified.estimate) baseline.estimate

/--
Build a capability from the tagged alternatives of `spec` and the family's own candidates: a
baseline, the alternatives it names itself (`named`), and an optional direct kernel.

`portfolio` holds the candidates tagged `@[compiler_optimize]` that instance search collected for
`spec`. A family's instance takes `[portfolio : Backend.Portfolio spec]` as an argument and
passes it on, so the collection happens where the capability is used and sees every candidate
imported there. The candidate set is the tagged alternatives, then `named`, then `direct` if
there is one, with `baseline` as the mandatory incumbent, and the planner selects among them
under the policy in scope.

The entry point calls a named kernel without a closure in two cases that the estimates decide:
`directRun` when `direct` wins after every other alternative (and `directEnabled`), and
`baselineRun` when no candidate beats the baseline. Otherwise it runs the memoized selection. In
each case the kernel that runs is the selected certificate's own (`execute_eq_implementation`),
so a newly tagged candidate that wins replaces the named kernels without any edit here.
-/
@[always_inline, instance_reducible] def ofTagged
    (operation : Backend.Operation)
    {spec : OperationSignature F operation}
    (portfolio : Backend.Portfolio spec)
    (baseline : Backend.Certified spec)
    (baselineRun : OperationSignature F operation := baseline.run)
    (baselineRun_eq : baselineRun = baseline.run := by rfl)
    (direct : Option (Backend.Certified spec) := none)
    (directRun : OperationSignature F operation := baselineRun)
    (directRun_eq : ∀ certified, direct = some certified → directRun = certified.run := by
      intro _ h; cases h)
    (directEnabled : Bool := true)
    (named : List (Backend.Certified spec) := []) :
    Capability F operation :=
  let alternatives := portfolio.alternatives ++ named
  let candidates : Backend.CandidateSet (Backend.Certified spec) :=
    { alternatives := alternatives ++ direct.toList, baseline }
  let selection := Thunk.mk fun _ => Backend.selectCertified planning.policy candidates
  { spec := spec
    candidates := candidates
    selection := selection
    execute := guarded operation
      (directSelected planning.policy alternatives baseline direct directEnabled)
      (baselineSelected planning.policy alternatives baseline direct)
      directRun baselineRun (Thunk.mk fun _ => selection.get.run)
    execute_eq_implementation := by
      rw [guarded_eq]
      split
      · rename_i wins
        rw [directSelected, Bool.and_eq_true] at wins
        cases direct with
        | none => simp at wins
        | some certified =>
            have selected := Backend.selectCertified_of_winsAfter planning.policy
              alternatives baseline certified (by simpa using wins.2)
            change directRun = (Backend.selectCertified planning.policy
              { alternatives := alternatives ++ [certified], baseline }).run
            rw [selected]
            exact directRun_eq certified rfl
      · split
        · rename_i wins
          have selected := Backend.selectCertified_of_baselineWins planning.policy
            (alternatives ++ direct.toList) baseline wins
          change baselineRun = (Backend.selectCertified planning.policy
            { alternatives := alternatives ++ direct.toList, baseline }).run
          rw [selected]
          exact baselineRun_eq
        · rfl }

/--
The static capability of a family for one operation: a capability whose kernel the family fixed
among its own candidates, so that the generated code calls that kernel.

A family with a static form declares an instance of `Static operation spec`, where `spec` is
its reference operation, and no `Capability` instance. `ofStatic` turns it into the capability
that runs, by the class of the candidates tagged `@[compiler_optimize]` for `spec` that instance
search finds where the operation is written (`Backend.Collected`). Where it proves that no
tagged candidate applies, the capability is the static one itself (`Resolved.closed`), and the
compiler reads its kernel through the instances as it does for a capability declared directly.
Otherwise the planner chooses among the kernel that the static capability selected and every
tagged alternative, and calls the static kernel directly when none beats it
(`Resolved.opened`). Both have the reference operation `spec`, so theorems about the format do
not depend on which one instance search finds.
-/
class Static (operation : Backend.Operation)
    (spec : outParam (OperationSignature F operation)) where
  /-- The capability with the family's kernel fixed. -/
  capability : Capability F operation
  /-- Its reference operation is `spec`, the term that tagged candidates are matched against. -/
  spec_eq : capability.spec = spec

/-- The entry point of a capability is the kernel of its selected certificate, under a cast of
the reference operation. -/
theorem execute_eq_cast {operation : Backend.Operation} (capability : Capability F operation)
    {spec : OperationSignature F operation} (h : capability.spec = spec) :
    capability.execute = (h ▸ capability.implementation).run := by
  subst h
  exact capability.execute_eq_implementation

/--
The capability that runs for a static capability, for one class of the tagged candidates. The
two instances are the two classes, so instance search always finds one.
-/
class Resolved (closure : Backend.Closure) (operation : Backend.Operation)
    (spec : OperationSignature F operation) where
  /-- The capability that public arithmetic runs. -/
  capability : Capability F operation

/-- No tagged alternative applies: the family's static capability runs as it is. -/
@[instance_reducible] instance Resolved.closed (operation : Backend.Operation)
    {spec : OperationSignature F operation} [static : Static operation spec] :
    Resolved .closed operation spec where
  capability := static.capability

/--
Tagged alternatives may apply: the planner chooses among them and the kernel that the static
capability selected.
-/
@[instance_reducible] instance Resolved.opened (operation : Backend.Operation)
    {spec : OperationSignature F operation} [static : Static operation spec]
    [portfolio : Backend.Portfolio spec] : Resolved .opened operation spec where
  capability :=
    ofTagged operation portfolio (static.spec_eq ▸ static.capability.implementation)
      static.capability.execute (execute_eq_cast static.capability static.spec_eq)

/--
The capability of a family with a static form: the static capability or the planner's choice,
by the class of the tagged candidates of its reference operation.

Its priority is below the default, so that a capability instance declared at the default
priority for the same format is found first, and above the low priority of a family's
representation-independent capability, which serves the carriers without a static form.
-/
-- `Static` and `Collected` find `spec` and `closure` in instance search; the value is `resolved`.
@[instance_reducible, nolint unusedArguments] instance (priority := 500) ofStatic
    (operation : Backend.Operation) {spec : OperationSignature F operation}
    {closure : Backend.Closure} [Static operation spec] [Backend.Collected spec closure]
    [resolved : Resolved closure operation spec] : Capability F operation :=
  resolved.capability

/-- Certified implementation selected from the candidates supplied by `F`. -/
@[inline] def selected {operation : Backend.Operation}
    [self : Capability F operation] : Backend.Certified self.spec :=
  self.implementation

/-- The stored selected certificate equals the planner's result. -/
theorem selected_eq_planner {operation : Backend.Operation}
    [self : Capability F operation] :
    selected (F := F) (operation := operation) =
      Backend.selectCertified planning.policy self.candidates :=
  self.implementation_is_selected

/-- Static estimate attached to the selected implementation. -/
@[inline] def selectedCandidate {operation : Backend.Operation}
    [Capability F operation] : Backend.Candidate :=
  (selected (F := F) (operation := operation)).estimate

/--
Execute the selected logical operation.

The operation is certified in Lean. A family-specific compiled replacement may add a trust
boundary, which that family documents.
-/
@[inline] def run {operation : Backend.Operation}
    [self : Capability F operation] : OperationSignature F operation :=
  self.execute

/-- `run` agrees with the capability's reference semantics. -/
theorem run_eq_spec {operation : Backend.Operation}
    [self : Capability F operation] :
    run (F := F) (operation := operation) = self.spec :=
  self.execute_eq_implementation.trans
    (selected (F := F) (operation := operation)).run_eq_spec

/--
`HasSpec cap spec` states that the capability `cap` has the reference operation `spec`.

Instance search proves it whenever `cap.spec` unfolds to `spec`, as it does for every capability
instance that names its reference operation. A theorem about a function that runs the selected
capability takes `HasSpec` as an instance argument to learn which reference the kernel computes,
and `run_eq_spec` then rewrites the kernel to that reference.
-/
class HasSpec {operation : Backend.Operation} (cap : Capability F operation)
    (spec : outParam (OperationSignature F operation)) : Prop where
  /-- The capability's reference operation is `spec`. -/
  spec_eq : cap.spec = spec

/-- Every capability has its own reference operation. -/
instance {operation : Backend.Operation} (cap : Capability F operation) :
    HasSpec cap cap.spec :=
  ⟨rfl⟩

/--
The static capability has the reference operation of its static form. Instance search finds this
before it unfolds the capability, so the reference is known for a family whose static capability
is a match on a storage plan.
-/
instance (priority := high) HasSpec.closed (operation : Backend.Operation)
    {spec : OperationSignature F operation} [static : Static operation spec]
    [Backend.Collected spec .closed] :
    HasSpec (ofStatic operation (resolved := Resolved.closed operation)) spec :=
  ⟨static.spec_eq⟩

/-- The planner's choice over a static form has the reference operation of that form. -/
instance (priority := high) HasSpec.opened (operation : Backend.Operation)
    {spec : OperationSignature F operation} [Static operation spec]
    [Backend.Collected spec .opened] [Backend.Portfolio spec] :
    HasSpec (ofStatic operation (resolved := Resolved.opened operation)) spec :=
  ⟨rfl⟩

end Capability
end ExecFloat
end FloatLib.Floats
