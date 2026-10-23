/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified
public import FloatLib.Floats.ExecFloat.Carrier

/-!
# Executable arithmetic capabilities

A capability bundles an operation's specification, its certified implementations, and their cost
estimates. The selector starts from a mandatory baseline and uses the estimates to consider
alternatives within the resource limits. The named operations in `ExecFloat.Core.Operations` use
this indexed contract.

`Capability.run_eq_spec` is an equality of Lean definitions. The binary software kernels use proved
refinements and `@[csimp]` replacements, so their compiled correctness also depends on the
compiler. The binary32/binary64 `NativeFPU.Unchecked` host functions are not capabilities, because
they have no packed-word equality theorem of the kind `Backend.Certified` requires.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

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

variable {F : Type u} [EncodedFormat F]
    [planning : Backend.PolicyFor F]

namespace Capability

/--
Build a capability from a candidate set and a first-order dispatcher equal to `spec`.

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
Build a singleton capability from one certified kernel and an entry point equal to its `run`.

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
Build a singleton capability whose entry point is the certificate's stored kernel `certified.run`.

Statically selected backends use it, so operation-specific planners do not repeat the same
certificate projection and `rfl` proof.
-/
@[always_inline, instance_reducible] def ofCertified
    (operation : Backend.Operation)
    {spec : OperationSignature F operation}
    (certified : Backend.Certified spec) :
    Capability F operation :=
  ofDirectKernel operation spec certified certified.run rfl

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

end Capability
end ExecFloat
end FloatLib.Floats
