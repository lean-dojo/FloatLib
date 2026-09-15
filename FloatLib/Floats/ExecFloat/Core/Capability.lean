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

A capability supplies an operation's specification, certified implementations, and cost estimates.
The selector starts with a mandatory baseline and considers alternatives within the resource
limits using those estimates. This indexed
contract is used by the named operations in `ExecFloat.Core.Operations`.

`Capability.run_eq_spec` proves equality of Lean definitions. The binary software kernels use
proved refinements and `@[csimp]` replacements; their compiled correctness also depends on the
compiler. The explicit binary32/binary64
`NativeFPU.Unchecked` host functions are deliberately not capabilities because they do not yet
have the packed-word equality theorem required by `Backend.Certified`.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

variable (F : Type u) [EncodedFormat F]
    [planning : Backend.PolicyFor F]

/--
Function type of a universal arithmetic operation over one encoded format.

Indexing the operation package by `Backend.Operation` keeps addition, subtraction,
multiplication, division, square root, and FMA as distinct capabilities even when some operations
have the same Lean function type.
-/
abbrev OperationSignature : Backend.Operation → Type _
  | .add | .sub | .mul | .div => ExecFloat F → ExecFloat F → ExecFloat F
  | .sqrt => ExecFloat F → ExecFloat F
  | .fma => ExecFloat F → ExecFloat F → ExecFloat F → ExecFloat F

/--
Semantics, certified kernels, and static selection for one arithmetic operation.

The operation index prevents accidental instance sharing between operations while avoiding six
structurally identical planner records.
-/
class Capability (operation : Backend.Operation) where
  /-- Clear reference operation for `F`. -/
  spec : OperationSignature F operation
  /-- Certified kernels offered by this capability for the operation on `F`. -/
  candidates : Backend.CandidateSet (Backend.Certified spec)
  /--
  Lazy, memoized automatic selection for capabilities that do not materialize a direct winner.

  The first projection evaluates the planner; subsequent projections reuse the selected
  certificate. Static built-in formats may bypass even this projection by supplying
  `implementation` directly.
  -/
  selection : Thunk (Backend.Certified spec) :=
    Thunk.mk fun _ => Backend.selectCertified planning.policy candidates
  /--
  Certified implementation executed by public arithmetic.

  The default reads the memoized automatic selection. A statically specialized package may store
  the planner's already-known winner directly, allowing Lean to erase both planning and closure
  dispatch from the generated hot path.
  -/
  implementation : Backend.Certified spec :=
    selection.get
  /--
  The stored certificate is, in Lean's logic, the winner of the advertised candidate plan under
  the policy in scope.

  A static package may materialize the winner for code generation, but it must then prove that
  the planner selects that same certificate. Inspection tools such as `#float_info` report
  `implementation`; `execute_eq_implementation` relates the public entry point to its logical
  operation. These equations establish equality of behavior in Lean, not identity of generated
  machine code.
  -/
  implementation_is_selected :
    implementation = Backend.selectCertified planning.policy candidates := by
    rfl
  /--
  First-order executable entry point used by public arithmetic.

  The default projects the selected certificate. Static formats may name the same proved kernel
  directly, which lets Lean erase the certificate and typeclass dictionaries from monomorphic
  calls without changing either selection metadata or the correctness boundary.
  -/
  execute : OperationSignature F operation :=
    implementation.run
  /--
  In Lean's logic, the first-order entry point is propositionally equal to the selected
  certificate's `run`.

  When a package supplies `execute := implementation.run`, or names the certificate's kernel and
  proves this field by `rfl`, the compiled code of `execute` is that certificate's kernel. Code
  named here must not acquire an unproved compiler replacement: this equation identifies the
  logical kernel but could not establish equality with such a substitute.
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
Build a capability from a policy-selected portfolio and a first-order dispatcher.

The candidates remain authoritative for inspection and certification. Naming `execute`
separately lets a format expose the same selected behavior without retaining a certificate
projection in monomorphic generated code.
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
Build a singleton capability whose public entry point names its certified kernel directly.

This is the common package for formats whose planner has one genuine implementation. The
singleton still participates in inspection and selection proofs, while `execute` remains a
first-order format kernel.
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
Build a direct capability from a certificate whose stored kernel is the public entry point.

This is the common case for statically selected backends. It keeps operation-specific planners
from repeating the same certificate projection and reflexive equality, while preserving the
first-order kernel stored in `certified.run`.
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

The operation is certified in Lean; a family-specific compiled replacement may have an additional
trust boundary documented by that family.
-/
@[inline] def run {operation : Backend.Operation}
    [self : Capability F operation] : OperationSignature F operation :=
  self.execute

/-- The selected executable operation agrees with its reference semantics. -/
theorem run_eq_spec {operation : Backend.Operation}
    [self : Capability F operation] :
    run (F := F) (operation := operation) = self.spec :=
  self.execute_eq_implementation.trans
    (selected (F := F) (operation := operation)).run_eq_spec

end Capability
end ExecFloat
end FloatLib.Floats
