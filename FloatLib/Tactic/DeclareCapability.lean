/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability

/-!
# The `declare_execfloat_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

/--
Generate the public operation namespace for one indexed arithmetic capability.

Only the arity-specific executable and pointwise refinement theorem differ between operations.
The `on` argument is the encoded family, and `using` supplies its planning policy. Passing them
explicitly lets the same command generate each operation namespace.
-/
syntax (name := declareExecFloatCapability)
  "declare_execfloat_capability " ident " for " term " on " term " using " term : command

macro_rules
  | `(declare_execfloat_capability spec for $op:term on $family:term using $_policy:term) =>
      `(
        /-- Clear reference operation for this capability. -/
        @[inline] def $(Lean.mkIdent `spec) [self : Capability $family $op] :
            OperationSignature $family $op :=
          Capability.spec (self := self))
  | `(declare_execfloat_capability candidates for $op:term on $family:term using $_policy:term) =>
      `(
        /-- Certified kernels offered by this capability. -/
        @[inline] def $(Lean.mkIdent `candidates) [self : Capability $family $op] :
            Backend.CandidateSet
              (Backend.Certified ($(Lean.mkIdent `spec) (F := $family))) :=
          Capability.candidates (self := self))
  | `(declare_execfloat_capability policy for $_op:term on $_family:term using $policy:term) =>
      `(
        /-- Workload and resource policy shared by planning and execution. -/
        @[inline] def $(Lean.mkIdent `policy) : Backend.Policy :=
          $policy)
  | `(declare_execfloat_capability selected for $op:term on $family:term using $_policy:term) =>
      `(
        /-- Certified implementation selected from the candidates supplied by the format. -/
        @[inline] def $(Lean.mkIdent `selected) [Capability $family $op] :
            Backend.Certified ($(Lean.mkIdent `spec) (F := $family)) :=
          Capability.selected (F := $family) (operation := $op))
  | `(declare_execfloat_capability selectedEqPlanner for $op:term on $family:term using
    $policy:term) =>
      `(
        /-- The stored selected certificate equals the planner's result. -/
        theorem $(Lean.mkIdent `selected_eq_planner) [Capability $family $op] :
            $(Lean.mkIdent `selected) (F := $family) =
              Backend.selectCertified $policy
                ($(Lean.mkIdent `candidates) (F := $family)) :=
          Capability.selected_eq_planner (F := $family) (operation := $op))
  | `(declare_execfloat_capability selectedCandidate for $op:term on $family:term using
    $_policy:term) =>
      `(
        /-- Static estimate attached to the selected implementation. -/
        @[inline] def $(Lean.mkIdent `selectedCandidate)
            [Capability $family $op] : Backend.Candidate :=
          Capability.selectedCandidate (F := $family) (operation := $op))
  | `(declare_execfloat_capability binaryRun for $op:term on $family:term using $_policy:term) =>
      `(
        /-- Execute the selected binary kernel. -/
        @[inline] def $(Lean.mkIdent `run) [Capability $family $op]
            (left right : ExecFloat $family) : ExecFloat $family :=
          Capability.run (F := $family) (operation := $op) left right)
  | `(declare_execfloat_capability binaryRefinement for $op:term on $family:term using
    $_policy:term) =>
      `(
        /-- The selected binary kernel agrees with its reference operation. -/
        theorem $(Lean.mkIdent `run_eq_spec) [Capability $family $op]
            (left right : ExecFloat $family) :
            $(Lean.mkIdent `run) left right =
              $(Lean.mkIdent `spec) left right := by
          exact congrFun
            (congrFun
              (Capability.run_eq_spec (F := $family) (operation := $op)) left)
            right)
  | `(declare_execfloat_capability unaryRun for $op:term on $family:term using $_policy:term) =>
      `(
        /-- Execute the selected unary kernel. -/
        @[inline] def $(Lean.mkIdent `run) [Capability $family $op]
            (value : ExecFloat $family) : ExecFloat $family :=
          Capability.run (F := $family) (operation := $op) value)
  | `(declare_execfloat_capability unaryRefinement for $op:term on $family:term using
    $_policy:term) =>
      `(
        /-- The selected unary kernel agrees with its reference operation. -/
        theorem $(Lean.mkIdent `run_eq_spec) [Capability $family $op]
            (value : ExecFloat $family) :
            $(Lean.mkIdent `run) value = $(Lean.mkIdent `spec) value := by
          exact congrFun
            (Capability.run_eq_spec (F := $family) (operation := $op)) value)
  | `(declare_execfloat_capability ternaryRun for $op:term on $family:term using $_policy:term) =>
      `(
        /-- Execute the selected ternary kernel. -/
        @[inline] def $(Lean.mkIdent `run) [Capability $family $op]
            (left right addend : ExecFloat $family) : ExecFloat $family :=
          Capability.run (F := $family) (operation := $op) left right addend)
  | `(declare_execfloat_capability ternaryRefinement for $op:term on $family:term using
    $_policy:term) =>
      `(
        /-- The selected ternary kernel agrees with its reference operation. -/
        theorem $(Lean.mkIdent `run_eq_spec) [Capability $family $op]
            (left right addend : ExecFloat $family) :
            $(Lean.mkIdent `run) left right addend =
              $(Lean.mkIdent `spec) left right addend := by
          exact congrFun
            (congrFun
              (congrFun
                (Capability.run_eq_spec (F := $family) (operation := $op)) left)
              right)
            addend)

end ExecFloat

end FloatLib.Floats
