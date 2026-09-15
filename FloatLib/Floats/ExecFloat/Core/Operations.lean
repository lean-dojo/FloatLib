/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Uniform operation-specific capability API

The public `Add`, `Sub`, `Mul`, `Div`, `Sqrt`, and `Fma` namespaces derive their interfaces from
the single indexed `Capability` contract. Each namespace exposes the same planning and
certification surface while retaining the operation's natural arity.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

variable {F : Type u} [EncodedFormat F]
    [planning : Backend.PolicyFor F]

/--
Generate the public operation namespace for one indexed arithmetic capability.

Only the arity-specific executable and pointwise refinement theorem differ between operations.
Keeping that distinction in a small local command vocabulary avoids six copies of the planner
projections while preserving the existing operation namespaces.
-/
local syntax (name := declareExecFloatCapability)
  "declare_execfloat_capability " ident " for " term : command

local macro_rules
  | `(declare_execfloat_capability spec for $op:term) =>
      `(
        /-- Clear reference operation for this capability. -/
        @[inline] def $(Lean.mkIdent `spec) [self : Capability F $op] :
            OperationSignature F $op :=
          Capability.spec (self := self))
  | `(declare_execfloat_capability candidates for $op:term) =>
      `(
        /-- Certified kernels offered by this capability. -/
        @[inline] def $(Lean.mkIdent `candidates) [self : Capability F $op] :
            Backend.CandidateSet
              (Backend.Certified ($(Lean.mkIdent `spec) (F := F))) :=
          Capability.candidates (self := self))
  | `(declare_execfloat_capability policy for $_op:term) =>
      `(
        /-- Workload and resource policy shared by planning and execution. -/
        @[inline] def $(Lean.mkIdent `policy) : Backend.Policy :=
          planning.policy)
  | `(declare_execfloat_capability selected for $op:term) =>
      `(
        /-- Certified implementation selected from the candidates supplied by the format. -/
        @[inline] def $(Lean.mkIdent `selected) [Capability F $op] :
            Backend.Certified ($(Lean.mkIdent `spec) (F := F)) :=
          Capability.selected (F := F) (operation := $op))
  | `(declare_execfloat_capability selectedEqPlanner for $op:term) =>
      `(
        /-- The stored selected certificate equals the planner's result. -/
        theorem $(Lean.mkIdent `selected_eq_planner) [Capability F $op] :
            $(Lean.mkIdent `selected) (F := F) =
              Backend.selectCertified planning.policy
                ($(Lean.mkIdent `candidates) (F := F)) :=
          Capability.selected_eq_planner (F := F) (operation := $op))
  | `(declare_execfloat_capability selectedCandidate for $op:term) =>
      `(
        /-- Static estimate attached to the selected implementation. -/
        @[inline] def $(Lean.mkIdent `selectedCandidate)
            [Capability F $op] : Backend.Candidate :=
          Capability.selectedCandidate (F := F) (operation := $op))
  | `(declare_execfloat_capability binaryRun for $op:term) =>
      `(
        /-- Execute the selected binary kernel. -/
        @[inline] def $(Lean.mkIdent `run) [Capability F $op]
            (left right : ExecFloat F) : ExecFloat F :=
          Capability.run (F := F) (operation := $op) left right)
  | `(declare_execfloat_capability binaryRefinement for $op:term) =>
      `(
        /-- The selected binary kernel agrees with its reference operation. -/
        theorem $(Lean.mkIdent `run_eq_spec) [Capability F $op]
            (left right : ExecFloat F) :
            $(Lean.mkIdent `run) left right =
              $(Lean.mkIdent `spec) left right := by
          exact congrFun
            (congrFun
              (Capability.run_eq_spec (F := F) (operation := $op)) left)
            right)
  | `(declare_execfloat_capability unaryRun for $op:term) =>
      `(
        /-- Execute the selected unary kernel. -/
        @[inline] def $(Lean.mkIdent `run) [Capability F $op]
            (value : ExecFloat F) : ExecFloat F :=
          Capability.run (F := F) (operation := $op) value)
  | `(declare_execfloat_capability unaryRefinement for $op:term) =>
      `(
        /-- The selected unary kernel agrees with its reference operation. -/
        theorem $(Lean.mkIdent `run_eq_spec) [Capability F $op]
            (value : ExecFloat F) :
            $(Lean.mkIdent `run) value = $(Lean.mkIdent `spec) value := by
          exact congrFun
            (Capability.run_eq_spec (F := F) (operation := $op)) value)
  | `(declare_execfloat_capability ternaryRun for $op:term) =>
      `(
        /-- Execute the selected ternary kernel. -/
        @[inline] def $(Lean.mkIdent `run) [Capability F $op]
            (left right addend : ExecFloat F) : ExecFloat F :=
          Capability.run (F := F) (operation := $op) left right addend)
  | `(declare_execfloat_capability ternaryRefinement for $op:term) =>
      `(
        /-- The selected ternary kernel agrees with its reference operation. -/
        theorem $(Lean.mkIdent `run_eq_spec) [Capability F $op]
            (left right addend : ExecFloat F) :
            $(Lean.mkIdent `run) left right addend =
              $(Lean.mkIdent `spec) left right addend := by
          exact congrFun
            (congrFun
              (congrFun
                (Capability.run_eq_spec (F := F) (operation := $op)) left)
              right)
            addend)

namespace Add

declare_execfloat_capability spec for .add
declare_execfloat_capability candidates for .add
declare_execfloat_capability policy for .add
declare_execfloat_capability selected for .add
declare_execfloat_capability selectedEqPlanner for .add
declare_execfloat_capability selectedCandidate for .add
declare_execfloat_capability binaryRun for .add
declare_execfloat_capability binaryRefinement for .add

end Add

namespace Sub

declare_execfloat_capability spec for .sub
declare_execfloat_capability candidates for .sub
declare_execfloat_capability policy for .sub
declare_execfloat_capability selected for .sub
declare_execfloat_capability selectedEqPlanner for .sub
declare_execfloat_capability selectedCandidate for .sub
declare_execfloat_capability binaryRun for .sub
declare_execfloat_capability binaryRefinement for .sub

end Sub

namespace Mul

declare_execfloat_capability spec for .mul
declare_execfloat_capability candidates for .mul
declare_execfloat_capability policy for .mul
declare_execfloat_capability selected for .mul
declare_execfloat_capability selectedEqPlanner for .mul
declare_execfloat_capability selectedCandidate for .mul
declare_execfloat_capability binaryRun for .mul
declare_execfloat_capability binaryRefinement for .mul

end Mul

namespace Div

declare_execfloat_capability spec for .div
declare_execfloat_capability candidates for .div
declare_execfloat_capability policy for .div
declare_execfloat_capability selected for .div
declare_execfloat_capability selectedEqPlanner for .div
declare_execfloat_capability selectedCandidate for .div
declare_execfloat_capability binaryRun for .div
declare_execfloat_capability binaryRefinement for .div

end Div

namespace Sqrt

declare_execfloat_capability spec for .sqrt
declare_execfloat_capability candidates for .sqrt
declare_execfloat_capability policy for .sqrt
declare_execfloat_capability selected for .sqrt
declare_execfloat_capability selectedEqPlanner for .sqrt
declare_execfloat_capability selectedCandidate for .sqrt
declare_execfloat_capability unaryRun for .sqrt
declare_execfloat_capability unaryRefinement for .sqrt

end Sqrt

namespace Fma

declare_execfloat_capability spec for .fma
declare_execfloat_capability candidates for .fma
declare_execfloat_capability policy for .fma
declare_execfloat_capability selected for .fma
declare_execfloat_capability selectedEqPlanner for .fma
declare_execfloat_capability selectedCandidate for .fma
declare_execfloat_capability ternaryRun for .fma
declare_execfloat_capability ternaryRefinement for .fma

end Fma

end ExecFloat
end FloatLib.Floats
