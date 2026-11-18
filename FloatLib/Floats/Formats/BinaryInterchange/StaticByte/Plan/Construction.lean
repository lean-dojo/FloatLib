/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.ByteCapability
public import FloatLib.Tactic.ByteTableCapability
public import FloatLib.Tactic.TablePlanCapability

/-!
# Static-byte capability construction

Here static-byte candidates and first-order dispatchers become verified `ExecFloat` capabilities.
The planner chooses between a table and a direct kernel, and these constructors attach the
matching refinement theorem and expose the result through the shared operation interfaces.
Runtime planning stays in `Plan.Runtime`, and the equations used here are in `Plan.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

namespace Plans

open FloatLib.Floats.ExecFloat

/--
The common table plan for a nominal static-byte format.

The record supplies certified tables and profile choices for four binary operations and square
root. FMA is handled on its own: a package can offer a table candidate or use a model kernel.

Concrete instances should be marked `instance_reducible`. The capability instances below can then
specialize each projection to the same first-order table kernel that a hand-written per-format
instance would name.
-/
class TablePlan (F : Type u) [Family F] where
  /-- Human-readable family prefix used in the five table candidate names. -/
  namePrefix : String
  /-- Built-in profile decisions for addition. -/
  addSelection :
    BuiltinSelection (Family.format (F := F)) (namePrefix ++ " addition table") .add
  /-- Certified addition table. -/
  addTable : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
    (encoding (Family.format (F := F)) (Family.width_le_eight (F := F)))
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add
  /-- Built-in profile decisions for subtraction. -/
  subSelection :
    BuiltinSelection (Family.format (F := F)) (namePrefix ++ " subtraction table") .sub
  /-- Certified subtraction table. -/
  subTable : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
    (encoding (Family.format (F := F)) (Family.width_le_eight (F := F)))
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub
  /-- Built-in profile decisions for multiplication. -/
  mulSelection :
    BuiltinSelection (Family.format (F := F)) (namePrefix ++ " multiplication table") .mul
  /-- Certified multiplication table. -/
  mulTable : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
    (encoding (Family.format (F := F)) (Family.width_le_eight (F := F)))
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul
  /-- Built-in profile decisions for division. -/
  divSelection :
    BuiltinSelection (Family.format (F := F)) (namePrefix ++ " division table") .div
  /-- Certified division table. -/
  divTable : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
    (encoding (Family.format (F := F)) (Family.width_le_eight (F := F)))
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div
  /-- Built-in profile decisions for square root. -/
  sqrtSelection :
    BuiltinSelection (Family.format (F := F)) (namePrefix ++ " square-root table") .sqrt
  /-- Certified square-root table. -/
  sqrtTable : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedUnary
    (encoding (Family.format (F := F)) (Family.width_le_eight (F := F)))
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt

namespace TablePlan

/-- Name reported for the certified addition table. -/
@[inline] def addName {F : Type u} [Family F] (plan : TablePlan F) : String :=
  plan.namePrefix ++ " addition table"

/-- Name reported for the certified subtraction table. -/
@[inline] def subName {F : Type u} [Family F] (plan : TablePlan F) : String :=
  plan.namePrefix ++ " subtraction table"

/-- Name reported for the certified multiplication table. -/
@[inline] def mulName {F : Type u} [Family F] (plan : TablePlan F) : String :=
  plan.namePrefix ++ " multiplication table"

/-- Name reported for the certified division table. -/
@[inline] def divName {F : Type u} [Family F] (plan : TablePlan F) : String :=
  plan.namePrefix ++ " division table"

/-- Name reported for the certified square-root table. -/
@[inline] def sqrtName {F : Type u} [Family F] (plan : TablePlan F) : String :=
  plan.namePrefix ++ " square-root table"

end TablePlan

namespace Internal

byte_capability Add add binaryTable executeBinary executeBinary_eq_spec (left right) "addition"
byte_capability Sub sub binaryTable executeBinary executeBinary_eq_spec (left right) "subtraction"
byte_capability Mul mul binaryTable executeBinary executeBinary_eq_spec (left right)
  "multiplication"
byte_capability Div div binaryTable executeBinary executeBinary_eq_spec (left right) "division"
byte_capability Sqrt sqrt unaryTable executeUnary executeUnary_eq_spec (value) "square-root"

/-- Construct a static-byte FMA capability from named table and exact kernels. -/
@[always_inline, instance_reducible] def fmaCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .fma)
    (run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (run_eq_spec :
      ∀ left right addend,
        run left right addend = Spec.fma left right addend)
    (exactRun :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (exactRun_eq_spec :
      ∀ left right addend,
        exactRun left right addend = Spec.fma left right addend) :
    FloatLib.Floats.ExecFloat.Fma F :=
  Capability.ofCandidates .fma Spec.fma
    (ternaryTable name .fma Spec.fma
      run exactRun run_eq_spec exactRun_eq_spec)
    (executeTernary name .fma selection run exactRun)
    (by
      funext left right addend
      exact executeTernary_eq_spec
        name .fma selection Spec.fma run exactRun
        run_eq_spec exactRun_eq_spec left right addend)

/-- Construct an exact-only static-byte FMA without retaining certificate closure dispatch. -/
@[always_inline, instance_reducible] def directFmaCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (run_eq_spec :
      ∀ left right addend,
        run left right addend = Spec.fma left right addend) :
    FloatLib.Floats.ExecFloat.Fma F :=
  Capability.ofDirectKernel .fma Spec.fma
    (FloatLib.Floats.ExecFloat.Backend.Certified.ternary
      (exactEstimate .fma) Spec.fma run run_eq_spec)
    run rfl

byte_table_capability Add add CertifiedBinary Backend.Table.binary
  Backend.Table.binary_eq_spec (left right) "an addition"
byte_table_capability Sub sub CertifiedBinary Backend.Table.binary
  Backend.Table.binary_eq_spec (left right) "a subtraction"
byte_table_capability Mul mul CertifiedBinary Backend.Table.binary
  Backend.Table.binary_eq_spec (left right) "a multiplication"
byte_table_capability Div div CertifiedBinary Backend.Table.binary
  Backend.Table.binary_eq_spec (left right) "a division"
byte_table_capability Sqrt sqrt CertifiedUnary Backend.Table.unary
  Backend.Table.unary_eq_spec (value) "a square-root"

end Internal

/--
Construct a policy-selected FMA capability from a certified table and a proved exact kernel.
-/
@[always_inline, instance_reducible] def fmaTableCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .fma)
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedTernary
      (encoding (Family.format (F := F)) width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma)
    (exactRun :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F)))
    (exactRun_eq_spec : ∀ left right addend,
      exactRun left right addend =
        FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma
          left right addend) :
    FloatLib.Floats.ExecFloat.Fma F :=
  Internal.fmaCapability name selection
    (Backend.Table.ternary (F := F)
      (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma)
      width_le_eight table)
    (fun left right addend => by
      simpa only [Spec.fma] using
        (Backend.Table.ternary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma)
          width_le_eight table left right addend))
    (Backend.Model.ternary (F := F) width_le_eight exactRun)
    (fun left right addend => by
      simpa only [Spec.fma] using
        (Backend.Model.ternary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma)
          width_le_eight exactRun exactRun_eq_spec left right addend))

/-- Construct an exact-only FMA capability from a proved model-level kernel. -/
@[always_inline, instance_reducible] def modelFmaCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (run :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F)))
    (run_eq_spec : ∀ left right addend,
      run left right addend =
        FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma
          left right addend) :
    FloatLib.Floats.ExecFloat.Fma F :=
  Internal.directFmaCapability
    (Backend.Model.ternary (F := F) width_le_eight run)
    (fun left right addend => by
      simpa only [Spec.fma] using
        (Backend.Model.ternary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma)
          width_le_eight run run_eq_spec left right addend))

/-!
The planned instances outrank the direct-family instances in `StaticByte.Backend.Construction` on
purpose. So a static-byte family without a `TablePlan` keeps its ordinary family kernels, and with
a `TablePlan` the planning profile chooses between a table and the exact baseline. Each instance
is a `Capability.Static`: a candidate tagged `@[compiler_optimize]` for the family's reference
operation is considered next to that choice.
-/

table_plan_capability Add add "addition"
table_plan_capability Sub sub "subtraction"
table_plan_capability Mul mul "multiplication"
table_plan_capability Div div "division"
table_plan_capability Sqrt sqrt "square root"

end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
