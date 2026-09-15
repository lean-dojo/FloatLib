/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Plan.Proof
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Static-byte capability construction

Static-byte candidates and first-order dispatchers form verified `ExecFloat` capabilities.
Runtime planning remains in `Plan.Runtime`; the equations consumed here are isolated in
`Plan.Proof`.

The planner chooses between a table and a direct kernel. These constructors attach the
corresponding refinement theorem and expose the result through the shared operation interfaces.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

namespace Plans

open FloatLib.Floats.ExecFloat

/--
The common table plan for a nominal static-byte format.

The record supplies certified tables and profile choices for four binary operations and square
root. FMA is separate: a package can offer a table candidate or use a model kernel directly.

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

/-- Construct a static-byte addition capability with certified profile selection. -/
@[always_inline, instance_reducible] def addCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .add)
    (run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec :
      ∀ left right, run left right = Spec.add left right) :
    FloatLib.Floats.ExecFloat.Add F :=
  Capability.ofCandidates .add Spec.add
    (binaryTable name .add Spec.add run run_eq_spec)
    (executeBinary name .add selection Spec.add run)
    (by
      funext left right
      exact executeBinary_eq_spec
        name .add selection Spec.add run run_eq_spec left right)

/-- Construct a static-byte subtraction capability with certified profile selection. -/
@[always_inline, instance_reducible] def subCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .sub)
    (run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec :
      ∀ left right, run left right = Spec.sub left right) :
    FloatLib.Floats.ExecFloat.Sub F :=
  Capability.ofCandidates .sub Spec.sub
    (binaryTable name .sub Spec.sub run run_eq_spec)
    (executeBinary name .sub selection Spec.sub run)
    (by
      funext left right
      exact executeBinary_eq_spec
        name .sub selection Spec.sub run run_eq_spec left right)

/-- Construct a static-byte multiplication capability with certified profile selection. -/
@[always_inline, instance_reducible] def mulCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .mul)
    (run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec :
      ∀ left right, run left right = Spec.mul left right) :
    FloatLib.Floats.ExecFloat.Mul F :=
  Capability.ofCandidates .mul Spec.mul
    (binaryTable name .mul Spec.mul run run_eq_spec)
    (executeBinary name .mul selection Spec.mul run)
    (by
      funext left right
      exact executeBinary_eq_spec
        name .mul selection Spec.mul run run_eq_spec left right)

/-- Construct a static-byte division capability with certified profile selection. -/
@[always_inline, instance_reducible] def divCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .div)
    (run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec :
      ∀ left right, run left right = Spec.div left right) :
    FloatLib.Floats.ExecFloat.Div F :=
  Capability.ofCandidates .div Spec.div
    (binaryTable name .div Spec.div run run_eq_spec)
    (executeBinary name .div selection Spec.div run)
    (by
      funext left right
      exact executeBinary_eq_spec
        name .div selection Spec.div run run_eq_spec left right)

/-- Construct a static-byte square-root capability with certified profile selection. -/
@[always_inline, instance_reducible] def sqrtCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .sqrt)
    (run : FloatLib.Floats.ExecFloat F → FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ value, run value = Spec.sqrt value) :
    FloatLib.Floats.ExecFloat.Sqrt F :=
  Capability.ofCandidates .sqrt Spec.sqrt
    (unaryTable name .sqrt Spec.sqrt run run_eq_spec)
    (executeUnary name .sqrt selection Spec.sqrt run)
    (by
      funext value
      exact executeUnary_eq_spec
        name .sqrt selection Spec.sqrt run run_eq_spec value)

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

/--
Construct an addition capability directly from a certified byte table.

The executable table lookup and its refinement proof are derived from the same certificate, so a
format package cannot accidentally pair a kernel with the wrong theorem.
-/
@[always_inline, instance_reducible] def addTableCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .add)
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add) :
    FloatLib.Floats.ExecFloat.Add F :=
  addCapability name selection
    (Backend.Table.binary (F := F)
      (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add)
      width_le_eight table)
    (fun left right => by
      simpa only [Spec.add] using
        (Backend.Table.binary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add)
          width_le_eight table left right))

/-- Construct a subtraction capability directly from a certified byte table. -/
@[always_inline, instance_reducible] def subTableCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .sub)
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub) :
    FloatLib.Floats.ExecFloat.Sub F :=
  subCapability name selection
    (Backend.Table.binary (F := F)
      (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub)
      width_le_eight table)
    (fun left right => by
      simpa only [Spec.sub] using
        (Backend.Table.binary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub)
          width_le_eight table left right))

/-- Construct a multiplication capability directly from a certified byte table. -/
@[always_inline, instance_reducible] def mulTableCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .mul)
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul) :
    FloatLib.Floats.ExecFloat.Mul F :=
  mulCapability name selection
    (Backend.Table.binary (F := F)
      (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul)
      width_le_eight table)
    (fun left right => by
      simpa only [Spec.mul] using
        (Backend.Table.binary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul)
          width_le_eight table left right))

/-- Construct a division capability directly from a certified byte table. -/
@[always_inline, instance_reducible] def divTableCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .div)
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div) :
    FloatLib.Floats.ExecFloat.Div F :=
  divCapability name selection
    (Backend.Table.binary (F := F)
      (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div)
      width_le_eight table)
    (fun left right => by
      simpa only [Spec.div] using
        (Backend.Table.binary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div)
          width_le_eight table left right))

/-- Construct a square-root capability directly from a certified byte table. -/
@[always_inline, instance_reducible] def sqrtTableCapability
    {F : Type u} [Family F]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (selection : BuiltinSelection (Family.format (F := F)) name .sqrt)
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedUnary
      (encoding (Family.format (F := F)) width_le_eight)
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt) :
    FloatLib.Floats.ExecFloat.Sqrt F :=
  sqrtCapability name selection
    (Backend.Table.unary (F := F)
      (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt)
      width_le_eight table)
    (fun value => by
      simpa only [Spec.sqrt] using
        (Backend.Table.unary_eq_spec (F := F)
          (modelSpec := FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt)
          width_le_eight table value))

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
The planned instances deliberately outrank the direct-family instances in
`StaticByte.Backend.Construction`. A static-byte family without a `TablePlan` therefore keeps its
ordinary family kernels. With a `TablePlan`, the planning profile chooses between a table and
the exact baseline.
-/

@[always_inline, instance_reducible] instance (priority := 200) tablePlanAddCapability
    (F : Type u) [Family F] [plan : TablePlan F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    FloatLib.Floats.ExecFloat.Add F :=
  Internal.addTableCapability plan.addName plan.addSelection
    (Family.width_le_eight (F := F)) plan.addTable

@[always_inline, instance_reducible] instance (priority := 200) tablePlanSubCapability
    (F : Type u) [Family F] [plan : TablePlan F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    FloatLib.Floats.ExecFloat.Sub F :=
  Internal.subTableCapability plan.subName plan.subSelection
    (Family.width_le_eight (F := F)) plan.subTable

@[always_inline, instance_reducible] instance (priority := 200) tablePlanMulCapability
    (F : Type u) [Family F] [plan : TablePlan F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    FloatLib.Floats.ExecFloat.Mul F :=
  Internal.mulTableCapability plan.mulName plan.mulSelection
    (Family.width_le_eight (F := F)) plan.mulTable

@[always_inline, instance_reducible] instance (priority := 200) tablePlanDivCapability
    (F : Type u) [Family F] [plan : TablePlan F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    FloatLib.Floats.ExecFloat.Div F :=
  Internal.divTableCapability plan.divName plan.divSelection
    (Family.width_le_eight (F := F)) plan.divTable

@[always_inline, instance_reducible] instance (priority := 200) tablePlanSqrtCapability
    (F : Type u) [Family F] [plan : TablePlan F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    FloatLib.Floats.ExecFloat.Sqrt F :=
  Internal.sqrtTableCapability plan.sqrtName plan.sqrtSelection
    (Family.width_le_eight (F := F)) plan.sqrtTable

end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
