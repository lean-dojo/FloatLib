/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Plan.Runtime

/-!
# Static-byte planning correctness

Static profile selection and first-order dispatch agree with the shared cost model and exact
operation specifications.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

namespace Plans
/-- Static profile selection is extensionally the shared cost-model decision. -/
theorem BuiltinSelection.select_eq_tablePreferred {format : FloatFormat}
    {name : String}
    {operation : FloatLib.Floats.ExecFloat.Backend.Operation}
    (selection : BuiltinSelection format name operation)
    (profile : FloatLib.Floats.ExecFloat.Backend.PolicyProfile) :
    selection.select profile =
      tablePreferred format profile.policy name operation := by
  cases profile with
  | latency => exact selection.latency_eq
  | balanced => exact selection.balanced_eq
  | throughput => exact selection.throughput_eq
  | custom policy => rfl
/-- First-order binary dispatch preserves the specification for every planning policy. -/
theorem executeBinary_eq_spec {F : Type u} [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (selection : BuiltinSelection (Family.format (F := F)) name operation)
    (spec run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ left right, run left right = spec left right)
    (left right : FloatLib.Floats.ExecFloat F) :
    executeBinary name operation selection spec run left right =
      spec left right := by
  unfold executeBinary
  split
  · exact run_eq_spec left right
  · rfl
/-- First-order unary dispatch preserves the specification for every planning policy. -/
theorem executeUnary_eq_spec {F : Type u} [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (selection : BuiltinSelection (Family.format (F := F)) name operation)
    (spec run :
      FloatLib.Floats.ExecFloat F → FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ value, run value = spec value)
    (value : FloatLib.Floats.ExecFloat F) :
    executeUnary name operation selection spec run value = spec value := by
  unfold executeUnary
  split
  · exact run_eq_spec value
  · rfl
/-- First-order ternary dispatch preserves the specification for every planning policy. -/
theorem executeTernary_eq_spec {F : Type u} [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (selection : BuiltinSelection (Family.format (F := F)) name operation)
    (spec tableRun exactRun :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (tableRun_eq_spec :
      ∀ left right addend,
        tableRun left right addend = spec left right addend)
    (exactRun_eq_spec :
      ∀ left right addend,
        exactRun left right addend = spec left right addend)
    (left right addend : FloatLib.Floats.ExecFloat F) :
    executeTernary name operation selection tableRun exactRun left right addend =
      spec left right addend := by
  unfold executeTernary
  split
  · exact tableRun_eq_spec left right addend
  · exact exactRun_eq_spec left right addend
end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
