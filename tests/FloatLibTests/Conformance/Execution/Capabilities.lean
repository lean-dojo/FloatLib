/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Automation
public import FloatLibTests.Fixtures.CustomByte
import FloatLib.Floats.ExecFloat.Backends.Selection.Report

/-!
# Capability automation checks

A custom byte carrier with a projection operation tests backend selection and rewriting nested
`ExecFloat` expressions to their specifications. The small reference operation makes the selected
candidate and resulting proof easy to inspect.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Execution.Capabilities

open FloatLibTests.Fixtures.CustomByte

/-- The same selector used by built-in formats chooses the custom format's faster certificate. -/
example :
    FloatLib.Floats.ExecFloat.Add.selectedCandidate (F := TestByte) =
      { name := "custom TestByte projection kernel"
        kind := .custom "custom projection kernel" 2
        steadyCost := 10 } := by
  rfl

/-- The decision report records why an otherwise faster custom kernel was rejected. -/
example :
    (FloatLib.Floats.ExecFloat.Backend.selectionReport
      FloatLib.Floats.ExecFloat.Backend.Policy.default
      (FloatLib.Floats.ExecFloat.Add.candidates (F := TestByte)).estimates).assessments.map
      (fun assessment => assessment.status) =
      [ .rejectedResidentMemory (32 * 1024 * 1024) (1024 * 1024)
      , .notPreferred
      , .selected
      , .notPreferred
      ] := by
  rfl

namespace LatencyPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningLatency

/-- A custom carrier automatically receives the latency policy without changing its value type. -/
example :
    FloatLib.Floats.ExecFloat.Add.policy (F := TestByte) =
      FloatLib.Floats.ExecFloat.Backend.Policy.latency := by
  rfl

/-- The first-call profile avoids the custom lazy specialization's setup cost. -/
example :
    (FloatLib.Floats.ExecFloat.Add.selectedCandidate (F := TestByte)).name =
      "custom TestByte projection kernel" := by
  rfl

end LatencyPlan

namespace ThroughputPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

/-- The identical custom type receives the throughput policy through the universal mechanism. -/
example :
    FloatLib.Floats.ExecFloat.Add.policy (F := TestByte) =
      FloatLib.Floats.ExecFloat.Backend.Policy.throughput := by
  rfl

/-- A long workload amortizes setup and changes the automatically selected custom kernel. -/
example :
    (FloatLib.Floats.ExecFloat.Add.selectedCandidate (F := TestByte)).name =
      "custom TestByte lazy specialization" := by
  rfl

end ThroughputPlan

/-- The universal tactic rewrites nested public calls without unfolding their backend. -/
example (left middle right : FloatLib.Floats.ExecFloat TestByte) :
    FloatLib.Floats.ExecFloat.add
        (FloatLib.Floats.ExecFloat.add left middle) right =
      FloatLib.Floats.ExecFloat.Spec.add
        (FloatLib.Floats.ExecFloat.Spec.add left middle) right := by
  execfloat_spec

end FloatLibTests.Conformance.Execution.Capabilities
