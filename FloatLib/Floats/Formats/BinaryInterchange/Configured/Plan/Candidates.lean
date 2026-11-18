/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Estimates
public import FloatLib.Tactic.CandidateSet
public import FloatLib.Tactic.CompilerOptimize

/-!
# Structural candidate portfolios for configured binary formats

Each operation receives the single structural route entered by its executable dispatcher. Callers
may prepend representation-specific direct candidates. For every precision and encoding, the
generic kernel is the certified total baseline.

The constructors are planning-time code and are marked `@[nospecialize]`. Their closures contain
the inlined word dispatchers. Specializing them for every storage plan of `Configured.Code` would
duplicate that code once per plan and operation, and it would do nothing for the arithmetic hot
path, which reaches the kernels through the first-order `execute` entry points.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend
/-! ## Complete per-operation candidate sets -/

candidate_set Add add binary "addition"
candidate_set Sub sub binary "subtraction"
candidate_set Mul mul binary "multiplication"
candidate_set Div div binary "division"
candidate_set Sqrt sqrt unary routed "square-root"
candidate_set Fma fma ternary routed "fused-multiply-add"

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
