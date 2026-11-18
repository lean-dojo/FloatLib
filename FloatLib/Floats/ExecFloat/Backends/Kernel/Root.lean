/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.KernelOptimize
public import FloatLib.Numerics.Kernel.RootProof

/-!
# Exact integer square roots for Lean's kernel

The shared `Numerics.Kernel.isqrt_eq` theorem identifies the checked Newton
candidate, with its unrestricted fallback, with `Nat.sqrt` for every natural
input. Register its reverse equation here so prepared functions in importing
modules can reuse both the implementation and the simplifier's proof.

The rule changes evaluation only. It adds no convergence assumption, trusted
evaluator or bound on kernel time.
-/

attribute [kernel_optimize ←] FloatLib.Numerics.Kernel.isqrt_eq
