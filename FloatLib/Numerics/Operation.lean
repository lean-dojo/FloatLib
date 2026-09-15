/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Proof
public import FloatLib.Numerics.Operation.Context
public import FloatLib.Numerics.Operation.Entropy
public import FloatLib.Numerics.Operation.Status

/-!
# Executable numerical-operation contracts

Numerical-operation contracts provide arity-neutral relations, named unary/binary/ternary forms,
standard total and checked semantics, proof-indexed application helpers, and composition laws.
All contracts are propositions, so optimized runtime kernels retain their concrete monomorphic
function signatures.
-/

@[expose] public section
