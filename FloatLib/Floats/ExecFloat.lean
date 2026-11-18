/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.CompilerBackends
public meta import FloatLib.Tactic.KernelCost
public meta import FloatLib.Tactic.KernelRules
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Numerics.Executable.Conversion.Proof
public import FloatLib.Numerics.Executable.Packed
public import FloatLib.Kernels.Execution.Proof
public import FloatLib.Kernels.Execution.Certificate
public import FloatLib.Floats.ExecFloat.Runtime
public import FloatLib.Kernels.Execution.Spec
public import FloatLib.Tactic.ExecFloatSpec
public import FloatLib.Tactic.FloatInfo
public import FloatLib.Tactic.KernelEval
public import FloatLib.Tactic.KernelTwin

/-!
# Executable numerical values

An `ExecFloat F` holds its value in whatever code type the format `F` chose, and each format
supplies its own arithmetic capabilities. Notation and named calls such as `ExecFloat.add` run the
same selected implementation, and `ExecFloat.Proof.*_eq_spec` rewrites either form to its
reference definition in `ExecFloat.Spec`.

A conversion is named by its destination type. Mixed operations such as `Mixed.add` name their
result type in the same way, and `roundOnce` evaluates a finite expression in the destination's
exact domain and quantizes it once.

Which backend a format gets is decided from certified candidates and their cost estimates.
`#float_info` shows you that choice and the theorems that come with it. The directory README
explains conversion, backend definitions and the checks on generated code. If you only need the
runtime pieces, without proofs or inspection commands, import `FloatLib.Floats.ExecFloat.Runtime`.

`#kernel_eval t` evaluates a term with Lean's kernel and prints the value and the time, which is
what a proof by `decide +kernel` pays for a computation.

`packed_values` brings a list of values of any format with an exact rational meaning into a packed
row at one common scale, for kernel-checked certificates about the numbers a program computed.
-/

@[expose] public section
