/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Proof
public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.ExecFloat.Spec.Arithmetic
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public import FloatLib.Floats.ExecFloat.Proof.Certificate
public import FloatLib.Floats.ExecFloat.Automation

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
-/

@[expose] public section
