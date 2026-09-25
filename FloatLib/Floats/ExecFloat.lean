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

`ExecFloat F` stores a value in the code type chosen by format `F`. Formats provide arithmetic
capabilities independently: notation and explicit calls such as `ExecFloat.add` use the same
selected implementation. `ExecFloat.Proof.*_eq_spec` rewrites each operation, in call or notation
form, to its reference definition in `ExecFloat.Spec`.

Conversions name the destination type. Mixed operations such as `addAs` name their result type;
`roundOnce` evaluates a finite expression in that destination's exact domain and quantizes once.

Backend selection uses certified candidates and their cost estimates. `#float_info` reports the
chosen implementation and available theorems. The directory README explains conversion, backend
definitions, and generated-code checks. For runtime infrastructure without proof or inspection
imports, use `FloatLib.Floats.ExecFloat.Runtime`.
-/

@[expose] public section
