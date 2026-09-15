/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.ExecFloat.Comparison
public import FloatLib.Floats.ExecFloat.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Dispatch
public import FloatLib.Floats.ExecFloat.Instances

/-!
# Execution-only `ExecFloat` interface

Import this module when a program needs the universal carrier, comparison, explicit conversion,
destination-driven mixed arithmetic, same-format arithmetic capabilities, public dispatch
functions, and ordinary operator instances without importing proof automation or the
`#float_info` elaborator.

Every installed arithmetic capability still stores a certified implementation. This import
avoids re-exporting reference
definitions, user-facing correctness theorems, automation attributes, and inspection commands
when a downstream runtime module does not use them.

Conversion remains proof-linked through this execution-only API: every destination
`Quantizer` stores a mathematical contract and an implementation theorem. The theorem names are
not re-exported through this runtime-focused import.

Use `FloatLib.Floats.ExecFloat` for the complete user interface.
-/

@[expose] public section
