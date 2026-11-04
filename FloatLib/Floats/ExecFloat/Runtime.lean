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

Import this module when a program needs the universal carrier, comparison, conversion,
destination-driven mixed arithmetic, same-format arithmetic capabilities, public dispatch functions,
and ordinary operator instances, and doesn't need proof automation or the `#float_info` elaborator.

Installed arithmetic capabilities keep their certified implementations. What the import leaves out
is the re-export of reference definitions, user-facing correctness theorems, automation attributes,
and inspection commands that a downstream runtime module doesn't use. Conversion stays proof-linked
through this execution-only API as well, since every destination `Quantizer` stores a mathematical
contract and an implementation theorem, but the theorem names aren't re-exported here.

For the complete user interface, use `FloatLib.Floats.ExecFloat`.
-/

@[expose] public section
