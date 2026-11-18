/-
Copyright (c) 2026 Robert Weller
Released under MIT license as described in the file LICENSE.
Authors: Robert Weller
-/
module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Proof
public import FloatLib.Tactic.FamilyCapability

/-!
# Default static-byte capability construction

Byte-sized binary families get their final wiring here. Each family-selected kernel is packaged
with its refinement theorem from `Backend.Proof`, tagged as the family's baseline
(`@[compiler_optimize baseline]`), and installed as an ordinary `ExecFloat` capability.

The construction is shared, so the six operations do not each need a family-specific adapter.
Every `Family` instance uses it and supplies its own certified kernel, which may use a table or
compute the operation itself. Where no tagged alternative applies the kernel is called
directly, and otherwise the planner selects among the kernel and the tagged alternatives.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

family_capability add "addition" binary

family_capability sub "subtraction" binary

family_capability mul "multiplication" binary

family_capability div "division" binary

family_capability sqrt "square root" unary

/-
`TablePlan` has no FMA table, so a plan does not replace the default fused multiply-add. A
package that wants a table or model FMA declares its own `Fma` instance, such as
`Plans.fmaTableCapability` or `Plans.modelFmaCapability`, which outranks this one.
-/
family_capability fma "fused multiply-add" ternary

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
