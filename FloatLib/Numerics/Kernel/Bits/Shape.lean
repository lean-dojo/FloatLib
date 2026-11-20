/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits
public import FloatLib.Tactic.KernelShape

/-!
# The bit operations as Lean's kernel evaluates them best

The definitions of `FloatLib.Numerics.Kernel.Bits` branch with `Bool.casesOn` and write their
constants as numerals, so that Lean compiles them. `kernel_shape` gives each the definition that
the kernel evaluates in fewer steps: recursors, literals, and the lane constants of a fixed
width computed once, when this module is checked. `size.kernel` has the lanes of 64 bits
unfolded with their two constants of 4,096 and 4,160 bits as literals, so a bit length below
`2 ^ 128` is one or two tests and five operations, and one below `2 ^ 256` two tests more. The
halvings above (`size256`, `size512`, `sizeAbove`) have their shapes too.

A staged definition that calls these functions reaches the shapes through its own
`kernel_shape`. The recursions `searchLength` and `windowLength` keep their definitions.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

kernel_shape laneOnes
kernel_shape laneOffsets
kernel_shape laneLength
kernel_shape size128 inlining [laneLength, laneOnes, laneOffsets]
kernel_shape size256
kernel_shape size512
kernel_shape sizeAbove
kernel_shape size inlining [laneLength, laneOnes, laneOffsets]
kernel_shape bitLength
kernel_shape bit
kernel_shape testBit
kernel_shape lowBits
kernel_shape ceilShift
kernel_shape ceilDiv
kernel_shape maxNat
kernel_shape minNat

end FloatLib.Numerics.Kernel
