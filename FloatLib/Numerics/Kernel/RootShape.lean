/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Shape
public import FloatLib.Numerics.Kernel.Root

/-!
# The integer roots as Lean's kernel evaluates them best

`isRoot.kernel`, `rootGuess.kernel`, `sqrtGuess.kernel` and `isqrt.kernel` are the definitions
of `FloatLib.Numerics.Kernel.Root` with recursors and literals, on `size.kernel`. A staged
definition that takes an integer square root reaches them through its own `kernel_shape`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

kernel_shape isRoot
kernel_shape rootGuess
kernel_shape sqrtGuess inlining [minNat, ceilDiv]
kernel_shape isqrt inlining [isRoot]

end FloatLib.Numerics.Kernel
