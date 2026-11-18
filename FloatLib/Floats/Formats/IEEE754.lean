/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.IEEE754.Native
public import FloatLib.Floats.Formats.IEEE754.Environment
public import FloatLib.Floats.Formats.IEEE754.Native
public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.Half
public import FloatLib.Floats.Formats.IEEE754.Native.Integer
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.Formats.IEEE754.Native.Sqrt

/-!
# IEEE 754 format packages

FloatLib computes binary32 and binary64 with its own proved software kernels, and Lean has
`Float32` and `Float` built in. This package is where the two meet. `IEEE754.Native` is the
boundary from the parameterized `ExecFloat.Binary` family to Lean's runtime `Float32` and binary64
`Float`, and every crossing is a call you make, with a model behind it. IEEE layouts, semantics,
and certified execution stay in `Formats.BinaryInterchange`. This package also exports the
separate native 16-bit carriers `Floats.Native.Half` and `Floats.Native.BFloat16`, which share one
parameterized representation. Their normalization is proved; their host arithmetic is unchecked.

Three groups of proofs accompany the binary32 and binary64 adapters. Representation proofs
connect the adapters to Lean's packed models, Lean's named NaN and infinity constants included.
Integer conversion proofs connect Lean's
constructors and signed casts to FloatLib's rounding specifications. Arithmetic bridges cover
addition, subtraction, multiplication and division on finite inputs and square root on every
input, with NaNs canonicalized at the native boundary. Importing this entry point also
registers `#float_info` reports for the two native runtime types.

`IEEE754.Environment` holds the operations of IEEE 754-2019 that concern the programming
environment and no datum: the conformance predicates `is754version1985`, `is754version2008` and
`is754version2019` (§5.7.1), and the dynamic rounding modes of §9.3 as a value, `Modes`.

## Reference

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
-/

@[expose] public section
