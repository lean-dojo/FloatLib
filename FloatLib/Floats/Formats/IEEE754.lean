/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.IEEE754.Native
public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.Integer
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.Formats.IEEE754.Native.Sqrt
public meta import FloatLib.Floats.Formats.IEEE754.Native.Info

/-!
# IEEE 754 format packages

`IEEE754.Native` provides the explicit, model-aware boundary from the parameterized
`ExecFloat.Binary` family to Lean's runtime `Float32` and binary64 `Float` types. IEEE layouts,
semantics, and certified execution remain in `Formats.BinaryInterchange`; there is no second
width-specific executable carrier. The representation proofs connect those adapters to Lean's
packed models, including the named NaN and infinity constants exposed in Lean 4.34.
Integer conversion proofs connect the newly exposed constructors and signed casts to FloatLib's
rounding specifications. Arithmetic bridges cover addition and subtraction on finite inputs and
square root on every input, with NaNs canonicalized at the native boundary.
Importing this entry point also registers `#float_info` reports for the two native runtime types.

## Reference

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
-/

@[expose] public section
