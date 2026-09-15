/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.IEEE754.Native
public meta import FloatLib.Floats.Formats.IEEE754.Native.Info

/-!
# IEEE 754 format packages

`IEEE754.Native` provides the explicit, model-aware boundary from the parameterized
`ExecFloat.Binary` family to Lean's runtime `Float32` and binary64 `Float` types. IEEE layouts,
semantics, and certified execution remain in `Formats.BinaryInterchange`; there is no second
width-specific executable carrier. Importing this entry point also registers
`#float_info` reports for the two native runtime types.

## Reference

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
-/

@[expose] public section
