/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.Integer.Constructors
public import FloatLib.Floats.Formats.IEEE754.Native.Integer.FromInt
public import FloatLib.Floats.Formats.IEEE754.Native.Integer.ToInt

/-!
# Native signed integer conversion

Lean 4.34 gives signed native casts logical definitions built on the floating-point models
introduced in Lean 4.33. It also exposes the arbitrary integer and natural constructors and adds
named floating-point constants. These definitions let us connect native conversion to FloatLib's
existing specifications through one shared rounding proof for both binary32 and binary64.

The integer-to-float theorems identify the imported native word with `ExecDType.intToFloat` at
nearest-even rounding. `Model.ofInt_conversion_spec` proves the underlying arbitrary-integer
model satisfies the conversion specification, including the specification's status calculation.
Native casts return only a value; the word equalities make no claim about native exception flags.

In the reverse direction, `ExecDType.floatToIntSaturating` uses the checked conversion's exact
decoder and toward-zero integral rounder. Native casts saturate overflow and infinities and send
NaN to zero. The checked API agrees when the truncated integer is in range and reports errors
for the exceptional cases. In particular, `127.75` truncates to `127` and fits in `Int8`.
-/
