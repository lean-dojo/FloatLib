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

Lean defines its signed native casts on top of its floating-point models, and it exposes the
arbitrary integer and natural constructors and named floating-point constants too. With those
definitions we can connect native conversion to FloatLib's specifications through one rounding
proof shared by binary32 and binary64.

From integers to floats, the theorems identify the imported native word with
`ExecDType.intToFloat` at nearest-even rounding. `Model.ofInt_conversion_spec` proves that the
underlying arbitrary-integer model gives the word and status of the reference conversion
`runWith`, and `Model.toReal_ofModel_ofInt_eq_roundAt` gives its finite value as nearest-even
rounding. Native casts return only a value, so the word equalities make no claim about native
exception flags.

In the reverse direction, `ExecDType.floatToIntSaturating` uses the checked conversion's exact
decoder and toward-zero integral rounder. Native casts saturate overflow and infinities and send
NaN to zero. The checked API agrees whenever the truncated integer is in range and reports errors
for the exceptional cases, so `127.75` truncates to `127` and fits in `Int8`, while `128.5` is an
error.
-/
