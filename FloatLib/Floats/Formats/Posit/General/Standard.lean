/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Rule
public import FloatLib.Floats.Formats.Posit.KernelPath.Standard

/-!
# The formats of the Posit Standard as the instance `es = 2`

The Posit Standard (2022) fixes two exponent bits. `Posit.General` proves the values, the order
and the rounding of the codes for every number `es` of exponent bits, as a FloatLib extension.
This module identifies the instance `es = 2` with the standard's model:

* `toRat?_eq_value`: the rational value of a word that is neither zero nor NaR (Posit Standard
  (2022), §3.2.2) is, up to its sign, `General.value` of its magnitude at `es = 2`, for every
  standard width.
* `KernelPath.round_eq` is the rounding instance: the standard's rounding of a nonzero dyadic
  number (§4.1) is `KernelPath.encode` at `es = 2`, the function whose results
  `General.encode_value`, `General.encode_between`, `General.encode_of_le_value_one` and
  `General.encode_of_value_max_le` characterize for every `es`.
* `other_exponent_sizes`: the same kernel operations evaluated by Lean's kernel in the 8-bit
  formats with zero, one and three exponent bits.

The arithmetic operations of `Posit.KernelPath.Core` take `es` as a parameter. Their equality
with a specification is proved at `es = 2` (`Posit.KernelPath.Standard`); for another `es` the
theorems of `Posit.General` cover decoding, the order and the rounding of one result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Floats.Formats.Posit.KernelPath FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
Posit Standard (2022), §3.2.2: the rational value of a word that is neither zero nor NaR is, up
to its sign, the general value of its magnitude with two exponent bits, for every standard width.
-/
theorem toRat?_eq_value (x : Model format) (hnar : x ≠ Model.nar format)
    (hzero : x ≠ Model.zero format) :
    x.toRat? =
      some ((if x.signBit then -1 else 1) * value format.payloadBits 2 x.magnitudeBits) := by
  have hv := value_eq_fields (es := 2) format.payloadBits_pos
    (Nat.pos_of_ne_zero (magnitudeBits_ne_zero_of_ne_zero x hzero))
    (magnitudeBits_lt_signMask_of_ne_nar x hnar)
  rw [toRat?_eq_toDyadic?_map, toDyadic?_eq x hnar hzero, Option.map_some, hv]
  congr 1
  unfold FloatLib.Numerics.Dyadic.toRat FloatLib.Numerics.Dyadic.signedSignificand fields
  cases x.signBit <;> simp

/--
The kernel operations with zero, one and three exponent bits, in the formats with seven payload
bits: `1 + 1 = 2`, `2 * 2 = 4` and `4 / 2 = 2` on the encodings of each format, where one is
`0x40` and two is `0x60`, `0x50` and `0x44`.
-/
theorem other_exponent_sizes :
    [add 7 0 0x40 0x40, mul 7 0 0x60 0x60, div 7 0 0x70 0x60] = [0x60, 0x70, 0x60] ∧
      [add 7 1 0x40 0x40, mul 7 1 0x50 0x50, div 7 1 0x60 0x50] = [0x50, 0x60, 0x50] ∧
      [add 7 3 0x40 0x40, mul 7 3 0x44 0x44, div 7 3 0x48 0x44] = [0x44, 0x48, 0x44] := by
  decide +kernel

end FloatLib.Floats.Formats.Posit.General
