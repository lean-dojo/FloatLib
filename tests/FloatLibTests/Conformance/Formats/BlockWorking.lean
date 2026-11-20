/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block
public import FloatLib.Tactic.FloatDecide

/-!
# NVFP4 quantized in binary32: blocks checked by the kernel

`Block.nvfp4Working` is the quantizer on binary32 encodings in the order of torchao's
`nvfp4_quantize`. Each expected word below is the one that the processor's binary32 arithmetic
gives for the same order of operations (`tests/oracles/nvfp4_working.py`, NumPy float32 with the
E4M3 and E2M1 roundings in exact fractions). The blocks cover a block without overflow, an outer
scale so small that the scale quotient and the reciprocal overflow, a product that overflows,
and the largest and the least binary32 magnitudes in one block.

`float_decide` evaluates a block through the rules of `Block.Working.KernelPath`, on natural
numbers. The last section instantiates the theorems of `Block.Working` on explicit data, so
that their premises are seen to hold.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.BlockWorking

open FloatLib.Floats.Formats FloatLib.Floats.Formats.Block
open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

/-- A binary32 word. -/
private def word (bits : Nat) : Model FloatFormat.binary32 :=
  Model.ofNatBits bits

/-- The values `1, 2, …, 8, -1, -2, …, -8`. -/
private def ramp : List (Model FloatFormat.binary32) :=
  [0x3F800000, 0x40000000, 0x40400000, 0x40800000, 0x40A00000, 0x40C00000, 0x40E00000,
    0x41000000, 0xBF800000, 0xC0000000, 0xC0400000, 0xC0800000, 0xC0A00000, 0xC0C00000,
    0xC0E00000, 0xC1000000].map word

/-- The largest finite value, the least subnormal, zeros of both signs, one and `2 ^ 127`, with
both signs of the first two. -/
private def extremes : List (Model FloatFormat.binary32) :=
  [0x7F7FFFFF, 0xFF7FFFFF, 0x00000001, 0x80000001, 0, 0x80000000, 0x3F800000, 0x7F000000,
    0x7F7FFFFF, 0xFF7FFFFF, 0x00000001, 0x80000001, 0, 0x80000000, 0x3F800000, 0x7F000000].map
    word

/-! ## Blocks -/

-- No overflow: the scale is `8 / 6` in E4M3 (word 59), and `7` and `8` saturate at `6`.
example : nvfp4Working.words (word 0x3F800000) ramp =
    (59, [1, 3, 4, 5, 6, 6, 7, 7, 9, 11, 12, 13, 14, 14, 15, 15]) := by
  float_decide

-- The outer scale `2 ^ -140`: the scale quotient overflows and is clamped to `448` (word 126),
-- and the reciprocal overflows to `+∞`, so every nonzero element saturates with its sign.
example : nvfp4Working.words (word 0x00000200) ramp =
    (126, [7, 7, 7, 7, 7, 7, 7, 7, 15, 15, 15, 15, 15, 15, 15, 15]) := by
  float_decide

-- The outer scale `2 ^ -100`: nothing overflows, the scale is clamped and every element
-- saturates.
example : nvfp4Working.words (word 0x0D800000) ramp =
    (126, [7, 7, 7, 7, 7, 7, 7, 7, 15, 15, 15, 15, 15, 15, 15, 15]) := by
  float_decide

-- The outer scale `2 ^ -20` under the largest finite value: the scale quotient overflows, the
-- reciprocal is finite, and the products of the two largest magnitudes overflow and saturate.
example : nvfp4Working.words (word 0x35800000) extremes =
    (126, [7, 15, 0, 8, 0, 8, 7, 7, 7, 15, 0, 8, 0, 8, 7, 7]) := by
  float_decide

-- The outer scale `2 ^ 127`: the scale is `448 / 2 ^ 127 * …` below the floor only after the
-- clamp, and the subnormals are flushed to zeros that keep their signs.
example : nvfp4Working.words (word 0x7F000000) extremes =
    (43, [7, 15, 0, 8, 0, 8, 0, 5, 7, 15, 0, 8, 0, 8, 0, 5]) := by
  float_decide

-- Without an outer scale: the outer scale is one.
example : nvfp4Working.words (posOne _) extremes =
    (126, [7, 15, 0, 8, 0, 8, 0, 7, 7, 15, 0, 8, 0, 8, 0, 7]) := by
  float_decide

/-! ## Single operations -/

-- One element as written, without the kernel rules: `3 * 0.25` rounds to `1 / 2` or `1`.
example : (nvfp4Working.element (word 0x3E800000) (word 0x40400000)).toNatBits = 2 := by
  decide +kernel

-- The reciprocal under the least subnormal outer scale is `+∞`.
example : nvfp4Working.reciprocal (word 0x00000001) (Model.ofNatBits 126) = posInf _ := by
  decide +kernel

-- A zero times that reciprocal is a NaN, and its element word is zero: the case that
-- `Working.Quantizer.toReal_element_posInf` leaves out.
example : (nvfp4Working.element (posInf _) (word 0)).toNatBits = 0 := by
  decide +kernel

/-! ## The theorems on explicit data -/

-- The premises of the error theorem hold for the outer scale one, the stored scale `8 / 6`
-- rounded to E4M3 (word 59, the value `11 / 8`) and the input `3`.
example :
    |toReal (nvfp4Working.element
          (nvfp4Working.reciprocal (posOne _) (Model.ofNatBits 59 : Model FloatFormat.e4m3))
          (word 0x40400000)) *
        (toReal (posOne FloatFormat.binary32) *
          toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3)) - toReal (word 0x40400000)| ≤
      (1 / 4 * (1 + ((1 + unitRoundoffAt .binary32) *
              (1 + ((1 + unitRoundoffAt .binary32) *
                (1 + (unitRoundoffAt .binary32 + underflowErrorAt .binary32 *
                  toReal (posOne FloatFormat.binary32))) - 1 +
                underflowErrorAt .binary32 * (toReal (posOne FloatFormat.binary32) *
                  toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3)))) - 1)) +
          ((1 + unitRoundoffAt .binary32) *
              (1 + ((1 + unitRoundoffAt .binary32) *
                (1 + (unitRoundoffAt .binary32 + underflowErrorAt .binary32 *
                  toReal (posOne FloatFormat.binary32))) - 1 +
                underflowErrorAt .binary32 * (toReal (posOne FloatFormat.binary32) *
                  toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3)))) - 1)) *
            |toReal (word 0x40400000)| +
        toReal (posOne FloatFormat.binary32) *
            toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3) *
          (1 / 4 + (1 + 1 / 4) * underflowErrorAt .binary32) +
        max 0 ((1 + ((1 + unitRoundoffAt .binary32) *
              (1 + ((1 + unitRoundoffAt .binary32) *
                (1 + (unitRoundoffAt .binary32 + underflowErrorAt .binary32 *
                  toReal (posOne FloatFormat.binary32))) - 1 +
                underflowErrorAt .binary32 * (toReal (posOne FloatFormat.binary32) *
                  toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3)))) - 1)) *
              |toReal (word 0x40400000)| +
            toReal (posOne FloatFormat.binary32) *
                toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3) *
              underflowErrorAt .binary32 -
            toReal (posOne FloatFormat.binary32) *
                toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3) * 6) :=
  nvfp4Working_abs_element_sub_le (isFinite_posOne _) (by rw [toReal_posOne]; norm_num)
    (by decide +kernel)
    (by
      rw [show toReal (Model.ofNatBits 59 : Model FloatFormat.e4m3) = ((11 / 8 : ℚ) : ℝ) by
        rw [← cast_toRat_eq_toReal]
        have h : toRat? (Model.ofNatBits 59 : Model FloatFormat.e4m3) = some (11 / 8) := by
          decide +kernel
        rw [h]
        rfl]
      norm_num)
    (by decide +kernel) (by decide +kernel) rfl

-- The stored scale of the first block is the E4M3 rounding of the clamped binary32 quotients.
example :
    toReal (nvfp4Working.scale (posOne _) ramp) =
      (Rounding.saturating .e4m3).round (max (1 / 64) (min 448
        (roundAt .binary32 (roundAt .binary32 (toReal (Working.blockMax ramp) / 6) /
          toReal (posOne FloatFormat.binary32))))) :=
  (nvfp4Working_toReal_scale (isFinite_posOne _) (by rw [toReal_posOne]; norm_num)
    (by decide +kernel)).2

-- An element is the saturating E2M1 rounding of the product rounded to binary32: here the
-- product of the input `3` and the reciprocal `1 / 4`.
example :
    toReal (nvfp4Working.element (word 0x3E800000) (word 0x40400000)) =
      (Rounding.saturating .e2m1).round
        (roundAt .binary32 (toReal (word 0x40400000) * toReal (word 0x3E800000))) :=
  (nvfp4Working_toReal_element (by decide +kernel) (by decide +kernel)).2

-- Under a reciprocal that overflowed to `+∞`, a finite input other than zero is stored as the
-- target with the sign of the input, rounded to E2M1.
example {x : Model FloatFormat.binary32} (hx : isFinite x = true) (hx0 : toReal x ≠ 0) :
    toReal (nvfp4Working.element (posInf _) x) =
      (Rounding.saturating .e2m1).round
        (if toReal x < 0 then -toReal nvfp4Working.target else toReal nvfp4Working.target) :=
  (nvfp4Working.toReal_element_posInf (by decide) nvfp4Working_target.1
    (by rw [nvfp4Working_target.2]; norm_num)
    (by rw [nvfp4Working_target.2, toReal_posMaxFinite_e2m1]) hx hx0).2

end FloatLibTests.Conformance.Formats.BlockWorking
