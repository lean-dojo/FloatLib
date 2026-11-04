/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.SharedScale.Core

/-!
# Executable shared-scale quantization

This is the executable kernel behind shared-scale quantization. It takes the caller's binary
exponent and rounds each exact rational lane to a nearest-even integer significand on that grid.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

/--
Quantize every rational lane at the shared exponent the caller supplies.

Each lane is divided by `2 ^ exponent` and rounded to the nearest integer significand, ties to
even. Significands are unbounded integers, so no lane saturates or overflows.
-/
@[inline] def quantizeAt {lanes : Nat} (exponent : Int) (input : Vector Rat lanes) :
    SharedScaleCode lanes where
  exponent := exponent
  significands :=
    if h : lanes = 0 then
      ⟨#[], by simp [h]⟩
    else
      let factor := scale exponent
      input.map fun value => roundRatEven (value / factor)

end FloatLib.Floats.Formats.Block
