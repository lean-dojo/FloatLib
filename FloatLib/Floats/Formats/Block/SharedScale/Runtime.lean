/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.SharedScale.Core

/-!
# Executable shared-scale quantization

The kernel rounds each exact rational lane to a nearest-even integer significand at the
caller-selected binary exponent.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

/-- Quantize every rational lane at an explicitly supplied shared exponent. -/
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
