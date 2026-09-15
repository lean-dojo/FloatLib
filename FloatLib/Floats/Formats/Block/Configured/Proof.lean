/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured.Runtime
public import FloatLib.Floats.Formats.Block.SharedScale.Proof

/-!
# Correctness of configured shared-scale blocks

Wrapping and unwrapping preserve the complete block code. `quantizesAt_quantizeAt` lifts the
model's lane-wise nearest-even rounding theorem to configured blocks, at the exponent supplied by
the caller.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.SharedScale

open FloatLib.Numerics

variable {lanes : Nat}

/-- Unwrapping a freshly wrapped shared-scale block returns the original code. -/
@[simp, grind =] theorem toCode_ofCode (code : Formats.Block.SharedScaleCode lanes) :
    toCode (ofCode code) = code :=
  rfl

/-- Rewrapping the code of a shared-scale block returns the original value. -/
@[simp, grind =] theorem ofCode_toCode (value : ExecFloat.SharedScale lanes) :
    ofCode value.toCode = value :=
  ExecFloat.ofRaw_raw value

/-- Quantization records exactly the shared exponent supplied by the caller. -/
@[simp, grind =] theorem exponent_quantizeAt
    (exponent : Int) (input : Vector Rat lanes) :
    (quantizeAt exponent input).exponent = exponent :=
  rfl

/-- Each decoded quantized lane is its nearest-even integer multiple of the shared scale. -/
@[simp, grind =] theorem decode_quantizeAt_get (exponent : Int)
    (input : Vector Rat lanes) (lane : Fin lanes) :
    (decode (quantizeAt exponent input))[lane.val] =
      (roundRatEven
        (input[lane.val] / Formats.Block.scale exponent) : Rat) *
        Formats.Block.scale exponent :=
  Formats.Block.decode_quantizeAt_get exponent input lane

/-- The configured wrapper preserves relational contextual quantization. -/
theorem quantizesAt_quantizeAt (exponent : Int) (input : Vector Rat lanes) :
    Formats.Block.QuantizesAt exponent input (quantizeAt exponent input).toCode :=
  Formats.Block.quantizesAt_quantizeAt exponent input

end FloatLib.Floats.ExecFloat.SharedScale
