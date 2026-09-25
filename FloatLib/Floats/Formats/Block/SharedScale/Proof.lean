/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.SharedScale.Runtime
public import FloatLib.Numerics.Capabilities.BlockScaled
import Mathlib.Tactic.NormNum

/-!
# Correctness of shared-scale blocks

The direct vector kernel implements contextual quantization, and the format satisfies the generic
block-scaled representation capability.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

/-- The common format represents exactly its vector-valued block denotation. -/
@[simp] theorem represents_iff {lanes : Nat} (code : FormatCode (SharedScale lanes))
    (value : Vector Rat lanes) :
    FormatRepresents (SharedScale lanes) code value ↔ decode code = value := by
  change NumericalValue.finite (decode code) = NumericalValue.finite value ↔ decode code = value
  simp

/-- The direct vector kernel satisfies the contextual relational specification. -/
theorem quantizesAt_quantizeAt {lanes : Nat} (exponent : Int) (input : Vector Rat lanes) :
    QuantizesAt exponent input (quantizeAt exponent input) := by
  constructor
  · rfl
  · intro lane
    simp [quantizeAt, Nat.ne_of_gt (Nat.zero_lt_of_lt lane.isLt)]

/-- `quantizeAt` implements shared-scale contextual quantization. -/
theorem quantizeAt_refines (lanes : Nat) :
    Quantization.Spec.Implements (QuantizesAt (lanes := lanes))
      (quantizeAt (lanes := lanes)) := by
  intro exponent input
  exact quantizesAt_quantizeAt exponent input

/-- The shared binary scale is strictly positive. -/
theorem scale_pos (exponent : Int) : 0 < scale exponent := by
  exact zpow_pos (by norm_num : (0 : Rat) < 2) exponent

/--
The proof-facing block-scaled capability for the unbounded shared-scale representation.

Executable decoding still projects the exponent and significands directly.
-/
theorem blockScaled_sharedScale (lanes : Nat) :
    BlockScaled (formatSystem (SharedScale lanes))
      (Fin lanes) Int Int Rat
      (fun (block : Vector Rat lanes) (lane : Fin lanes) => block[lane.val])
      (fun (code : SharedScaleCode lanes) => code.exponent)
      (fun (code : SharedScaleCode lanes) (lane : Fin lanes) =>
        code.significands[lane.val])
      (fun (exponent : Int) (significand : Int) =>
        (significand : Rat) * scale exponent) := by
  intro code block hcode lane
  have hdecode : decode code = block :=
    (represents_iff code block).1 hcode
  rw [← hdecode]
  simp [decode, Nat.ne_of_gt (Nat.zero_lt_of_lt lane.isLt)]

/-- Decoding a freshly quantized block exposes nearest-even reconstruction lane by lane. -/
@[simp] theorem decode_quantizeAt_get {lanes : Nat} (exponent : Int)
    (input : Vector Rat lanes) (lane : Fin lanes) :
    (decode (quantizeAt exponent input))[lane.val] =
      (roundRatEven (input[lane.val] / scale exponent) : Rat) * scale exponent := by
  simp [decode, quantizeAt, Nat.ne_of_gt (Nat.zero_lt_of_lt lane.isLt)]

end FloatLib.Floats.Formats.Block
