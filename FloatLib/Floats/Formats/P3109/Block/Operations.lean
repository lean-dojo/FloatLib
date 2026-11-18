/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Proof
public meta import FloatLib.Tactic.P3109Block
public import FloatLib.Floats.Formats.P3109.Block.Root.Proof

/-!
# Named P3109 block operations

The unapproved P3109 interim report v4.1 (14 September 2026), §5.7, obtains
elementwise block operations from scalar operations by decoding each input block,
applying the exact closed operation lane by lane, and normalizing at the supplied
result scale before projecting. These names instantiate the three arity schemas;
the schemas' projection theorems apply to every instance and every block length.

Only exact closed rational operations are instantiated here. Square root,
reciprocal square root and hypotenuse use the independently proved root evaluator
in `Block.Root`. This module does not supply transcendental evaluators.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Block

open FloatLib.Numerics FloatLib.Floats.ExecFloat Arithmetic


/-- P3109 interim report v4.1, §5.7: decode and rescale each lane before one destination
    projection. -/
block_unary BlockConvert := id
/-- P3109 interim report v4.1, §5.7 with §4.10.1: exact absolute value before result-scale
    normalization. -/
block_unary BlockAbs := Arithmetic.Abs
/-- P3109 interim report v4.1, §5.7 with §4.10.1: exact negation before result-scale
    normalization. -/
block_unary BlockNegate := Arithmetic.Negate
/-- P3109 interim report v4.1, §5.7 with §4.10.8: reciprocal with the report's zero-to-NaN rule. -/
block_unary BlockRecip := Arithmetic.Recip

/-- P3109 interim report v4.1, §5.7 with §4.10.2: copy signs of exact decoded lanes. -/
block_binary BlockCopySign := Arithmetic.CopySign
/-- P3109 interim report v4.1, §5.7 with §4.10.3: add exact decoded lanes, then project once. -/
block_binary BlockAdd := Arithmetic.Add
/-- P3109 interim report v4.1, §5.7 with §4.10.3: subtract exact decoded lanes, then project
    once. -/
block_binary BlockSubtract := Arithmetic.Subtract
/-- P3109 interim report v4.1, §5.7 with §4.10.4: multiply exact decoded lanes, then project
    once. -/
block_binary BlockMultiply := Arithmetic.Multiply
/-- P3109 interim report v4.1, §5.7 with §4.10.5: divide exact decoded lanes with zero
    denominators mapped to
    NaN. -/
block_binary BlockDivide := Arithmetic.Divide
/-- P3109 interim report v4.1, §5.7 with §4.11: minimum with NaN propagation, before
    normalization. -/
block_binary BlockMinimum := Arithmetic.Minimum
/-- P3109 interim report v4.1, §5.7 with §4.11: maximum with NaN propagation, before
    normalization. -/
block_binary BlockMaximum := Arithmetic.Maximum
/-- P3109 interim report v4.1, §5.7 with §4.11: minimum preferring a non-NaN argument. -/
block_binary BlockMinimumNumber := Arithmetic.MinimumNumber
/-- P3109 interim report v4.1, §5.7 with §4.11: maximum preferring a non-NaN argument. -/
block_binary BlockMaximumNumber := Arithmetic.MaximumNumber
/-- P3109 interim report v4.1, §5.7 with §4.11: minimum by magnitude, using the scalar tie rule. -/
block_binary BlockMinimumMagnitude := Arithmetic.MinimumMagnitude
/-- P3109 interim report v4.1, §5.7 with §4.11: maximum by magnitude, using the scalar tie rule. -/
block_binary BlockMaximumMagnitude := Arithmetic.MaximumMagnitude
/-- P3109 interim report v4.1, §5.7 with §4.11: minimum by magnitude preferring non-NaN. -/
block_binary BlockMinimumMagnitudeNumber := Arithmetic.MinimumMagnitudeNumber
/-- P3109 interim report v4.1, §5.7 with §4.11: maximum by magnitude preferring non-NaN. -/
block_binary BlockMaximumMagnitudeNumber := Arithmetic.MaximumMagnitudeNumber
/-- P3109 interim report v4.1, §5.7 with §4.11: minimum preferring a finite argument. -/
block_binary BlockMinimumFinite := Arithmetic.MinimumFinite
/-- P3109 interim report v4.1, §5.7 with §4.11: maximum preferring a finite argument. -/
block_binary BlockMaximumFinite := Arithmetic.MaximumFinite

/-- P3109 interim report v4.1, §5.7 with §4.10.6: retain the exact product and addend until
    final projection. -/
block_ternary BlockFMA := Arithmetic.FMA
/-- P3109 interim report v4.1, §5.7 with §4.10.7: retain both exact additions until final
    projection. -/
block_ternary BlockFAA := Arithmetic.FAA
/-- P3109 interim report v4.1, §5.7 with §4.11: clamp exact lanes before result-scale
    normalization. -/
block_ternary BlockClamp := Arithmetic.Clamp

end FloatLib.Floats.Formats.P3109.Block
