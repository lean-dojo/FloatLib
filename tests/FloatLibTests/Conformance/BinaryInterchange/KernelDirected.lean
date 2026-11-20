/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.KernelPath

/-!
# The functions of IEEE 754-2019 §9.2 in the directed rounding directions, in Lean's kernel

The recommended functions of clause 9.2 round the exact result once, in a direction. To nearest,
an enclosure of the result usually settles the rounding. In a directed direction a result that
lies next to a value of the format is settled by exact comparisons only, and these search for
an enclosure that separates the result from the boundary. `float_decide` decides the statements
of this module: the search is `Numerics.findLeastFrom`, which Lean's kernel runs without
reducing the proof that the search ends.

The cases are the trigonometric, exponential, logarithmic and hyperbolic functions and the
powers at ordinary operands of binary32, each toward positive infinity, toward negative
infinity, toward zero and to nearest with ties away; results one unit in the last place from a
value of the format (`sin` of `2 ^ -30`, `exp2` of `1e-30`, `cos` of `1e-10`, `tanh` of `20`);
binary16 and binary64; and operands of magnitude `2 ^ -100000` in a format of 256 bits, where
the result differs from a value of the format by one part in `2 ^ 200000`.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.KernelDirected

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open ExecFloat.Binary

/-- A format of 256 bits: 19 exponent bits and 236 fraction bits. -/
abbrev Binary256 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 236)

/-- The trigonometric functions and their inverses at ordinary operands, in four directions. -/
theorem binary32_trigonometric :
    toNat (CorrectlyRounded.sin (1 : Binary32) .up).value = 0x3f576aa5 ∧
      toNat (CorrectlyRounded.sin (1 : Binary32) .down).value = 0x3f576aa4 ∧
      toNat (CorrectlyRounded.sin (1 : Binary32) .towardZero).value = 0x3f576aa4 ∧
      toNat (CorrectlyRounded.sin (1 : Binary32) .nearestAway).value = 0x3f576aa4 ∧
      toNat (CorrectlyRounded.cos (1 : Binary32) .up).value = 0x3f0a5141 ∧
      toNat (CorrectlyRounded.cos (1 : Binary32) .down).value = 0x3f0a5140 ∧
      toNat (CorrectlyRounded.cos (1 : Binary32) .towardZero).value = 0x3f0a5140 ∧
      toNat (CorrectlyRounded.cos (1 : Binary32) .nearestAway).value = 0x3f0a5140 ∧
      toNat (CorrectlyRounded.tan (1 : Binary32) .up).value = 0x3fc75923 ∧
      toNat (CorrectlyRounded.tan (1 : Binary32) .down).value = 0x3fc75922 ∧
      toNat (CorrectlyRounded.tan (1 : Binary32) .towardZero).value = 0x3fc75922 ∧
      toNat (CorrectlyRounded.tan (1 : Binary32) .nearestAway).value = 0x3fc75923 ∧
      toNat (CorrectlyRounded.sinPi (0.25 : Binary32) .up).value = 0x3f3504f4 ∧
      toNat (CorrectlyRounded.sinPi (0.25 : Binary32) .down).value = 0x3f3504f3 ∧
      toNat (CorrectlyRounded.sinPi (0.25 : Binary32) .towardZero).value = 0x3f3504f3 ∧
      toNat (CorrectlyRounded.sinPi (0.25 : Binary32) .nearestAway).value = 0x3f3504f3 ∧
      toNat (CorrectlyRounded.atan (1 : Binary32) .up).value = 0x3f490fdb ∧
      toNat (CorrectlyRounded.atan (1 : Binary32) .down).value = 0x3f490fda ∧
      toNat (CorrectlyRounded.atan (1 : Binary32) .towardZero).value = 0x3f490fda ∧
      toNat (CorrectlyRounded.atan (1 : Binary32) .nearestAway).value = 0x3f490fdb ∧
      toNat (CorrectlyRounded.asin (0.5 : Binary32) .up).value = 0x3f060a92 ∧
      toNat (CorrectlyRounded.asin (0.5 : Binary32) .down).value = 0x3f060a91 ∧
      toNat (CorrectlyRounded.asin (0.5 : Binary32) .towardZero).value = 0x3f060a91 ∧
      toNat (CorrectlyRounded.asin (0.5 : Binary32) .nearestAway).value = 0x3f060a92 ∧
      toNat (CorrectlyRounded.atan2 (1 : Binary32) (2 : Binary32) .up).value = 0x3eed6339 ∧
      toNat (CorrectlyRounded.atan2 (1 : Binary32) (2 : Binary32) .down).value = 0x3eed6338 ∧
      toNat (CorrectlyRounded.atan2 (1 : Binary32) (2 : Binary32) .towardZero).value = 0x3eed6338 ∧
      toNat (CorrectlyRounded.atan2 (1 : Binary32) (2 : Binary32) .nearestAway).value =
        0x3eed6338 := by
  float_decide

/-- info: 'FloatLibTests.Conformance.BinaryInterchange.KernelDirected.binary32_trigonometric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms binary32_trigonometric

/-- The exponentials, logarithms and hyperbolic functions, in four directions. -/
theorem binary32_exponential :
    toNat (CorrectlyRounded.exp2 (0.5 : Binary32) .up).value = 0x3fb504f4 ∧
      toNat (CorrectlyRounded.exp2 (0.5 : Binary32) .down).value = 0x3fb504f3 ∧
      toNat (CorrectlyRounded.exp2 (0.5 : Binary32) .towardZero).value = 0x3fb504f3 ∧
      toNat (CorrectlyRounded.exp2 (0.5 : Binary32) .nearestAway).value = 0x3fb504f3 ∧
      toNat (CorrectlyRounded.exp10 (-1 : Binary32) .up).value = 0x3dcccccd ∧
      toNat (CorrectlyRounded.exp10 (-1 : Binary32) .down).value = 0x3dcccccc ∧
      toNat (CorrectlyRounded.exp10 (-1 : Binary32) .towardZero).value = 0x3dcccccc ∧
      toNat (CorrectlyRounded.exp10 (-1 : Binary32) .nearestAway).value = 0x3dcccccd ∧
      toNat (CorrectlyRounded.log2 (3 : Binary32) .up).value = 0x3fcae00e ∧
      toNat (CorrectlyRounded.log2 (3 : Binary32) .down).value = 0x3fcae00d ∧
      toNat (CorrectlyRounded.log2 (3 : Binary32) .towardZero).value = 0x3fcae00d ∧
      toNat (CorrectlyRounded.log2 (3 : Binary32) .nearestAway).value = 0x3fcae00d ∧
      toNat (CorrectlyRounded.log10 (2 : Binary32) .up).value = 0x3e9a209b ∧
      toNat (CorrectlyRounded.log10 (2 : Binary32) .down).value = 0x3e9a209a ∧
      toNat (CorrectlyRounded.log10 (2 : Binary32) .towardZero).value = 0x3e9a209a ∧
      toNat (CorrectlyRounded.log10 (2 : Binary32) .nearestAway).value = 0x3e9a209b ∧
      toNat (CorrectlyRounded.sinh (1 : Binary32) .up).value = 0x3f966cff ∧
      toNat (CorrectlyRounded.sinh (1 : Binary32) .down).value = 0x3f966cfe ∧
      toNat (CorrectlyRounded.sinh (1 : Binary32) .towardZero).value = 0x3f966cfe ∧
      toNat (CorrectlyRounded.sinh (1 : Binary32) .nearestAway).value = 0x3f966cfe ∧
      toNat (CorrectlyRounded.tanh (0.5 : Binary32) .up).value = 0x3eec9a9f ∧
      toNat (CorrectlyRounded.tanh (0.5 : Binary32) .down).value = 0x3eec9a9e ∧
      toNat (CorrectlyRounded.tanh (0.5 : Binary32) .towardZero).value = 0x3eec9a9e ∧
      toNat (CorrectlyRounded.tanh (0.5 : Binary32) .nearestAway).value = 0x3eec9a9f ∧
      toNat (CorrectlyRounded.atanh (0.5 : Binary32) .up).value = 0x3f0c9f54 ∧
      toNat (CorrectlyRounded.atanh (0.5 : Binary32) .down).value = 0x3f0c9f53 ∧
      toNat (CorrectlyRounded.atanh (0.5 : Binary32) .towardZero).value = 0x3f0c9f53 ∧
      toNat (CorrectlyRounded.atanh (0.5 : Binary32) .nearestAway).value = 0x3f0c9f54 := by
  float_decide

/-- The powers `powr` and `compound`, with positive and negative exponents, in four directions. -/
theorem binary32_power :
    toNat (CorrectlyRounded.powr (2 : Binary32) (0.5 : Binary32) .up).value = 0x3fb504f4 ∧
      toNat (CorrectlyRounded.powr (2 : Binary32) (0.5 : Binary32) .down).value = 0x3fb504f3 ∧
      toNat (CorrectlyRounded.powr (2 : Binary32) (0.5 : Binary32) .towardZero).value = 0x3fb504f3 ∧
      toNat (CorrectlyRounded.powr (2 : Binary32) (0.5 : Binary32) .nearestAway).value =
        0x3fb504f3 ∧
      toNat (CorrectlyRounded.powr (3 : Binary32) (-1.5 : Binary32) .up).value = 0x3e4511a3 ∧
      toNat (CorrectlyRounded.powr (3 : Binary32) (-1.5 : Binary32) .down).value = 0x3e4511a2 ∧
      toNat (CorrectlyRounded.powr (3 : Binary32) (-1.5 : Binary32) .towardZero).value =
        0x3e4511a2 ∧
      toNat (CorrectlyRounded.powr (3 : Binary32) (-1.5 : Binary32) .nearestAway).value =
        0x3e4511a3 ∧
      toNat (CorrectlyRounded.compound (0.1 : Binary32) 5 .up).value = 0x3fce2532 ∧
      toNat (CorrectlyRounded.compound (0.1 : Binary32) 5 .down).value = 0x3fce2531 ∧
      toNat (CorrectlyRounded.compound (0.1 : Binary32) 5 .towardZero).value = 0x3fce2531 ∧
      toNat (CorrectlyRounded.compound (0.1 : Binary32) 5 .nearestAway).value = 0x3fce2531 ∧
      toNat (CorrectlyRounded.compound (0.5 : Binary32) (-3) .up).value = 0x3e97b426 ∧
      toNat (CorrectlyRounded.compound (0.5 : Binary32) (-3) .down).value = 0x3e97b425 ∧
      toNat (CorrectlyRounded.compound (0.5 : Binary32) (-3) .towardZero).value = 0x3e97b425 ∧
      toNat (CorrectlyRounded.compound (0.5 : Binary32) (-3) .nearestAway).value = 0x3e97b426 := by
  float_decide

/--
Results one unit in the last place from a value of the format: `sin` of `2 ^ -30` is below its
operand, `exp2` of `1e-30` above one, and `cos` of `1e-10` and `tanh` of `20` below one.
-/
theorem binary32_next_to_a_value :
    toNat (CorrectlyRounded.sin (ofNat 0x31800000 : Binary32) .up).value = 0x31800000 ∧
      toNat (CorrectlyRounded.sin (ofNat 0x31800000 : Binary32) .down).value = 0x317fffff ∧
      toNat (CorrectlyRounded.sin (ofNat 0x31800000 : Binary32) .towardZero).value = 0x317fffff ∧
      toNat (CorrectlyRounded.sin (ofNat 0x31800000 : Binary32) .nearestAway).value = 0x31800000 ∧
      toNat (CorrectlyRounded.exp2 (1e-30 : Binary32) .up).value = 0x3f800001 ∧
      toNat (CorrectlyRounded.exp2 (1e-30 : Binary32) .down).value = 0x3f800000 ∧
      toNat (CorrectlyRounded.exp2 (1e-30 : Binary32) .towardZero).value = 0x3f800000 ∧
      toNat (CorrectlyRounded.exp2 (1e-30 : Binary32) .nearestAway).value = 0x3f800000 ∧
      toNat (CorrectlyRounded.cos (1e-10 : Binary32) .up).value = 0x3f800000 ∧
      toNat (CorrectlyRounded.cos (1e-10 : Binary32) .down).value = 0x3f7fffff ∧
      toNat (CorrectlyRounded.cos (1e-10 : Binary32) .towardZero).value = 0x3f7fffff ∧
      toNat (CorrectlyRounded.cos (1e-10 : Binary32) .nearestAway).value = 0x3f800000 ∧
      toNat (CorrectlyRounded.tanh (20 : Binary32) .up).value = 0x3f800000 ∧
      toNat (CorrectlyRounded.tanh (20 : Binary32) .down).value = 0x3f7fffff ∧
      toNat (CorrectlyRounded.tanh (20 : Binary32) .towardZero).value = 0x3f7fffff ∧
      toNat (CorrectlyRounded.tanh (20 : Binary32) .nearestAway).value = 0x3f800000 := by
  float_decide

/--
The same in binary16 and binary64, and at an operand of magnitude `2 ^ -100000` in a format of
256 bits: `sin` rounded toward zero is the value of the format below the operand, and `exp2`
rounded toward positive infinity is the value above one.
-/
theorem directed_by_format :
    toNat (CorrectlyRounded.sin (1 : Binary16) .up).value = 0x3abc ∧
      toNat (CorrectlyRounded.sin (1 : Binary16) .down).value = 0x3abb ∧
      toNat (CorrectlyRounded.sin (1 : Binary16) .towardZero).value = 0x3abb ∧
      toNat (CorrectlyRounded.exp2 (0.5 : Binary64) .up).value = 0x3ff6a09e667f3bcd ∧
      toNat (CorrectlyRounded.exp2 (0.5 : Binary64) .down).value = 0x3ff6a09e667f3bcc ∧
      toNat (CorrectlyRounded.exp2 (0.5 : Binary64) .towardZero).value = 0x3ff6a09e667f3bcc ∧
      toNat (CorrectlyRounded.powr (2 : Binary64) (0.5 : Binary64) .up).value = 0x3ff6a09e667f3bcd ∧
      toNat (CorrectlyRounded.powr (2 : Binary64) (0.5 : Binary64) .down).value =
        0x3ff6a09e667f3bcc ∧
      toNat (CorrectlyRounded.powr (2 : Binary64) (0.5 : Binary64) .towardZero).value =
        0x3ff6a09e667f3bcc ∧
      toNat (CorrectlyRounded.sin (ofNat (162143 * 2 ^ 236) : Binary256) .towardZero).value =
        162143 * 2 ^ 236 - 1 ∧
      toNat (CorrectlyRounded.exp2 (ofNat (162143 * 2 ^ 236) : Binary256) .up).value =
        262143 * 2 ^ 236 + 1 := by
  float_decide

end FloatLibTests.Conformance.BinaryInterchange.KernelDirected
