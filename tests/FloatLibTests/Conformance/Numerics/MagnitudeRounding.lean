/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic.MagnitudeRounding
public import FloatLib.Numerics.ShiftRightJam

/-!
# Magnitude rounding rule checks

Kernel-checked boundary cases for the four `MagnitudeRounding` rules applied to shifts and
quotients: a zero shift, exact quotients, exact ties, sticky-only and guard-and-sticky remainders,
carries into the next power of two, shifts at and beyond the operand width, and zero denominators.
Every row lists the results of `down`, `up`, `nearestEven`, and `nearestAway` in that order.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.MagnitudeRounding

open FloatLib.Numerics

/-- The four rules in the order the expected rows below list them. -/
private def rules : List MagnitudeRounding := [.down, .up, .nearestEven, .nearestAway]

/-- Shift rounding of `value` by `shift` under each rule. -/
private def shifted (value shift : Nat) : List Nat :=
  rules.map fun rule => roundShiftRight rule value shift

/-- Quotient rounding of `numerator / denominator` under each rule. -/
private def divided (numerator denominator : Nat) : List Nat :=
  rules.map fun rule => roundQuotient rule numerator denominator

/-! ## Increment decisions -/

-- Every rule on all eight combinations of the least retained, guard, and sticky bits.
example :
    ([false, true].flatMap fun lsb => [false, true].flatMap fun guard =>
        [false, true].map fun sticky =>
          rules.map fun rule => rule.increment lsb guard sticky) =
      [ [false, false, false, false], [false, true, false, false]
      , [false, true, false, true], [false, true, true, true]
      , [false, false, false, false], [false, true, false, false]
      , [false, true, true, true], [false, true, true, true] ] := by
  decide

/-! ## Shift rounding -/

-- A zero shift is exact under every rule.
example : shifted 13 0 = [13, 13, 13, 13] := by decide

-- Exact quotients, including zero.
example : shifted 12 2 = [3, 3, 3, 3] := by decide
example : shifted 0 5 = [0, 0, 0, 0] := by decide

-- Exact ties: 10 / 4 = 2.5 and 14 / 4 = 3.5. Nearest-even keeps the even neighbour and
-- nearest-away takes the larger one.
example : shifted 10 2 = [2, 3, 2, 3] := by decide
example : shifted 14 2 = [3, 4, 4, 4] := by decide

-- A set sticky bit with a clear guard bit (9 / 4 = 2.25), and both set (11 / 4 = 2.75).
example : shifted 9 2 = [2, 3, 2, 2] := by decide
example : shifted 11 2 = [2, 3, 3, 3] := by decide

-- Carries into the next power of two: 15 / 8 = 1.875 and 12 / 8 = 1.5.
example : shifted 15 3 = [1, 2, 2, 2] := by decide
example : shifted 12 3 = [1, 2, 2, 2] := by decide

-- A shift equal to the operand width (5 / 8 = 0.625) and far beyond it.
example : shifted 5 3 = [0, 1, 1, 1] := by decide
example : shifted 5 64 = [0, 1, 0, 0] := by decide

-- Exactly half at a shift equal to the operand width: 512 / 1024 = 0.5.
example : shifted 512 10 = [0, 1, 0, 1] := by decide

-- Tie detection reads only the guard bit and the bits below it.
example :
    [shiftRightIsTie 10 2, shiftRightIsTie 11 2, shiftRightIsTie 9 2, shiftRightIsTie 8 0,
      shiftRightIsTie 4 3, shiftRightIsTie 4 64] =
      [true, false, false, false, true, false] := by
  decide

-- Shift and quotient rounding agree at the corresponding power of two.
example :
    ([10, 11, 14, 15, 512].flatMap fun value => [0, 1, 2, 3, 10].map fun shift =>
        shifted value shift == divided value (2 ^ shift)).all id = true := by
  decide

-- Jamming the bits below position 1 into a sticky bit leaves a later rounding by three bits
-- unchanged under every rule: 45 = 101101b rounds by 3 bits from either form.
example :
    rules.map (fun rule => roundShiftRight rule (shiftRightJam 45 1) 2) = shifted 45 3 := by
  decide

/-! ## Quotient rounding -/

-- Exact quotients and the two kinds of tie: 5 / 2 = 2.5 and 7 / 2 = 3.5.
example : divided 12 3 = [4, 4, 4, 4] := by decide
example : divided 5 2 = [2, 3, 2, 3] := by decide
example : divided 7 2 = [3, 4, 4, 4] := by decide

-- Remainders below and above one half: 10 / 3 and 11 / 3.
example : divided 10 3 = [3, 4, 3, 3] := by decide
example : divided 11 3 = [3, 4, 4, 4] := by decide

-- A zero numerator with a nonzero denominator.
example : divided 0 7 = [0, 0, 0, 0] := by decide

-- Zero denominators: truncation, rounding up, and nearest-away return zero, while nearest-even
-- keeps the convention of `roundQuotientEven`.
example : divided 7 0 = [0, 0, 1, 0] := by decide
example : divided 0 0 = [0, 0, 0, 0] := by decide

end FloatLibTests.Conformance.Numerics.MagnitudeRounding
