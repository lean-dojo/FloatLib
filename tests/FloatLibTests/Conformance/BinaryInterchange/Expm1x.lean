/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Expm1x
meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.Expm1x

/-!
# `expm1x`: `exp x - 1 - x`, correctly rounded in every rounding attribute

The checks cover the six rounding attributes at three precisions.

* In the format `ieee 2 1`, whose finite magnitudes are `0, 1/2, 1, 3/2, 2, 3`, the kernel
  evaluates the function: at `3/2` the value `1.98…` rounds to `2` or down to `3/2`, at `1` the
  value `0.718…` rounds to `1/2` or up to `1`, at `3` the value overflows to `+∞` or down to the
  largest finite value, at the subnormal `1/2` the value `0.148…` rounds to zero or up to `1/2`,
  and at `-1` the value `0.367…` rounds to `1/2` or down to zero. Either zero gives `+0`.
* In binary32 and binary64 the compiled function is compared with values computed at 400 bits:
  near zero (`2⁻¹⁰`, `2⁻³⁰` and `2⁻⁸⁰`, where the result is subnormal or zero), at moderate
  arguments of both signs, and at an overflow. At `2⁻³⁰` in binary64 the expression
  `exp x - 1 - x` evaluated operation by operation is zero.
* The theorems are applied to an arbitrary finite input: the rounding in each attribute, the
  mixed error with the unit roundoff of the attribute, and the sign.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.Expm1x

open FloatLib.Floats FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals

/-! ## The six attributes in a format with six finite magnitudes -/

/-- The value of `ieee 2 1` with the given bits. -/
abbrev tiny (bits : Nat) : Model (.ieee 2 1) := Model.ofNatBits bits

/-- The bits of `expm1x` at the bits of an input of `ieee 2 1`. -/
abbrev tinyBits (bits : Nat) (mode : Model.IEEERoundingMode) : Nat :=
  (CorrectlyRounded.expm1x (tiny bits) mode).toNatBits

-- `exp (3/2) - 5/2 = 1.98…`, between `3/2` and `2`.
example : tinyBits 3 .nearest = 4 ∧ tinyBits 3 .nearestAway = 4 ∧ tinyBits 3 .towardZero = 3 ∧
    tinyBits 3 .up = 4 ∧ tinyBits 3 .down = 3 ∧ tinyBits 3 .away = 4 := by decide +kernel

-- `exp 1 - 2 = 0.718…`, between `1/2` and `1`.
example : tinyBits 2 .nearest = 1 ∧ tinyBits 2 .nearestAway = 1 ∧ tinyBits 2 .towardZero = 1 ∧
    tinyBits 2 .up = 2 ∧ tinyBits 2 .down = 1 ∧ tinyBits 2 .away = 2 := by decide +kernel

-- `exp 3 - 4 = 16.08…` overflows: `+∞`, or the largest finite value `3` when rounded downward.
example : tinyBits 5 .nearest = 6 ∧ tinyBits 5 .nearestAway = 6 ∧ tinyBits 5 .towardZero = 5 ∧
    tinyBits 5 .up = 6 ∧ tinyBits 5 .down = 5 ∧ tinyBits 5 .away = 6 := by decide +kernel

-- `exp (1/2) - 3/2 = 0.148…`, below half the least subnormal `1/2`.
example : tinyBits 1 .nearest = 0 ∧ tinyBits 1 .towardZero = 0 ∧ tinyBits 1 .up = 1 ∧
    tinyBits 1 .down = 0 := by decide +kernel

-- `exp (-1) = 0.367…` at the negative argument `-1`: the result is positive.
example : tinyBits 10 .nearest = 1 ∧ tinyBits 10 .down = 0 ∧ tinyBits 10 .up = 1 := by
  decide +kernel

-- Either zero gives `+0`, in every attribute.
example : tinyBits 0 .nearest = 0 ∧ tinyBits 8 .nearest = 0 ∧ tinyBits 8 .down = 0 ∧
    tinyBits 8 .up = 0 := by decide +kernel

/-! ## Binary32 and binary64 against 400-bit values -/

/-- The six roundings of `exp q - 1 - q` in binary32, as exact rationals. -/
meta def single (q : ℚ) : List (Option ℚ) :=
  Model.IEEERoundingMode.all.map fun mode =>
    Model.toRat? (CorrectlyRounded.expm1x (Model.ofRat FloatFormat.binary32 q) mode)

/-- The six roundings of `exp q - 1 - q` in binary64, as exact rationals. -/
meta def double (q : ℚ) : List (Option ℚ) :=
  Model.IEEERoundingMode.all.map fun mode =>
    Model.toRat? (CorrectlyRounded.expm1x (Model.ofRat FloatFormat.binary64 q) mode)

-- The attributes in the order nearest, nearestAway, towardZero, up, down, away.
#guard single (1 / 1024) == [some (8391339 / 17592186044416), some (8391339 / 17592186044416),
  some (8391339 / 17592186044416), some (2097835 / 4398046511104),
  some (8391339 / 17592186044416), some (2097835 / 4398046511104)]

#guard single (-1 / 1024) == [some (4192939 / 8796093022208), some (4192939 / 8796093022208),
  some (16771755 / 35184372088832), some (4192939 / 8796093022208),
  some (16771755 / 35184372088832), some (4192939 / 8796093022208)]

#guard single 3 == [some (4216727 / 262144), some (4216727 / 262144), some (8433453 / 524288),
  some (4216727 / 262144), some (8433453 / 524288), some (4216727 / 262144)]

#guard single (-20) == [some 19, some 19, some 19, some (9961473 / 524288), some 19,
  some (9961473 / 524288)]

-- `2⁻⁸⁰`: the value `2⁻¹⁶¹` is below half the least subnormal `2⁻¹⁴⁹`.
#guard single (1 / 2 ^ 80) == [some 0, some 0, some 0, some (1 / 2 ^ 149), some 0,
  some (1 / 2 ^ 149)]

-- `exp 100` overflows binary32: `+∞`, or the largest finite value when rounded downward.
#guard single 100 == [none, none, some 340282346638528859811704183484516925440, none,
  some 340282346638528859811704183484516925440, none]

-- `2⁻³⁰` in binary64, where `exp x - 1 - x` evaluated operation by operation is zero.
#guard double (1 / 2 ^ 30) == [some (4503599628768597 / 2 ^ 113), some (4503599628768597 / 2 ^ 113),
  some (4503599628768597 / 2 ^ 113), some (2251799814384299 / 2 ^ 112),
  some (4503599628768597 / 2 ^ 113), some (2251799814384299 / 2 ^ 112)]

#guard double (1 / 2) == [some (2679124237228655 / 18014398509481984),
  some (2679124237228655 / 18014398509481984), some (2679124237228655 / 18014398509481984),
  some (5358248474457311 / 36028797018963968), some (2679124237228655 / 18014398509481984),
  some (5358248474457311 / 36028797018963968)]

/-! ## The theorems at an arbitrary finite input -/

section Statements

variable {fmt : FloatFormat}

/-- A finite result below `2 ^ (emax + 1)` is the rounding of the real value in its attribute. -/
example (hfmt : fmt.isIEEE = true) (x : Model fmt) (hx : Model.isFinite x = true)
    (mode : Model.IEEERoundingMode)
    (hfinite : Model.isFinite (CorrectlyRounded.expm1x x mode) = true)
    (hrange : Real.exp (Model.toReal x) - 1 - Model.toReal x <
      FloatLib.Floats.Formats.Flocq.bpow binaryRadix (fmt.maxNormalExponent + 1)) :
    Model.toReal (CorrectlyRounded.expm1x x mode) =
      Model.roundAt fmt (Real.exp (Model.toReal x) - 1 - Model.toReal x) mode :=
  CorrectlyRounded.toReal_expm1x_of_isFinite hfmt hx mode hfinite hrange

/-- Rounded downward, the result is finite and correctly rounded below the overflow threshold,
with the unit roundoff of a directed attribute. -/
example (hfmt : fmt.isIEEE = true) (x : Model fmt) (hx : Model.isFinite x = true)
    (hrange : Real.exp (Model.toReal x) - 1 - Model.toReal x < Certified.overflowThreshold fmt) :
    MixedError (Model.toReal (CorrectlyRounded.expm1x x .down))
      (Real.exp (Model.toReal x) - 1 - Model.toReal x) (2 * Model.unitRoundoffAt fmt)
      (2 * Model.underflowErrorAt fmt) := by
  have h := CorrectlyRounded.mixedError_toReal_expm1x hfmt hx .down
    (CorrectlyRounded.isFinite_expm1x hfmt hx rfl hrange)
    (hrange.trans (CorrectlyRounded.overflowThreshold_lt_bpow fmt))
  simpa [Model.unitRoundoffIn, Model.underflowErrorIn, Model.IEEERoundingMode.halfUlps] using h

/-- At most the largest finite value, the result is finite and correctly rounded in every one of
the six attributes, the two upward ones included. -/
example (hfmt : fmt.isIEEE = true) (x : Model fmt) (hx : Model.isFinite x = true)
    (mode : Model.IEEERoundingMode)
    (hrange : Real.exp (Model.toReal x) - 1 - Model.toReal x ≤
      Model.toReal (Model.posMaxFinite fmt)) :
    Model.isFinite (CorrectlyRounded.expm1x x mode) = true ∧
      Model.toReal (CorrectlyRounded.expm1x x mode) =
        Model.roundAt fmt (Real.exp (Model.toReal x) - 1 - Model.toReal x) mode :=
  ⟨CorrectlyRounded.isFinite_expm1x_of_le_posMaxFinite hfmt hx mode hrange,
    CorrectlyRounded.toReal_expm1x_eq_roundAt_of_le_posMaxFinite hfmt hx mode hrange⟩

/-- The result is never negative, whatever the input and the attribute. -/
example (hfmt : fmt.isIEEE = true) (x : Model fmt) (mode : Model.IEEERoundingMode) :
    0 ≤ Model.toReal (CorrectlyRounded.expm1x x mode) :=
  CorrectlyRounded.toReal_expm1x_nonneg hfmt x mode

/-- Off the rationals the two nearest attributes round alike. -/
example (q : ℚ) (hq : q ≠ 0) :
    Model.roundAt fmt (Real.exp (q : ℝ) - 1 - q) .nearestAway =
      Model.roundAt fmt (Real.exp (q : ℝ) - 1 - q) :=
  CorrectlyRounded.roundAt_nearestAway_eq_of_irrational fmt
    (CorrectlyRounded.irrational_exp_sub_one_sub q hq)

end Statements

end FloatLibTests.Conformance.BinaryInterchange.Expm1x
