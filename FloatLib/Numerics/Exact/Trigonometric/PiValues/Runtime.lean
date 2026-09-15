/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Floor

/-!
# Exact rational values at rational multiples of pi

Most rational angles have irrational sine and cosine. The exceptions must be handled before
interval refinement: an interval may otherwise straddle an exact rounding boundary forever.
Reduction modulo one leaves four cosine cases; the removed integer controls the sign.
No approximate value of pi enters this classification.
-/

@[expose] public section

namespace FloatLib.Numerics.TrigonometricComparison

/--
Sign contributed by an integer number of half-turns.

Only parity matters. Reducing modulo two also avoids passing an arbitrarily large exponent
to the runtime's power operation for wide posit inputs.
-/
def halfTurnSign (turns : ℤ) : ℚ :=
  if turns % 2 = 0 then 1 else -1

/-- The rational cosine value, when it exists, at the angle `argument * π`. -/
def cosPiExact (argument : ℚ) : Option ℚ :=
  let fraction := Int.fract argument
  let sign := halfTurnSign (Int.floor argument)
  if fraction = 0 then some sign
  else if fraction = 1 / 3 then some (sign / 2)
  else if fraction = 1 / 2 then some 0
  else if fraction = 2 / 3 then some (-sign / 2)
  else none

/-- Classify exact sine values by the complementary cosine angle. -/
def sinPiExact (argument : ℚ) : Option ℚ :=
  cosPiExact (1 / 2 - argument)

/-- Reduce a pi-scaled angle to `[-1/2, 1/2)`, preserving its tangent. -/
def centeredPi (argument : ℚ) : ℚ :=
  let fraction := Int.fract argument
  if fraction < 1 / 2 then fraction else fraction - 1

/-- Exact rational tangent values; half-integer poles are checked separately. -/
def tanPiExact (argument : ℚ) : Option ℚ :=
  let angle := centeredPi argument
  if angle = -1 / 4 then some (-1)
  else if angle = 0 then some 0
  else if angle = 1 / 4 then some 1
  else none

/-- The rational values of inverse tangent divided by pi. -/
def arctanPiExact (argument : ℚ) : Option ℚ :=
  if argument = -1 then some (-1 / 4)
  else if argument = 0 then some 0
  else if argument = 1 then some (1 / 4)
  else none

/-- The rational values of inverse sine divided by pi on its real domain. -/
def arcsinPiExact (argument : ℚ) : Option ℚ :=
  if argument = -1 then some (-1 / 2)
  else if argument = -1 / 2 then some (-1 / 6)
  else if argument = 0 then some 0
  else if argument = 1 / 2 then some (1 / 6)
  else if argument = 1 then some (1 / 2)
  else none

/-- Inverse cosine uses the complementary inverse sine angle. -/
def arccosPiExact (argument : ℚ) : Option ℚ :=
  (arcsinPiExact argument).map (1 / 2 - ·)

end FloatLib.Numerics.TrigonometricComparison
