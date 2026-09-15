/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Human-readable exact dyadic formatting

Dyadics with normalized exponents in `[-18, 18]` are printed as exact decimals; the remaining
values use a significand times a power of two. This diagnostic notation limits expansion caused
by the exponent, while the printed significand can still be arbitrarily large. Formatting uses
integer arithmetic throughout.
-/

@[expose] public section

namespace FloatLib.Numerics.Dyadic

namespace Formatting

/-- Fuel-bounded worker that removes trailing binary zeroes from a magnitude. -/
def normalizeMagnitudeLoop :
    Nat → Nat → Int → Nat × Int
  | 0, current, currentExponent => (current, currentExponent)
  | remaining + 1, current, currentExponent =>
      if current != 0 && current % 2 == 0 then
        normalizeMagnitudeLoop remaining (Nat.shiftRight current 1) (currentExponent + 1)
      else
        (current, currentExponent)

/-- Remove powers of two from a nonzero significand. -/
def normalizeMagnitude (significand : Nat) (exponent : Int) : Nat × Int :=
  normalizeMagnitudeLoop (Nat.log2 significand + 1) significand exponent

/-- Remove decimal zeroes that carry no information after the decimal point. -/
def trimFraction (digits : String) : String :=
  String.ofList (digits.toList.reverse.dropWhile (· == '0') |>.reverse)

/-- Insert a decimal point `places` digits from the right. -/
def withDecimalPoint (digits : String) (places : Nat) : String :=
  if places = 0 then
    digits
  else
    let length := digits.length
    if places < length then
      let split := length - places
      let integer := (digits.take split).toString
      let fraction := trimFraction (digits.drop split).toString
      if fraction.isEmpty then
        integer
      else
        integer ++ "." ++ fraction
    else
      "0." ++ String.ofList (List.replicate (places - length) '0') ++ digits

end Formatting

/--
Format an exact dyadic without changing its value.

The decimal branch is deliberately bounded. An arbitrary static format may have an enormous
exponent range, so attempting to materialize every exact decimal expansion would make inspecting
one extreme value allocate an unreasonable string.
-/
def format (value : Dyadic) : String :=
  let sign := if value.negative then "-" else ""
  if value.significand = 0 then
    sign ++ "0"
  else
    let normalized := Formatting.normalizeMagnitude value.significand value.exponent
    let magnitude := normalized.1
    let exponent := normalized.2
    if 0 ≤ exponent ∧ exponent ≤ 18 then
      sign ++ toString (magnitude * 2 ^ exponent.toNat)
    else if -18 ≤ exponent ∧ exponent < 0 then
      let places := (-exponent).toNat
      sign ++ Formatting.withDecimalPoint (toString (magnitude * 5 ^ places)) places
    else
      sign ++ s!"{magnitude} * 2^{exponent}"

end FloatLib.Numerics.Dyadic
