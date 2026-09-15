/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.ExpLog
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime

/-!
# Executable floating-point powers

`Model.pow` provides one deterministic power policy for every `FloatFormat`. Small nonnegative
integer exponents use a linear sequence of rounded multiplications. Small negative integer
exponents of finite nonzero bases use an exact scaled rational and round once, avoiding intermediate
overflow or underflow before inversion. Larger integer exponents and non-integer exponents use the
generic `exp` and `log` kernels.

Integer exponents are classified directly from their dyadic representation. The classifier records
sign, parity, and an optional bounded magnitude without constructing an integer whose bit length is
controlled by the floating-point exponent field. This is essential for formats with wide exponent
fields.

The general `exp`/`log` path is approximate; this module does not prove correct rounding for real
exponentiation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Power

/-- Largest integer magnitude evaluated directly rather than through `exp` and `log`. -/
def smallPowLimit : Nat := 256

/--
Information needed to evaluate a finite integral floating-point exponent.

`smallMagnitude?` is populated exactly when the magnitude is at most `smallPowLimit`.
-/
structure IntegerExponent where
  /-- Whether the nonzero integer is negative. -/
  negative : Bool
  /-- Whether its magnitude is odd. -/
  odd : Bool
  /-- Its magnitude when small enough for direct evaluation. -/
  smallMagnitude? : Option Nat
  deriving Repr, DecidableEq

/-- Return a magnitude when it is within the direct evaluation limit. -/
@[inline] def smallMagnitude (magnitude : Nat) : Option Nat :=
  if magnitude ≤ smallPowLimit then some magnitude else none

/--
Classify a finite dyadic as an integer.

For a nonnegative dyadic exponent, the left shift is bounded by `log₂ smallPowLimit`; the shifted
magnitude is then checked against the limit. For a negative exponent, divisibility is checked
only when the right shift is no greater than the significand's leading bit index.
-/
def classifyIntegerDyadic? (value : Numerics.Dyadic) : Option IntegerExponent :=
  if value.significand == 0 then
    some { negative := false, odd := false, smallMagnitude? := some 0 }
  else
    match value.exponent with
    | .ofNat shift =>
        let odd := shift == 0 && value.significand % 2 == 1
        let small? :=
          if shift ≤ Nat.log2 smallPowLimit then
            smallMagnitude (Nat.shiftLeft value.significand shift)
          else
            none
        some { negative := value.negative, odd, smallMagnitude? := small? }
    | .negSucc shift =>
        let denominatorShift := shift + 1
        if Nat.log2 value.significand < denominatorShift then
          none
        else
          let magnitude := Nat.shiftRight value.significand denominatorShift
          if Nat.shiftLeft magnitude denominatorShift == value.significand then
            some
              { negative := value.negative
                odd := magnitude % 2 == 1
                smallMagnitude? := smallMagnitude magnitude }
          else
            none

/-- Classify an executable finite value as an integer exponent. -/
@[inline] def classifyInteger? {fmt : FloatFormat}
    (value : Model fmt) : Option IntegerExponent :=
  (toDyadic? value).bind classifyIntegerDyadic?

/-- Repeated rounded multiplication with recurrence `p₀ = 1`, `pₙ₊₁ = base * pₙ`. -/
def powNatLinear {fmt : FloatFormat} (base : Model fmt) : Nat → Model fmt
  | 0 => posOne fmt
  | exponent + 1 => mul base (powNatLinear base exponent)

/--
Evaluate the direct integer-power path. Callers select magnitudes at most `smallPowLimit`.

For a finite nonzero base `s * 2^e`, a negative exponent of magnitude `n` is rounded from
`(1 / s^n) * 2^(-e*n)`. Only the significand is raised to a power, so the denominator's size is
bounded by the input precision and `smallPowLimit`, independently of the exponent range.
Exceptional bases retain the division and multiplication policies of the format.
-/
@[inline] def powSmallInteger {fmt : FloatFormat}
    (base : Model fmt) (metadata : IntegerExponent) (magnitude : Nat) : Model fmt :=
  if metadata.negative then
    match toDyadic? base with
    | some exact =>
        if exact.significand == 0 then
          div (posOne fmt) (powNatLinear base magnitude)
        else
          roundRatScaled fmt (exact.negative && magnitude % 2 == 1)
            1 (exact.significand ^ magnitude) (-(exact.exponent * Int.ofNat magnitude))
    | none => div (posOne fmt) (powNatLinear base magnitude)
  else
    powNatLinear base magnitude

/--
Evaluate the integer-power branch before `pow` applies the negative-base sign rule.

Large magnitudes use the deterministic general path `exp (b * log |a|)`.
-/
def powIntegerDet {fmt : FloatFormat}
    (base exponent : Model fmt) (metadata : IntegerExponent) : Model fmt :=
  match metadata.smallMagnitude? with
  | some magnitude => powSmallInteger base metadata magnitude
  | none => exp (mul exponent (log (abs base)))

end Power

/--
Deterministic executable floating-point exponentiation.

The special cases and branch order are explicit:

* `x^(+-0) = 1`, including a NaN base;
* `1^y = 1` except for a signaling-NaN exponent;
* infinite exponents are classified by `|x|` relative to one;
* finite negative bases require an integral exponent;
* signed zero and negative infinity retain a negative result exactly for odd integer exponents.
-/
def pow {fmt : FloatFormat} (base exponent : Model fmt) : Model fmt :=
  if isZero exponent then
    posOne fmt
  else if compare base (posOne fmt) = some .eq && !isSNaN exponent then
    posOne fmt
  else
    match chooseNaN2 base exponent with
    | some nan => nan
    | none =>
        if compare exponent (posOne fmt) = some .eq then
          base
        else if isInf exponent then
          match compare (abs base) (posOne fmt) with
          | some .lt =>
              if signBit exponent then nativeOverflow fmt false else zero fmt false
          | some .eq => posOne fmt
          | some .gt =>
              if signBit exponent then zero fmt false else nativeOverflow fmt false
          | none => invalidResult fmt
        else
          match compare base (zero fmt false) with
          | some .eq =>
              match Power.classifyInteger? exponent with
              | some metadata =>
                  match compare exponent (zero fmt false) with
                  | some .lt =>
                      nativeOverflow fmt (signBit base && metadata.odd)
                  | some .gt =>
                      zero fmt (signBit base && metadata.odd)
                  | _ => zero fmt false
              | none =>
                  match compare exponent (zero fmt false) with
                  | some .lt => nativeOverflow fmt false
                  | _ => zero fmt false
          | some .lt =>
              match Power.classifyInteger? exponent with
              | none =>
                  if isInf base then
                    match compare exponent (zero fmt false) with
                    | some .lt => zero fmt false
                    | some .gt => nativeOverflow fmt false
                    | _ => invalidResult fmt
                  else
                    invalidResult fmt
              | some metadata =>
                  let magnitude := Power.powIntegerDet base exponent metadata
                  if metadata.odd then neg (abs magnitude) else abs magnitude
          | _ =>
              match Power.classifyInteger? exponent with
              | some metadata => Power.powIntegerDet base exponent metadata
              | none => exp (mul exponent (log base))

end Model
end FloatLib.Floats.Formats.BinaryInterchange
