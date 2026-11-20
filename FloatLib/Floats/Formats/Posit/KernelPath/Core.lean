/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Root

/-!
# Posit operations on natural-number encodings

Lean's kernel computes natively on natural-number literals only. This module defines the posit
operations as functions of the encodings, with nothing but the kernel's fast operations
(`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, shifts, masks, comparisons) and `Bool.casesOn`, for
a tapered format with `p` payload bits below the sign (`p + 1` bits in all) and `es` exponent
bits. The Posit Standard (2022) fixes `es = 2`; every other `es` is a FloatLib extension.

A positive magnitude `m` (`0 < m < 2 ^ p`) is read without a scan of its regime:

* `complement p m` is `m` when its first regime bit is clear and `2 ^ p - 1 - m` otherwise, and
  `tailLength p m` is the bit length `z` of that number. The regime run has `p - z` bits, and
  `z - 1` bits follow the regime terminator: the exponent and the fraction.
* `significand`, `exponent` and `fractionBits` are the decoded fields. The value is
  `significand * 2 ^ (exponent - bias p es)`: exponents carry the bias `regimeBias p * 2 ^ es`,
  so that every intermediate stays a natural number.

`encode p es bK M E` rounds the positive value `M * 2 ^ (E - bK * 2 ^ es)` to a code by the
Posit Standard's rule: it writes the exponent field and the fraction below the leading bit of `M`
as one integer (the stream), keeps the bits that fit after the regime, and rounds to nearest
with ties to the even code. Regimes that fill the payload give `maxPos` and `minPos`.

`add`, `sub`, `mul`, `div`, `sqrt` and `fma` decode, compute exactly on integers and round once
with `encode`. Division (`quotient`) and square root keep `p + 1` quotient or root bits and
record a nonzero remainder in the low bit, and `ofRatio` rounds a ratio of natural numbers the
same way, which is how a literal is rounded. NaR is `2 ^ p`, and a negative value is the two's
    complement of its
magnitude in `p + 1` bits. `neg`, `abs`, `next` and `prior` are the negation, the absolute
value and the neighbouring encodings, `signedKey`, `lt` and `le` the comparison key (the
encoding plus the sign bit modulo the width, so that keys are ordered like values and NaR is
the least) and its two tests, and `cast` the change of width. `toSigned` and `toUnsigned` are
the words of the conversions to a signed and to an unsigned integer of `w` bits (§6.4), with
`nearestNat` the nearest integer of a decoded value.

`FloatLib.Floats.Formats.Posit.KernelPath.Standard` proves each of them equal to the reference
operation at `es = 2`, for every width and every operand, and
`FloatLib.Floats.Formats.Posit.General` proves each of them against a specification on values
for every `es`.

Reference: Standard for Posit Arithmetic (2022), §§3.3, 4.1 and 5.2–5.7.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Numerics.Kernel

/-- The bias of a regime value: `8 * (p + 1)`, above every regime that the operations meet. -/
def regimeBias (p : Nat) : Nat := Nat.mul 8 (Nat.succ p)

/-- The bias of a binary exponent: `regimeBias p * 2 ^ es`. -/
def bias (p es : Nat) : Nat := Nat.shiftLeft (regimeBias p) es

/-- The NaR encoding `2 ^ p`, which is also the sign bit. -/
def nar (p : Nat) : Nat := Nat.shiftLeft 1 p

/-- The magnitude of an encoding: the encoding itself below the sign bit, and its two's
complement in `p + 1` bits otherwise. -/
def magnitude (p a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nar p) a)
    a (Nat.sub (Nat.shiftLeft 1 (Nat.succ p)) a)

/-- The encoding of the value with the sign bit `s` (zero or one) and the nonzero magnitude
code `c`. -/
def withSign (p s c : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq s 0)
    (Nat.sub (Nat.shiftLeft 1 (Nat.succ p)) c) c

/-- The negation of an encoding: the two's complement in `p + 1` bits, which fixes zero and
NaR. -/
def neg (p a : Nat) : Nat :=
  Nat.land (Nat.sub (Nat.shiftLeft 1 (Nat.succ p)) a) (Nat.sub (Nat.shiftLeft 1 (Nat.succ p)) 1)

/-- A magnitude with its first regime bit set is replaced by its complement in `p` bits, so that
the regime run is a run of zeros in either case. -/
def complement (p m : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.shiftLeft 1 (Nat.sub p 1)) m)
    m (Nat.sub (Nat.sub (Nat.shiftLeft 1 p) 1) m)

/-- The bit length of `complement p m`: the payload width minus the regime run. -/
def tailLength (p m : Nat) : Nat := bitLength p (complement p m)

/-- The number of fraction bits of the magnitude whose `tailLength` is `z`. -/
def fractionBits (es z : Nat) : Nat := Nat.sub (Nat.sub z 1) es

/-- The significand of a magnitude, with the leading one: `2 ^ fb + fraction`, `fb` the number of
fraction bits. -/
def significand (es m z : Nat) : Nat :=
  (fun fb => Nat.add (Nat.shiftLeft 1 fb) (lowBits m fb)) (fractionBits es z)

/--
The biased binary exponent of the unit of the significand: the magnitude `m` has the value
`significand es m z * 2 ^ (exponent p es m z - bias p es)`, with `z = tailLength p m`.
-/
def exponent (p es m z : Nat) : Nat :=
  (fun t =>
    (fun used fb =>
      Nat.sub
        (Nat.add
          (Nat.shiftLeft
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.shiftLeft 1 (Nat.sub p 1)) m)
              (Nat.sub (Nat.add (regimeBias p) z) p)
              (Nat.sub (Nat.sub (Nat.add (regimeBias p) p) z) 1))
            es)
          (Nat.shiftLeft (lowBits (Nat.shiftRight m fb) used) (Nat.sub es used)))
        fb)
      (minNat es t) (Nat.sub t es))
    (Nat.sub z 1)

/--
Round the stream `raw` of `w` bits to its first `t` bits above the code `base`, to nearest with
ties to the even code. A stream shorter than `t + 1` bits is padded with zeros.
-/
def roundTail (t base raw w : Nat) : Nat :=
  (fun d =>
    (fun sh padded =>
      (fun lower rem =>
        Bool.casesOn (motive := fun _ => Nat)
          (Nat.ble (Nat.succ (Nat.shiftLeft 1 sh))
            (Nat.add (Nat.shiftLeft rem 1) (Nat.land lower 1)))
          lower (Nat.succ lower))
        (Nat.add base (Nat.shiftRight padded sh)) (lowBits padded sh))
      (Nat.sub (Nat.add w d) t) (Nat.shiftLeft raw d))
    (Nat.sub (Nat.succ t) w)

/--
The code of the positive value `M * 2 ^ (E - bK * 2 ^ es)`, `M ≠ 0`, rounded by the Posit
Standard's rule in a format with `p` payload bits and `es` exponent bits.
-/
def encode (p es bK M E : Nat) : Nat :=
  (fun L =>
    (fun S =>
      (fun K raw =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.ble bK K)
          ((fun run =>
            Bool.casesOn (motive := fun _ => Nat) (Nat.ble p run)
              ((fun t => roundTail t (Nat.shiftLeft 1 t) raw (Nat.add L es))
                (Nat.sub (Nat.sub p run) 1))
              1)
            (Nat.sub bK K))
          ((fun run =>
            Bool.casesOn (motive := fun _ => Nat) (Nat.ble p run)
              ((fun t =>
                roundTail t (Nat.sub (Nat.shiftLeft 1 p) (Nat.shiftLeft 1 (Nat.sub p run))) raw
                  (Nat.add L es))
                (Nat.sub (Nat.sub p run) 1))
              (Nat.sub (Nat.shiftLeft 1 p) 1))
            (Nat.succ (Nat.sub K bK))))
        (Nat.shiftRight S es)
        (Nat.add (Nat.shiftLeft (lowBits S es) L) (Nat.sub M (Nat.shiftLeft 1 L))))
      (Nat.add E L))
    (Nat.sub (size M) 1)

/-- The encoding of the sum of the values with sign bits `s₁`, `s₂`, significands `m₁`, `m₂` and
exponents `e₁`, `e₂` biased by `bK * 2 ^ es`: exact alignment, one signed sum, one rounding. -/
def sumFields (p es bK s₁ m₁ e₁ s₂ m₂ e₂ : Nat) : Nat :=
  (fun a b E =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq s₁ s₂)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble b a)
        (withSign p s₂ (encode p es bK (Nat.sub b a) E))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a b)
          (withSign p s₁ (encode p es bK (Nat.sub a b) E))
          0))
      (withSign p s₁ (encode p es bK (Nat.add a b) E)))
    (Nat.shiftLeft m₁ (Nat.sub e₁ e₂)) (Nat.shiftLeft m₂ (Nat.sub e₂ e₁)) (minNat e₁ e₂)

/-- The sum of two encodings whose second operand has its sign bit replaced by `s₂`: the common
part of addition and subtraction, for operands that are neither zero nor NaR. -/
def sumFinite (p es a b s₂ : Nat) : Nat :=
  (fun ma mb =>
    (fun za zb =>
      sumFields p es (regimeBias p) (Nat.shiftRight a p) (significand es ma za)
        (exponent p es ma za) s₂ (significand es mb zb) (exponent p es mb zb))
      (tailLength p ma) (tailLength p mb))
    (magnitude p a) (magnitude p b)

/-- The encoding of the sum of the values encoded by `a` and `b`, rounded once. -/
def add (p es a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq a (nar p)) (Nat.beq b (nar p)))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq b 0)
        (sumFinite p es a b (Nat.shiftRight b p))
        a)
      b)
    (nar p)

/-- The encoding of the difference of the values encoded by `a` and `b`, rounded once. -/
def sub (p es a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq a (nar p)) (Nat.beq b (nar p)))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq b 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
        (sumFinite p es a b (Nat.sub 1 (Nat.shiftRight b p)))
        (neg p b))
      a)
    (nar p)

/-- The encoding of the product of the values encoded by `a` and `b`, rounded once. -/
def mul (p es a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq a (nar p)) (Nat.beq b (nar p)))
    (Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq a 0) (Nat.beq b 0))
      ((fun ma mb =>
        (fun za zb =>
          withSign p (Nat.xor (Nat.shiftRight a p) (Nat.shiftRight b p))
            (encode p es (Nat.mul 2 (regimeBias p))
              (Nat.mul (significand es ma za) (significand es mb zb))
              (Nat.add (exponent p es ma za) (exponent p es mb zb))))
          (tailLength p ma) (tailLength p mb))
        (magnitude p a) (magnitude p b))
      0)
    (nar p)

/-- A quotient or root prefix with a nonzero remainder recorded in its low bit. -/
def jam (q r : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq r 0) (Nat.lor q 1) q

/--
The magnitude code of the quotient of the positive integers `m₁` and `m₂`, whose leading bits
are at `l₁` and `l₂`, rounded once: `p + 1` quotient bits (`steps` is `p`, or `p + 1` when the
aligned numerator is below the denominator) and the remainder in the low bit. The quotient
prefix stands for `prefix * 2 ^ (E₀ - steps - bK * 2 ^ es)`.
-/
def quotient (p es bK m₁ l₁ m₂ l₂ E₀ : Nat) : Nat :=
  (fun common =>
    (fun N D =>
      (fun steps =>
        (fun scaled =>
          encode p es bK (jam (Nat.div scaled D) (Nat.mod scaled D)) (Nat.sub E₀ steps))
          (Nat.shiftLeft N steps))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble D N) (Nat.succ p) p))
      (Nat.shiftLeft m₁ (Nat.sub common l₁)) (Nat.shiftLeft m₂ (Nat.sub common l₂)))
    (maxNat l₁ l₂)

/-- The encoding of the quotient of the values encoded by `a` and `b`, rounded once. A zero or
NaR divisor and a NaR dividend give NaR. -/
def div (p es a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.or (Nat.beq a (nar p)) (Bool.or (Nat.beq b (nar p)) (Nat.beq b 0)))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
      ((fun ma mb =>
        (fun za zb =>
          (fun fa fb =>
            withSign p (Nat.xor (Nat.shiftRight a p) (Nat.shiftRight b p))
              (quotient p es (regimeBias p) (significand es ma za) fa (significand es mb zb) fb
                (Nat.sub (Nat.add (Nat.add (exponent p es ma za) (bias p es)) fa)
                  (Nat.add (exponent p es mb zb) fb))))
            (fractionBits es za) (fractionBits es zb))
          (tailLength p ma) (tailLength p mb))
        (magnitude p a) (magnitude p b))
      0)
    (nar p)

/--
The encoding of the ratio `(-1) ^ s * num / den` of two natural numbers, `den ≠ 0`, rounded
once. The bias `bK * 2 ^ es` is taken above the length of the denominator, so that every
exponent is a natural number whatever the operands.
-/
def ofRatio (p es s num den : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq num 0)
    ((fun la lb =>
      (fun bK =>
        withSign p s
          (quotient p es bK num la den lb (Nat.sub (Nat.add (Nat.shiftLeft bK es) la) lb)))
        (Nat.succ (Nat.shiftRight (Nat.add lb (Nat.succ p)) es)))
      (Nat.sub (size num) 1) (Nat.sub (size den) 1))
    0

/-- The encoding of the square root of the value encoded by `a`, rounded once: `p + 1` root
bits and the square remainder. A negative value and NaR give NaR. -/
def sqrt (p es a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nar p) a)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
      ((fun z =>
        (fun e =>
          (fun scaled =>
            (fun root =>
              encode p es (regimeBias p) (jam root (Nat.sub scaled (Nat.mul root root)))
                (Nat.sub (Nat.add (Nat.shiftRight e 1) (Nat.shiftRight (bias p es) 1)) p))
              (isqrt scaled))
            (Nat.shiftLeft (significand es a z) (Nat.add (Nat.land e 1) (Nat.mul 2 p))))
          (exponent p es a z))
        (tailLength p a))
      0)
    (nar p)

/-- The encoding of `a * b + c` on the values, rounded once. -/
def fma (p es a b c : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.or (Nat.beq a (nar p)) (Bool.or (Nat.beq b (nar p)) (Nat.beq c (nar p))))
    (Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq a 0) (Nat.beq b 0))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq c 0)
        ((fun ma mb mc =>
          (fun za zb zc =>
            sumFields p es (Nat.mul 2 (regimeBias p))
              (Nat.xor (Nat.shiftRight a p) (Nat.shiftRight b p))
              (Nat.mul (significand es ma za) (significand es mb zb))
              (Nat.add (exponent p es ma za) (exponent p es mb zb))
              (Nat.shiftRight c p) (significand es mc zc)
              (Nat.add (exponent p es mc zc) (bias p es)))
            (tailLength p ma) (tailLength p mb) (tailLength p mc))
          (magnitude p a) (magnitude p b) (magnitude p c))
        (mul p es a b))
      c)
    (nar p)

/-- The comparison key of an encoding: the encoding plus the sign bit, reduced to the width, so
that keys are ordered like the values and NaR has the least key. -/
def signedKey (p a : Nat) : Nat :=
  Nat.mod (Nat.add a (nar p)) (Nat.shiftLeft 1 (Nat.succ p))

/-- Whether the value encoded by `a` is below the value encoded by `b`, with NaR below every
value. -/
def lt (p a b : Nat) : Bool := Nat.ble (Nat.succ (signedKey p a)) (signedKey p b)

/-- Whether the value encoded by `a` is at most the value encoded by `b`, with NaR below every
value. -/
def le (p a b : Nat) : Bool := Nat.ble (signedKey p a) (signedKey p b)

/-- The absolute value of an encoding: the negation from the sign bit on, which fixes NaR. -/
def abs (p a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nar p) a) a (neg p a)

/-- The encoding after `a`, wrapping at the width. -/
def next (p a : Nat) : Nat := Nat.mod (Nat.succ a) (Nat.shiftLeft 1 (Nat.succ p))

/-- The encoding before `a`, wrapping at the width. -/
def prior (p a : Nat) : Nat :=
  (fun M => Nat.mod (Nat.sub (Nat.add a M) 1) M) (Nat.shiftLeft 1 (Nat.succ p))

/-- The encoding in the format `(q, es')` of the value encoded by `a` in the format `(p, es)`,
rounded once. The exponent is carried to a bias `bK * 2 ^ es'` above the source bias. -/
def cast (p es q es' a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq a (nar p))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
      ((fun m bK =>
        (fun z =>
          withSign q (Nat.shiftRight a p)
            (encode q es' bK (significand es m z)
              (Nat.sub (Nat.add (exponent p es m z) (Nat.shiftLeft bK es')) (bias p es))))
          (tailLength p m))
        (magnitude p a) (Nat.succ (Nat.shiftRight (bias p es) es')))
      0)
    (nar q)

/--
The natural number nearest to `M * 2 ^ (E - B)`, ties to even: the significand shifted up when
the exponent is at least the bias, and otherwise its quotient by the power of two, rounded by
the remainder.
-/
def nearestNat (M E B : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble B E)
    ((fun den =>
      (fun q r =>
        Nat.add q
          (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ (Nat.mul 2 r)) den)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.mul 2 r) den) 1 (Nat.mod q 2))
            0))
        (Nat.div M den) (Nat.mod M den))
      (Nat.shiftLeft 1 (Nat.sub B E)))
    (Nat.shiftLeft M (Nat.sub E B))

/--
The word of the signed integer of `w` bits that the value encoded by `a` converts to: the word
with only its most significant bit set for NaR and for a rounded value outside the range, zero
for zero, and otherwise the nearest integer of the value, ties to even, in two's complement.
-/
def toSigned (p es w a : Nat) : Nat :=
  (fun half =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq a (nar p))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
        ((fun m =>
          (fun z =>
            (fun n =>
              Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nar p) a)
                (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ n) half) half n)
                (Bool.casesOn (motive := fun _ => Nat) (Nat.ble n half) half
                  (Nat.mod (Nat.sub (Nat.shiftLeft 1 w) n) (Nat.shiftLeft 1 w))))
              (nearestNat (significand es m z) (exponent p es m z) (bias p es)))
            (tailLength p m))
          (magnitude p a))
        0)
      half)
    (Nat.shiftLeft 1 (Nat.sub w 1))

/--
The word of the unsigned integer of `w` bits that the value encoded by `a` converts to: the
word with only its most significant bit set for NaR and for a rounded value outside the range,
and otherwise the nearest integer of the value, ties to even.
-/
def toUnsigned (p es w a : Nat) : Nat :=
  (fun half =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq a (nar p))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
        ((fun m =>
          (fun z =>
            (fun n =>
              Bool.casesOn (motive := fun _ => Nat) (Nat.ble (nar p) a)
                (Bool.casesOn (motive := fun _ => Nat)
                  (Nat.ble (Nat.succ n) (Nat.shiftLeft 1 w)) half n)
                (Bool.casesOn (motive := fun _ => Nat) (Nat.beq n 0) half 0))
              (nearestNat (significand es m z) (exponent p es m z) (bias p es)))
            (tailLength p m))
          (magnitude p a))
        0)
      half)
    (Nat.shiftLeft 1 (Nat.sub w 1))

end FloatLib.Floats.Formats.Posit.KernelPath
