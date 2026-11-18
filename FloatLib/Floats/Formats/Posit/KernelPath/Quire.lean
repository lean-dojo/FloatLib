/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.KernelPath.Core

/-!
# Quire operations on natural-number encodings

The quire of an `n`-bit posit (Posit Standard (2022), §3.4 and §5.11) is a two's-complement
fixed-point word of `16 * n` bits whose unit is `2 ^ (16 - 8 * n)`, and its most negative word is
the quire NaR. These are its operations as functions of the encodings, with the kernel's fast
operations only, for a posit with `p` payload bits (`n = p + 1`) and the standard's two exponent
bits:

* `quireAccumulate p q s c`: the word of the ordinary quire `q` plus the signed integer
  `(-1) ^ s * c` in quire units, or the quire NaR when the sum is not an ordinary coefficient;
* `quireAddPosit` and `quireAddProduct`: the accumulation of a posit and of the exact product
  of two posits, with a flag that subtracts instead (the conversion of a posit is its
  accumulation into the zero quire);
* `quireAddQuire`, `quireNeg`, `quireAbs`: quire addition and subtraction, negation and
  absolute value;
* `quireRound`: the posit nearest to a quire, by one `encode`.

`KernelPath.QuireProof` proves each of them equal to the reference operation of
`Quire.Model`, for every width and every operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Numerics.Kernel

/-- The width of the quire of a posit with `p` payload bits: `16 * (p + 1)`. -/
def quireWidth (p : Nat) : Nat := Nat.mul 16 (Nat.succ p)

/-- The quire NaR word `2 ^ (quireWidth p - 1)`, which is also the sign bit. -/
def quireNar (p : Nat) : Nat := Nat.shiftLeft 1 (Nat.sub (quireWidth p) 1)

/--
The word of the ordinary quire `q` plus `(-1) ^ s * c` quire units, and the quire NaR when the
sum is not an ordinary coefficient. With `H` the NaR word, the coefficient of `q` plus `H` is
`(q + H) % (2 * H)`, and the sum is ordinary exactly when that key plus `H ± c` lies strictly
between `H` and `3 * H`.
-/
def quireAccumulate (p q s c : Nat) : Nat :=
  (fun H =>
    (fun K =>
      Bool.casesOn (motive := fun _ => Nat)
        (Bool.and (Nat.ble (Nat.succ H) K) (Nat.ble (Nat.succ K) (Nat.mul 3 H)))
        H (Nat.mod K (Nat.shiftLeft H 1)))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq s 0)
        (Nat.sub (Nat.add (Nat.mod (Nat.add q H) (Nat.shiftLeft H 1)) H) c)
        (Nat.add (Nat.add (Nat.mod (Nat.add q H) (Nat.shiftLeft H 1)) H) c)))
    (quireNar p)

/-- The quire `q` plus the posit `a`, or minus it when `flip` is one. NaR in either gives the
quire NaR. -/
def quireAddPosit (p q a flip : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq q (quireNar p)) (Nat.beq a (nar p)))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a 0)
      ((fun m =>
        (fun z =>
          quireAccumulate p q (Nat.xor (Nat.shiftRight a p) flip)
            (Nat.shiftLeft (significand 2 m z)
              (Nat.sub (Nat.add (exponent p 2 m z) (Nat.mul 8 (Nat.succ p)))
                (Nat.add (bias p 2) 16))))
          (tailLength p m))
        (magnitude p a))
      q)
    (quireNar p)

/-- The quire `q` plus the exact product of the posits `a` and `b`, or minus it when `flip` is
one. NaR in any operand gives the quire NaR. -/
def quireAddProduct (p q a b flip : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.or (Nat.beq q (quireNar p)) (Bool.or (Nat.beq a (nar p)) (Nat.beq b (nar p))))
    (Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq a 0) (Nat.beq b 0))
      ((fun ma mb =>
        (fun za zb =>
          quireAccumulate p q (Nat.xor (Nat.xor (Nat.shiftRight a p) (Nat.shiftRight b p)) flip)
            (Nat.shiftLeft (Nat.mul (significand 2 ma za) (significand 2 mb zb))
              (Nat.sub
                (Nat.add (Nat.add (exponent p 2 ma za) (exponent p 2 mb zb))
                  (Nat.mul 8 (Nat.succ p)))
                (Nat.add (Nat.mul 2 (bias p 2)) 16))))
          (tailLength p ma) (tailLength p mb))
        (magnitude p a) (magnitude p b))
      q)
    (quireNar p)

/-- The quire `q` plus the quire `r`, or minus it when `flip` is one. -/
def quireAddQuire (p q r flip : Nat) : Nat :=
  (fun H =>
    Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.beq q H) (Nat.beq r H))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble H r)
        (quireAccumulate p q flip r)
        (quireAccumulate p q (Nat.sub 1 flip) (Nat.sub (Nat.shiftLeft H 1) r)))
      H)
    (quireNar p)

/-- The negation of a quire: the two's complement, which fixes zero and NaR. -/
def quireNeg (p q : Nat) : Nat :=
  (fun M => Nat.mod (Nat.sub M q) M) (Nat.shiftLeft 1 (quireWidth p))

/-- The absolute value of a quire. NaR stays NaR. -/
def quireAbs (p q : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (quireNar p) q) q (quireNeg p q)

/-- The posit nearest to the quire `q`, by the Posit Standard's rounding. The quire NaR gives the
posit NaR.

Reference: Standard for Posit Arithmetic (2022), §§4.1 and 6.2.
-/
def quireRound (p q : Nat) : Nat :=
  (fun H =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq q H)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq q 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble H q)
          (encode p 2 (Nat.mul 2 (Nat.succ p)) q 16)
          (withSign p 1 (encode p 2 (Nat.mul 2 (Nat.succ p)) (Nat.sub (Nat.shiftLeft H 1) q) 16)))
        0)
      (nar p))
    (quireNar p)

end FloatLib.Floats.Formats.Posit.KernelPath
