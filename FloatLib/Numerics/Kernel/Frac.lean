/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Signed

/-!
# Fractions for Lean's kernel: no gcd per operation

Lean's `Rat` keeps every value in lowest terms. A computation that only compares its final
result can defer reduction and use cross-multiplication for the comparison.

A `Frac` is three naturals `plus`, `minus`, `den` with `0 < den`, and stands for the rational
`(plus - minus) / den` (`toRat`). Nothing is reduced: a sum multiplies across, a product multiplies
numerators and denominators, and a comparison cross-multiplies, all with the bare `Nat` functions
that the kernel computes with GMP. `normalize` divides by the gcd where the caller asks for it,
which pays off before a long chain of operations on the same value.

The sign is carried as in `Signed`: the numerator is the pair `(plus, minus)`, and the operations
need no case distinction on it. Each fraction carries a proof that its denominator is positive.
The arithmetic and comparison theorems in `FracProof` apply to unreduced fractions.

## Main definitions

* `Frac.toRat`, `Frac.ofRat`, `Frac.ofInt`, `Frac.ofNat`, `Frac.ofSigned`, `Frac.ofScientific`.
* `add`, `sub`, `neg`, `mul`, `inv`, `div`, `pow`, `mulPow2`, `divPow2`, `normalize`.
* `le`, `lt`, `beq`, `isNeg`: comparisons as Booleans.
* `floor`, `ceil`: the integers next to a fraction, as `Signed`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
The rational `(plus - minus) / den`, kept as three naturals so that Lean's kernel computes on it
natively. The denominator is positive and nothing is reduced to lowest terms.
-/
structure Frac where
  /-- The part of the numerator that counts positively. -/
  plus : Nat
  /-- The part of the numerator that counts negatively. -/
  minus : Nat
  /-- The denominator. -/
  den : Nat
  /-- The denominator is positive. -/
  den_pos : 0 < den := by decide

namespace Frac

/-- `m + (1 - m)` is `m` for a positive `m` and one for zero, so it is always positive. -/
theorem add_one_sub_pos (m : Nat) : 0 < Nat.add m (Nat.sub 1 m) := by
  change 0 < m + (1 - m)
  omega

/-- A positive number shifted left is positive. -/
theorem shiftLeft_pos {d : Nat} (hd : 0 < d) (k : Nat) : 0 < Nat.shiftLeft d k := by
  change 0 < d <<< k
  rw [Nat.shiftLeft_eq]
  exact Nat.mul_pos hd (Nat.two_pow_pos k)

/-- The quotient of a positive number by its gcd with another number is positive. -/
theorem div_gcd_pos {d : Nat} (hd : 0 < d) (m : Nat) : 0 < Nat.div d (Nat.gcd m d) :=
  Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right m d)) (Nat.gcd_pos_of_pos_right m hd)

/-- The numerator, as a pair. -/
def num (x : Frac) : Signed := ⟨x.plus, x.minus⟩

/-- The rational number `(plus - minus) / den`. -/
def toRat (x : Frac) : Rat := mkRat x.num.toInt x.den

/-- The fraction `z / 1` of an integer given as a pair. -/
def ofSigned (z : Signed) : Frac := ⟨z.plus, z.minus, 1, Nat.zero_lt_one⟩

/-- The fraction `n / 1` of a natural number. -/
def ofNat (n : Nat) : Frac := ⟨n, 0, 1, Nat.zero_lt_one⟩

/-- The fraction `z / 1` of an integer. -/
def ofInt (z : Int) : Frac :=
  Int.casesOn (motive := fun _ => Frac) z (fun n => ⟨n, 0, 1, Nat.zero_lt_one⟩)
    (fun n => ⟨0, Nat.succ n, 1, Nat.zero_lt_one⟩)

/-- The fraction of a rational number: its numerator over its denominator. -/
def ofRat (q : Rat) : Frac :=
  Int.casesOn (motive := fun _ => Frac) q.num
    (fun n => ⟨n, 0, q.den, Nat.pos_of_ne_zero q.den_nz⟩)
    (fun n => ⟨0, Nat.succ n, q.den, Nat.pos_of_ne_zero q.den_nz⟩)

/--
The fraction of a decimal literal: `mantissa / 10 ^ exponent` when `exponentSign` is set and
`mantissa * 10 ^ exponent` otherwise.
-/
def ofScientific (mantissa : Nat) (exponentSign : Bool) (exponent : Nat) : Frac :=
  Bool.casesOn (motive := fun _ => Frac) exponentSign
    ⟨Nat.mul mantissa (Nat.pow 10 exponent), 0, 1, Nat.zero_lt_one⟩
    ⟨mantissa, 0, Nat.pow 10 exponent, Nat.pow_pos (by decide)⟩

/-- The sum, with a normal numerator. -/
def add (x y : Frac) : Frac :=
  ⟨Nat.sub (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.plus x.den))
      (Nat.add (Nat.mul x.minus y.den) (Nat.mul y.minus x.den)),
    Nat.sub (Nat.add (Nat.mul x.minus y.den) (Nat.mul y.minus x.den))
      (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.plus x.den)),
    Nat.mul x.den y.den, Nat.mul_pos x.den_pos y.den_pos⟩

/-- The difference, with a normal numerator. -/
def sub (x y : Frac) : Frac :=
  ⟨Nat.sub (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.minus x.den))
      (Nat.add (Nat.mul x.minus y.den) (Nat.mul y.plus x.den)),
    Nat.sub (Nat.add (Nat.mul x.minus y.den) (Nat.mul y.plus x.den))
      (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.minus x.den)),
    Nat.mul x.den y.den, Nat.mul_pos x.den_pos y.den_pos⟩

/-- The negation: the two parts of the numerator change places. -/
def neg (x : Frac) : Frac := ⟨x.minus, x.plus, x.den, x.den_pos⟩

/-- The product. -/
def mul (x y : Frac) : Frac :=
  ⟨Nat.add (Nat.mul x.plus y.plus) (Nat.mul x.minus y.minus),
    Nat.add (Nat.mul x.plus y.minus) (Nat.mul x.minus y.plus),
    Nat.mul x.den y.den, Nat.mul_pos x.den_pos y.den_pos⟩

/--
The inverse, and zero for zero. The denominator goes to the part of the numerator that carries
the sign, and the absolute value of the numerator becomes the denominator (one for zero).
-/
def inv (x : Frac) : Frac :=
  ⟨Nat.mul x.den (Nat.sub 1 (Nat.sub 1 (Nat.sub x.plus x.minus))),
    Nat.mul x.den (Nat.sub 1 (Nat.sub 1 (Nat.sub x.minus x.plus))),
    Nat.add (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus))
      (Nat.sub 1 (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus))),
    add_one_sub_pos _⟩

/-- The quotient, and zero when the divisor is zero. -/
def div (x y : Frac) : Frac := x.mul y.inv

/-- The power `x ^ n`, with a normal numerator. -/
def pow (x : Frac) (n : Nat) : Frac :=
  ⟨(x.num.pow n).plus, (x.num.pow n).minus, Nat.pow x.den n, Nat.pow_pos x.den_pos⟩

/-- `x * 2 ^ k`. -/
def mulPow2 (x : Frac) (k : Nat) : Frac :=
  ⟨Nat.shiftLeft x.plus k, Nat.shiftLeft x.minus k, x.den, x.den_pos⟩

/-- `x / 2 ^ k`. -/
def divPow2 (x : Frac) (k : Nat) : Frac :=
  ⟨x.plus, x.minus, Nat.shiftLeft x.den k, shiftLeft_pos x.den_pos k⟩

/--
The same rational in lowest terms with a normal numerator: one gcd of the absolute value of the
numerator with the denominator, and two divisions.
-/
def normalize (x : Frac) : Frac :=
  ⟨Nat.div (Nat.sub x.plus x.minus)
      (Nat.gcd (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus)) x.den),
    Nat.div (Nat.sub x.minus x.plus)
      (Nat.gcd (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus)) x.den),
    Nat.div x.den (Nat.gcd (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus)) x.den),
    div_gcd_pos x.den_pos _⟩

/-- Whether `x ≤ y`, by cross-multiplication. -/
def le (x y : Frac) : Bool :=
  Nat.ble (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.minus x.den))
    (Nat.add (Nat.mul y.plus x.den) (Nat.mul x.minus y.den))

/-- Whether `x < y`, by cross-multiplication. -/
def lt (x y : Frac) : Bool :=
  Nat.ble (Nat.succ (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.minus x.den)))
    (Nat.add (Nat.mul y.plus x.den) (Nat.mul x.minus y.den))

/-- Whether `x` and `y` are the same rational, by cross-multiplication. -/
def beq (x y : Frac) : Bool :=
  Nat.beq (Nat.add (Nat.mul x.plus y.den) (Nat.mul y.minus x.den))
    (Nat.add (Nat.mul y.plus x.den) (Nat.mul x.minus y.den))

/-- Whether `x < 0`. -/
def isNeg (x : Frac) : Bool := Nat.ble (Nat.succ x.plus) x.minus

/-- The largest integer at most `x`. -/
def floor (x : Frac) : Signed := x.num.floorDiv x.den

/-- The smallest integer at least `x`. -/
def ceil (x : Frac) : Signed := x.num.ceilDiv x.den

end Frac

end FloatLib.Numerics.Kernel
