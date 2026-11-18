/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Z

/-!
# Integers for Lean's kernel: differences of two naturals

A `Signed` is a pair of naturals `plus` and `minus` that stands for the integer `plus - minus`
(`toInt`). Sums, products and comparisons of such pairs are a few operations on naturals with no
case distinction on a sign:

* `(a - b) + (c - d) = (a + c) - (b + d)`,
* `(a - b) * (c - d) = (a * c + b * d) - (a * d + b * c)`,
* `a - b ≤ c - d` exactly when `a + d ≤ c + b`.

A pair is *normal* when one of its two parts is zero. `ofInt`, `norm`, `add`, `sub` and the
rounding operations return normal pairs, and `mul` returns one when its arguments are normal, in
which case three of its four products have a zero factor. The arithmetic and comparisons
represent the corresponding integer operations for arbitrary input pairs (`SignedProof`).
Equality of represented integers implies equality of their pairs when both pairs are normal.

The definitions use the bare `Nat` functions, so the kernel's fast path fires and no instance
is unfolded. They all have compiled code: `toInt` compiles to core's `Int.subNatNat`
(`Z.subNat_eq_compiled`).

## Main definitions

* `Signed.toInt`, `Signed.ofInt`, `Signed.ofNat`: the integer of a pair, and the normal pair of
  an integer or a natural number.
* `add`, `sub`, `neg`, `mul`, `pow`, `natAbs`, `norm`, `shiftLeft`.
* `le`, `lt`, `beq`, `isNeg`: comparisons as Booleans.
* `floorShift`, `ceilShift`, `floorDiv`, `ceilDiv`, `mod`: division by a power of two or by a
  natural number, rounded down or up, and the remainder in `[0, d)`.
* `min`, `max`: the smaller and the larger, part by part.
* `Normal`: one of the two parts is zero.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- The integer `plus - minus`, kept as two naturals so that Lean's kernel computes on it
natively. -/
structure Signed where
  /-- The part that counts positively. -/
  plus : Nat
  /-- The part that counts negatively. -/
  minus : Nat
  deriving DecidableEq, Repr

namespace Signed

/-- The integer `plus - minus` of a pair. -/
def toInt (x : Signed) : Int := Z.subNat x.plus x.minus

/-- The normal pair of an integer: `(n, 0)` for `n ≥ 0` and `(0, n)` for `-n < 0`. -/
def ofInt (z : Int) : Signed :=
  Int.casesOn (motive := fun _ => Signed) z (fun n => ⟨n, 0⟩) (fun n => ⟨0, Nat.succ n⟩)

/-- The pair `(n, 0)` of a natural number. -/
def ofNat (n : Nat) : Signed := ⟨n, 0⟩

/-- The normal pair of the same integer: the smaller part is subtracted from both. -/
def norm (x : Signed) : Signed := ⟨Nat.sub x.plus x.minus, Nat.sub x.minus x.plus⟩

/-- The sum, as a normal pair. -/
def add (x y : Signed) : Signed :=
  ⟨Nat.sub (Nat.add x.plus y.plus) (Nat.add x.minus y.minus),
    Nat.sub (Nat.add x.minus y.minus) (Nat.add x.plus y.plus)⟩

/-- The difference, as a normal pair. -/
def sub (x y : Signed) : Signed :=
  ⟨Nat.sub (Nat.add x.plus y.minus) (Nat.add x.minus y.plus),
    Nat.sub (Nat.add x.minus y.plus) (Nat.add x.plus y.minus)⟩

/-- The negation: the two parts change places. -/
def neg (x : Signed) : Signed := ⟨x.minus, x.plus⟩

/-- The product. It is normal when both factors are. -/
def mul (x y : Signed) : Signed :=
  ⟨Nat.add (Nat.mul x.plus y.plus) (Nat.mul x.minus y.minus),
    Nat.add (Nat.mul x.plus y.minus) (Nat.mul x.minus y.plus)⟩

/-- The absolute value, as a natural number. -/
def natAbs (x : Signed) : Nat := Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus)

/--
The power `x ^ n`, as a normal pair: one `Nat.pow` of the absolute value, which counts negatively
when `x` is negative and `n` is odd.
-/
def pow (x : Signed) (n : Nat) : Signed :=
  (fun magnitude odd =>
    ⟨Nat.mul (Nat.sub 1 odd) magnitude, Nat.mul odd magnitude⟩)
    (Nat.pow (natAbs x) n)
    (Nat.mul (Nat.mod n 2) (Nat.sub 1 (Nat.sub 1 (Nat.sub x.minus x.plus))))

/-- `x * 2 ^ k`. -/
def shiftLeft (x : Signed) (k : Nat) : Signed := ⟨Nat.shiftLeft x.plus k, Nat.shiftLeft x.minus k⟩

/-- Whether `x ≤ y`. -/
def le (x y : Signed) : Bool := Nat.ble (Nat.add x.plus y.minus) (Nat.add y.plus x.minus)

/-- Whether `x < y`. -/
def lt (x y : Signed) : Bool := Nat.ble (Nat.succ (Nat.add x.plus y.minus)) (Nat.add y.plus x.minus)

/-- Whether `x` and `y` are the same integer. -/
def beq (x y : Signed) : Bool := Nat.beq (Nat.add x.plus y.minus) (Nat.add y.plus x.minus)

/-- Whether `x < 0`. -/
def isNeg (x : Signed) : Bool := Nat.ble (Nat.succ x.plus) x.minus

/-- `⌊x / 2 ^ k⌋`, as a normal pair. -/
def floorShift (x : Signed) (k : Nat) : Signed :=
  ⟨Nat.shiftRight (Nat.sub x.plus x.minus) k, Kernel.ceilShift (Nat.sub x.minus x.plus) k⟩

/-- `⌈x / 2 ^ k⌉`, as a normal pair. -/
def ceilShift (x : Signed) (k : Nat) : Signed :=
  ⟨Kernel.ceilShift (Nat.sub x.plus x.minus) k, Nat.shiftRight (Nat.sub x.minus x.plus) k⟩

/-- `⌊x / d⌋` for a natural number `d`, as a normal pair. For `d = 0` it is zero. -/
def floorDiv (x : Signed) (d : Nat) : Signed :=
  ⟨Nat.div (Nat.sub x.plus x.minus) d, Kernel.ceilDiv (Nat.sub x.minus x.plus) d⟩

/-- `⌈x / d⌉` for a natural number `d`, as a normal pair. For `d = 0` it is zero. -/
def ceilDiv (x : Signed) (d : Nat) : Signed :=
  ⟨Kernel.ceilDiv (Nat.sub x.plus x.minus) d, Nat.div (Nat.sub x.minus x.plus) d⟩

/-- The remainder of `x` modulo a natural number `d`, in `[0, d)` for `d ≠ 0`. -/
def mod (x : Signed) (d : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mod x.plus d) (Nat.sub d (Nat.mod x.minus d))) d

/--
The smaller of `x` and `y`, as a normal pair. On normal pairs the smaller integer has the smaller
positive part and the larger negative part, so no comparison of the two integers is needed.
-/
def min (x y : Signed) : Signed :=
  ⟨minNat (Nat.sub x.plus x.minus) (Nat.sub y.plus y.minus),
    maxNat (Nat.sub x.minus x.plus) (Nat.sub y.minus y.plus)⟩

/-- The larger of `x` and `y`, as a normal pair. -/
def max (x y : Signed) : Signed :=
  ⟨maxNat (Nat.sub x.plus x.minus) (Nat.sub y.plus y.minus),
    minNat (Nat.sub x.minus x.plus) (Nat.sub y.minus y.plus)⟩

/-- A pair is normal when one of its parts is zero: it is then the only normal pair of its
integer. -/
def Normal (x : Signed) : Prop := x.plus = 0 ∨ x.minus = 0

end Signed

end FloatLib.Numerics.Kernel
