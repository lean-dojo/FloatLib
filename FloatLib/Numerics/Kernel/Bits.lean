/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Bit length, bits and ceilings in few kernel steps

Lean's kernel computes `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.gcd`,
`Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` and
`Nat.pow` on literals with GMP, and it interprets everything else one step at a time (Lean v4.36.0).
`Nat.log2` costs it about eight microseconds per bit and `Nat.testBit` fifty-five microseconds,
because they are unfolded through instances and recursion. This module computes the same values
from the fast operations alone. Large powers of two are written as shifts of one: the kernel
computes both, and Lean's elaborator, which a tactic may use to evaluate the same definitions,
refuses `Nat.pow` with an exponent above 256. It imports nothing beyond core Lean, so a module
that only checks numbers can import it without loading Mathlib or Lean's own elaborator.

`compiled_as f := g by lemma` (`FloatLib.Tactic.CompiledAs`) is the command by which the proof
modules give a kernel-shaped definition the compiled code of the ordinary function it equals.

## Bit length

`laneLength B n` compares `n` with every power `2 ^ j`, `j < B`, at once. It spreads `n` over `B`
lanes of `B + 1` bits, adds `2 ^ B - 2 ^ j` in lane `j`, so that bit `B` of the lane is set exactly
when `2 ^ j ≤ n`, and adds up those bits with one remainder modulo `2 ^ (B + 1) - 1`. The lane
constants depend on `B` only, so the kernel computes them once per proof. They have `B * (B + 1)`
bits, which is cheap up to a few hundred bits and too much beyond.

`windowLength W k n acc` is a binary search with `k` steps for `n < 2 ^ (W * 2 ^ k)`: each step
shifts out the upper half of the remaining bits when it is not zero and counts it, and the lane
method measures the `W` bits that are left. `searchLength k n acc` is the search down to one bit,
which the lane programs of the small formats use.

`bitLength B n` is for a number with a known bound `n < 2 ^ B`: the lane method for `B ≤ 384`,
and for `384 < B ≤ 2 ^ 24` the search down to a window of 128 bits, with as many steps as
`(B - 1) / 128` has bits, so that its cost grows with the logarithm of the width.

`size n` needs no bound. Below `2 ^ 64` it is the lanes of 64 bits, below `2 ^ 128` the lanes
of 64 bits on the upper half, and below `2 ^ 256` the same two cases on the upper 128 bits
(`size128`), so that the common sizes multiply by a constant of 4,096 bits only. `sizeAbove n`
takes the rest: below `2 ^ 1024` the same halving of the upper 256 or 512 bits (`size256`,
`size512`), and otherwise the search down to a window of 128 bits with 5, 7, 10, 17 or 25 steps,
whichever is the first that covers `n`. A number of `2 ^ 32` bits or more, which the kernel
cannot hold, falls back on `Nat.log2`.

## Bits and ceilings

`bit n i` is bit `i` of `n` as zero or one, `testBit` is the same as a Boolean, and `lowBits n k`
is `n % 2 ^ k`, each by one shift and one mask. `ceilShift n k` is `⌈n / 2 ^ k⌉` and `ceilDiv a b`
is `⌈a / b⌉`.

`popCount n` is the number of set bits. The kernel has no such operation on its GMP numbers, so
this adds neighbouring lanes of 1, 2, 4, … bits with two masks and one addition per level
(`pairSum`), and adds the lanes of the last level with one remainder. A number of 64 bits takes
three levels and one of 100,000 bits five. `factorial n` is `n !` by `Nat.rec`.

The theorems are in `FloatLib.Numerics.Kernel.BitsProof`: `size_eq` (`size n = Nat.size n`),
`bitLength_eq`, `testBit_eq`, `ceilShift_eq`, `popCount_eq`, `factorial_eq` and their siblings.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- `∑ j < B, 2 ^ (j * (B + 1))`: a one in bit zero of each of `B` lanes of `B + 1` bits. -/
def laneOnes (B : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul B (Nat.succ B))) 1)
    (Nat.sub (Nat.shiftLeft 1 (Nat.succ B)) 1)

/-- `∑ j < B, (2 ^ B - 2 ^ j) * 2 ^ (j * (B + 1))`: the comparison offset of each lane. -/
def laneOffsets (B : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (laneOnes B) B)
    (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul B (Nat.add B 2))) 1)
      (Nat.sub (Nat.shiftLeft 1 (Nat.add B 2)) 1))

/--
The number of `j < B` with `2 ^ j ≤ n`. For `n < 2 ^ B` this is the bit length of `n`
(`laneLength_eq`). The definition uses seven kernel-accelerated operations on `n`.
-/
def laneLength (B n : Nat) : Nat :=
  Nat.mod
    (Nat.land (Nat.shiftRight (Nat.add (Nat.mul n (laneOnes B)) (laneOffsets B)) B) (laneOnes B))
    (Nat.sub (Nat.shiftLeft 1 (Nat.succ B)) 1)

/--
`acc` plus the bit length of `n`, for `n < 2 ^ 2 ^ k`, by `k` steps of a binary search
(`searchLength_eq`): when the bits of `n` above the lowest `2 ^ k` are not all zero, they replace
`n` and `2 ^ k` is counted.
-/
def searchLength : Nat → Nat → Nat → Nat
  | 0, n, acc => Nat.add acc n
  | k + 1, n, acc =>
      (fun upper =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq upper 0)
          (searchLength k upper (Nat.add acc (Nat.pow 2 k)))
          (searchLength k n acc))
        (Nat.shiftRight n (Nat.pow 2 k))

/--
`acc` plus the bit length of `n`, for `n < 2 ^ (W * 2 ^ k)` (`windowLength_eq`): `k` steps of a
binary search, then the lane method on a window of `W` bits. When the bits of `n` above the
lowest `W * 2 ^ k` are not all zero, they replace `n` and `W * 2 ^ k` is counted. The recursion
is on `Nat.rec`, which costs the kernel about twelve microseconds per step.
-/
def windowLength (W k n acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun n acc => Nat.add acc (laneLength W n))
    (fun k next n acc =>
      (fun upper =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq upper 0)
          (next upper (Nat.add acc (Nat.mul W (Nat.pow 2 k))))
          (next n acc))
        (Nat.shiftRight n (Nat.mul W (Nat.pow 2 k))))
    k n acc

/--
The bit length of `n` for `n < 2 ^ B` (`bitLength_eq`): the lane method for `B ≤ 384`, and for
`384 < B ≤ 2 ^ 24` the binary search down to a window of 128 bits, with as many steps as
`(B - 1) / 128` has bits.
-/
def bitLength (B n : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble B 384)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble B 16777216)
      (laneLength B n)
      (windowLength 128 (laneLength 17 (Nat.div (Nat.sub B 1) 128)) n 0))
    (laneLength B n)

/--
`windowLength 128 k n 0` when `n < 2 ^ (128 * 2 ^ k)`, and `other` when it is not. With `other`
the bit length of `n`, the value is the bit length of `n` either way (`windowBelow_eq`).
-/
def windowBelow (k n other : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n (Nat.shiftLeft 128 k)) 0)
    other (windowLength 128 k n 0)

/--
The bit length of `n` for `n < 2 ^ 128` (`size128_eq`): the `laneLength` of 64 bits of `n`, or
of its upper 64 bits plus 64.
-/
def size128 (n : Nat) : Nat :=
  (fun upper =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq upper 0)
      (Nat.add 64 (laneLength 64 upper)) (laneLength 64 n))
    (Nat.shiftRight n 64)

/--
The bit length of `n` for `n < 2 ^ 256` (`size256_eq`): `size128` of `n`, or of its upper 128
bits plus 128.
-/
def size256 (n : Nat) : Nat :=
  (fun upper =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq upper 0)
      (Nat.add 128 (size128 upper)) (size128 n))
    (Nat.shiftRight n 128)

/--
The bit length of `n` for `n < 2 ^ 512` (`size512_eq`): `size256` of `n`, or of its upper 256
bits plus 256.
-/
def size512 (n : Nat) : Nat :=
  (fun upper =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq upper 0)
      (Nat.add 256 (size256 upper)) (size256 n))
    (Nat.shiftRight n 256)

/--
The bit length `n.log2 + 1` of `n` for `2 ^ 256 ≤ n` (`sizeAbove_eq`): below `2 ^ 512` it is
`size256` of the upper 256 bits plus 256, below `2 ^ 1024` `size512` of the upper 512 bits plus
512, and above a `windowLength` of 5, 7, 10, 17 or 25 steps down to a window of 128 bits.
-/
def sizeAbove (n : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 512) 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 1024) 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 4096) 0)
        (windowBelow 7 n (windowBelow 10 n (windowBelow 17 n (windowBelow 25 n
          (Nat.succ (Nat.log2 n))))))
        (windowLength 128 5 n 0))
      (Nat.add 512 (size512 (Nat.shiftRight n 512))))
    (Nat.add 256 (size256 (Nat.shiftRight n 256)))

/--
The bit length of `n`: zero for zero and `n.log2 + 1` otherwise (`size_eq`, `size_eq_log2`), for
every `n`. Below `2 ^ 64` it is one `laneLength`, below `2 ^ 128` the `laneLength` of the upper
64 bits plus 64, below `2 ^ 256` `size128` of the upper 128 bits plus 128, and `sizeAbove n`
beyond.
-/
def size (n : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 64) 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 128) 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 256) 0)
        (sizeAbove n)
        (Nat.add 128 (size128 (Nat.shiftRight n 128))))
      (Nat.add 64 (laneLength 64 (Nat.shiftRight n 64))))
    (laneLength 64 n)

/-- Bit `i` of `n`, as zero or one (`bit_eq`). One shift and one mask. -/
def bit (n i : Nat) : Nat := Nat.land (Nat.shiftRight n i) 1

/-- Whether bit `i` of `n` is set: `Nat.testBit n i` (`testBit_eq`) in three kernel operations. -/
def testBit (n i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight n i) 1) 1

/-- The lowest `k` bits of `n`: `n % 2 ^ k` (`lowBits_eq`). -/
def lowBits (n k : Nat) : Nat := Nat.land n (Nat.sub (Nat.shiftLeft 1 k) 1)

/-- `⌈n / 2 ^ k⌉` (`ceilShift_eq`), where `Nat.shiftRight n k` is `⌊n / 2 ^ k⌋`. -/
def ceilShift (n k : Nat) : Nat :=
  Nat.shiftRight (Nat.add n (Nat.sub (Nat.shiftLeft 1 k) 1)) k

/-- `⌈a / b⌉` for `b ≠ 0`, and zero for `b = 0`: Mathlib's `a ⌈/⌉ b` (`ceilDiv_eq_nat`), with
the bounds `le_mul_ceilDiv` and `mul_ceilDiv_lt`. -/
def ceilDiv (a b : Nat) : Nat := Nat.div (Nat.add a (Nat.sub b 1)) b

/-- The larger of two naturals without a branch: `a + (b - a)`. -/
def maxNat (a b : Nat) : Nat := Nat.add a (Nat.sub b a)

/-- The smaller of two naturals without a branch: `a - (a - b)`. -/
def minNat (a b : Nat) : Nat := Nat.sub a (Nat.sub a b)

/--
The mask of the lowest `w` bits of every lane of `2 * w` bits, over `total` bits:
`(2 ^ total - 1) / (2 ^ w + 1)`, for `total` a multiple of `2 * w`.
-/
def pairMask (w total : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 total) 1) (Nat.succ (Nat.shiftLeft 1 w))

/--
One level of the population count. With `m` the mask `pairMask w total`, every lane of `2 * w`
bits of the result holds the sum of the two lanes of `w` bits of `x` that it covers.
-/
def pairSum (m w x : Nat) : Nat :=
  Nat.add (Nat.land x m) (Nat.land (Nat.shiftRight x w) m)

/--
`k` levels of `pairSum` on a number of `total` bits, from lanes of `w` bits to lanes of
`w * 2 ^ k` bits. The lanes of the result add up to what the lanes of `x` add up to
(`pairLevels_mod` states it for `w = 1`).
-/
noncomputable def pairLevels (total k w x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ x => x)
    (fun _ next w x => next (Nat.add w w) (pairSum (pairMask w total) w x))
    k w x

/--
The number of set bits of `n`, the sum of its binary digits (`popCount_eq`), for every `n`.
The kernel has no population count on its GMP numbers. This adds neighbouring lanes of 1, 2,
4, … bits until one lane can hold the whole count, and then adds all lanes with one remainder
modulo `2 ^ W - 1`. Below `2 ^ 64` these are three levels with literal masks and the remainder
modulo 255. Above, the lane width is `W = 2 ^ k` with `k` the bit length of the bit length of
the bit length of `n`: 32 bits and five levels for a number of 100,000 bits.
-/
noncomputable def popCount (n : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n 64) 0)
    ((fun L =>
      (fun k =>
        (fun W =>
          Nat.mod (pairLevels (Nat.mul W (Nat.succ (Nat.div L W))) k 1 n)
            (Nat.sub (Nat.shiftLeft 1 W) 1))
          (Nat.shiftLeft 1 k))
        (size (size L)))
      (size n))
    (Nat.mod
      (pairSum 0x0f0f0f0f0f0f0f0f 4
        (pairSum 0x3333333333333333 2 (pairSum 0x5555555555555555 1 n)))
      255)

/--
`n !` (`factorial_eq`) by `Nat.rec`, one multiplication per step. The kernel takes about a
quarter of the time per step that the recursion by pattern matching of `Nat.factorial` takes.
-/
noncomputable def factorial (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun k product => Nat.mul (Nat.succ k) product) n

end FloatLib.Numerics.Kernel
