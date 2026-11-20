/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits

/-!
# `Int` operations for Lean's kernel

Lean's kernel computes on natural-number literals with GMP. To evaluate core integer arithmetic,
it also unfolds instances and matches on the constructors of `Int`.

The functions here take and return `Int` and compute the same values (`ZProof`) using `Int.rec`
to read each operand and `Nat` operations on its magnitude. The next operation can read the
result directly from its constructor.

Core Lean has the comparisons in this form already (`Int.ble'`, `Int.blt'`, `Int.beq'`, "for
kernel reduction"), and this module adds the arithmetic. A statement about integers can therefore
be rewritten operation by operation (`a * b + c ≤ d` becomes
`Int.ble' (Z.add (Z.mul a b) c) d = true`) and then decided by the kernel.

The definitions use recursors, so they have no compiled code of their own (`noncomputable`).
The theorems named `…_eq_compiled` make compiled code run core's operation in place of each: the
ones for the arithmetic are at the end of this module, proved with core Lean only, and `ZProof`
has the rest. So a definition that calls these functions is cheap for the kernel and compiles to
what it compiled to before.

## Main definitions

* `Z.subNat p n`: the integer `p - n` of two naturals; `Z.negOfNat n`: the integer `-n`.
* `Z.neg`, `Z.add`, `Z.sub`, `Z.mul`, `Z.pow`, `Z.natAbs`, `Z.toNat`.
* `Z.min`, `Z.max`, on core's `Int.ble'`.
* `Z.shiftLeft`, `Z.shiftRight`, `Z.ceilShift`: multiplication by `2 ^ k`, and division by
  `2 ^ k` rounded down and up.
* `Z.floorDiv`, `Z.ceilDiv`, `Z.tdivNat`, `Z.mod`: division by a natural number rounded down, up
  and toward zero, and the remainder in `[0, d)`.
* `Z.ediv`, `Z.emod`, `Z.fdiv`: the divisions `/`, `%` and `Int.fdiv` by an integer.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Z

/--
The integer `p - n` of two naturals. One subtraction decides the sign: `n - p` is zero exactly
when the value is not negative.
-/
noncomputable def subNat (p n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat (Nat.sub p n)) (fun k _ => Int.negSucc k)
    (Nat.sub n p)

/-- The integer `-n` of a natural number. -/
noncomputable def negOfNat (n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat 0) (fun k _ => Int.negSucc k) n

/-- `-x`. -/
noncomputable def neg (x : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => negOfNat m) (fun m => Int.ofNat (Nat.succ m)) x

/-- `x + y`. -/
noncomputable def add (x y : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int)
      (fun n => Int.ofNat (Nat.add m n)) (fun n => subNat m (Nat.succ n)) y)
    (fun m => Int.rec (motive := fun _ => Int)
      (fun n => subNat n (Nat.succ m)) (fun n => Int.negSucc (Nat.succ (Nat.add m n))) y) x

/-- `x - y`. -/
noncomputable def sub (x y : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int)
      (fun n => subNat m n) (fun n => Int.ofNat (Nat.succ (Nat.add m n))) y)
    (fun m => Int.rec (motive := fun _ => Int)
      (fun n => Int.negSucc (Nat.add m n)) (fun n => subNat n m) y) x

/-- `x * y`. -/
noncomputable def mul (x y : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Int.rec (motive := fun _ => Int)
      (fun n => Int.ofNat (Nat.mul m n)) (fun n => negOfNat (Nat.mul m (Nat.succ n))) y)
    (fun m => Int.rec (motive := fun _ => Int)
      (fun n => negOfNat (Nat.mul (Nat.succ m) n))
      (fun n => Int.ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) y) x

/-- The absolute value, as a natural number. -/
noncomputable def natAbs (x : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun m => m) (fun m => Nat.succ m) x

/-- `x` for `x ≥ 0`, and zero for a negative `x`. -/
noncomputable def toNat (x : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun m => m) (fun _ => 0) x

/--
`x ^ n`: one `Nat.pow` of the absolute value, negated when `x` is negative and `n` is odd.
-/
noncomputable def pow (x : Int) (n : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Nat.pow m n))
    (fun m => Nat.rec (motive := fun _ => Int) (Int.ofNat (Nat.pow (Nat.succ m) n))
      (fun _ _ => negOfNat (Nat.pow (Nat.succ m) n)) (Nat.mod n 2)) x

/-- The smaller of `x` and `y`. -/
noncomputable def min (x y : Int) : Int :=
  Bool.rec (motive := fun _ => Int) y x (Int.ble' x y)

/-- The larger of `x` and `y`. -/
noncomputable def max (x y : Int) : Int :=
  Bool.rec (motive := fun _ => Int) x y (Int.ble' x y)

/-- `x * 2 ^ k`. -/
noncomputable def shiftLeft (x : Int) (k : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Nat.shiftLeft m k))
    (fun m => Int.negSucc (Nat.sub (Nat.shiftLeft (Nat.succ m) k) 1)) x

/-- `⌊x / 2 ^ k⌋`, the shift `x >>> k` of integers. -/
noncomputable def shiftRight (x : Int) (k : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Nat.shiftRight m k))
    (fun m => Int.negSucc (Nat.shiftRight m k)) x

/-- `⌈x / 2 ^ k⌉`. -/
noncomputable def ceilShift (x : Int) (k : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Kernel.ceilShift m k))
    (fun m => negOfNat (Nat.shiftRight (Nat.succ m) k)) x

/-- `⌊x / d⌋` for a natural number `d`: the division `x / d` of integers. Zero for `d = 0`. -/
noncomputable def floorDiv (x : Int) (d : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Nat.div m d))
    (fun m => negOfNat (Kernel.ceilDiv (Nat.succ m) d)) x

/-- `⌈x / d⌉` for a natural number `d`. Zero for `d = 0`. -/
noncomputable def ceilDiv (x : Int) (d : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Kernel.ceilDiv m d))
    (fun m => negOfNat (Nat.div (Nat.succ m) d)) x

/--
`x / d` rounded toward zero, for a natural number `d`: the quotient of the absolute value with
the sign of `x`. It is the exact quotient when `d` divides `x`, and zero for `d = 0`.
-/
noncomputable def tdivNat (x : Int) (d : Nat) : Int :=
  Int.rec (motive := fun _ => Int) (fun m => Int.ofNat (Nat.div m d))
    (fun m => negOfNat (Nat.div (Nat.succ m) d)) x

/-- The remainder of `x` modulo a natural number `d`, in `[0, d)` for `d ≠ 0`. -/
noncomputable def mod (x : Int) (d : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun m => Nat.mod m d)
    (fun m => Nat.sub d (Nat.succ (Nat.mod m d))) x

/-- `x / y`, the division of integers whose remainder is not negative. -/
noncomputable def ediv (x y : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun d => floorDiv x d)
    (fun d => neg (floorDiv x (Nat.succ d))) y

/-- `x % y`, the remainder of integers that is not negative. For `y = 0` it is `x`. -/
noncomputable def emod (x y : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun d => Nat.rec (motive := fun _ => Int) x (fun _ _ => Int.ofNat (mod x d)) d)
    (fun d => Int.ofNat (mod x (Nat.succ d))) y

/-- `Int.fdiv x y`: the quotient rounded down, and zero for `y = 0`. -/
noncomputable def fdiv (x y : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun d => floorDiv x d)
    (fun d => floorDiv (neg x) (Nat.succ d)) y

/-! ### The arithmetic is core's

These equations are proved with core Lean only, so that a module that does not load the rest of
Mathlib can state what its checks mean and can run them as compiled code. `ZProof` has the
equations of the other functions.
-/

/-- `subNat p n` is `p - n`. -/
theorem subNat_eq (p n : Nat) : subNat p n = (p : Int) - n := by
  change Nat.rec (motive := fun _ => Int) (Int.ofNat (p - n)) (fun k _ => Int.negSucc k) (n - p) = _
  rcases h : n - p with _ | k
  · change Int.ofNat (p - n) = (p : Int) - (n : Int)
    simp only [Int.ofNat_eq_natCast]
    omega
  · change Int.negSucc k = (p : Int) - (n : Int)
    rw [Int.negSucc_eq]
    omega

/-- `negOfNat` is core's `Int.negOfNat`. -/
theorem negOfNat_eq_core (n : Nat) : negOfNat n = Int.negOfNat n := by
  cases n <;> rfl

/-- `negOfNat n` is `-n`. -/
theorem negOfNat_eq (n : Nat) : negOfNat n = -(n : Int) := by
  rw [negOfNat_eq_core, Int.negOfNat_eq]
  rfl

/-- `Z.neg` is negation. -/
theorem neg_eq (x : Int) : neg x = -x := by
  cases x with
  | ofNat m => exact negOfNat_eq_core m
  | negSucc m => rfl

/-- `Z.neg` is core's `Int.neg`, for statements written with the bare function. -/
theorem neg_eq_core (x : Int) : neg x = Int.neg x := neg_eq x

/-- `Z.add` is addition. -/
theorem add_eq (x y : Int) : add x y = x + y := by
  cases x <;> cases y <;>
    simp only [add, subNat_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.add_eq,
      Nat.succ_eq_add_one] <;> omega

/-- `Z.sub` is subtraction. -/
theorem sub_eq (x y : Int) : sub x y = x - y := by
  cases x <;> cases y <;>
    simp only [sub, subNat_eq, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.add_eq,
      Nat.succ_eq_add_one] <;> omega

/-- `Z.mul` is multiplication. -/
theorem mul_eq (x y : Int) : mul x y = x * y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => rfl
    | negSucc n => exact negOfNat_eq_core _
  | negSucc m =>
    cases y with
    | ofNat n => exact negOfNat_eq_core _
    | negSucc n => rfl

/-- `Z.natAbs` is the absolute value. -/
theorem natAbs_eq (x : Int) : natAbs x = x.natAbs := by
  cases x <;> rfl

/-- `Z.toNat` is `Int.toNat`. -/
theorem toNat_eq (x : Int) : toNat x = x.toNat := by
  cases x <;> rfl

/-- `Z.shiftLeft` is the shift `x <<< k`, which multiplies by `2 ^ k`. -/
theorem shiftLeft_eq (x : Int) (k : Nat) : shiftLeft x k = x <<< k := by
  cases x <;> rfl

/-- `Z.shiftRight` is the shift `x >>> k`, which divides by `2 ^ k` and rounds down. -/
theorem shiftRight_eq (x : Int) (k : Nat) : shiftRight x k = x >>> k := by
  cases x <;> rfl

/-- Compiled code runs `Int.subNatNat` in place of `Z.subNat`. -/
@[csimp] theorem subNat_eq_compiled : @subNat = @Int.subNatNat := by
  funext p n
  rw [subNat_eq, Int.subNatNat_eq_coe]

/-- Compiled code runs `Int.negOfNat` in place of `Z.negOfNat`. -/
@[csimp] theorem negOfNat_eq_compiled : @negOfNat = @Int.negOfNat := by
  funext
  exact negOfNat_eq_core ..

/-- Compiled code runs `Int.neg` in place of `Z.neg`. -/
@[csimp] theorem neg_eq_compiled : @neg = @Int.neg := by
  funext
  exact neg_eq ..

/-- Compiled code runs `Int.add` in place of `Z.add`. -/
@[csimp] theorem add_eq_compiled : @add = @Int.add := by
  funext
  exact add_eq ..

/-- Compiled code runs `Int.sub` in place of `Z.sub`. -/
@[csimp] theorem sub_eq_compiled : @sub = @Int.sub := by
  funext
  exact sub_eq ..

/-- Compiled code runs `Int.mul` in place of `Z.mul`. -/
@[csimp] theorem mul_eq_compiled : @mul = @Int.mul := by
  funext
  exact mul_eq ..

/-- Compiled code runs `Int.natAbs` in place of `Z.natAbs`. -/
@[csimp] theorem natAbs_eq_compiled : @natAbs = @Int.natAbs := by
  funext
  exact natAbs_eq ..

/-- Compiled code runs `Int.toNat` in place of `Z.toNat`. -/
@[csimp] theorem toNat_eq_compiled : @toNat = @Int.toNat := by
  funext
  exact toNat_eq ..

/-- Compiled code runs `Int.shiftLeft` in place of `Z.shiftLeft`. -/
@[csimp] theorem shiftLeft_eq_compiled : @shiftLeft = @Int.shiftLeft := by
  funext
  exact shiftLeft_eq ..

/-- Compiled code runs `Int.shiftRight` in place of `Z.shiftRight`. -/
@[csimp] theorem shiftRight_eq_compiled : @shiftRight = @Int.shiftRight := by
  funext
  exact shiftRight_eq ..

end FloatLib.Numerics.Kernel.Z
