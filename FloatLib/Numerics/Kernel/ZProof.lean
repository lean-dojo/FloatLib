/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Arithmetic
public import FloatLib.Numerics.Kernel.Bits.Proof.PopCount
public import FloatLib.Numerics.Kernel.Z

/-!
# The kernel `Int` operations are the `Int` operations

Each function of `FloatLib.Numerics.Kernel.Z` equals the operation of core Lean it stands for, for
all integers. The equations of the arithmetic (`add_eq : Z.add x y = x + y`, `sub_eq`, `mul_eq`,
`neg_eq`, `natAbs_eq`, `toNat_eq`, `shiftLeft_eq`, `shiftRight_eq`) are in `Z` itself, proved
with core Lean. This module has the rest: `pow_eq`, `min_eq`, `max_eq`, `ediv_eq`, `emod_eq`,
`fdiv_eq`, `tdivNat_eq`. The Boolean comparisons are core's `Int.ble'`, `Int.blt'` and
`Int.beq'`, with `ble'_iff`, `blt'_iff` and `beq'_iff`. The rounded divisions are stated against
`Int` division, which rounds down: `floorDiv_eq`, `ceilDiv_eq`, `ceilShift_eq`, `mod_eq`.

The theorems named `…_eq_compiled` are tagged `@[csimp]`: compiled code runs core's operation in
place of each kernel function, so a definition that uses these functions keeps its compiled speed.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Z

/-- `Z.pow` is the power. -/
theorem pow_eq (x : Int) (n : Nat) : pow x n = x ^ n := by
  cases x with
  | ofNat m =>
    change Int.ofNat (m ^ n) = _
    simp
  | negSucc m =>
    change Nat.rec (motive := fun _ => Int) (Int.ofNat ((m + 1) ^ n))
      (fun _ _ => negOfNat ((m + 1) ^ n)) (n % 2) = _
    rw [Int.negSucc_eq]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [hn, Even.neg_pow (Nat.even_iff.2 hn)]
      change Int.ofNat ((m + 1) ^ n) = _
      simp
    · rw [hn, Odd.neg_pow (Nat.odd_iff.2 hn)]
      change negOfNat ((m + 1) ^ n) = _
      rw [negOfNat_eq]
      simp

/-- `Z.min` is the smaller of two integers. -/
theorem min_eq (x y : Int) : min x y = Min.min x y := by
  unfold min
  rcases hle : Int.ble' x y with _ | _
  · have h : ¬ x ≤ y := by rwa [Int.ble'_eq_false] at hle
    change y = _
    omega
  · have h : x ≤ y := by rwa [Int.ble'_eq_true] at hle
    change x = _
    omega

/-- `Z.max` is the larger of two integers. -/
theorem max_eq (x y : Int) : max x y = Max.max x y := by
  unfold max
  rcases hle : Int.ble' x y with _ | _
  · have h : ¬ x ≤ y := by rwa [Int.ble'_eq_false] at hle
    change x = _
    omega
  · have h : x ≤ y := by rwa [Int.ble'_eq_true] at hle
    change y = _
    omega

/-- `Z.floorDiv` is the division of integers by a natural number, which rounds down. -/
theorem floorDiv_eq (x : Int) (d : Nat) : floorDiv x d = x / (d : Int) := by
  cases x with
  | ofNat m => rfl
  | negSucc m =>
    change negOfNat (Kernel.ceilDiv (m + 1) d) = _
    rw [negOfNat_eq, Int.negSucc_eq]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [Kernel.ceilDiv_eq]
    · rw [← neg_ediv_natCast hd]
      norm_cast

/-- `Z.ceilDiv` is the quotient rounded up: the negated quotient of the negation. -/
theorem ceilDiv_eq (x : Int) (d : Nat) : ceilDiv x d = -((-x) / (d : Int)) := by
  cases x with
  | ofNat m =>
    change Int.ofNat (Kernel.ceilDiv m d) = _
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [Kernel.ceilDiv_eq]
    · simp only [Int.ofNat_eq_natCast]
      rw [neg_ediv_natCast hd, neg_neg]
  | negSucc m =>
    change negOfNat ((m + 1) / d) = _
    rw [negOfNat_eq, Int.negSucc_eq, neg_neg]
    norm_cast

/-- `Z.ceilShift` is the quotient by `2 ^ k` rounded up. -/
theorem ceilShift_eq (x : Int) (k : Nat) : ceilShift x k = -((-x) >>> k) := by
  have h : ceilShift x k = ceilDiv x (2 ^ k) := by
    cases x with
    | ofNat m =>
      change Int.ofNat (Kernel.ceilShift m k) = Int.ofNat (Kernel.ceilDiv m (2 ^ k))
      rw [Kernel.ceilShift_eq]
    | negSucc m =>
      change negOfNat ((m + 1) >>> k) = negOfNat ((m + 1) / 2 ^ k)
      rw [Nat.shiftRight_eq_div_pow]
  rw [h, ceilDiv_eq, Int.shiftRight_eq_div_pow]

/-- `Z.mod` is the remainder modulo a positive natural number. -/
theorem mod_eq (x : Int) {d : Nat} (hd : 0 < d) : ((mod x d : Nat) : Int) = x % (d : Int) := by
  cases x with
  | ofNat m =>
    change ((m % d : Nat) : Int) = _
    rw [Int.natCast_mod]
    rfl
  | negSucc m =>
    change ((d - (m % d + 1) : Nat) : Int) = _
    have hlt : m % d < d := Nat.mod_lt m hd
    rw [Int.negSucc_emod m (by exact_mod_cast hd), ← Int.natCast_mod]
    omega

/-- `Z.ediv` is the division `/` of integers. -/
theorem ediv_eq (x y : Int) : ediv x y = x / y := by
  cases y with
  | ofNat d => exact floorDiv_eq x d
  | negSucc d =>
    change neg (floorDiv x (d + 1)) = _
    rw [neg_eq, floorDiv_eq, Int.negSucc_eq, Int.ediv_neg]
    norm_cast

/-- `Z.emod` is the remainder `%` of integers. -/
theorem emod_eq (x y : Int) : emod x y = x % y := by
  cases y with
  | ofNat d =>
    cases d with
    | zero =>
      change x = x % ((0 : Nat) : Int)
      simp
    | succ d =>
      change Int.ofNat (mod x (d + 1)) = _
      rw [Int.ofNat_eq_natCast, mod_eq x (Nat.succ_pos d)]
      rfl
  | negSucc d =>
    change Int.ofNat (mod x (d + 1)) = _
    rw [Int.ofNat_eq_natCast, mod_eq x (Nat.succ_pos d), Int.negSucc_eq, Int.emod_neg]
    norm_cast

/-- `Z.fdiv` is `Int.fdiv`, the quotient rounded down. -/
theorem fdiv_eq (x y : Int) : fdiv x y = x.fdiv y := by
  cases y with
  | ofNat d =>
    change floorDiv x d = _
    rw [floorDiv_eq, Int.ofNat_eq_natCast, Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg d)]
  | negSucc d =>
    change floorDiv (neg x) (d + 1) = _
    have h := Int.neg_fdiv_neg (-x) ((d : Int) + 1)
    rw [neg_neg] at h
    rw [floorDiv_eq, neg_eq, Int.negSucc_eq, h, Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    norm_cast

/--
A `Bool.casesOn` on a test is the `if` on the proposition that the test decides. The kernel
definitions branch with `Bool.casesOn`, and this states them with `if`.
-/
theorem casesOn_eq_ite {α : Sort*} {p : Prop} [Decidable p] {c : Bool} (h : c = true ↔ p)
    (e t : α) : Bool.casesOn (motive := fun _ => α) c e t = if p then t else e := by
  cases c
  · rw [ite_eq_right (fun hp => Bool.false_ne_true (h.2 hp))]
  · rw [ite_eq_left (h.1 rfl)]

/-- `tdivNat` is the division of integers rounded toward zero. -/
theorem tdivNat_eq (x : Int) (d : Nat) : tdivNat x d = x.tdiv (d : Int) := by
  cases x with
  | ofNat m => rfl
  | negSucc m =>
    change negOfNat ((m + 1) / d) = _
    rw [negOfNat_eq]
    rfl

/-! ### Compiled code

The kernel functions are written with recursors, which Lean does not compile. Each of them is
replaced in compiled code by the operation of core Lean it equals, so a definition that calls them
is evaluated by the kernel in a few steps and still runs as fast as before when compiled.
-/

namespace Compiled

/-- Compiled form of core's `Int.ble'`. -/
def le (x y : Int) : Bool := decide (x ≤ y)

/-- Compiled form of core's `Int.blt'`. -/
def lt (x y : Int) : Bool := decide (x < y)

/-- Compiled form of core's `Int.beq'`. -/
def beq (x y : Int) : Bool := decide (x = y)

/-- Compiled form of `Z.min`. -/
def min (x y : Int) : Int := if x ≤ y then x else y

/-- Compiled form of `Z.max`. -/
def max (x y : Int) : Int := if x ≤ y then y else x

/-- Compiled form of `Z.floorDiv`. -/
def floorDiv (x : Int) (d : Nat) : Int := x / (d : Int)

/-- Compiled form of `Z.ceilDiv`. -/
def ceilDiv (x : Int) (d : Nat) : Int := -((-x) / (d : Int))

/-- Compiled form of `Z.ceilShift`. -/
def ceilShift (x : Int) (k : Nat) : Int := -((-x) >>> k)

/-- Compiled form of `Z.mod`. -/
def mod (x : Int) (d : Nat) : Nat := if d = 0 then x.toNat else (x % (d : Int)).toNat

/-- Compiled form of `Z.tdivNat`. -/
def tdivNat (x : Int) (d : Nat) : Int := x.tdiv (d : Int)

end Compiled

compiled_as tdivNat := Compiled.tdivNat by tdivNat_eq

compiled_as pow := Int.pow by pow_eq

/-- Compiled code runs `Z.Compiled.le` in place of `Int.ble'`. -/
@[csimp] theorem ble'_eq_compiled : @Int.ble' = @Compiled.le := by
  funext x y
  rw [Compiled.le, Bool.eq_iff_iff, Int.ble'_eq_true, decide_eq_true_eq]

/-- Compiled code runs `Z.Compiled.lt` in place of `Int.blt'`. -/
@[csimp] theorem blt'_eq_compiled : @Int.blt' = @Compiled.lt := by
  funext x y
  rw [Compiled.lt, Bool.eq_iff_iff, Int.blt'_eq_true, decide_eq_true_eq]

/-- Compiled code runs `Z.Compiled.beq` in place of `Int.beq'`. -/
@[csimp] theorem beq'_eq_compiled : @Int.beq' = @Compiled.beq := by
  funext x y
  rw [Compiled.beq, Bool.eq_iff_iff, Int.beq'_eq, decide_eq_true_eq]

/-- Core's `Int.ble'` decides `≤`. -/
theorem ble'_iff (x y : Int) : Int.ble' x y = true ↔ x ≤ y := by
  rw [Int.ble'_eq_true]

/-- Core's `Int.blt'` decides `<`. -/
theorem blt'_iff (x y : Int) : Int.blt' x y = true ↔ x < y := by
  rw [Int.blt'_eq_true]

/-- Core's `Int.beq'` decides equality. -/
theorem beq'_iff (x y : Int) : Int.beq' x y = true ↔ x = y := by
  rw [Int.beq'_eq]

/-- Compiled code runs `Z.Compiled.min` in place of `Z.min`. -/
@[csimp] theorem min_eq_compiled : @min = @Compiled.min := by
  funext x y
  rw [min_eq, Compiled.min]
  split <;> omega

/-- Compiled code runs `Z.Compiled.max` in place of `Z.max`. -/
@[csimp] theorem max_eq_compiled : @max = @Compiled.max := by
  funext x y
  rw [max_eq, Compiled.max]
  split <;> omega

compiled_as ceilShift := Compiled.ceilShift by ceilShift_eq

compiled_as floorDiv := Compiled.floorDiv by floorDiv_eq

compiled_as ceilDiv := Compiled.ceilDiv by ceilDiv_eq

/-- Compiled code runs `Z.Compiled.mod` in place of `Z.mod`. -/
@[csimp] theorem mod_eq_compiled : @mod = @Compiled.mod := by
  funext x d
  rw [Compiled.mod]
  split
  · subst d
    cases x with
    | ofNat m => exact Nat.mod_zero m
    | negSucc m => exact Nat.zero_sub _
  · have hd : 0 < d := by omega
    have h := mod_eq x hd
    omega

compiled_as ediv := Int.ediv by ediv_eq

compiled_as emod := Int.emod by emod_eq

compiled_as fdiv := Int.fdiv by fdiv_eq

end FloatLib.Numerics.Kernel.Z
