/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Lanes

import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Basic

/-!
# A lane machine: one kernel operation for all lanes

Lean's kernel computes on natural-number literals with GMP and interprets everything else. A
proof that evaluates one small operation on many inputs (all pairs of an eight-bit format, a
table, a sweep) therefore pays the interpreter once per input. The lane machine pays it once per
operation instead: it keeps the inputs in rows, one input per lane of `w` bits, and every step
is a few kernel operations on whole rows.

A step must never let one lane disturb its neighbour, whatever the lanes hold. So a value of the
machine (`Val`) is a pair of rows: a *value* row, whose lanes always stay below `2 ^ (w - 1)`
(the top bit of every lane is free for carries and comparisons), and an *error* row, whose lane
is not zero when the value of that lane is not the exact result (it did not fit the lane, or a
shift count was out of range). An error is local to its lane, and a selection between two
values keeps the error of the selected one only, so a lane that overflows on a path it does not
take stays exact.

`Holds F xs p` says that the machine value `p` stands for the numbers `xs k`, one per lane: the
value row is well formed, and `lane k` of the value is `xs k` for every lane whose error is
zero. Each step comes with the theorem that it preserves `Holds` for the natural-number
operation it implements (`add_holds`, `sub_holds`, `shiftLeft_holds`, …), with no side
condition: an overflow is reported in the error row, never assumed away.

The steps are `const`, `add`, `sub` (truncated), `land`, `lor`, `xor`, shifts by a constant
(`shrC`, `shlC`), `nonzero`, `atLeast`, `select`, and on top of them shifts by a lane-dependent
count (`shiftRight`, `shiftLeft`) and the product of two rows (`mul`), which run a fixed number
of conditional constant steps. `Packed.Program` evaluates whole expressions with them.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed.Machine

/-- The constants of a machine with `count` lanes of `width` bits, computed once. -/
structure Frame where
  /-- Bits per lane. -/
  width : Nat
  /-- Number of lanes. -/
  count : Nat
  /-- `width - 1`: the number of value bits of a lane. -/
  bits : Nat
  /-- `2 ^ bits - 1`: the largest value of a lane. -/
  low : Nat
  /-- The row with a one in every lane. -/
  ones : Nat
  /-- The row with `low` in every lane. -/
  lows : Nat
  /-- The row with the top bit of every lane. -/
  tops : Nat
  /-- The row with every bit of every lane. -/
  full : Nat
  /-- The number of conditional steps of a shift by a lane-dependent count. -/
  depth : Nat

/-- The frame of `n` lanes of `w` bits, with shift counts below `2 ^ depth`. -/
def Frame.make (w n depth : Nat) : Frame :=
  (fun m o =>
    (fun low =>
      { width := w, count := n, bits := m, low := low, ones := o, lows := Nat.mul o low
        tops := Nat.shiftLeft o m, full := Nat.mul o (Nat.sub (pow2 w) 1), depth := depth })
      (Nat.sub (pow2 m) 1))
    (Nat.sub w 1) (Packed.ones w n)

/-- A frame whose constants are those of its width and count. -/
structure Frame.Valid (F : Frame) : Prop where
  /-- A lane has a value bit and a spare bit. -/
  width : 2 ≤ F.width
  /-- The value bits are all but the top bit. -/
  bits : F.bits = F.width - 1
  /-- The largest lane value. -/
  low : F.low = 2 ^ F.bits - 1
  /-- A one in every lane. -/
  ones : F.ones = Packed.ones F.width F.count
  /-- The largest value in every lane. -/
  lows : F.lows = F.ones * F.low
  /-- The top bit of every lane. -/
  tops : F.tops = F.ones * 2 ^ F.bits
  /-- Every bit of every lane. -/
  full : F.full = F.ones * (2 ^ F.width - 1)
  /-- Shift counts below `2 ^ depth` cover every bit position of a lane value. -/
  depth : F.bits ≤ 2 ^ F.depth

/-- A value of the machine: a row of lane values and a row of lane errors. -/
structure Val where
  /-- The value row: every lane is below `2 ^ (width - 1)`. -/
  value : Nat
  /-- The error row: a lane that is not zero marks a value that is not exact. -/
  error : Nat

/--
The machine value `p` stands for the numbers `xs k`, one per lane: its value row is well formed
(every lane below `2 ^ bits`, no lane from `count` on), and each lane whose error is zero holds
`xs k`.
-/
structure Holds (F : Frame) (xs : Nat → Nat) (p : Val) : Prop where
  /-- Every lane of the value row has its top bit clear. -/
  clean : ∀ k, lane F.width k p.value < 2 ^ F.bits
  /-- The value row has no lane from `count` on. -/
  bounded : ∀ k, F.count ≤ k → lane F.width k p.value = 0
  /-- A lane without an error holds its number. -/
  exact : ∀ k, k < F.count → lane F.width k p.error = 0 → lane F.width k p.value = xs k

namespace Frame.Valid

variable {F : Frame} (hF : F.Valid)
include hF

/-- A lane is one bit wider than its value. -/
theorem width_eq : F.width = F.bits + 1 := by
  have := hF.width
  have := hF.bits
  omega

/-- A lane value is below a lane. -/
theorem pow_bits_lt : 2 ^ F.bits < 2 ^ F.width := by
  rw [hF.width_eq, Nat.pow_succ]
  have := Nat.two_pow_pos F.bits
  omega

/-- The top of a lane is two top bits. -/
theorem pow_width : 2 ^ F.width = 2 ^ F.bits + 2 ^ F.bits := by
  rw [hF.width_eq, Nat.pow_succ]
  omega

/-- The lanes of the row of ones. -/
theorem lane_ones (k : Nat) : lane F.width k F.ones = if k < F.count then 1 else 0 := by
  rw [hF.ones]
  exact Packed.lane_ones (by have := hF.width; omega) _ _

/-- The lanes of a repeated number. -/
theorem lane_repeat {c : Nat} (hc : c < 2 ^ F.width) (k : Nat) :
    lane F.width k (F.ones * c) = if k < F.count then c else 0 := by
  rw [hF.ones]
  exact Packed.lane_const (by have := hF.width; omega) hc _ _

/-- The lanes of the row of largest values. -/
theorem lane_lows (k : Nat) :
    lane F.width k F.lows = if k < F.count then 2 ^ F.bits - 1 else 0 := by
  rw [hF.lows, hF.low]
  exact hF.lane_repeat (by have := hF.pow_bits_lt; have := Nat.two_pow_pos F.bits; omega) k

/-- The lanes of the row of top bits. -/
theorem lane_tops (k : Nat) : lane F.width k F.tops = if k < F.count then 2 ^ F.bits else 0 := by
  rw [hF.tops]
  exact hF.lane_repeat hF.pow_bits_lt k

/-- The lanes of the row of all bits. -/
theorem lane_full (k : Nat) :
    lane F.width k F.full = if k < F.count then 2 ^ F.width - 1 else 0 := by
  rw [hF.full]
  exact hF.lane_repeat (by have := Nat.two_pow_pos F.width; omega) k

end Frame.Valid

/-- `Frame.make` builds a valid frame. -/
theorem Frame.make_valid {w n depth : Nat} (hw : 2 ≤ w) (hdepth : w - 1 ≤ 2 ^ depth) :
    (Frame.make w n depth).Valid where
  width := hw
  bits := rfl
  low := by simp [Frame.make, pow2_eq]
  ones := rfl
  lows := rfl
  tops := by simp [Frame.make, Nat.shiftLeft_eq]
  full := by simp [Frame.make, pow2_eq]
  depth := hdepth

/-! ## Rows as given -/

/--
Whether the row `u` is a well-formed input of the frame: no lane from `count` on, and the top
bit of every lane clear. One comparison and one conjunction.
-/
def Frame.accepts (F : Frame) (u : Nat) : Bool :=
  Nat.ble u F.full && Nat.beq (Nat.land u F.tops) 0

/-- An accepted row, with no error. -/
def input (u : Nat) : Val :=
  ⟨u, 0⟩

/-- A row that is all errors: it stands for anything. -/
def poison (F : Frame) : Val :=
  ⟨0, F.ones⟩

/-! ## Lane facts shared by the steps -/

/-- A number below `2 ^ (m + 1)` whose bit `m` is clear is below `2 ^ m`. -/
theorem lt_of_and_two_pow_eq_zero {a m : Nat} (ha : a < 2 ^ (m + 1)) (h : a &&& 2 ^ m = 0) :
    a < 2 ^ m := by
  have hbit : a.testBit m = false := by
    have := congrArg (fun v => Nat.testBit v m) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow_self] using this
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not] at hbit
  have hq : a / 2 ^ m < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)]
    rw [Nat.pow_succ] at ha
    omega
  have hzero : a / 2 ^ m = 0 := by
    generalize a / 2 ^ m = q at hbit hq
    omega
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos m)).1 hzero

namespace Frame.Valid

variable {F : Frame} (hF : F.Valid)
include hF

/-- The low bits of every lane: a conjunction with the row of largest values. -/
theorem lane_land_lows (z k : Nat) :
    lane F.width k (Nat.land z F.lows) =
      if k < F.count then lane F.width k z % 2 ^ F.bits else 0 := by
  change lane F.width k (z &&& F.lows) = _
  rw [lane_land, hF.lane_lows]
  split
  · exact Nat.and_two_pow_sub_one_eq_mod _ _
  · exact Nat.and_zero _

/-- The top bit of every lane, as a zero or a one at the bottom of the lane. -/
theorem lane_top_flag (z k : Nat) :
    lane F.width k (Nat.land (Nat.shiftRight z F.bits) F.ones) =
      if k < F.count then lane F.width k z / 2 ^ F.bits else 0 := by
  change lane F.width k ((z >>> F.bits) &&& F.ones) = _
  rw [lane_land, hF.lane_ones]
  split
  · have hshift := lane_shiftRight_mod (w := F.width) (s := F.bits) (by have := hF.bits; omega) k z
    rw [show F.width - F.bits = 1 by have := hF.width_eq; omega, Nat.pow_one] at hshift
    rw [Nat.and_one_is_mod, hshift, Nat.shiftRight_eq_div_pow]
  · exact Nat.and_zero _

/-- A lane flag is at most one. -/
theorem lane_top_flag_le (z k : Nat) :
    lane F.width k (Nat.land (Nat.shiftRight z F.bits) F.ones) ≤ 1 := by
  change lane F.width k ((z >>> F.bits) &&& F.ones) ≤ 1
  rw [lane_land, hF.lane_ones]
  split
  · exact Nat.and_le_right
  · simp

/-- A row below the row of all bits has no lane from `count` on. -/
theorem lane_eq_zero_of_le_full {u k : Nat} (hu : u ≤ F.full) (hk : F.count ≤ k) :
    lane F.width k u = 0 := by
  have hfull : F.full < 2 ^ (F.width * F.count) := by
    rw [hF.full, hF.ones, Nat.mul_comm]
    exact (lanes_mul_ones (n := F.count) (by have := hF.width; omega)
      (by have := Nat.two_pow_pos F.width; omega)).2
  rw [lane_eq, Nat.div_eq_of_lt
    (lt_of_le_of_lt hu (lt_of_lt_of_le hfull
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hk)))), Nat.zero_mod]

end Frame.Valid

/-! ## Inputs and constants -/

/-- An accepted row stands for its own lanes. -/
theorem input_holds {F : Frame} (hF : F.Valid) {u : Nat} (h : F.accepts u = true) :
    Holds F (fun k => lane F.width k u) (input u) := by
  unfold Frame.accepts at h
  rw [Bool.and_eq_true] at h
  have hfull : u ≤ F.full := Nat.le_of_ble_eq_true h.1
  have htops : u &&& F.tops = 0 := Nat.eq_of_beq_eq_true h.2
  refine ⟨fun k => ?_, fun k hk => hF.lane_eq_zero_of_le_full hfull hk, fun _ _ _ => rfl⟩
  change lane F.width k u < 2 ^ F.bits
  have hlane : lane F.width k u &&& lane F.width k F.tops = 0 := by
    rw [← lane_land, htops, lane_zero_row]
  rw [hF.lane_tops] at hlane
  by_cases hk : k < F.count
  · rw [ite_eq_left hk] at hlane
    exact lt_of_and_two_pow_eq_zero (by rw [← hF.width_eq]; exact lane_lt _ _ _) hlane
  · rw [hF.lane_eq_zero_of_le_full hfull (Nat.le_of_not_lt hk)]
    exact Nat.two_pow_pos _

/-- The poisoned row stands for any numbers. -/
theorem poison_holds {F : Frame} (hF : F.Valid) (xs : Nat → Nat) : Holds F xs (poison F) := by
  refine ⟨fun k => by simp [poison], fun k _ => by simp [poison],
    fun k hk herr => ?_⟩
  rw [show (poison F).error = F.ones from rfl, hF.lane_ones, ite_eq_left hk] at herr
  exact absurd herr (by decide)

/-- The number `c` in every lane, or the poisoned row when `c` does not fit a lane. -/
def const (F : Frame) (c : Nat) : Val :=
  Bool.casesOn (motive := fun _ => Val) (Nat.ble c F.low) (poison F) ⟨Nat.mul F.ones c, 0⟩

/-- `const` stands for its number in every lane. -/
theorem const_holds {F : Frame} (hF : F.Valid) (c : Nat) : Holds F (fun _ => c) (const F c) := by
  unfold const
  cases hfit : Nat.ble c F.low
  · exact poison_holds hF _
  · have hc : c < 2 ^ F.bits := by
      have := Nat.le_of_ble_eq_true hfit
      rw [hF.low] at this
      have := Nat.two_pow_pos F.bits
      omega
    have hlane := hF.lane_repeat (lt_trans hc hF.pow_bits_lt)
    refine ⟨fun k => ?_, fun k hk => ?_, fun k hk _ => ?_⟩
    · change lane F.width k (F.ones * c) < _
      rw [hlane]
      split
      · exact hc
      · exact Nat.two_pow_pos _
    · change lane F.width k (F.ones * c) = 0
      rw [hlane, ite_eq_right (Nat.not_lt.mpr hk)]
    · change lane F.width k (F.ones * c) = c
      rw [hlane, ite_eq_left hk]

/-! ## Addition and truncated subtraction -/

/-- The lanewise sum. A lane whose sum does not fit is marked in the error row. -/
def add (F : Frame) (x y : Val) : Val :=
  (fun z =>
    ⟨Nat.land z F.lows,
      Nat.lor (Nat.lor x.error y.error) (Nat.land (Nat.shiftRight z F.bits) F.ones)⟩)
    (Nat.add x.value y.value)

/-- `add` stands for the lanewise sum. -/
theorem add_holds {F : Frame} (hF : F.Valid) {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) : Holds F (fun k => xs k + ys k) (add F x y) := by
  have hsum : ∀ k, lane F.width k (x.value + y.value) =
      lane F.width k x.value + lane F.width k y.value :=
    lane_add fun j => by
      have := hx.clean j
      have := hy.clean j
      rw [hF.pow_width]
      omega
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · change lane F.width k (Nat.land (x.value + y.value) F.lows) < _
    rw [hF.lane_land_lows]
    split
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · exact Nat.two_pow_pos _
  · change lane F.width k (Nat.land (x.value + y.value) F.lows) = 0
    rw [hF.lane_land_lows, ite_eq_right (Nat.not_lt.mpr hk)]
  · have herr' : lane F.width k x.error ||| lane F.width k y.error |||
        lane F.width k (Nat.land (Nat.shiftRight (x.value + y.value) F.bits) F.ones) = 0 := by
      rw [← lane_lor, ← lane_lor]
      exact herr
    obtain ⟨hxy, hflag⟩ := Nat.or_eq_zero_iff.1 herr'
    obtain ⟨hxe, hye⟩ := Nat.or_eq_zero_iff.1 hxy
    rw [hF.lane_top_flag, ite_eq_left hk, hsum] at hflag
    have hfit : lane F.width k x.value + lane F.width k y.value < 2 ^ F.bits :=
      (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 hflag
    change lane F.width k (Nat.land (x.value + y.value) F.lows) = xs k + ys k
    rw [hF.lane_land_lows, ite_eq_left hk, hsum, Nat.mod_eq_of_lt hfit, hx.exact k hk hxe,
      hy.exact k hk hye]

/--
The lanewise comparison `y ≤ x` as a flag row: the top bit of `(x + 2 ^ bits) - y`, moved to the
bottom of its lane.
-/
def atLeastFlags (F : Frame) (x y : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.sub (Nat.lor x F.tops) y) F.bits) F.ones

/-- The difference `(x + 2 ^ bits) - y` of two clean rows, lane by lane. -/
theorem lane_biased_sub {F : Frame} (hF : F.Valid) {x y : Nat}
    (hx : ∀ k, lane F.width k x < 2 ^ F.bits) (hxn : ∀ k, F.count ≤ k → lane F.width k x = 0)
    (hy : ∀ k, lane F.width k y < 2 ^ F.bits) (hyn : ∀ k, F.count ≤ k → lane F.width k y = 0)
    (k : Nat) :
    lane F.width k (Nat.sub (Nat.lor x F.tops) y) =
      if k < F.count then 2 ^ F.bits + lane F.width k x - lane F.width k y else 0 := by
  have hbiased : ∀ j, lane F.width j (x ||| F.tops) =
      if j < F.count then 2 ^ F.bits + lane F.width j x else 0 := fun j => by
    rw [lane_lor, hF.lane_tops]
    split
    · have hor := Nat.two_pow_add_eq_or_of_lt (hx j) 1
      rw [Nat.mul_one] at hor
      rw [Nat.or_comm, hor]
    · rename_i hj
      rw [hxn j (Nat.le_of_not_lt hj)]
      rfl
  change lane F.width k ((x ||| F.tops) - y) = _
  rw [lane_sub (by have := hF.width; omega) (fun j => by
    rw [hbiased]
    split
    · have := hy j
      omega
    · rename_i hj
      rw [hyn j (Nat.le_of_not_lt hj)]), hbiased]
  split
  · rfl
  · rename_i hk
    rw [hyn k (Nat.le_of_not_lt hk)]

/-- `atLeastFlags` is one in the lanes where `y ≤ x`, and zero elsewhere. -/
theorem lane_atLeastFlags {F : Frame} (hF : F.Valid) {x y : Nat}
    (hx : ∀ k, lane F.width k x < 2 ^ F.bits) (hxn : ∀ k, F.count ≤ k → lane F.width k x = 0)
    (hy : ∀ k, lane F.width k y < 2 ^ F.bits) (hyn : ∀ k, F.count ≤ k → lane F.width k y = 0)
    (k : Nat) :
    lane F.width k (atLeastFlags F x y) =
      if k < F.count ∧ lane F.width k y ≤ lane F.width k x then 1 else 0 := by
  unfold atLeastFlags
  rw [hF.lane_top_flag, lane_biased_sub hF hx hxn hy hyn]
  have hpos := Nat.two_pow_pos F.bits
  have := hx k
  have := hy k
  by_cases hk : k < F.count
  · rw [ite_eq_left hk, ite_eq_left hk]
    by_cases hle : lane F.width k y ≤ lane F.width k x
    · rw [ite_eq_left ⟨hk, hle⟩]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · rw [ite_eq_right (fun h => hle h.2)]
      exact Nat.div_eq_of_lt (by omega)
  · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.1)]

/-- The lanewise truncated difference `x - y`, which is zero where `x < y`. It has no error. -/
def sub (F : Frame) (x y : Val) : Val :=
  (fun d =>
    ⟨Nat.land d (Nat.mul (Nat.land (Nat.shiftRight d F.bits) F.ones) F.low),
      Nat.lor x.error y.error⟩)
    (Nat.sub (Nat.lor x.value F.tops) y.value)

/-- `sub` stands for the lanewise truncated difference. -/
theorem sub_holds {F : Frame} (hF : F.Valid) {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) : Holds F (fun k => xs k - ys k) (sub F x y) := by
  have hpos := Nat.two_pow_pos F.bits
  have hd := lane_biased_sub hF hx.clean hx.bounded hy.clean hy.bounded
  have hflag := lane_atLeastFlags hF hx.clean hx.bounded hy.clean hy.bounded
  unfold atLeastFlags at hflag
  -- The lanes of the value row.
  have hvalue : ∀ k, lane F.width k (sub F x y).value =
      if k < F.count then lane F.width k x.value - lane F.width k y.value else 0 := fun k => by
    change lane F.width k (Nat.sub (Nat.lor x.value F.tops) y.value &&&
      Nat.land (Nat.shiftRight (Nat.sub (Nat.lor x.value F.tops) y.value) F.bits) F.ones *
        F.low) = _
    rw [lane_land, lane_mul F.low (fun j => by
      have hle := hF.lane_top_flag_le (Nat.sub (Nat.lor x.value F.tops) y.value) j
      have hlow : F.low < 2 ^ F.width := by
        rw [hF.low]
        have := hF.pow_bits_lt
        omega
      calc _ ≤ 1 * F.low := Nat.mul_le_mul_right _ hle
        _ < 2 ^ F.width := by rw [Nat.one_mul]; exact hlow), hflag, hd]
    have := hx.clean k
    have := hy.clean k
    by_cases hk : k < F.count
    · rw [ite_eq_left hk, ite_eq_left hk]
      by_cases hle : lane F.width k y.value ≤ lane F.width k x.value
      · rw [ite_eq_left ⟨hk, hle⟩, Nat.one_mul, hF.low, Nat.and_two_pow_sub_one_eq_mod]
        have hsplit : 2 ^ F.bits + lane F.width k x.value - lane F.width k y.value =
            (lane F.width k x.value - lane F.width k y.value) + 2 ^ F.bits * 1 := by omega
        rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      · rw [ite_eq_right (fun h => hle h.2), Nat.zero_mul, Nat.and_zero]
        omega
    · rw [ite_eq_right hk, ite_eq_right hk, Nat.zero_and]
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · rw [hvalue]
    have := hx.clean k
    split <;> omega
  · rw [hvalue, ite_eq_right (Nat.not_lt.mpr hk)]
  · have herr' : lane F.width k x.error ||| lane F.width k y.error = 0 := by
      rw [← lane_lor]
      exact herr
    obtain ⟨hxe, hye⟩ := Nat.or_eq_zero_iff.1 herr'
    rw [hvalue, ite_eq_left hk, hx.exact k hk hxe, hy.exact k hk hye]

/-! ## Bitwise steps and shifts by a constant -/

/-- The lanewise conjunction. -/
def land (x y : Val) : Val :=
  ⟨Nat.land x.value y.value, Nat.lor x.error y.error⟩

/-- The lanewise disjunction. -/
def lor (x y : Val) : Val :=
  ⟨Nat.lor x.value y.value, Nat.lor x.error y.error⟩

/-- The lanewise exclusive disjunction. -/
def xor (x y : Val) : Val :=
  ⟨Nat.xor x.value y.value, Nat.lor x.error y.error⟩

/-- A bitwise step of two machine values stands for the bitwise operation of the lanes. -/
theorem bitwise_holds {F : Frame} {xs ys : Nat → Nat} {x y : Val} (op : Nat → Nat → Nat)
    (row : Nat → Nat → Nat)
    (hlane : ∀ u v k, lane F.width k (row u v) = op (lane F.width k u) (lane F.width k v))
    (hlt : ∀ a b, a < 2 ^ F.bits → b < 2 ^ F.bits → op a b < 2 ^ F.bits) (hzero : op 0 0 = 0)
    (hx : Holds F xs x) (hy : Holds F ys y) :
    Holds F (fun k => op (xs k) (ys k)) ⟨row x.value y.value, Nat.lor x.error y.error⟩ := by
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · change lane F.width k (row x.value y.value) < _
    rw [hlane]
    exact hlt _ _ (hx.clean k) (hy.clean k)
  · change lane F.width k (row x.value y.value) = 0
    rw [hlane, hx.bounded k hk, hy.bounded k hk, hzero]
  · have herr' : lane F.width k x.error ||| lane F.width k y.error = 0 := by
      rw [← lane_lor]
      exact herr
    obtain ⟨hxe, hye⟩ := Nat.or_eq_zero_iff.1 herr'
    change lane F.width k (row x.value y.value) = _
    rw [hlane, hx.exact k hk hxe, hy.exact k hk hye]

/-- `land` stands for the lanewise conjunction. -/
theorem land_holds {F : Frame} {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) : Holds F (fun k => xs k &&& ys k) (land x y) :=
  bitwise_holds (· &&& ·) Nat.land (fun u v k => lane_land _ k u v)
    (fun _ _ ha _ => lt_of_le_of_lt Nat.and_le_left ha) rfl hx hy

/-- `lor` stands for the lanewise disjunction. -/
theorem lor_holds {F : Frame} {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) : Holds F (fun k => xs k ||| ys k) (lor x y) :=
  bitwise_holds (· ||| ·) Nat.lor (fun u v k => lane_lor _ k u v)
    (fun _ _ ha hb => Nat.or_lt_two_pow ha hb) rfl hx hy

/-- `xor` stands for the lanewise exclusive disjunction. -/
theorem xor_holds {F : Frame} {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) : Holds F (fun k => xs k ^^^ ys k) (xor x y) :=
  bitwise_holds (· ^^^ ·) Nat.xor (fun u v k => lane_xor _ k u v)
    (fun _ _ ha hb => Nat.xor_lt_two_pow ha hb) rfl hx hy

/-- Every lane shifted right by the constant `s`: one shift and one mask. It has no error. -/
def shrC (F : Frame) (s : Nat) (x : Val) : Val :=
  ⟨Nat.land (Nat.shiftRight x.value s) (Nat.mul F.ones (Nat.sub (pow2 (Nat.sub F.width s)) 1)),
    x.error⟩

/-- `shrC` stands for the lanewise right shift by `s`. -/
theorem shrC_holds {F : Frame} (hF : F.Valid) (s : Nat) {xs : Nat → Nat} {x : Val}
    (hx : Holds F xs x) : Holds F (fun k => xs k >>> s) (shrC F s x) := by
  have hmask : ∀ k, lane F.width k (F.ones * (2 ^ (F.width - s) - 1)) =
      if k < F.count then 2 ^ (F.width - s) - 1 else 0 := fun k =>
    hF.lane_repeat (by
      have : 2 ^ (F.width - s) ≤ 2 ^ F.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      have := Nat.two_pow_pos (F.width - s)
      omega) k
  have hvalue : ∀ k, lane F.width k (shrC F s x).value =
      if k < F.count then lane F.width k x.value >>> s else 0 := fun k => by
    change lane F.width k ((x.value >>> s) &&& (F.ones * (pow2 (F.width - s) - 1))) = _
    rw [lane_land, pow2_eq, hmask]
    split
    · rw [Nat.and_two_pow_sub_one_eq_mod]
      by_cases hs : s ≤ F.width
      · exact lane_shiftRight_mod hs k x.value
      · have hzero : F.width - s = 0 := by omega
        rw [hzero, Nat.pow_zero, Nat.mod_one, Nat.shiftRight_eq_div_pow]
        refine (Nat.div_eq_of_lt (lt_of_lt_of_le (lane_lt _ _ _) ?_)).symm
        exact Nat.pow_le_pow_right (by decide) (by omega)
    · exact Nat.and_zero _
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · rw [hvalue]
    split
    · rw [Nat.shiftRight_eq_div_pow]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (hx.clean k)
    · exact Nat.two_pow_pos _
  · rw [hvalue, ite_eq_right (Nat.not_lt.mpr hk)]
  · rw [hvalue, ite_eq_left hk, hx.exact k hk herr]

/-- The lanes that are not zero, as a flag row: one where the lane of `x` is not zero. -/
def nonzeroFlags (F : Frame) (x : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.add x F.lows) F.bits) F.ones

/-- `nonzeroFlags` is one in the lanes of a clean row that are not zero. -/
theorem lane_nonzeroFlags {F : Frame} (hF : F.Valid) {x : Nat}
    (hx : ∀ k, lane F.width k x < 2 ^ F.bits) (k : Nat) :
    lane F.width k (nonzeroFlags F x) =
      if k < F.count ∧ lane F.width k x ≠ 0 then 1 else 0 := by
  have hpos := Nat.two_pow_pos F.bits
  unfold nonzeroFlags
  rw [hF.lane_top_flag]
  have hsum : lane F.width k (x + F.lows) = lane F.width k x + lane F.width k F.lows :=
    lane_add (fun j => by
      have := hx j
      rw [hF.lane_lows, hF.pow_width]
      split <;> omega) k
  change (if k < F.count then lane F.width k (x + F.lows) / 2 ^ F.bits else 0) = _
  rw [hsum, hF.lane_lows]
  have := hx k
  by_cases hk : k < F.count
  · rw [ite_eq_left hk, ite_eq_left hk]
    by_cases hzero : lane F.width k x = 0
    · rw [ite_eq_right (fun h => h.2 hzero), hzero, Nat.zero_add]
      exact Nat.div_eq_of_lt (by omega)
    · rw [ite_eq_left ⟨hk, hzero⟩]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.1)]

/--
Every lane shifted left by the constant `s`. A lane that loses bits above its value bits is
marked in the error row.
-/
def shlC (F : Frame) (s : Nat) (x : Val) : Val :=
  (fun keep =>
    ⟨Nat.shiftLeft keep s, Nat.lor x.error (nonzeroFlags F (Nat.sub x.value keep))⟩)
    (Nat.land x.value (Nat.mul F.ones (Nat.sub (pow2 (Nat.sub F.bits s)) 1)))

/-- `shlC` stands for the lanewise left shift by `s`. -/
theorem shlC_holds {F : Frame} (hF : F.Valid) (s : Nat) {xs : Nat → Nat} {x : Val}
    (hx : Holds F xs x) : Holds F (fun k => xs k <<< s) (shlC F s x) := by
  have hpos := Nat.two_pow_pos F.bits
  have hsmall : 2 ^ (F.bits - s) ≤ 2 ^ F.bits := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hposs := Nat.two_pow_pos (F.bits - s)
  have hmask : ∀ k, lane F.width k (F.ones * (2 ^ (F.bits - s) - 1)) =
      if k < F.count then 2 ^ (F.bits - s) - 1 else 0 := fun k =>
    hF.lane_repeat (by have := hF.pow_bits_lt; omega) k
  -- The lanes of the kept low bits.
  have hkeep : ∀ k, lane F.width k (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) =
      if k < F.count then lane F.width k x.value % 2 ^ (F.bits - s) else 0 := fun k => by
    rw [lane_land, hmask]
    split
    · exact Nat.and_two_pow_sub_one_eq_mod _ _
    · exact Nat.and_zero _
  have hkeepLt : ∀ k, lane F.width k (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) <
      2 ^ (F.bits - s) := fun k => by
    rw [hkeep]
    split
    · exact Nat.mod_lt _ hposs
    · exact hposs
  -- Shifting the kept bits stays inside the value bits.
  have hshift : ∀ k, lane F.width k ((x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) <<< s) =
      lane F.width k (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) * 2 ^ s := fun k => by
    rw [Nat.shiftLeft_eq]
    refine lane_mul (2 ^ s) (fun j => ?_) k
    by_cases hs : s ≤ F.bits
    · calc _ < 2 ^ (F.bits - s) * 2 ^ s :=
              Nat.mul_lt_mul_of_pos_right (hkeepLt j) (Nat.two_pow_pos s)
        _ = 2 ^ F.bits := by rw [← Nat.pow_add]; congr 1; omega
        _ < 2 ^ F.width := hF.pow_bits_lt
    · have hzero : lane F.width j (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) = 0 := by
        have hone : 2 ^ (F.bits - s) = 1 := by rw [show F.bits - s = 0 by omega, Nat.pow_zero]
        have := hkeepLt j
        omega
      rw [hzero, Nat.zero_mul]
      exact Nat.two_pow_pos _
  have hbound : ∀ k, lane F.width k (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) * 2 ^ s <
      2 ^ F.bits := fun k => by
    by_cases hs : s ≤ F.bits
    · calc _ < 2 ^ (F.bits - s) * 2 ^ s :=
              Nat.mul_lt_mul_of_pos_right (hkeepLt k) (Nat.two_pow_pos s)
        _ = 2 ^ F.bits := by rw [← Nat.pow_add]; congr 1; omega
    · have hzero : lane F.width k (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) = 0 := by
        have hone : 2 ^ (F.bits - s) = 1 := by rw [show F.bits - s = 0 by omega, Nat.pow_zero]
        have := hkeepLt k
        omega
      rw [hzero, Nat.zero_mul]
      exact hpos
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · change lane F.width k ((x.value &&& (F.ones * (pow2 (F.bits - s) - 1))) <<< s) < _
    rw [pow2_eq, hshift]
    exact hbound k
  · change lane F.width k ((x.value &&& (F.ones * (pow2 (F.bits - s) - 1))) <<< s) = 0
    rw [pow2_eq, hshift, hkeep, ite_eq_right (Nat.not_lt.mpr hk), Nat.zero_mul]
  · -- The lost bits are zero, so the lane was below `2 ^ (bits - s)`.
    have herr' : lane F.width k x.error ||| lane F.width k (nonzeroFlags F
        (x.value - (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))))) = 0 := by
      rw [← lane_lor, ← pow2_eq]
      exact herr
    obtain ⟨hxe, hlost⟩ := Nat.or_eq_zero_iff.1 herr'
    have hdiff : ∀ j, lane F.width j (x.value - (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1)))) =
        lane F.width j x.value -
          lane F.width j (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1))) :=
      lane_sub (by have := hF.width; omega) fun j => by
        rw [lane_land]
        exact Nat.and_le_left
    rw [lane_nonzeroFlags hF (fun j => by
      rw [hdiff]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (hx.clean j))] at hlost
    have hzero : lane F.width k (x.value - (x.value &&& (F.ones * (2 ^ (F.bits - s) - 1)))) =
      0 := by
      by_contra hne
      rw [ite_eq_left ⟨hk, hne⟩] at hlost
      exact absurd hlost (by decide)
    rw [hdiff, hkeep, ite_eq_left hk] at hzero
    have hfits : lane F.width k x.value % 2 ^ (F.bits - s) = lane F.width k x.value := by
      have := Nat.mod_le (lane F.width k x.value) (2 ^ (F.bits - s))
      omega
    change lane F.width k ((x.value &&& (F.ones * (pow2 (F.bits - s) - 1))) <<< s) = xs k <<< s
    rw [pow2_eq, hshift, hkeep, ite_eq_left hk, hfits, hx.exact k hk hxe, Nat.shiftLeft_eq]

/-! ## Conditions and selection -/

/-- One in the lanes where `x` is not zero. -/
def nonzero (F : Frame) (x : Val) : Val :=
  ⟨nonzeroFlags F x.value, x.error⟩

/-- A flag row of a valid frame is clean and has no lane from `count` on. -/
theorem flags_holds {F : Frame} (hF : F.Valid) {xs : Nat → Nat} {flags error : Nat}
    {condition : Nat → Prop} [∀ k, Decidable (condition k)]
    (hlane : ∀ k, lane F.width k flags = if k < F.count ∧ condition k then 1 else 0)
    (hexact : ∀ k, k < F.count → lane F.width k error = 0 →
      xs k = if condition k then 1 else 0) :
    Holds F xs ⟨flags, error⟩ := by
  have hone : (1 : Nat) < 2 ^ F.bits := Nat.one_lt_two_pow (by
    have := hF.width
    have := hF.bits
    omega)
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · change lane F.width k flags < _
    rw [hlane]
    split <;> omega
  · change lane F.width k flags = 0
    rw [hlane, ite_eq_right (fun h => absurd h.1 (Nat.not_lt.mpr hk))]
  · change lane F.width k flags = xs k
    rw [hlane, hexact k hk herr]
    by_cases hc : condition k
    · rw [ite_eq_left ⟨hk, hc⟩, ite_eq_left hc]
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_right hc]

/-- `nonzero` stands for the lanewise test `x ≠ 0`, as zero or one. -/
theorem nonzero_holds {F : Frame} (hF : F.Valid) {xs : Nat → Nat} {x : Val} (hx : Holds F xs x) :
    Holds F (fun k => if xs k ≠ 0 then 1 else 0) (nonzero F x) :=
  flags_holds hF (condition := fun k => lane F.width k x.value ≠ 0)
    (lane_nonzeroFlags hF hx.clean) fun k hk herr => by
      rw [hx.exact k hk herr]

/-- One in the lanes where `y ≤ x`. -/
def atLeast (F : Frame) (x y : Val) : Val :=
  ⟨atLeastFlags F x.value y.value, Nat.lor x.error y.error⟩

/-- `atLeast` stands for the lanewise test `y ≤ x`, as zero or one. -/
theorem atLeast_holds {F : Frame} (hF : F.Valid) {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) :
    Holds F (fun k => if ys k ≤ xs k then 1 else 0) (atLeast F x y) :=
  flags_holds hF (condition := fun k => lane F.width k y.value ≤ lane F.width k x.value)
    (lane_atLeastFlags hF hx.clean hx.bounded hy.clean hy.bounded) fun k hk herr => by
      have herr' : lane F.width k x.error ||| lane F.width k y.error = 0 := by
        rw [← lane_lor]
        exact herr
      obtain ⟨hxe, hye⟩ := Nat.or_eq_zero_iff.1 herr'
      rw [hx.exact k hk hxe, hy.exact k hk hye]

/--
The lanes of `t` where the lane of `c` is not zero, and the lanes of `e` elsewhere. The error of
a lane is the error of its condition and of the value it selects: an error of the other value
does not reach the result.
-/
def select (F : Frame) (c t e : Val) : Val :=
  (fun flags =>
    (fun mask all =>
      ⟨Nat.lor (Nat.land t.value mask) (Nat.land e.value (Nat.sub F.lows mask)),
        Nat.lor c.error
          (Nat.lor (Nat.land t.error all) (Nat.land e.error (Nat.sub F.full all)))⟩)
      (Nat.mul flags F.low) (Nat.mul flags (Nat.sub (pow2 F.width) 1)))
    (nonzeroFlags F c.value)

/-- `select` stands for the lanewise choice between two values. -/
theorem select_holds {F : Frame} (hF : F.Valid) {cs ts es : Nat → Nat} {c t e : Val}
    (hc : Holds F cs c) (ht : Holds F ts t) (he : Holds F es e) :
    Holds F (fun k => if cs k ≠ 0 then ts k else es k) (select F c t e) := by
  have hpos := Nat.two_pow_pos F.bits
  have hposw := Nat.two_pow_pos F.width
  have hbits := hF.pow_bits_lt
  have hflags := lane_nonzeroFlags hF hc.clean
  have hflagsLe : ∀ j, lane F.width j (nonzeroFlags F c.value) ≤ 1 := fun j => by
    rw [hflags]
    split <;> omega
  -- The masks: all value bits, or all bits, of the lanes whose condition is not zero.
  have hmask : ∀ k, lane F.width k (nonzeroFlags F c.value * F.low) =
      if k < F.count ∧ lane F.width k c.value ≠ 0 then 2 ^ F.bits - 1 else 0 := fun k => by
    rw [lane_mul F.low (fun j => by
      calc _ ≤ 1 * F.low := Nat.mul_le_mul_right _ (hflagsLe j)
        _ < 2 ^ F.width := by rw [Nat.one_mul, hF.low]; omega), hflags, hF.low]
    split <;> simp
  have hall : ∀ k, lane F.width k (nonzeroFlags F c.value * (2 ^ F.width - 1)) =
      if k < F.count ∧ lane F.width k c.value ≠ 0 then 2 ^ F.width - 1 else 0 := fun k => by
    rw [lane_mul (2 ^ F.width - 1) (fun j => by
      calc _ ≤ 1 * (2 ^ F.width - 1) := Nat.mul_le_mul_right _ (hflagsLe j)
        _ < 2 ^ F.width := by omega), hflags]
    split <;> simp
  have hrest : ∀ k, lane F.width k (F.lows - nonzeroFlags F c.value * F.low) =
      if k < F.count ∧ lane F.width k c.value = 0 then 2 ^ F.bits - 1 else 0 := fun k => by
    rw [lane_sub (by have := hF.width; omega) (fun j => by
      rw [hmask, hF.lane_lows]
      by_cases hj : j < F.count
      · rw [ite_eq_left hj]
        split <;> omega
      · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.1)]), hmask, hF.lane_lows]
    by_cases hk : k < F.count
    · by_cases hz : lane F.width k c.value = 0
      · rw [ite_eq_left hk, ite_eq_right (fun h => h.2 hz), ite_eq_left ⟨hk, hz⟩, Nat.sub_zero]
      · rw [ite_eq_left hk, ite_eq_left ⟨hk, hz⟩, ite_eq_right (fun h => hz h.2), Nat.sub_self]
    · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.1), ite_eq_right (fun h => hk h.1)]
  have hrestAll : ∀ k, lane F.width k (F.full - nonzeroFlags F c.value * (2 ^ F.width - 1)) =
      if k < F.count ∧ lane F.width k c.value = 0 then 2 ^ F.width - 1 else 0 := fun k => by
    rw [lane_sub (by have := hF.width; omega) (fun j => by
      rw [hall, hF.lane_full]
      by_cases hj : j < F.count
      · rw [ite_eq_left hj]
        split <;> omega
      · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.1)]), hall, hF.lane_full]
    by_cases hk : k < F.count
    · by_cases hz : lane F.width k c.value = 0
      · rw [ite_eq_left hk, ite_eq_right (fun h => h.2 hz), ite_eq_left ⟨hk, hz⟩, Nat.sub_zero]
      · rw [ite_eq_left hk, ite_eq_left ⟨hk, hz⟩, ite_eq_right (fun h => hz h.2), Nat.sub_self]
    · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.1), ite_eq_right (fun h => hk h.1)]
  -- The lanes of the value row.
  have hvalue : ∀ k, lane F.width k (select F c t e).value =
      if k < F.count then
        if lane F.width k c.value ≠ 0 then lane F.width k t.value else lane F.width k e.value
      else 0 := fun k => by
    change lane F.width k ((t.value &&& (nonzeroFlags F c.value * F.low)) |||
      (e.value &&& (F.lows - nonzeroFlags F c.value * F.low))) = _
    rw [lane_lor, lane_land, lane_land, hmask, hrest]
    have htk := ht.clean k
    have hek := he.clean k
    by_cases hk : k < F.count
    · rw [ite_eq_left hk]
      by_cases hz : lane F.width k c.value = 0
      · rw [ite_eq_right (fun h => h.2 hz), ite_eq_left ⟨hk, hz⟩, ite_eq_right (fun h => h hz),
          Nat.and_zero, Nat.zero_or, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hek]
      · rw [ite_eq_left ⟨hk, hz⟩, ite_eq_right (fun h => hz h.2), ite_eq_left hz,
          Nat.and_zero, Nat.or_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt htk]
    · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.1), ite_eq_right (fun h => hk h.1),
        Nat.and_zero, Nat.and_zero]
      rfl
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk herr => ?_⟩
  · rw [hvalue]
    have := ht.clean k
    have := he.clean k
    split
    · split <;> assumption
    · exact hpos
  · rw [hvalue, ite_eq_right (Nat.not_lt.mpr hk)]
  · have herr' : lane F.width k c.error |||
        ((lane F.width k t.error &&& lane F.width k (nonzeroFlags F c.value * (2 ^ F.width - 1)))
          |||
          (lane F.width k e.error &&&
            lane F.width k (F.full - nonzeroFlags F c.value * (2 ^ F.width - 1)))) = 0 := by
      rw [← lane_land, ← lane_land, ← lane_lor, ← lane_lor, ← pow2_eq]
      exact herr
    obtain ⟨hce, hbranch⟩ := Nat.or_eq_zero_iff.1 herr'
    obtain ⟨hte, hee⟩ := Nat.or_eq_zero_iff.1 hbranch
    rw [hall] at hte
    rw [hrestAll] at hee
    have hcs := hc.exact k hk hce
    rw [hvalue, ite_eq_left hk]
    change (if lane F.width k c.value ≠ 0 then lane F.width k t.value else lane F.width k e.value) =
      if cs k ≠ 0 then ts k else es k
    rw [hcs]
    by_cases hz : cs k = 0
    · rw [ite_eq_right (fun h => h hz), ite_eq_right (fun h => h hz)]
      rw [ite_eq_left ⟨hk, hcs.trans hz⟩, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (lane_lt _ _ _)] at hee
      exact he.exact k hk hee
    · rw [ite_eq_left hz, ite_eq_left hz]
      rw [ite_eq_left ⟨hk, fun h => hz (hcs.symm.trans h)⟩, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (lane_lt _ _ _)] at hte
      exact ht.exact k hk hte

/-! ## Shifts by a lane-dependent count, and products -/

/-- `Holds` only depends on the numbers lane by lane. -/
theorem Holds.congr {F : Frame} {xs ys : Nat → Nat} {p : Val} (h : Holds F xs p)
    (heq : ∀ k, xs k = ys k) : Holds F ys p :=
  ⟨h.clean, h.bounded, fun k hk herr => (h.exact k hk herr).trans (heq k)⟩

/-- Bit `j` of every lane, as zero or one. -/
def bitAt (F : Frame) (j : Nat) (s : Val) : Val :=
  land (shrC F j s) (const F 1)

/-- `bitAt` stands for bit `j` of each lane. -/
theorem bitAt_holds {F : Frame} (hF : F.Valid) (j : Nat) {ss : Nat → Nat} {s : Val}
    (hs : Holds F ss s) : Holds F (fun k => (ss k >>> j) &&& 1) (bitAt F j s) :=
  land_holds (shrC_holds hF j hs) (const_holds hF 1)

/-- A count splits into its bit `j` and the bits below. -/
theorem mod_two_pow_succ' (s j : Nat) :
    s % 2 ^ (j + 1) = ((s >>> j) &&& 1) * 2 ^ j + s % 2 ^ j := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.mod_pow_succ, Nat.mul_comm,
    Nat.add_comm]

/-- A count below `2 ^ depth` is its remainder, and the test `count >>> depth ≠ 0` says so. -/
theorem mod_of_shiftRight_eq_zero {s depth : Nat} (h : s >>> depth = 0) : s % 2 ^ depth = s := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact Nat.mod_eq_of_lt ((Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 h)

/--
Shift by the low `j` bits of the count in the same lane of `s`: one conditional shift by a
constant, `step (2 ^ i)`, per bit `i < j` of the count.
-/
def shiftLoop (F : Frame) (step : Nat → Val → Val) : Nat → Val → Val → Val
  | 0, x, _ => x
  | j + 1, x, s => shiftLoop F step j (select F (bitAt F j s) (step (pow2 j) x) x) s

/--
`shiftLoop` applies `op` to each lane and its count modulo `2 ^ j`, for a constant step that
stands for `op` and an `op` that composes by adding counts (a left or a right shift).
-/
theorem shiftLoop_holds {F : Frame} (hF : F.Valid) {step : Nat → Val → Val}
    {op : Nat → Nat → Nat}
    (hstep : ∀ (c : Nat) {xs : Nat → Nat} {x : Val}, Holds F xs x →
      Holds F (fun k => op (xs k) c) (step c x))
    (hzero : ∀ v, op v 0 = v) (hadd : ∀ v a b, op (op v a) b = op v (a + b)) (j : Nat) :
    ∀ {xs ss : Nat → Nat} {x s : Val}, Holds F xs x → Holds F ss s →
      Holds F (fun k => op (xs k) (ss k % 2 ^ j)) (shiftLoop F step j x s) := by
  induction j with
  | zero =>
      intro xs ss x s hx _
      exact hx.congr fun k => by rw [Nat.pow_zero, Nat.mod_one, hzero]
  | succ j ih =>
      intro xs ss x s hx hs
      have hselect := select_holds hF (bitAt_holds hF j hs) (hstep (pow2 j) hx) hx
      refine (ih hselect hs).congr fun k => ?_
      rw [mod_two_pow_succ', pow2_eq]
      have hbit : (ss k >>> j) &&& 1 = 0 ∨ (ss k >>> j) &&& 1 = 1 := by
        have := Nat.and_le_right (n := ss k >>> j) (m := 1)
        omega
      rcases hbit with h | h
      · rw [h, ite_eq_right (fun hne => hne rfl), Nat.zero_mul, Nat.zero_add]
      · rw [h, ite_eq_left (by decide), Nat.one_mul, hadd, Nat.add_comm]

/--
Every lane shifted by the count in the same lane of `s`, with the constant shift `step`. A lane
whose count is `2 ^ depth` or more is marked in the error row.
-/
def shiftBy (F : Frame) (step : Nat → Val → Val) (x s : Val) : Val :=
  select F (shrC F F.depth s) (poison F) (shiftLoop F step F.depth x s)

/-- `shiftBy` stands for `op` of each lane and its count, under the premises of `shiftLoop`. -/
theorem shiftBy_holds {F : Frame} (hF : F.Valid) {step : Nat → Val → Val}
    {op : Nat → Nat → Nat}
    (hstep : ∀ (c : Nat) {xs : Nat → Nat} {x : Val}, Holds F xs x →
      Holds F (fun k => op (xs k) c) (step c x))
    (hzero : ∀ v, op v 0 = v) (hadd : ∀ v a b, op (op v a) b = op v (a + b))
    {xs ss : Nat → Nat} {x s : Val} (hx : Holds F xs x) (hs : Holds F ss s) :
    Holds F (fun k => op (xs k) (ss k)) (shiftBy F step x s) :=
  (select_holds hF (shrC_holds hF F.depth hs) (poison_holds hF fun k => op (xs k) (ss k))
    (shiftLoop_holds hF hstep hzero hadd F.depth hx hs)).congr fun k => by
      by_cases hbig : ss k >>> F.depth = 0
      · rw [ite_eq_right (fun h => h hbig), mod_of_shiftRight_eq_zero hbig]
      · rw [ite_eq_left hbig]

/--
Every lane shifted right by the count in the same lane of `s`. A lane whose count is `2 ^ depth`
or more is marked in the error row.
-/
def shiftRight (F : Frame) (x s : Val) : Val :=
  shiftBy F (shrC F) x s

/-- `shiftRight` stands for the lanewise right shift. -/
theorem shiftRight_holds {F : Frame} (hF : F.Valid) {xs ss : Nat → Nat} {x s : Val}
    (hx : Holds F xs x) (hs : Holds F ss s) :
    Holds F (fun k => xs k >>> ss k) (shiftRight F x s) :=
  shiftBy_holds hF (op := fun v c => v >>> c) (fun c _ _ h => shrC_holds hF c h) (fun _ => rfl)
    (fun v a b => (Nat.shiftRight_add v a b).symm) hx hs

/--
Every lane shifted left by the count in the same lane of `s`. A lane that loses bits, or whose
count is `2 ^ depth` or more, is marked in the error row.
-/
def shiftLeft (F : Frame) (x s : Val) : Val :=
  shiftBy F (shlC F) x s

/-- `shiftLeft` stands for the lanewise left shift. -/
theorem shiftLeft_holds {F : Frame} (hF : F.Valid) {xs ss : Nat → Nat} {x s : Val}
    (hx : Holds F xs x) (hs : Holds F ss s) :
    Holds F (fun k => xs k <<< ss k) (shiftLeft F x s) :=
  shiftBy_holds hF (op := fun v c => v <<< c) (fun c _ _ h => shlC_holds hF c h) (fun _ => rfl)
    (fun v a b => (Nat.shiftLeft_add v a b).symm) hx hs

/-- The product with the low `j` bits of `y`: one conditional shifted copy of `x` per bit. -/
def mulLoop (F : Frame) (x y : Val) : Nat → Val
  | 0 => const F 0
  | j + 1 => add F (mulLoop F x y j) (select F (bitAt F j y) (shlC F j x) (const F 0))

/-- `mulLoop` multiplies each lane of `x` by the low `j` bits of the lane of `y`. -/
theorem mulLoop_holds {F : Frame} (hF : F.Valid) {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) (j : Nat) :
    Holds F (fun k => xs k * (ys k % 2 ^ j)) (mulLoop F x y j) := by
  induction j with
  | zero => exact (const_holds hF 0).congr fun k => by simp [Nat.mod_one]
  | succ j ih =>
      have hterm := select_holds hF (bitAt_holds hF j hy) (shlC_holds hF j hx) (const_holds hF 0)
      refine (add_holds hF ih hterm).congr fun k => ?_
      rw [mod_two_pow_succ']
      have hbit : (ys k >>> j) &&& 1 = 0 ∨ (ys k >>> j) &&& 1 = 1 := by
        have := Nat.and_le_right (n := ys k >>> j) (m := 1)
        omega
      rcases hbit with h | h
      · rw [h, ite_eq_right (fun hne => hne rfl), Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      · rw [h, ite_eq_left (by decide), Nat.one_mul, Nat.shiftLeft_eq, Nat.mul_add,
          Nat.add_comm]

/--
The lanewise product of two rows, for factors `y` below `2 ^ bound`. A lane whose product does
not fit, or whose second factor has more than `bound` bits, is marked in the error row.
-/
def mul (F : Frame) (bound : Nat) (x y : Val) : Val :=
  select F (shrC F bound y) (poison F) (mulLoop F x y bound)

/-- `mul` stands for the lanewise product. -/
theorem mul_holds {F : Frame} (hF : F.Valid) (bound : Nat) {xs ys : Nat → Nat} {x y : Val}
    (hx : Holds F xs x) (hy : Holds F ys y) :
    Holds F (fun k => xs k * ys k) (mul F bound x y) :=
  (select_holds hF (shrC_holds hF bound hy) (poison_holds hF fun k => xs k * ys k)
    (mulLoop_holds hF hx hy bound)).congr fun k => by
      by_cases hbig : ys k >>> bound = 0
      · rw [ite_eq_right (fun h => h hbig), mod_of_shiftRight_eq_zero hbig]
      · rw [ite_eq_left hbig]

end FloatLib.Numerics.Packed.Machine
