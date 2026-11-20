/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelRefl
public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath.Scan
public import FloatLib.Numerics.Kernel.Bisection
public import FloatLib.Numerics.Kernel.Bits
import Mathlib.Tactic.Linarith.Frontend

/-!
# Element rounding of OCP MX 1.0 for Lean's kernel

`Standard.KernelPath.Scan` states nearest-even element rounding on natural numbers: the word is
the code of the least packed entry `key * 2 ^ width + code` over the finite codes, and `scan`
finds it with one step per code. This module finds the same entry in a few steps and registers
the result for `float_decide`.

* `nearest` is for the five sign-magnitude profiles, whose magnitudes grow with the magnitude
  field. A bisection (`Numerics.Kernel.bisect`, seven steps for an eight-bit profile) finds the
    largest finite
  field whose magnitude is at most the input, and the result is the least of three entries: the
  code of that field with the sign of the input, the code of the next field when it is finite,
  and the zero of the other sign.
* `int8Nearest` is for INT8, whose codes are a two's-complement grid with one zero. The
  bisection runs over the magnitudes of the sign of the input, with the zero counted for both
  signs, and the result is the least of two entries.
* `nearestAll` is `nearest` and `int8Nearest` with the constants of each profile in place: the
  form that the kernel evaluates.
* `nearestGuessed` and `int8NearestGuessed` take a guess of the field that the bisection finds
  (`fieldGuess`: the quotient of the input, read as an exponent and a fraction; `int8Guess`:
  the quotient itself) and confirm it with two tests, so that the bisection runs only when the
  guess is wrong (`nearestGuessed_eq`, `int8NearestGuessed_eq`, from
  `Numerics.Kernel.guarded_eq`). `nearestFast` is their flat form.

What is proved, for all six profiles and every input:

* `layoutCheck_eq`, `finite_of_lt`: in a sign-magnitude profile the sign bit, the magnitude and
  the finiteness of a code are those of its two fields, the finite magnitude fields are an
  initial segment, and their magnitudes increase. One kernel evaluation per profile checks it.
* `Numerics.Kernel.bisect_spec`: the bisection returns the largest number at which a downward
    closed test holds.
* `scan_eq_nearest`: for a sign-magnitude profile the scan of all codes is `nearest`. Every
  other code of the sign of the input is farther from the input than one of the two fields that
  the bisection brackets it with, and every other code of the other sign is farther than the
  zero.
* `scan_eq_int8Nearest`: for INT8 the scan of all codes is `int8Nearest`, by the same bracket
  on magnitudes (`int8Code_spec`, `int8_cases`).
* `quantizeFinite_eq_round`: `quantizeFinite profile input` is the word of `roundCode profile
  input`, which is `nearestAll` at the numerator, the denominator and the sign bit of the
  input. It is tagged `@[kernel_optimize]`, and `Element.quantize` is tagged to be unfolded, so
  `float_decide` evaluates an element conversion by bisection.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.3 and 6.3.

-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/-! ## The layout of a sign-magnitude profile -/

/-- The value of the sign bit of a profile: `2 ^ (width - 1)`. -/
def signValue (profile : Profile) : Nat :=
  Nat.pow 2 (Nat.sub profile.width 1)

/--
What the bisection uses of a sign-magnitude profile, as one check over its codes: the sign bit
of a code is its quotient by the sign value, and its magnitude and finiteness are those of its
remainder; a finite magnitude field has a finite field with a smaller magnitude just below it;
and code zero is finite with magnitude zero.
-/
def layoutCheck (profile : Profile) : Bool :=
  ((List.range (2 ^ profile.width)).all fun c =>
    signBit profile c == c / signValue profile &&
      magnitude profile c == magnitude profile (c % signValue profile) &&
      finiteCode profile c == finiteCode profile (c % signValue profile)) &&
  ((List.range (signValue profile - 1)).all fun j =>
    !finiteCode profile (j + 1) ||
      (finiteCode profile j && decide (magnitude profile j < magnitude profile (j + 1)))) &&
  (finiteCode profile 0 && magnitude profile 0 == 0)

/-- Every sign-magnitude profile passes the layout check. -/
theorem layoutCheck_eq (profile : Profile) (h : twosComplement profile = false) :
    layoutCheck profile = true := by
  cases profile <;> first | decide +kernel | cases h

/-- The facts of the layout check. -/
theorem layout (profile : Profile) (h : twosComplement profile = false) :
    (∀ c, c < 2 ^ profile.width →
      signBit profile c = c / signValue profile ∧
        magnitude profile c = magnitude profile (c % signValue profile) ∧
        finiteCode profile c = finiteCode profile (c % signValue profile)) ∧
    (∀ j, j < signValue profile - 1 → finiteCode profile (j + 1) = true →
      finiteCode profile j = true ∧ magnitude profile j < magnitude profile (j + 1)) ∧
    finiteCode profile 0 = true ∧ magnitude profile 0 = 0 := by
  have hcheck := layoutCheck_eq profile h
  simp only [layoutCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcheck
  obtain ⟨⟨hcodes, hsteps⟩, hzero⟩ := hcheck
  refine ⟨fun c hc => ?_, fun j hj hfinite => ?_, hzero⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hcodes c hc
    exact ⟨h1, h2, h3⟩
  · rcases hsteps j hj with hnot | hboth
    · rw [hnot] at hfinite; cases hfinite
    · exact hboth

/-- The sign value is positive. -/
theorem signValue_pos (profile : Profile) : 0 < signValue profile :=
  Nat.pow_pos (by decide)

/-- A profile has twice as many codes as its sign value. -/
theorem two_mul_signValue (profile : Profile) : 2 ^ profile.width = 2 * signValue profile := by
  cases profile <;> rfl

/-- Under a finite magnitude field, every field is finite and has a smaller magnitude. -/
theorem finite_of_lt (profile : Profile) (h : twosComplement profile = false) :
    ∀ j, j < signValue profile → finiteCode profile j = true → ∀ i, i < j →
      finiteCode profile i = true ∧ magnitude profile i < magnitude profile j
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | j + 1, hj, hfinite, i, hi => by
      obtain ⟨hstep, hlt⟩ := (layout profile h).2.1 j (by omega) hfinite
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt' | rfl
      · obtain ⟨hfi, hmi⟩ := finite_of_lt profile h j (by omega) hstep i hlt'
        exact ⟨hfi, Nat.lt_trans hmi hlt⟩
      · exact ⟨hstep, hlt⟩

/-- The code with sign bit `s` and magnitude field `j`. -/
theorem code_layout (profile : Profile) (h : twosComplement profile = false) {s j : Nat}
    (hs : s ≤ 1) (hj : j < signValue profile) :
    s * signValue profile + j < 2 ^ profile.width ∧
      signBit profile (s * signValue profile + j) = s ∧
      magnitude profile (s * signValue profile + j) = magnitude profile j ∧
      finiteCode profile (s * signValue profile + j) = finiteCode profile j := by
  have hpos := signValue_pos profile
  have hlt : s * signValue profile + j < 2 ^ profile.width := by
    rw [two_mul_signValue]
    have : s * signValue profile ≤ 1 * signValue profile := Nat.mul_le_mul_right _ hs
    omega
  have hdiv : (s * signValue profile + j) / signValue profile = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (s * signValue profile + j) % signValue profile = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  obtain ⟨h1, h2, h3⟩ := (layout profile h).1 _ hlt
  rw [hdiv] at h1
  rw [hmod] at h2 h3
  exact ⟨hlt, h1, h2, h3⟩

/-- The distance of a code whose sign is the sign of the input. -/
theorem distance_same (profile : Profile) (sp ap q code : Nat) (hsign : signBit profile code = sp) :
    distance profile sp ap q code =
      magnitude profile code * q - ap * denominator profile +
        (ap * denominator profile - magnitude profile code * q) := by
  unfold distance
  rw [hsign, show Nat.beq sp sp = true from Nat.beq_refl sp]
  rfl

/-- The distance of a code whose sign is not the sign of the input. -/
theorem distance_other (profile : Profile) (sp ap q code : Nat) (hsign : signBit profile code ≠
    sp) :
    distance profile sp ap q code =
      magnitude profile code * q + ap * denominator profile := by
  unfold distance
  have hbeq : Nat.beq (signBit profile code) sp = false := by
    cases hb : Nat.beq (signBit profile code) sp
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hsign
  rw [hbeq]
  rfl

/-- A code at a smaller distance has a smaller packed entry. -/
theorem packed_lt_of_distance_lt (profile : Profile) (sp ap q : Nat) {neg a b : Nat}
    (hneg : neg ≤ 1) (ha : a < 2 ^ profile.width)
    (hd : distance profile sp ap q a < distance profile sp ap q b) :
    packed profile sp neg ap q a < packed profile sp neg ap q b := by
  have hta := tie_lt profile hneg a
  change codeKey profile sp neg ap q a * 2 ^ profile.width + a <
    codeKey profile sp neg ap q b * 2 ^ profile.width + b
  have hkey : codeKey profile sp neg ap q a + 1 ≤ codeKey profile sp neg ap q b := by
    change 4 * distance profile sp ap q a + tie profile neg a + 1 ≤
      4 * distance profile sp ap q b + tie profile neg b
    omega
  have := Nat.mul_le_mul_right (2 ^ profile.width) hkey
  rw [Nat.succ_mul] at this
  omega

/-! ## The nearest code by bisection -/

/-- Whether the magnitude field `j` is finite and its magnitude times `q` is at most `apD`. -/
def below (profile : Profile) (apD q j : Nat) : Bool :=
  Bool.casesOn (motive := fun _ => Bool) (Nat.blt j (signValue profile)) false
    (Bool.casesOn (motive := fun _ => Bool) (finiteCode profile j) false
      (Nat.ble (Nat.mul (magnitude profile j) q) apD))

/-- `below` as a proposition. -/
theorem below_iff (profile : Profile) (apD q j : Nat) :
    below profile apD q j = true ↔
      j < signValue profile ∧ finiteCode profile j = true ∧ magnitude profile j * q ≤ apD := by
  unfold below
  cases hrange : Nat.blt j (signValue profile)
  · refine ⟨fun hfalse => Bool.noConfusion hfalse, fun hall => ?_⟩
    have hblt : Nat.blt j (signValue profile) = true := by
      rw [Nat.blt_eq]
      exact hall.1
    rw [hrange] at hblt
    exact Bool.noConfusion hblt
  · have hlt : j < signValue profile := by
      rw [← Nat.blt_eq]
      exact hrange
    cases finiteCode profile j
    · exact ⟨fun hfalse => Bool.noConfusion hfalse, fun hall => Bool.noConfusion hall.2.1⟩
    · exact ⟨fun hle => ⟨hlt, rfl, Nat.le_of_ble_eq_true hle⟩,
        fun hall => Nat.ble_eq_true_of_le hall.2.2⟩

/-- The packed entry of a code, written with the kernel's operations. -/
def entry (profile : Profile) (sp neg ap q code : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (codeKey profile sp neg ap q code) profile.width) code

/-- `entry` is `packed`. -/
theorem entry_eq (profile : Profile) (sp neg ap q code : Nat) :
    entry profile sp neg ap q code = packed profile sp neg ap q code := by
  change codeKey profile sp neg ap q code <<< profile.width + code = _
  rw [Nat.shiftLeft_eq]
  rfl

/-- The smaller of two numbers, by one comparison. -/
def least (a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble a b) b a

/-- `least a b` is at most `a`. -/
theorem least_le_left (a b : Nat) : least a b ≤ a := by
  unfold least
  cases h : Nat.ble a b
  · refine Nat.le_of_lt (Nat.lt_of_not_le fun hle => ?_)
    rw [Nat.ble_eq_true_of_le hle] at h
    cases h
  · exact Nat.le_refl a

/-- `least a b` is at most `b`. -/
theorem least_le_right (a b : Nat) : least a b ≤ b := by
  unfold least
  cases h : Nat.ble a b
  · exact Nat.le_refl b
  · exact Nat.le_of_ble_eq_true h

/-- `least a b` is `a` or `b`. -/
theorem least_eq (a b : Nat) : least a b = a ∨ least a b = b := by
  unfold least
  cases Nat.ble a b
  · exact Or.inr rfl
  · exact Or.inl rfl

/--
The skeleton of `nearest`: a bisection with the test `below` finds a magnitude field `j`, and the
result is the least of the entries of the code with sign `sp` and field `j`, of the zero of the
other sign, and of the code with sign `sp` and field `j + 1` when that field is below `half` and
`finite`.
-/
def nearestWith (below finite : Nat → Bool) (entry : Nat → Nat) (half bits sp : Nat) : Nat :=
  (fun j =>
    (fun first =>
      Bool.casesOn (motive := fun _ => Nat)
        (Bool.casesOn (motive := fun _ => Bool) (Nat.blt (Nat.succ j) half) false
          (finite (Nat.succ j)))
        first
        (least first (entry (Nat.add (Nat.mul sp half) (Nat.succ j)))))
      (least (entry (Nat.add (Nat.mul sp half) j)) (entry (Nat.mul (Nat.sub 1 sp) half))))
    (Numerics.Kernel.bisect below bits 0)

/--
The least packed entry over the finite codes of a sign-magnitude profile, for the input `± ap / q`
(negative when `sp = 1`) with sign bit `neg`: a bisection finds the largest finite magnitude field
whose magnitude is at most the input, and the result is the least entry among the code of that
field with the sign of the input, the code of the next field when it is finite, and the zero of
the other sign (`scan_eq_nearest`).
-/
def nearest (profile : Profile) (sp neg ap q : Nat) : Nat :=
  nearestWith (below profile (Nat.mul ap (denominator profile)) q) (finiteCode profile)
    (entry profile sp neg ap q) (signValue profile) (Nat.sub profile.width 1) sp

/-- The test of the bisection is downward closed. -/
theorem below_down (profile : Profile) (h : twosComplement profile = false) (apD q : Nat) :
    ∀ i j, i ≤ j → below profile apD q j = true → below profile apD q i = true := by
  intro i j hij hbj
  rw [below_iff] at hbj ⊢
  obtain ⟨hj, hfj, hmj⟩ := hbj
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · obtain ⟨hfi, hmi⟩ := finite_of_lt profile h j hj hfj i hlt
    exact ⟨Nat.lt_trans hlt hj, hfi,
      Nat.le_trans (Nat.mul_le_mul_right q (Nat.le_of_lt hmi)) hmj⟩
  · exact ⟨hj, hfj, hmj⟩

/-- The test of the bisection holds at the magnitude field zero. -/
theorem below_zero (profile : Profile) (h : twosComplement profile = false) (apD q : Nat) :
    below profile apD q 0 = true := by
  obtain ⟨-, -, hfinite0, hmag0⟩ := layout profile h
  rw [below_iff]
  exact ⟨signValue_pos profile, hfinite0, by rw [hmag0, Nat.zero_mul]; exact Nat.zero_le _⟩

/-- The test of the bisection fails beyond the magnitude fields. -/
theorem below_up (profile : Profile) (apD q : Nat) :
    ∀ j, 0 + 2 ^ (profile.width - 1) ≤ j → below profile apD q j = false := by
  intro j hj
  cases hb : below profile apD q j
  · rfl
  · rw [below_iff] at hb
    have hlt : j < 2 ^ (profile.width - 1) := hb.1
    omega

/--
The skeleton of `nearest` at the magnitude field `j`: the least of the entries of the code with
sign `sp` and field `j`, of the zero of the other sign, and of the code with sign `sp` and field
`j + 1` when that field is below `half` and `finite`.
-/
def nearestAt (finite : Nat → Bool) (entry : Nat → Nat) (half sp j : Nat) : Nat :=
  (fun first =>
    Bool.casesOn (motive := fun _ => Nat)
      (Bool.casesOn (motive := fun _ => Bool) (Nat.blt (Nat.succ j) half) false
        (finite (Nat.succ j)))
      first
      (least first (entry (Nat.add (Nat.mul sp half) (Nat.succ j)))))
    (least (entry (Nat.add (Nat.mul sp half) j)) (entry (Nat.mul (Nat.sub 1 sp) half)))

/--
A guess of the largest finite magnitude field whose magnitude times `q` is at most `apD`, from
the quotient `t = apD / q`: the field whose exponent is the bit length of `t` above the fraction
bits and whose fraction is the leading bits of `t`, at most the largest finite field. The guess
does not have to be right: `nearestGuessed` confirms it with two tests.
-/
def fieldGuess (profile : Profile) (apD q : Nat) : Nat :=
  (fun t f =>
    (fun s =>
      Numerics.Kernel.minNat (Nat.add (Nat.shiftLeft s f) (Nat.shiftRight t s))
        (Numerics.Kernel.minNat (Nat.sub (signValue profile) 1)
          (Nat.sub (Nat.shiftLeft (nonFiniteMask profile) (nonFiniteShift profile)) 1)))
      (Nat.sub (Nat.sub (Numerics.Kernel.size t) f) 1))
    (Nat.div apD q) (fractionBits profile)

/--
`nearest` without the bisection when the guess of `fieldGuess` is the field that the bisection
finds, which two tests confirm, and `other` when it is not (`nearestGuessed_eq`).
-/
def nearestGuessed (profile : Profile) (sp neg ap q other : Nat) : Nat :=
  Numerics.Kernel.guarded (below profile (Nat.mul ap (denominator profile)) q)
    (fieldGuess profile (Nat.mul ap (denominator profile)) q)
    (nearestAt (finiteCode profile) (entry profile sp neg ap q) (signValue profile) sp) other

/-- With `nearest` as the alternative, the guessed form is `nearest`, for every sign-magnitude
profile and every input. -/
theorem nearestGuessed_eq (profile : Profile) (h : twosComplement profile = false)
    (sp neg ap q : Nat) :
    nearestGuessed profile sp neg ap q (nearest profile sp neg ap q) =
      nearest profile sp neg ap q :=
  Numerics.Kernel.guarded_eq _ (below_down profile h _ q) (profile.width - 1)
    (below_zero profile h _ q) (below_up profile _ q) _
    (nearestAt (finiteCode profile) (entry profile sp neg ap q) (signValue profile) sp)

/-- The scan of all codes of a sign-magnitude profile is the entry that the bisection finds. -/
theorem scan_eq_nearest (profile : Profile) (h : twosComplement profile = false)
    (sp neg ap q : Nat) (hsp : sp ≤ 1) (hneg : neg ≤ 1) (hq : 0 < q) :
    scan profile sp neg ap q (2 ^ profile.width) = some (nearest profile sp neg ap q) := by
  have hpos := signValue_pos profile
  obtain ⟨hlayout, -, hfinite0, hmag0⟩ := layout profile h
  -- the bisection
  have hdown := below_down profile h (ap * denominator profile) q
  have hzero := below_zero profile h (ap * denominator profile) q
  have hup := below_up profile (ap * denominator profile) q
  obtain ⟨hstar, hmax⟩ := Numerics.Kernel.bisect_spec _ hdown (profile.width - 1) 0 hzero hup
  have hnearest : nearest profile sp neg ap q =
      (fun j =>
        Bool.casesOn (motive := fun _ => Nat)
          (Bool.and (Nat.blt (j + 1) (signValue profile)) (finiteCode profile (j + 1)))
          (least (packed profile sp neg ap q (sp * signValue profile + j))
            (packed profile sp neg ap q ((1 - sp) * signValue profile)))
          (least
            (least (packed profile sp neg ap q (sp * signValue profile + j))
              (packed profile sp neg ap q ((1 - sp) * signValue profile)))
            (packed profile sp neg ap q (sp * signValue profile + (j + 1)))))
        (Numerics.Kernel.bisect (below profile (ap * denominator profile) q) (profile.width - 1)
          0) := by
    unfold nearest nearestWith
    simp only [entry_eq]
    rfl
  rw [hnearest]
  generalize Numerics.Kernel.bisect (below profile (ap * denominator profile) q) (profile.width
    - 1) 0 = j
    at hstar hmax
  dsimp only
  rw [below_iff] at hstar
  obtain ⟨hjS, hfj, hmj⟩ := hstar
  -- the candidates
  obtain ⟨hc1, hs1, hm1, hf1⟩ := code_layout profile h hsp hjS
  obtain ⟨hc0, hs0, hm0, hf0⟩ := code_layout profile h (s := 1 - sp) (Nat.sub_le 1 sp) hpos
  rw [Nat.add_zero] at hc0 hs0 hm0 hf0
  generalize htest :
    Bool.and (Nat.blt (j + 1) (signValue profile)) (finiteCode profile (j + 1)) = test
  generalize hN : (Bool.casesOn (motive := fun _ => Nat) test
      (least (packed profile sp neg ap q (sp * signValue profile + j))
        (packed profile sp neg ap q ((1 - sp) * signValue profile)))
      (least
        (least (packed profile sp neg ap q (sp * signValue profile + j))
          (packed profile sp neg ap q ((1 - sp) * signValue profile)))
        (packed profile sp neg ap q (sp * signValue profile + (j + 1)))) : Nat) = N
  have hle1 : N ≤ packed profile sp neg ap q (sp * signValue profile + j) := by
    rw [← hN]
    cases test
    · exact least_le_left _ _
    · exact Nat.le_trans (least_le_left _ _) (least_le_left _ _)
  have hle0 : N ≤ packed profile sp neg ap q ((1 - sp) * signValue profile) := by
    rw [← hN]
    cases test
    · exact least_le_right _ _
    · exact Nat.le_trans (least_le_left _ _) (least_le_right _ _)
  have hle2 : test = true →
      N ≤ packed profile sp neg ap q (sp * signValue profile + (j + 1)) := by
    intro ht
    rw [← hN, ht]
    exact least_le_right _ _
  have hnext : test = true → j + 1 < signValue profile ∧ finiteCode profile (j + 1) = true := by
    intro ht
    rw [ht, Bool.and_eq_true, Nat.blt_eq] at htest
    exact htest
  have hmem : N = packed profile sp neg ap q (sp * signValue profile + j) ∨
      N = packed profile sp neg ap q ((1 - sp) * signValue profile) ∨
      (test = true ∧ N = packed profile sp neg ap q (sp * signValue profile + (j + 1))) := by
    rw [← hN]
    cases test
    · rcases least_eq (packed profile sp neg ap q (sp * signValue profile + j))
        (packed profile sp neg ap q ((1 - sp) * signValue profile)) with h1 | h0
      · exact Or.inl h1
      · exact Or.inr (Or.inl h0)
    · rcases least_eq
        (least (packed profile sp neg ap q (sp * signValue profile + j))
          (packed profile sp neg ap q ((1 - sp) * signValue profile)))
        (packed profile sp neg ap q (sp * signValue profile + (j + 1))) with hfirst | h2
      · rcases least_eq (packed profile sp neg ap q (sp * signValue profile + j))
          (packed profile sp neg ap q ((1 - sp) * signValue profile)) with h1 | h0
        · exact Or.inl (hfirst.trans h1)
        · exact Or.inr (Or.inl (hfirst.trans h0))
      · exact Or.inr (Or.inr ⟨rfl, h2⟩)
  subst hN
  apply scan_eq_some
  · -- the result is the entry of a finite code
    rcases hmem with h1 | h0 | ⟨ht, h2⟩
    · exact ⟨_, hc1, hf1.trans hfj, h1⟩
    · exact ⟨_, hc0, hf0.trans hfinite0, h0⟩
    · obtain ⟨hlt, hfin⟩ := hnext ht
      obtain ⟨hc2, -, -, hf2⟩ := code_layout profile h hsp hlt
      exact ⟨_, hc2, hf2.trans hfin, h2⟩
  · -- and no finite code has a smaller entry
    intro c hc hfc
    obtain ⟨hsc, hmc, hfcm⟩ := hlayout c hc
    have hi : c % signValue profile < signValue profile := Nat.mod_lt _ hpos
    have hs : c / signValue profile ≤ 1 := by
      rw [two_mul_signValue] at hc
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).2 hc)
    have hform : c = c / signValue profile * signValue profile + c % signValue profile := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod c (signValue profile)).symm
    rw [hfcm] at hfc
    generalize c / signValue profile = s at hsc hs hform
    generalize c % signValue profile = i at hmc hi hform hfc
    by_cases hsign : s = sp
    · -- a code with the sign of the input
      subst hsign
      rcases Nat.lt_trichotomy i j with hlt | heq | hgt
      · obtain ⟨-, hmlt⟩ := finite_of_lt profile h j hjS hfj i hlt
        have hprod := Nat.mul_lt_mul_of_pos_right hmlt hq
        refine Nat.le_trans hle1 (Nat.le_of_lt
          (packed_lt_of_distance_lt profile s ap q hneg hc1 ?_))
        rw [distance_same _ _ _ _ _ hs1, distance_same _ _ _ _ _ hsc, hm1, hmc]
        generalize magnitude profile i * q = x at hprod
        generalize magnitude profile j * q = y at hprod hmj
        omega
      · subst heq
        rw [hform]
        exact hle1
      · have hlt1 : j + 1 < signValue profile := by omega
        have hfin1 : finiteCode profile (j + 1) = true := by
          rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hgt) with hlt' | heq'
          · exact (finite_of_lt profile h i hi hfc (j + 1) hlt').1
          · rw [show j + 1 = i from heq']; exact hfc
        have ht : test = true := by
          rw [← htest, Bool.and_eq_true, Nat.blt_eq]
          exact ⟨hlt1, hfin1⟩
        rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hgt) with hlt' | heq'
        · obtain ⟨hc2, hs2, hm2, -⟩ := code_layout profile h hs hlt1
          obtain ⟨-, hmlt⟩ := finite_of_lt profile h i hi hfc (j + 1) hlt'
          have hprod := Nat.mul_lt_mul_of_pos_right hmlt hq
          have hnot : ¬ magnitude profile (j + 1) * q ≤ ap * denominator profile := by
            intro hle
            have hb : below profile (ap * denominator profile) q (j + 1) = true :=
              (below_iff _ _ _ _).2 ⟨hlt1, hfin1, hle⟩
            rw [hmax (j + 1) (Nat.lt_succ_self j)] at hb
            cases hb
          refine Nat.le_trans (hle2 ht) (Nat.le_of_lt
            (packed_lt_of_distance_lt profile s ap q hneg hc2 ?_))
          rw [distance_same _ _ _ _ _ hs2, distance_same _ _ _ _ _ hsc, hm2, hmc]
          generalize magnitude profile i * q = x at hprod
          generalize magnitude profile (j + 1) * q = y at hprod hnot
          omega
        · rw [hform, ← show j + 1 = i from heq']
          exact hle2 ht
    · -- a code with the other sign
      have hs' : s = 1 - sp := by omega
      subst hs'
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        rw [hform]
        exact hle0
      · obtain ⟨-, hmpos⟩ := finite_of_lt profile h i hi hfc 0 hipos
        rw [hmag0] at hmpos
        have hprod : q ≤ magnitude profile i * q := Nat.le_mul_of_pos_left q hmpos
        refine Nat.le_trans hle1 (Nat.le_of_lt
          (packed_lt_of_distance_lt profile sp ap q hneg hc1 ?_))
        rw [distance_same _ _ _ _ _ hs1, distance_other _ _ _ _ _ (hsc ▸ hsign), hm1, hmc]
        generalize magnitude profile i * q = x at hprod
        generalize magnitude profile j * q = y at hmj
        omega

/-! ## INT8 by bisection -/

/--
The layout of INT8 as one check over its codes: every code is finite, its sign bit is its
quotient by 128, and its magnitude is the code below 128 and its two's complement from 128 on.
-/
def int8Check : Bool :=
  (List.range 256).all fun c =>
    finiteCode .int8 c && signBit .int8 c == c / 128 &&
      magnitude .int8 c == if c < 128 then c else 256 - c

/-- The facts of the INT8 check. -/
theorem int8_layout {c : Nat} (hc : c < 256) :
    finiteCode .int8 c = true ∧ signBit .int8 c = c / 128 ∧
      magnitude .int8 c = if c < 128 then c else 256 - c := by
  have hcheck : int8Check = true := by decide +kernel
  simp only [int8Check, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
    at hcheck
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcheck c hc
  exact ⟨h1, h2, h3⟩

/-- The INT8 code of the magnitude `i` with the sign `sp`: `i` itself for `sp = 0` and its two's
complement for `sp = 1`, where the magnitude zero is the code zero. -/
def int8Code (sp i : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add (Nat.mul sp 256) i) (Nat.mul (Nat.mul 2 sp) i)) 256

/-- The code of a magnitude that exists for the sign `sp` is a code, and its distance to the
input is the distance of the magnitude. -/
theorem int8Code_spec {sp : Nat} (hsp : sp ≤ 1) (ap q : Nat) {i : Nat} (hi : i < 128 + sp) :
    int8Code sp i < 256 ∧
      distance .int8 sp ap q (int8Code sp i) = i * q - ap * 64 + (ap * 64 - i * q) := by
  have hlt : int8Code sp i < 256 := Nat.mod_lt _ (by decide)
  refine ⟨hlt, ?_⟩
  obtain ⟨-, hsign, hmag⟩ := int8_layout hlt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsp with rfl | rfl
  · -- a nonnegative input: the code is the magnitude
    have hcode : int8Code 0 i = i := by
      change (0 * 256 + i - 2 * 0 * i) % 256 = i
      omega
    rw [hcode] at hsign hmag ⊢
    have hs : signBit .int8 i = 0 := by rw [hsign]; omega
    rw [distance_same _ _ _ _ _ hs, hmag, ite_eq_left (by omega)]
    rfl
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- the zero has the other sign and the same distance
      have hcode : int8Code 1 0 = 0 := by decide
      rw [hcode] at hsign hmag ⊢
      have hs : signBit .int8 0 ≠ 1 := by rw [hsign]; decide
      rw [distance_other _ _ _ _ _ hs, hmag]
      have hden : denominator .int8 = 64 := rfl
      rw [hden]
      simp
    · have hcode : int8Code 1 i = 256 - i := by
        change (1 * 256 + i - 2 * 1 * i) % 256 = 256 - i
        omega
      rw [hcode] at hsign hmag ⊢
      have hs : signBit .int8 (256 - i) = 1 := by rw [hsign]; omega
      rw [distance_same _ _ _ _ _ hs, hmag, ite_eq_right (by omega)]
      have : 256 - (256 - i) = i := by omega
      rw [this]
      rfl

/-- Every INT8 code is the code of a magnitude that exists for the sign `sp`, or is farther from
the input than the zero. -/
theorem int8_cases {sp : Nat} (hsp : sp ≤ 1) (ap q : Nat) {c : Nat} (hc : c < 256) :
    (∃ i, i < 128 + sp ∧ c = int8Code sp i) ∨ ap * 64 + q ≤ distance .int8 sp ap q c := by
  obtain ⟨-, hsign, hmag⟩ := int8_layout hc
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsp with rfl | rfl
  · rcases Nat.lt_or_ge c 128 with hlt | hge
    · refine Or.inl ⟨c, by omega, ?_⟩
      change c = (0 * 256 + c - 2 * 0 * c) % 256
      omega
    · refine Or.inr ?_
      have hs : signBit .int8 c ≠ 0 := by rw [hsign]; omega
      rw [distance_other _ _ _ _ _ hs, hmag, ite_eq_right (by omega)]
      have hpos : 1 ≤ 256 - c := by omega
      have := Nat.mul_le_mul_right q hpos
      change ap * 64 + q ≤ (256 - c) * q + ap * denominator .int8
      have hden : denominator .int8 = 64 := rfl
      rw [hden]
      omega
  · rcases Nat.lt_or_ge c 128 with hlt | hge
    · rcases Nat.eq_zero_or_pos c with rfl | hcpos
      · exact Or.inl ⟨0, by omega, by decide⟩
      · refine Or.inr ?_
        have hs : signBit .int8 c ≠ 1 := by rw [hsign]; omega
        rw [distance_other _ _ _ _ _ hs, hmag, ite_eq_left hlt]
        have := Nat.mul_le_mul_right q hcpos
        change ap * 64 + q ≤ c * q + ap * denominator .int8
        have hden : denominator .int8 = 64 := rfl
        rw [hden]
        omega
    · refine Or.inl ⟨256 - c, by omega, ?_⟩
      change c = (1 * 256 + (256 - c) - 2 * 1 * (256 - c)) % 256
      omega

/-- Whether the magnitude `i` exists for the sign `sp` and `i * q ≤ apD`. -/
def int8Below (sp apD q i : Nat) : Bool :=
  Bool.casesOn (motive := fun _ => Bool) (Nat.blt i (Nat.add 128 sp)) false
    (Nat.ble (Nat.mul i q) apD)

/-- `int8Below` as a proposition. -/
theorem int8Below_iff (sp apD q i : Nat) :
    int8Below sp apD q i = true ↔ i < 128 + sp ∧ i * q ≤ apD := by
  unfold int8Below
  cases hrange : Nat.blt i (Nat.add 128 sp)
  · refine ⟨fun hfalse => Bool.noConfusion hfalse, fun hall => ?_⟩
    have hblt : Nat.blt i (Nat.add 128 sp) = true := by
      rw [Nat.blt_eq]
      exact hall.1
    rw [hrange] at hblt
    exact Bool.noConfusion hblt
  · have hlt : i < 128 + sp := by
      rw [← Nat.blt_eq]
      exact hrange
    exact ⟨fun hle => ⟨hlt, Nat.le_of_ble_eq_true hle⟩, fun hall => Nat.ble_eq_true_of_le hall.2⟩

/--
The skeleton of `int8Nearest`: a bisection with the test `below` finds a magnitude `i`, and the
result is the least of the entry of `i` and of the entry of `i + 1` when that magnitude exists
for the sign `sp`.
-/
def int8NearestWith (below : Nat → Bool) (entry : Nat → Nat) (sp : Nat) : Nat :=
  (fun i =>
    (fun first =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.blt (Nat.succ i) (Nat.add 128 sp)) first
        (least first (entry (Nat.succ i))))
      (entry i))
    (Numerics.Kernel.bisect below 8 0)

/--
The least packed entry over the codes of INT8 for the input `± ap / q` (negative when `sp = 1`)
with sign bit `neg`: a bisection finds the largest magnitude of the sign of the input that is at
most the input, where the zero counts for both signs, and the result is the least entry of its
code and of the code of the next magnitude when that exists (`scan_eq_int8Nearest`).
-/
def int8Nearest (sp neg ap q : Nat) : Nat :=
  int8NearestWith (int8Below sp (Nat.mul ap 64) q)
    (fun i => entry .int8 sp neg ap q (int8Code sp i)) sp

/-- The test of the INT8 bisection is downward closed. -/
theorem int8Below_down (sp apD q : Nat) :
    ∀ i j, i ≤ j → int8Below sp apD q j = true → int8Below sp apD q i = true := by
  intro i j hij hbj
  rw [int8Below_iff] at hbj ⊢
  exact ⟨by omega, Nat.le_trans (Nat.mul_le_mul_right q hij) hbj.2⟩

/-- The test of the INT8 bisection holds at the magnitude zero. -/
theorem int8Below_zero (sp apD q : Nat) : int8Below sp apD q 0 = true := by
  rw [int8Below_iff]
  exact ⟨by omega, by rw [Nat.zero_mul]; exact Nat.zero_le _⟩

/-- The test of the INT8 bisection fails beyond the magnitudes, for a sign bit `sp`. -/
theorem int8Below_up {sp : Nat} (hsp : sp ≤ 1) (apD q : Nat) :
    ∀ j, 0 + 2 ^ 8 ≤ j → int8Below sp apD q j = false := by
  intro j hj
  cases hb : int8Below sp apD q j
  · rfl
  · rw [int8Below_iff] at hb
    have : (2 : Nat) ^ 8 = 256 := by decide
    omega

/--
The skeleton of `int8Nearest` at the magnitude `i`: the least of the entry of `i` and of the
entry of `i + 1` when that magnitude exists for the sign `sp`.
-/
def int8NearestAt (entry : Nat → Nat) (sp i : Nat) : Nat :=
  (fun first =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.blt (Nat.succ i) (Nat.add 128 sp)) first
      (least first (entry (Nat.succ i))))
    (entry i)

/-- A guess of the largest magnitude of the sign `sp` that is at most the input: the quotient
`apD / q`, at most the largest magnitude of that sign. -/
def int8Guess (sp apD q : Nat) : Nat :=
  Numerics.Kernel.minNat (Nat.div apD q) (Nat.add 127 sp)

/--
`int8Nearest` without the bisection when the guess of `int8Guess` is the magnitude that the
bisection finds, which two tests confirm, and `other` when it is not or when `sp` is not a
sign bit (`int8NearestGuessed_eq`).
-/
def int8NearestGuessed (sp neg ap q other : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble sp 1) other
    (Numerics.Kernel.guarded (int8Below sp (Nat.mul ap 64) q) (int8Guess sp (Nat.mul ap 64) q)
      (int8NearestAt (fun i => entry .int8 sp neg ap q (int8Code sp i)) sp) other)

/-- With `int8Nearest` as the alternative, the guessed form is `int8Nearest`, for every
input. -/
theorem int8NearestGuessed_eq (sp neg ap q : Nat) :
    int8NearestGuessed sp neg ap q (int8Nearest sp neg ap q) = int8Nearest sp neg ap q := by
  unfold int8NearestGuessed
  cases hsp : Nat.ble sp 1
  · rfl
  · exact Numerics.Kernel.guarded_eq _ (int8Below_down sp _ q) 8 (int8Below_zero sp _ q)
      (int8Below_up (Nat.le_of_ble_eq_true hsp) _ q) _
      (int8NearestAt (fun i => entry .int8 sp neg ap q (int8Code sp i)) sp)

/-- The scan of all codes of INT8 is the entry that the bisection finds. -/
theorem scan_eq_int8Nearest (sp neg ap q : Nat) (hsp : sp ≤ 1) (hneg : neg ≤ 1) (hq : 0 < q) :
    scan .int8 sp neg ap q 256 = some (int8Nearest sp neg ap q) := by
  -- the bisection
  have hdown := int8Below_down sp (ap * 64) q
  have hzero := int8Below_zero sp (ap * 64) q
  have hup := int8Below_up hsp (ap * 64) q
  obtain ⟨hstar, hmax⟩ := Numerics.Kernel.bisect_spec _ hdown 8 0 hzero hup
  have hnearest : int8Nearest sp neg ap q =
      (fun i =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.blt (i + 1) (128 + sp))
          (packed .int8 sp neg ap q (int8Code sp i))
          (least (packed .int8 sp neg ap q (int8Code sp i))
            (packed .int8 sp neg ap q (int8Code sp (i + 1)))))
        (Numerics.Kernel.bisect (int8Below sp (ap * 64) q) 8 0) := by
    unfold int8Nearest int8NearestWith
    simp only [entry_eq]
    rfl
  rw [hnearest]
  generalize Numerics.Kernel.bisect (int8Below sp (ap * 64) q) 8 0 = i at hstar hmax
  dsimp only
  rw [int8Below_iff] at hstar
  obtain ⟨hi, hle⟩ := hstar
  obtain ⟨hc1, hd1⟩ := int8Code_spec hsp ap q hi
  generalize htest : Nat.blt (i + 1) (128 + sp) = test
  generalize hN : (Bool.casesOn (motive := fun _ => Nat) test
      (packed .int8 sp neg ap q (int8Code sp i))
      (least (packed .int8 sp neg ap q (int8Code sp i))
        (packed .int8 sp neg ap q (int8Code sp (i + 1)))) : Nat) = N
  have hle1 : N ≤ packed .int8 sp neg ap q (int8Code sp i) := by
    rw [← hN]
    cases test
    · exact Nat.le_refl _
    · exact least_le_left _ _
  have hle2 : test = true → N ≤ packed .int8 sp neg ap q (int8Code sp (i + 1)) := by
    intro ht
    rw [← hN, ht]
    exact least_le_right _ _
  have hnext : test = true → i + 1 < 128 + sp := by
    intro ht
    rw [ht, Nat.blt_eq] at htest
    exact htest
  have hmem : N = packed .int8 sp neg ap q (int8Code sp i) ∨
      (test = true ∧ N = packed .int8 sp neg ap q (int8Code sp (i + 1))) := by
    rw [← hN]
    cases test
    · exact Or.inl rfl
    · rcases least_eq (packed .int8 sp neg ap q (int8Code sp i))
        (packed .int8 sp neg ap q (int8Code sp (i + 1))) with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, h2⟩
  subst hN
  apply scan_eq_some
  · rcases hmem with h1 | ⟨ht, h2⟩
    · exact ⟨_, hc1, (int8_layout hc1).1, h1⟩
    · obtain ⟨hc2, -⟩ := int8Code_spec hsp ap q (hnext ht)
      exact ⟨_, hc2, (int8_layout hc2).1, h2⟩
  · intro c hc _
    rcases int8_cases hsp ap q hc with ⟨k, hk, rfl⟩ | hfar
    · -- the code of a magnitude of the sign of the input
      obtain ⟨_, hdk⟩ := int8Code_spec hsp ap q hk
      rcases Nat.lt_trichotomy k i with hlt | heq | hgt
      · have hprod := Nat.mul_lt_mul_of_pos_right hlt hq
        refine Nat.le_trans hle1 (Nat.le_of_lt
          (packed_lt_of_distance_lt .int8 sp ap q hneg hc1 ?_))
        rw [hd1, hdk]
        generalize k * q = x at hprod
        generalize i * q = y at hprod hle
        omega
      · subst heq
        exact hle1
      · have ht : test = true := by
          rw [← htest, Nat.blt_eq]
          omega
        rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hgt) with hlt' | heq'
        · obtain ⟨hc2, hd2⟩ := int8Code_spec hsp ap q (hnext ht)
          have hprod := Nat.mul_lt_mul_of_pos_right hlt' hq
          have hnot : ¬ (i + 1) * q ≤ ap * 64 := by
            intro hle'
            have hb : int8Below sp (ap * 64) q (i + 1) = true :=
              (int8Below_iff _ _ _ _).2 ⟨hnext ht, hle'⟩
            rw [hmax (i + 1) (Nat.lt_succ_self i)] at hb
            cases hb
          refine Nat.le_trans (hle2 ht) (Nat.le_of_lt
            (packed_lt_of_distance_lt .int8 sp ap q hneg hc2 ?_))
          rw [hd2, hdk]
          generalize k * q = x at hprod
          generalize (i + 1) * q = y at hprod hnot
          omega
        · rw [← show i + 1 = k from heq']
          exact hle2 ht
    · -- a code that is farther than the zero
      refine Nat.le_trans hle1 (Nat.le_of_lt
        (packed_lt_of_distance_lt .int8 sp ap q hneg hc1 ?_))
      rw [hd1]
      generalize i * q = y at hle
      omega

end FloatLib.Floats.Formats.OCP.MX.Standard.Element
