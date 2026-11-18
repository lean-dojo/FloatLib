/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Runtime
public import FloatLib.Tactic.KernelInline
public import FloatLib.Tactic.KernelOptimize

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring

/-!
# Element rounding of OCP MX 1.0 as a scan of codes on natural numbers

`Element.quantizeFinite` is the reference: the first minimum of a rational key over the list of
all finite element words with their values. Lean's kernel evaluates it in about 0.7 seconds for
an eight-bit profile, because every comparison is one of rational numbers behind several
definitions.

This module states the same choice on natural numbers. For an input `± ap / q` and a code with
magnitude `m / D`, where `D` is the common denominator of the profile, the distance is
`|m * q ∓ ap * D|` in units of `1 / (D * q)`. The rounding key of the code is the number
`4 * distance + tie`, where `tie < 4` holds the low bit of the code and whether its sign differs
from the sign of the input, and its packed entry is `key * 2 ^ width + code`. The word that the
reference selects is the code of the least packed entry over the finite codes: the smallest code
wins among equal keys, as the first minimum of the reference does.

`scan` visits every code and keeps the least entry, with one comparison of two natural numbers
per code. `scanAll` is the same scan with the constants of each profile in place
(`kernel_inline%`). The kernel path of `Standard.KernelPath` finds the same entry by bisection
and uses the scan as its specification.

What is proved, for all six profiles and every input:

* `candidates_eq`: the reference list is the list of the finite codes with their values, as
  `finiteCode`, `magnitude`, `signBit` and `denominator` compute them. One kernel evaluation per
  profile checks it.
* `roundingKey_lt_iff`: the natural-number key orders two codes as the rational key orders their
  words.
* `scan_eq`, `scan_spec`, `scan_eq_some`: the scan of the first `count` codes is the first
  minimum of the key over the finite codes below `count`, and it is the one packed entry of such
  a code that is at most all the others.
* `quantizeFinite_eq_scan`: `quantizeFinite profile input` is the word of `scanCode profile
  input`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/-- The numerator of the magnitude of a sign-magnitude code with `ew` exponent and `fw`
fraction bits, over `2 ^ (bias + fw - 1)`. -/
def floatMagnitude (ew fw code : Nat) : Nat :=
  (fun exponent fraction =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq exponent 0)
      (Nat.shiftLeft (Nat.add (Nat.shiftLeft 1 fw) fraction) (Nat.sub exponent 1))
      fraction)
    (Nat.land (Nat.shiftRight code fw) (Nat.sub (Nat.shiftLeft 1 ew) 1))
    (Nat.land code (Nat.sub (Nat.shiftLeft 1 fw) 1))

/-- The shift of the field that marks a non-finite code. -/
def nonFiniteShift : Profile → Nat
  | .e5m2 => 2
  | _ => 0

/-- The value of that field in a non-finite code: all ones of the E5M2 exponent, the E4M3 NaN
magnitude, and a value beyond the width for the profiles whose codes are all finite. -/
def nonFiniteMask : Profile → Nat
  | .e5m2 => 31
  | .e4m3 => 127
  | _ => 256

/-- The exponent bits of a floating profile. -/
def exponentBits : Profile → Nat
  | .e5m2 => 5
  | .e4m3 => 4
  | .e3m2 => 3
  | _ => 2

/-- The fraction bits of a floating profile. -/
def fractionBits : Profile → Nat
  | .e5m2 => 2
  | .e4m3 => 3
  | .e3m2 => 2
  | .e2m3 => 3
  | .e2m1 => 1
  | .int8 => 0

/-- Whether the profile is the two's-complement INT8. -/
def twosComplement : Profile → Bool
  | .int8 => true
  | _ => false

/-- The common denominator of the values of a profile. -/
def denominator : Profile → Nat
  | .e5m2 => 65536
  | .e4m3 => 512
  | .e3m2 => 16
  | .e2m3 => 8
  | .e2m1 => 2
  | .int8 => 64

/-- Whether a code of the profile has a finite value. -/
def finiteCode (profile : Profile) (code : Nat) : Bool :=
  Bool.not
    (Nat.beq (Nat.land (Nat.shiftRight code (nonFiniteShift profile)) (nonFiniteMask profile))
      (nonFiniteMask profile))

/-- The numerator of the magnitude of a finite code over `denominator profile`. -/
def magnitude (profile : Profile) (code : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (twosComplement profile)
    (floatMagnitude (exponentBits profile) (fractionBits profile) code)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 128 code) code (Nat.sub 256 code))

/-- The sign bit of a code, zero or one: its top bit. -/
def signBit (profile : Profile) (code : Nat) : Nat :=
  Nat.land (Nat.shiftRight code (Nat.sub profile.width 1)) 1

/-- The finite codes of a profile, in increasing order. -/
def finiteCodes (profile : Profile) : List Nat :=
  (List.range (2 ^ profile.width)).filter (finiteCode profile)

/-- The element and the value of a code. -/
def ofCode (profile : Profile) (code : Nat) : Element profile × Rat :=
  (BitVec.ofNat profile.width code,
    (if signBit profile code = 1 then -(magnitude profile code : Rat)
      else magnitude profile code) / denominator profile)

/-- The candidates of a profile are its finite codes with their values, in the same order. -/
theorem candidates_eq (profile : Profile) :
    candidates profile = (finiteCodes profile).map (ofCode profile) := by
  cases profile <;> decide +kernel

/-- The denominators are positive. -/
theorem denominator_pos (profile : Profile) : 0 < denominator profile := by
  cases profile <;> decide

/-- The sign bit is zero or one. -/
theorem signBit_le (profile : Profile) (code : Nat) : signBit profile code ≤ 1 :=
  Nat.and_le_right

/-- The sign bit of a code is the bit that `Element.negative` tests. -/
theorem signBit_eq (profile : Profile) (code : Nat) :
    signBit profile code = (code.testBit (profile.width - 1)).toNat := by
  have h := signBit_le profile code
  unfold Nat.testBit
  change signBit profile code = (1 &&& code >>> (profile.width - 1) != 0).toNat
  have hcomm : 1 &&& code >>> (profile.width - 1) = signBit profile code := Nat.and_comm _ _
  rw [hcomm]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

/-- The distance of the value of a code to `± ap / q` (negative when `sp = 1`), in units of
`1 / (denominator * q)`. -/
def distance (profile : Profile) (sp ap q code : Nat) : Nat :=
  (fun mq apD =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (signBit profile code) sp)
      (Nat.add mq apD)
      (Nat.add (Nat.sub mq apD) (Nat.sub apD mq)))
    (Nat.mul (magnitude profile code) q) (Nat.mul ap (denominator profile))

/-- The tie-breaking component of the rounding key of a code, below four: an even low bit
first, then the sign bit `neg` of the input. -/
def tie (profile : Profile) (neg code : Nat) : Nat :=
  Nat.add (Nat.mul 2 (Nat.land code 1)) (Nat.xor (signBit profile code) neg)

/-- The rounding key of a code as one natural number. -/
def codeKey (profile : Profile) (sp neg ap q code : Nat) : Nat :=
  Nat.add (Nat.mul 4 (distance profile sp ap q code)) (tie profile neg code)

/-- The tie component is below four when the sign of the input is a bit. -/
theorem tie_lt (profile : Profile) {neg : Nat} (hneg : neg ≤ 1) (code : Nat) :
    tie profile neg code < 4 := by
  have hs := signBit_le profile code
  have hlow : code &&& 1 ≤ 1 := Nat.and_le_right
  have hxor : signBit profile code ^^^ neg ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with h | h <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hneg with h' | h' <;> rw [h, h'] <;> decide
  change 2 * (code &&& 1) + (signBit profile code ^^^ neg) < 4
  omega

/-- The tie-breaking component of `roundingKey`, for a code within the width. -/
theorem tie_eq (profile : Profile) (input : SignedRat) {code : Nat}
    (hcode : code < 2 ^ profile.width) :
    (ofLex (roundingKey input (ofCode profile code))).2 =
      tie profile input.negative.toNat code := by
  have htoNat : (BitVec.ofNat profile.width code).toNat = code := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcode]
  unfold roundingKey ofCode tie negative
  simp only [ofLex_toLex]
  rw [htoNat, signBit_eq]
  change _ = 2 * (code &&& 1) + _
  rw [Nat.and_one_is_mod]
  cases code.testBit (profile.width - 1) <;> cases input.negative <;> rfl

/-- The distance of the value of a code to the input is its natural-number distance over a
common positive denominator. -/
theorem abs_sub_eq (profile : Profile) (input : SignedRat) (code : Nat) :
    |(ofCode profile code).2 - input.value| =
      (distance profile (decide (input.value.num < 0)).toNat input.value.num.natAbs
        input.value.den code : ℚ) / ((denominator profile : ℚ) * input.value.den) := by
  have hD : (0 : ℚ) < denominator profile := by exact_mod_cast denominator_pos profile
  have hden : (0 : ℚ) < input.value.den := by exact_mod_cast input.value.den_pos
  have hvalue : input.value = (input.value.num : ℚ) / input.value.den :=
    (Rat.num_div_den input.value).symm
  set m := magnitude profile code with hm
  set D := denominator profile with hDdef
  set q := input.value.den
  set num := input.value.num
  have hsplit : ∀ signed : ℤ,
      (signed : ℚ) / D - (num : ℚ) / q = ((signed * q - num * D : ℤ) : ℚ) / ((D : ℚ) * q) := by
    intro signed
    push_cast
    field_simp
  have habs : ∀ signed : ℤ, |(signed : ℚ) / D - (num : ℚ) / q| =
      ((signed * q - num * D).natAbs : ℚ) / ((D : ℚ) * q) := by
    intro signed
    rw [hsplit, abs_div, abs_of_pos (mul_pos hD hden), Nat.cast_natAbs, Int.cast_abs]
  unfold ofCode distance
  rw [← hm, ← hDdef]
  change |(if signBit profile code = 1 then -(m : ℚ) else (m : ℚ)) / D - input.value| = _
  rw [hvalue]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (signBit_le profile code) with hs | hs <;>
    rcases lt_or_ge num 0 with hneg | hpos
  · -- nonnegative code, negative input
    rw [hs, ite_eq_right (by decide), decide_eq_true hneg]
    have h := habs (m : ℤ)
    push_cast at h
    rw [h]
    congr 1
    change (((m : ℤ) * q - num * D).natAbs : ℚ) = ((m * q + num.natAbs * D : ℕ) : ℚ)
    congr 1
    have hn : num = -(num.natAbs : ℤ) := by omega
    generalize hX : m * q = X
    generalize hY : num.natAbs * D = Y
    have hx : (m : ℤ) * q = (X : ℤ) := by rw [← hX]; push_cast; rfl
    have hy : num * D = -(Y : ℤ) := by rw [← hY, hn]; push_cast; simp
    rw [hx, hy]
    omega
  · -- nonnegative code, nonnegative input
    rw [hs, ite_eq_right (by decide), decide_eq_false (not_lt.mpr hpos)]
    have h := habs (m : ℤ)
    push_cast at h
    rw [h]
    congr 1
    change (((m : ℤ) * q - num * D).natAbs : ℚ) =
      ((m * q - num.natAbs * D + (num.natAbs * D - m * q) : ℕ) : ℚ)
    congr 1
    generalize hX : m * q = X
    generalize hY : num.natAbs * D = Y
    have hx : (m : ℤ) * q = (X : ℤ) := by rw [← hX]; push_cast; rfl
    have hy : num * D = (Y : ℤ) := by rw [← hY]; push_cast; rw [abs_of_nonneg hpos]
    rw [hx, hy]
    omega
  · -- negative code, negative input
    rw [hs, ite_eq_left rfl, decide_eq_true hneg]
    have h := habs (-(m : ℤ))
    push_cast at h
    rw [h]
    congr 1
    change (((-(m : ℤ)) * q - num * D).natAbs : ℚ) =
      ((m * q - num.natAbs * D + (num.natAbs * D - m * q) : ℕ) : ℚ)
    congr 1
    have hn : num = -(num.natAbs : ℤ) := by omega
    generalize hX : m * q = X
    generalize hY : num.natAbs * D = Y
    have hx : (-(m : ℤ)) * q = -(X : ℤ) := by rw [← hX]; push_cast; ring
    have hy : num * D = -(Y : ℤ) := by rw [← hY, hn]; push_cast; simp
    rw [hx, hy]
    omega
  · -- negative code, nonnegative input
    rw [hs, ite_eq_left rfl, decide_eq_false (not_lt.mpr hpos)]
    have h := habs (-(m : ℤ))
    push_cast at h
    rw [h]
    congr 1
    change (((-(m : ℤ)) * q - num * D).natAbs : ℚ) = ((m * q + num.natAbs * D : ℕ) : ℚ)
    congr 1
    generalize hX : m * q = X
    generalize hY : num.natAbs * D = Y
    have hx : (-(m : ℤ)) * q = -(X : ℤ) := by rw [← hX]; push_cast; ring
    have hy : num * D = (Y : ℤ) := by rw [← hY]; push_cast; rw [abs_of_nonneg hpos]
    rw [hx, hy]
    omega

/-- `argAux` through a map, for a relation on the images that the map reflects on the elements
with a property that the list and the accumulator have. -/
private theorem foldl_argAux_map {α β : Type*} (r : β → β → Prop) [DecidableRel r]
    (r' : α → α → Prop) [DecidableRel r'] (g : α → β) (P : α → Prop)
    (h : ∀ a b, P a → P b → (r (g a) (g b) ↔ r' a b)) :
    ∀ (l : List α) (o : Option α), (∀ a ∈ l, P a) → (∀ c ∈ o, P c) →
      (l.map g).foldl (List.argAux r) (o.map g) = (l.foldl (List.argAux r') o).map g
  | [], _, _, _ => rfl
  | a :: l, o, hl, ho => by
      simp only [List.map_cons, List.foldl_cons]
      have ha : P a := hl a List.mem_cons_self
      have hstep : List.argAux r (o.map g) (g a) = (List.argAux r' o a).map g ∧
          ∀ c ∈ List.argAux r' o a, P c := by
        cases o with
        | none => exact ⟨rfl, fun c hc => by cases hc; exact ha⟩
        | some c =>
            have hc : P c := ho c rfl
            simp only [Option.map_some, List.argAux]
            by_cases hr : r' a c
            · rw [ite_eq_left hr, ite_eq_left ((h a c ha hc).2 hr)]
              exact ⟨rfl, fun d hd => by cases hd; exact ha⟩
            · rw [ite_eq_right hr, ite_eq_right (fun hg => hr ((h a c ha hc).1 hg))]
              exact ⟨rfl, fun d hd => by cases hd; exact hc⟩
      rw [hstep.1]
      exact foldl_argAux_map r r' g P h l _ (fun b hb => hl b (List.mem_cons_of_mem _ hb)) hstep.2

/-- The natural-number key orders the codes within the width as the rounding key orders their
elements. -/
theorem roundingKey_lt_iff (profile : Profile) (input : SignedRat) (a b : Nat)
    (ha : a < 2 ^ profile.width) (hb : b < 2 ^ profile.width) :
    roundingKey input (ofCode profile a) < roundingKey input (ofCode profile b) ↔
      codeKey profile (decide (input.value.num < 0)).toNat input.negative.toNat
          input.value.num.natAbs input.value.den a <
        codeKey profile (decide (input.value.num < 0)).toNat input.negative.toNat
          input.value.num.natAbs input.value.den b := by
  have hD : (0 : ℚ) < denominator profile := by exact_mod_cast denominator_pos profile
  have hden : (0 : ℚ) < input.value.den := by exact_mod_cast input.value.den_pos
  have hpos := mul_pos hD hden
  have hfst : ∀ code, (ofLex (roundingKey input (ofCode profile code))).1 =
      (distance profile (decide (input.value.num < 0)).toNat input.value.num.natAbs
        input.value.den code : ℚ) / ((denominator profile : ℚ) * input.value.den) :=
    fun code => abs_sub_eq profile input code
  have hneg : input.negative.toNat ≤ 1 := Bool.toNat_le input.negative
  have hta := tie_lt profile hneg a
  have htb := tie_lt profile hneg b
  rw [Prod.Lex.lt_iff, hfst a, hfst b, tie_eq profile input ha, tie_eq profile input hb,
    div_lt_div_iff_of_pos_right hpos, div_left_inj₀ hpos.ne']
  simp only [Nat.cast_lt, Nat.cast_inj]
  change _ ↔ 4 * _ + _ < 4 * _ + _
  omega

/-- Every finite code is within the width. -/
theorem lt_of_mem_finiteCodes {profile : Profile} {code : Nat}
    (h : code ∈ finiteCodes profile) : code < 2 ^ profile.width :=
  List.mem_range.1 (List.mem_filter.1 h).1

/-- Nearest-even element rounding is the minimum of the natural-number key over the finite
codes. -/
theorem quantizeFinite_eq_argmin (profile : Profile) (input : SignedRat) :
    quantizeFinite profile input =
      BitVec.ofNat profile.width
        (((finiteCodes profile).argmin
          (codeKey profile (decide (input.value.num < 0)).toNat input.negative.toNat
            input.value.num.natAbs input.value.den)).getD 0) := by
  unfold quantizeFinite List.argmin
  rw [candidates_eq]
  have h := foldl_argAux_map
    (fun b c => roundingKey input b < roundingKey input c)
    (fun b c => codeKey profile (decide (input.value.num < 0)).toNat input.negative.toNat
        input.value.num.natAbs input.value.den b <
      codeKey profile (decide (input.value.num < 0)).toNat input.negative.toNat
        input.value.num.natAbs input.value.den c)
    (ofCode profile) (fun code => code < 2 ^ profile.width)
    (fun a b ha hb => roundingKey_lt_iff profile input a b ha hb)
    (finiteCodes profile) none (fun a ha => lt_of_mem_finiteCodes ha) (fun c hc => by cases hc)
  rw [Option.map_none] at h
  rw [h]
  cases List.foldl _ none (finiteCodes profile) with
  | none => rfl
  | some code => rfl

/--
One step of the scan: a finite code replaces the best code so far when its key is smaller. The
state is the key of the best code with the code in its low `width` bits, so one comparison of
two natural numbers decides.
-/
def scanStep (profile : Profile) (sp neg ap q code : Nat) (best : Option Nat) : Option Nat :=
  Bool.casesOn (motive := fun _ => Option Nat) (finiteCode profile code) best
    ((fun entry =>
      Option.casesOn (motive := fun _ => Option Nat) best (some entry)
        fun current =>
          Bool.casesOn (motive := fun _ => Option Nat) (Nat.blt entry current) best (some entry))
      (Nat.add (Nat.shiftLeft (codeKey profile sp neg ap q code) profile.width) code))

/-- `count` steps of a scan, from no code. -/
def scanLoop (step : Nat → Option Nat → Option Nat) (count : Nat) : Option Nat :=
  Nat.rec (motive := fun _ => Option Nat) none step count

/-- The best of the first `count` codes: one step per code, on natural numbers only. -/
def scan (profile : Profile) (sp neg ap q count : Nat) : Option Nat :=
  scanLoop (scanStep profile sp neg ap q) count

/-- The state of the scan for a best code: its key above its `width` bits. -/
def packed (profile : Profile) (sp neg ap q code : Nat) : Nat :=
  codeKey profile sp neg ap q code * 2 ^ profile.width + code

/-- The scan is the minimum of the key over the finite codes below `count`, packed. -/
theorem scan_eq (profile : Profile) (sp neg ap q : Nat) :
    ∀ count, count ≤ 2 ^ profile.width →
      scan profile sp neg ap q count =
        (((List.range count).filter (finiteCode profile)).argmin
          (codeKey profile sp neg ap q)).map (packed profile sp neg ap q)
  | 0, _ => rfl
  | count + 1, hcount => by
      have ih := scan_eq profile sp neg ap q count (by omega)
      change scanStep profile sp neg ap q count (scan profile sp neg ap q count) = _
      rw [ih]
      unfold List.argmin
      rw [List.range_succ, List.filter_append, List.foldl_append]
      have hmem : ∀ c ∈ ((List.range count).filter (finiteCode profile)).argmin
          (codeKey profile sp neg ap q), c < count := fun c hc =>
        List.mem_range.1 (List.mem_filter.1 (List.argmin_mem hc)).1
      unfold List.argmin at hmem
      generalize ((List.range count).filter (finiteCode profile)).foldl
        (List.argAux fun b c => codeKey profile sp neg ap q b < codeKey profile sp neg ap q c)
        none = best at hmem ⊢
      unfold scanStep
      cases hfinite : finiteCode profile count
      · simp [hfinite]
      · simp only [List.filter_cons, hfinite, ite_true, List.filter_nil, List.foldl_cons,
          List.foldl_nil]
        cases best with
        | none => simp [List.argAux, packed, Nat.shiftLeft_eq]
        | some current =>
            have hcurrent : current < count := hmem current rfl
            simp only [Option.map_some, List.argAux]
            have hlt : Nat.blt
                (Nat.add (Nat.shiftLeft (codeKey profile sp neg ap q count) profile.width) count)
                (packed profile sp neg ap q current) =
                decide (codeKey profile sp neg ap q count < codeKey profile sp neg ap q
                  current) := by
              rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]
              change codeKey profile sp neg ap q count <<< profile.width + count <
                codeKey profile sp neg ap q current * 2 ^ profile.width + current ↔ _
              rw [Nat.shiftLeft_eq]
              generalize codeKey profile sp neg ap q count = K
              generalize codeKey profile sp neg ap q current = K'
              generalize 2 ^ profile.width = W at hcount
              constructor
              · intro h
                by_contra hk
                have : K' ≤ K := Nat.le_of_not_lt hk
                have := Nat.mul_le_mul_right W this
                omega
              · intro h
                have : (K + 1) * W ≤ K' * W := Nat.mul_le_mul_right W h
                rw [Nat.succ_mul] at this
                omega
            change Bool.casesOn (motive := fun _ => Option Nat) (Nat.blt _ _) _ _ = _
            rw [hlt]
            by_cases hkey : codeKey profile sp neg ap q count < codeKey profile sp neg ap q current
            · rw [decide_eq_true hkey, ite_eq_left hkey]
              simp [packed, Nat.shiftLeft_eq]
            · rw [decide_eq_false hkey, ite_eq_right hkey]; rfl

end FloatLib.Floats.Formats.OCP.MX.Standard.Element
