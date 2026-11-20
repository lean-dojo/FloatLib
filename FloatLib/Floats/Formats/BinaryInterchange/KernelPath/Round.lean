/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.KernelInline
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.BitLength
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Encoding
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Agreement

import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic

/-!
# Rounding and packing on natural-number encodings, in every rounding direction

`round fmt mode B sign zeroSign mag Ep Em guard special` rounds the exact value
`± mag * 2 ^ (Ep - Em) * 2 ^ fmt.minSubnormalExponent` in the direction `mode` and returns the
natural-number encoding of the result in `fmt`. It is written for Lean's kernel: every step is a
kernel-accelerated operation on naturals (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`,
`Nat.shiftLeft`, `Nat.land`, `Nat.pow`, `Nat.ble`, `Nat.beq`), the exponent is a pair of naturals
so that no integer arithmetic is unfolded, and there are two branches on the common path: the
choice of the direction and the range check.

* `mag < 2 ^ B` is the exact magnitude and `B` bounds its bit length (`bitLength B mag`).
* `sign` and `zeroSign` are `0` or `1`. `zeroSign` is the sign of the exact value, zero included,
  and `sign` only has to agree with it when `mag ≠ 0`, so a caller can pass a cheaper expression.
* `guard ≠ 0` selects `special` instead, the caller's answer for operands that are not finite.

The result's biased exponent field minus one is `t = (bitLength + Ep) - (Em + fracWidth + 1)`,
truncated at zero for subnormal results. The magnitude is scaled to a quotient `num / den` in
units of that exponent, `roundQuotient` rounds it to an integer significand by its floor and
remainder (`roundUp` is the increment of each direction), and the packed word is
`t * 2 ^ fracWidth + significand`, in which a rounding carry and the step from the subnormal to
the normal range need no case of their own. Zero results and overflow leave the common path
through one comparison. Division and literals round a quotient of two integers with the same
`roundQuotient`.

`round_eq` proves that the result is the encoding of `Model.Internal.Directed.roundDyadic`, the
rounding step of every directed kernel of the reference, for every `FloatFormat` (any exponent and
fraction width, any bias, all four encodings) and all six directions. The proof goes through the
policy rounder `Model.Policy.roundDyadicGeneral`, one definition for all directions, and its
agreement with the directed rounders (`Model.Policy.roundDyadicGeneral_toRoundingMode`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (bitLength bitLength_eq searchLength searchLength_eq)

/-!
The field formulas of a descriptor are unfolded inside the copies declared below. A constant
that an operation reads (the position of the sign, a mask, a bound) is such a copy: the kernel
computes a call of it on a literal format once in a proof, and every later operation finds the
value again, which costs less than computing the formula again.
-/
attribute [kernel_inline] FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
  FloatFormat.maxFiniteFracField FloatFormat.quietBitNat
  FloatFormat.Encoding.maxFiniteExponent FloatFormat.bitWidth

kernel_constant FloatFormat.maxFiniteExpField

/-- Bit position of the sign: the exponent and fraction fields lie below it. -/
def signPos (fmt : FloatFormat) : Nat :=
  fmt.expWidth + fmt.fracWidth

kernel_constant signPos

/-- Mask of the exponent and fraction fields. -/
def magnitudeMask (fmt : FloatFormat) : Nat :=
  2 ^ (fmt.expWidth + fmt.fracWidth) - 1

kernel_constant magnitudeMask

/-- Exponent and fraction fields of the largest finite value, as one word. -/
def maxFinite (fmt : FloatFormat) : Nat :=
  fmt.maxFiniteExpField * 2 ^ fmt.fracWidth + fmt.maxFiniteFracField

kernel_constant maxFinite

/-- One more than `maxFinite`. -/
def maxFiniteSucc (fmt : FloatFormat) : Nat :=
  maxFinite fmt + 1

kernel_constant maxFiniteSucc

/--
Encoding of the zero with sign `negative`, `Model.zero` (`zeroWord_eq`): the sign bit for a
negative zero of an encoding with signed zeros, and zero otherwise. It is written on the two
widths, so that Lean's kernel computes it without unpacking a word of the model.
-/
def zeroWord (fmt : FloatFormat) (negative : Bool) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) negative 0
    (FloatFormat.Encoding.casesOn (motive := fun _ => Nat) fmt.encoding
      (2 ^ signPos fmt) (2 ^ signPos fmt) 0 (2 ^ signPos fmt))

/-- `zeroWord` is the encoding of the zero of the model, for every format and both signs. -/
theorem zeroWord_eq (fmt : FloatFormat) (negative : Bool) :
    zeroWord fmt negative = (Model.zero fmt negative).toNatBits := by
  cases negative
  · change 0 = (Model.zero fmt false).toNatBits
    simp [Model.zero]
  · unfold zeroWord Model.zero
    cases h : fmt.encoding <;>
      simp [FloatFormat.supportsSignedZero, h, signPos, FloatFormat.signMaskNat_eq_two_pow]

kernel_constant zeroWord

/--
Encoding of the overflow result with sign `negative`, `Model.nativeOverflow` (`overflowWord_eq`),
by the encoding: the signed infinity, the NaN of a format whose largest pattern is its NaN, the
NaN of a format with one zero, and the largest finite value with the sign. It is written on the
two widths, so that Lean's kernel computes it without unpacking a word of the model.
-/
def overflowWord (fmt : FloatFormat) (negative : Bool) : Nat :=
  FloatFormat.Encoding.casesOn (motive := fun _ => Nat) fmt.encoding
    (Bool.casesOn (motive := fun _ => Nat) negative
      ((2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth % 2 ^ fmt.bitWidth)
      (2 ^ (fmt.expWidth + fmt.fracWidth) % 2 ^ fmt.bitWidth |||
        (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth % 2 ^ fmt.bitWidth))
    (Bool.casesOn (motive := fun _ => Nat) negative 0 (2 ^ signPos fmt) +
      ((2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth + (2 ^ fmt.fracWidth - 1)))
    (2 ^ signPos fmt)
    (Bool.casesOn (motive := fun _ => Nat) negative 0 (2 ^ signPos fmt) + maxFinite fmt)

/--
Encoding of the result of a rounding in the direction `mode` that overflows with sign `negative`:
the native overflow result when the direction carries the magnitude up, and the largest finite
value otherwise, `Model.directedOverflow` (`roundOverflowWord_eq`).
-/
def roundOverflowWord (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool) :
    Nat :=
  Bool.casesOn (motive := fun _ => Nat) (mode.overflowRoundsMagnitudeUp negative)
    (Bool.casesOn (motive := fun _ => Nat) negative 0 (2 ^ signPos fmt) + maxFinite fmt)
    (overflowWord fmt negative)

kernel_constant overflowWord

kernel_constant roundOverflowWord

/--
One when the quotient `q + r / den`, with `r < den`, rounds up to `q + 1` in the direction `mode`
for a result of sign `sign` (zero or one), and zero when it rounds to `q` (`roundUp_eq`).
-/
def roundUp (mode : Model.IEEERoundingMode) (sign q r den : Nat) : Nat :=
  Model.IEEERoundingMode.casesOn (motive := fun _ => Nat) mode
    (Nat.div (Nat.sub (Nat.add (Nat.add r r) (Nat.land q 1)) 1) den)
    (Nat.div (Nat.add r r) den)
    0
    (Nat.mul (Nat.sub 1 sign) (Nat.sub 1 (Nat.sub 1 r)))
    (Nat.mul sign (Nat.sub 1 (Nat.sub 1 r)))
    (Nat.sub 1 (Nat.sub 1 r))

/--
`roundUp` over the denominator `2 ^ g`, with a shift in place of the division
(`roundUpShift_eq`). The kernel shifts a number right by any amount, and refuses to build a
power of two whose exponent does not fit in 32 bits, which is the size of an exponent gap in a
format with a wide exponent field.
-/
def roundUpShift (mode : Model.IEEERoundingMode) (sign q r g : Nat) : Nat :=
  Model.IEEERoundingMode.casesOn (motive := fun _ => Nat) mode
    (Nat.shiftRight (Nat.sub (Nat.add (Nat.add r r) (Nat.land q 1)) 1) g)
    (Nat.shiftRight (Nat.add r r) g)
    0
    (Nat.mul (Nat.sub 1 sign) (Nat.sub 1 (Nat.sub 1 r)))
    (Nat.mul sign (Nat.sub 1 (Nat.sub 1 r)))
    (Nat.sub 1 (Nat.sub 1 r))

/-- `roundUpShift` is `roundUp` over the denominator `2 ^ g`. -/
theorem roundUpShift_eq (mode : Model.IEEERoundingMode) (sign q r g : Nat) :
    roundUpShift mode sign q r g = roundUp mode sign q r (2 ^ g) := by
  unfold roundUpShift roundUp
  cases mode <;>
    first
      | rfl
      | (simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
         rfl)

/-- The zero or the overflow result, by the rounded significand `mantissa`. -/
def packRare (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (zeroSign mantissa : Nat) :
    Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq mantissa 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq zeroSign 0)
      (roundOverflowWord fmt mode true) (roundOverflowWord fmt mode false))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq zeroSign 0)
      (zeroWord fmt true) (zeroWord fmt false))

kernel_constant packRare

/--
Pack a rounded significand `mantissa` whose exponent field minus one is `t` (zero for a subnormal
result). The common path is one comparison and one addition.
-/
def pack (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign t mantissa guard special : Nat) : Nat :=
  (fun word =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.ble
        (Nat.add word (Nat.mul (Nat.add (Nat.sub 1 mantissa) guard) (maxFiniteSucc fmt)))
        (maxFinite fmt))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq guard 0) special
        (packRare fmt mode zeroSign mantissa))
      (Nat.add (Nat.shiftLeft sign (signPos fmt)) word))
    (Nat.add (Nat.shiftLeft t fmt.fracWidth) mantissa)

/--
Round the quotient `num / den` to an integer significand in the direction `mode`, from its floor
and remainder, then pack it with the exponent field `t + 1`.
-/
def roundQuotient (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign guard special t num den : Nat) : Nat :=
  (fun q =>
    pack fmt mode sign zeroSign t (Nat.add q (roundUp mode sign q (Nat.mod num den) den))
      guard special)
    (Nat.div num den)

/--
Choose the exponent field and the alignment shifts from the bit length `length` of `mag`, and
round the magnitude at that place (`roundAt_def`). The quotient, the remainder and the rounding
increment are taken with shifts by the distance `D` to the rounding place, so that no power of
two of the size of `D` is built: for a result far below the subnormal range `D` is as large as
the exponent range of the format.
-/
def roundAt (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag Ep Em guard special length : Nat) : Nat :=
  (fun t =>
    (fun D num =>
      (fun q =>
        pack fmt mode sign zeroSign t
          (Nat.add q (roundUpShift mode sign q (Nat.sub num (Nat.shiftLeft q D)) D))
          guard special)
        (Nat.shiftRight num D))
      (Nat.sub (Nat.add t Em) Ep) (Nat.shiftLeft mag (Nat.sub Ep (Nat.add t Em))))
    (Nat.sub (Nat.add length Ep) (Nat.add (Nat.add Em fmt.fracWidth) 1))

/--
`roundAt` is the rounding of a quotient by a power of two: `roundQuotient` of the shifted
magnitude over `2 ^ D`.
-/
theorem roundAt_def (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag Ep Em guard special length : Nat) :
    roundAt fmt mode sign zeroSign mag Ep Em guard special length =
      (fun t =>
        roundQuotient fmt mode sign zeroSign guard special t
          (Nat.shiftLeft mag (Nat.sub Ep (Nat.add t Em)))
          (Nat.pow 2 (Nat.sub (Nat.add t Em) Ep)))
        (Nat.sub (Nat.add length Ep) (Nat.add (Nat.add Em fmt.fracWidth) 1)) := by
  unfold roundAt roundQuotient
  dsimp only
  generalize Nat.sub (Nat.add length Ep) (Nat.add (Nat.add Em fmt.fracWidth) 1) = t
  generalize Nat.shiftLeft mag (Nat.sub Ep (Nat.add t Em)) = num
  generalize Nat.sub (Nat.add t Em) Ep = D
  have hq : Nat.shiftRight num D = Nat.div num (Nat.pow 2 D) := Nat.shiftRight_eq_div_pow num D
  have hr : Nat.sub num (Nat.shiftLeft (Nat.div num (Nat.pow 2 D)) D) =
      Nat.mod num (Nat.pow 2 D) := by
    change num - (num / 2 ^ D) <<< D = num % 2 ^ D
    rw [Nat.shiftLeft_eq, Nat.mod_def, Nat.mul_comm]
  rw [hq, hr, roundUpShift_eq]
  rfl

/--
Encoding of `± mag * 2 ^ (Ep - Em) * 2 ^ fmt.minSubnormalExponent` rounded in the direction
`mode`, for `mag < 2 ^ B`; `special` when `guard ≠ 0`. See the module documentation.
-/
def round (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (B sign zeroSign mag Ep Em guard special : Nat) : Nat :=
  roundAt fmt mode sign zeroSign mag Ep Em guard special (bitLength B mag)

/--
Pack the exact value `± mag * 2 ^ e * 2 ^ fmt.minSubnormalExponent` of a magnitude whose bit
length `length` is at most `fracWidth + 1`: the magnitude is shifted left to its place, by at
most `e` places, and packed. Nothing is rounded, so no quotient, remainder or rounding increment
is computed (`roundAt_exact`). A difference of two close values whose leading bits cancel has
this shape: it is exact, and it only needs to be normalized.
-/
def packExact (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag e guard special length : Nat) : Nat :=
  (fun t => pack fmt mode sign zeroSign t (Nat.shiftLeft mag (Nat.sub e t)) guard special)
    (Nat.sub (Nat.add length e) (Nat.succ fmt.fracWidth))

/-- No direction rounds an exact quotient up. -/
theorem roundUpShift_exact (mode : Model.IEEERoundingMode) (sign q : Nat) :
    roundUpShift mode sign q 0 0 = 0 := by
  unfold roundUpShift
  cases mode <;>
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftRight_eq', Nat.land_eq,
      Nat.shiftRight_zero, Nat.add_zero, Nat.zero_add, Nat.sub_zero, Nat.sub_self, Nat.mul_zero]
  have hbit : q &&& 1 ≤ 1 := Nat.and_le_right
  omega

/--
For a magnitude of at most `fracWidth + 1` bits on a grid at or above the least subnormal
number, the general rounding is the exact normalization `packExact`, in every direction.
-/
theorem roundAt_exact (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign mag e guard special length : Nat) (hlength : length ≤ fmt.fracWidth + 1) :
    roundAt fmt mode sign zeroSign mag e 0 guard special length =
      packExact fmt mode sign zeroSign mag e guard special length := by
  unfold roundAt packExact
  dsimp only
  have ht : Nat.sub (Nat.add length e) (Nat.add (Nat.add 0 fmt.fracWidth) 1) =
      Nat.sub (Nat.add length e) (Nat.succ fmt.fracWidth) := by
    simp only [Nat.add_eq, Nat.sub_eq, Nat.zero_add, Nat.succ_eq_add_one]
  rw [ht]
  generalize hT : Nat.sub (Nat.add length e) (Nat.succ fmt.fracWidth) = t
  have hle : t ≤ e := by
    simp only [Nat.add_eq, Nat.sub_eq, Nat.succ_eq_add_one] at hT
    omega
  have hD : Nat.sub (Nat.add t 0) e = 0 := by
    simp only [Nat.add_eq, Nat.sub_eq, Nat.add_zero]
    omega
  rw [hD, show Nat.add t 0 = t from rfl]
  generalize Nat.shiftLeft mag (Nat.sub e t) = num
  have hq : Nat.shiftRight num 0 = num := rfl
  have hr : Nat.sub num (Nat.shiftLeft num 0) = 0 := by
    change num - num <<< 0 = 0
    rw [Nat.shiftLeft_zero, Nat.sub_self]
  rw [hq, hr, roundUpShift_exact]
  rfl

/-! ## Quotient rounding in a direction -/

/-- `Nat.div` is `/`. -/
theorem div_def (a b : Nat) : Nat.div a b = a / b := rfl

/-- `Nat.mod` is `%`. -/
theorem mod_def (a b : Nat) : Nat.mod a b = a % b := rfl

/-- The sign of a result as a natural number. -/
def signNat (negative : Bool) : Nat :=
  if negative then 1 else 0

/--
`roundUp` is the increment of the reference quotient rounding `Model.Policy.roundQuot`, in each of
the six directions: the floor of `num / den` plus `roundUp` of the floor and the remainder is the
rounded quotient.
-/
theorem roundUp_eq (mode : Model.IEEERoundingMode) (negative : Bool) (entropy num den : Nat)
    (hden : 0 < den) :
    num / den + roundUp mode (signNat negative) (num / den) (num % den) den =
      Model.Policy.roundQuot mode.toRoundingMode negative entropy num den := by
  have hr : num % den < den := Nat.mod_lt _ hden
  unfold Model.Policy.roundQuot
  simp only []
  generalize num / den = q
  generalize num % den = r at hr
  have hparity : q % 2 < 2 := Nat.mod_lt _ (by decide)
  have hflag : 1 - (1 - r) = if r = 0 then 0 else 1 := by
    split <;> omega
  unfold roundUp signNat
  cases mode <;>
    simp only [Model.IEEERoundingMode.toRoundingMode, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
      div_def, Nat.land_eq, Nat.and_one_is_mod, beq_iff_eq, gt_iff_lt, hflag]
  · -- nearest, ties to even
    by_cases h0 : r = 0
    · subst h0
      rw [ite_eq_left rfl, Nat.div_eq_of_lt (by omega)]
      rfl
    · rw [ite_eq_right h0]
      by_cases h1 : 2 * r < den
      · rw [ite_eq_left h1, Nat.div_eq_of_lt (by omega)]
        rfl
      · rw [ite_eq_right h1]
        by_cases h2 : den < 2 * r
        · rw [ite_eq_left h2, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
        · rw [ite_eq_right h2]
          by_cases h3 : q % 2 = 0
          · rw [ite_eq_left h3, Nat.div_eq_of_lt (by omega)]
            rfl
          · rw [ite_eq_right h3, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  · -- nearest, ties away
    by_cases h0 : r = 0
    · subst h0
      simp
    · rw [ite_eq_right h0]
      by_cases h1 : 2 * r < den
      · rw [ite_eq_left h1, Nat.div_eq_of_lt (by omega)]
        rfl
      · rw [ite_eq_right h1, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  · -- toward zero
    simp
  · -- up
    by_cases h0 : r = 0 <;> cases negative <;> simp [h0]
  · -- down
    by_cases h0 : r = 0 <;> cases negative <;> simp [h0]
  · -- away
    by_cases h0 : r = 0 <;> simp [h0]

/-- Quotient rounding in a deterministic direction is invariant under a common factor. -/
theorem roundQuot_mul_right (mode : Model.IEEERoundingMode) (negative : Bool)
    (entropy n d c : Nat) (hc : 0 < c) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy (n * c) (d * c) =
      Model.Policy.roundQuot mode.toRoundingMode negative entropy n d := by
  have h0 : (n % d * c = 0) ↔ (n % d = 0) := by
    constructor
    · intro h
      rcases Nat.mul_eq_zero.1 h with h | h
      · exact h
      · omega
    · intro h; simp [h]
  have h1 : 2 * (n % d * c) < d * c ↔ 2 * (n % d) < d := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hc
  have h2 : d * c < 2 * (n % d * c) ↔ d < 2 * (n % d) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hc
  unfold Model.Policy.roundQuot
  cases mode <;>
    simp only [Model.IEEERoundingMode.toRoundingMode, Nat.mul_div_mul_right _ _ hc,
      Nat.mul_mod_mul_right, beq_iff_eq, h0, h1, h2, gt_iff_lt]

/-- Quotient rounding in a deterministic direction depends on the quotient as a rational only. -/
theorem roundQuot_eq_of_cross (mode : Model.IEEERoundingMode) (negative : Bool) (entropy : Nat)
    {n₁ d₁ n₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hcross : n₁ * d₂ = n₂ * d₁) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy n₁ d₁ =
      Model.Policy.roundQuot mode.toRoundingMode negative entropy n₂ d₂ := by
  rw [← roundQuot_mul_right mode negative entropy n₁ d₁ d₂ h₂,
    ← roundQuot_mul_right mode negative entropy n₂ d₂ d₁ h₁, hcross, Nat.mul_comm d₁ d₂]

/-- A rounded quotient is the floor or the floor plus one, and the floor for an exact quotient. -/
theorem roundQuot_cases (mode : Model.IEEERoundingMode) (negative : Bool) (entropy n d : Nat) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy n d = n / d ∨
      (n % d ≠ 0 ∧
        Model.Policy.roundQuot mode.toRoundingMode negative entropy n d = n / d + 1) := by
  unfold Model.Policy.roundQuot
  by_cases h0 : n % d = 0
  · left; simp [h0]
  · cases mode <;> simp only [Model.IEEERoundingMode.toRoundingMode, beq_iff_eq, h0, ite_false]
    · split_ifs <;> simp [h0]
    · split_ifs <;> simp [h0]
    · simp
    · cases negative <;> simp [h0]
    · cases negative <;> simp [h0]
    · simp [h0]

/-- A quotient of at least `k` rounds to at least `k`. -/
theorem le_roundQuot (mode : Model.IEEERoundingMode) (negative : Bool) (entropy : Nat)
    {n d k : Nat} (hd : 0 < d) (h : k * d ≤ n) :
    k ≤ Model.Policy.roundQuot mode.toRoundingMode negative entropy n d := by
  have hq : k ≤ n / d := (Nat.le_div_iff_mul_le hd).2 h
  rcases roundQuot_cases mode negative entropy n d with h | ⟨_, h⟩ <;> omega

/-- A quotient of at most `k` rounds to at most `k`. -/
theorem roundQuot_le (mode : Model.IEEERoundingMode) (negative : Bool) (entropy : Nat)
    {n d k : Nat} (hd : 0 < d) (h : n ≤ k * d) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy n d ≤ k := by
  have hq : n / d ≤ k := by
    calc n / d ≤ k * d / d := Nat.div_le_div_right h
      _ = k := Nat.mul_div_cancel _ hd
  rcases roundQuot_cases mode negative entropy n d with h' | ⟨hrem, h'⟩
  · omega
  · have hlt : n / d < k := by
      rcases Nat.lt_or_ge (n / d) k with hlt | hge
      · exact hlt
      · exfalso
        have hk : n / d = k := by omega
        have hmul : d * (n / d) + n % d = n := Nat.div_add_mod n d
        rw [hk, Nat.mul_comm] at hmul
        omega
    omega

/-- The direction of a magnitude below half the least subnormal, for the six directions. -/
theorem tinyRoundsMagnitudeUp?_toRoundingMode (mode : Model.IEEERoundingMode) (negative : Bool) :
    Model.Policy.tinyRoundsMagnitudeUp? mode.toRoundingMode negative =
      some (mode.roundsAwayFromZero negative) := by
  cases mode <;> rfl

/-- A positive quotient below one half rounds to zero or to one, by the direction alone. -/
theorem roundQuot_tiny (mode : Model.IEEERoundingMode) (negative : Bool) (entropy : Nat)
    {n d : Nat} (hn : n ≠ 0) (h : 2 * n < d) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy n d =
      if mode.roundsAwayFromZero negative then 1 else 0 := by
  have hq : n / d = 0 := Nat.div_eq_of_lt (by omega)
  have hr : n % d = n := Nat.mod_eq_of_lt (by omega)
  unfold Model.Policy.roundQuot
  cases mode <;> cases negative <;>
    simp [Model.IEEERoundingMode.toRoundingMode, Model.IEEERoundingMode.roundsAwayFromZero, hq,
      hr, hn, h]

/-! ## Encodings of packed fields -/

/-- The encoding of in-range fields: sign bit, exponent field and fraction field side by side. -/
theorem toNatBits_ofFields (fmt : FloatFormat) (negative : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth) (hfraction : fraction < 2 ^ fmt.fracWidth) :
    (Model.ofFields fmt negative exponent fraction).toNatBits =
      (if negative then 2 ^ signPos fmt else 0) +
        (exponent * 2 ^ fmt.fracWidth + fraction) := by
  unfold Model.ofFields Model.ofBits Model.toNatBits
  rw [Model.mkBits_eq_internal_apply]
  unfold Model.Internal.mkBits
  rw [BitVec.toNat_ofNatLT]
  have he : exponent &&& FloatFormat.expAllOnesNat fmt = exponent := by
    unfold FloatFormat.expAllOnesNat
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hexponent]
  have hf : fraction &&& FloatFormat.fracMaskNat fmt = fraction := by
    unfold FloatFormat.fracMaskNat
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hfraction]
  rw [he, hf]
  have hlow : exponent * 2 ^ fmt.fracWidth + fraction < 2 ^ signPos fmt := by
    unfold signPos
    rw [Nat.pow_add]
    calc exponent * 2 ^ fmt.fracWidth + fraction
        < exponent * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by omega
      _ = (exponent + 1) * 2 ^ fmt.fracWidth := by ring
      _ ≤ 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := Nat.mul_le_mul_right _ hexponent
  have hinner : Nat.shiftLeft exponent fmt.fracWidth ||| fraction =
      exponent * 2 ^ fmt.fracWidth + fraction := by
    change exponent <<< fmt.fracWidth ||| fraction = _
    rw [← Nat.shiftLeft_add_eq_or_of_lt hfraction, Nat.shiftLeft_eq]
  rw [Nat.lor_assoc, hinner]
  cases negative
  · simp
  · simp only [ite_true]
    change 1 <<< signPos fmt ||| _ = _
    rw [← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq, Nat.one_mul]

/-- `overflowWord` is the encoding of the overflow result of the model, for every format and
both signs. -/
theorem overflowWord_eq (fmt : FloatFormat) (negative : Bool) :
    overflowWord fmt negative = (Model.nativeOverflow fmt negative).toNatBits := by
  have hE : fmt.expAllOnesNat < 2 ^ fmt.expWidth :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hF : fmt.fracMaskNat < 2 ^ fmt.fracWidth :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  unfold overflowWord Model.nativeOverflow
  cases h : fmt.encoding
  · cases negative
    · simp only [Bool.false_eq_true, ite_false, Model.posInf, Model.ofBits, Model.toNatBits,
        FloatFormat.expMask, FloatFormat.ofWordNat, BitVec.toNat_ofNat, FloatFormat.expMaskNat,
        FloatFormat.expAllOnesNat]
    · simp only [ite_true, Model.negInf, Model.ofBits, Model.toNatBits, FloatFormat.expMask,
        FloatFormat.signMask, FloatFormat.ofWordNat, BitVec.toNat_or, BitVec.toNat_ofNat,
        FloatFormat.expMaskNat, FloatFormat.expAllOnesNat, FloatFormat.signMaskNat_eq_two_pow]
  · simp only [Model.propagatedNaN, h]
    rw [toNatBits_ofFields fmt negative _ _ hE hF]
    cases negative <;> rfl
  · simp [Model.invalidResult, h, signPos, FloatFormat.signMaskNat_eq_two_pow]
  · simp only [Model.maxFinite]
    rw [toNatBits_ofFields fmt negative _ _ fmt.maxFiniteExpField_lt_two_pow
      fmt.maxFiniteFracField_lt_two_pow]
    cases negative <;> rfl

/-- `roundOverflowWord` is the encoding of the directed overflow result of the model, for every
format, rounding direction and sign. -/
theorem roundOverflowWord_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (negative : Bool) :
    roundOverflowWord fmt mode negative =
      (Model.directedOverflow fmt negative
        (mode.overflowRoundsMagnitudeUp negative)).toNatBits := by
  unfold roundOverflowWord Model.directedOverflow
  cases mode.overflowRoundsMagnitudeUp negative
  · simp only [Bool.false_eq_true, ite_false, Model.maxFinite]
    rw [toNatBits_ofFields fmt negative _ _ fmt.maxFiniteExpField_lt_two_pow
      fmt.maxFiniteFracField_lt_two_pow]
    cases negative <;> rfl
  · simp only [ite_true]
    exact overflowWord_eq fmt negative

/-- A word is at most `maxFinite` exactly when its fields are, in lexicographic order. -/
theorem le_maxFinite_iff (fmt : FloatFormat) (exponent fraction : Nat)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    exponent * 2 ^ fmt.fracWidth + fraction ≤ maxFinite fmt ↔
      exponent < fmt.maxFiniteExpField ∨
        (exponent = fmt.maxFiniteExpField ∧ fraction ≤ fmt.maxFiniteFracField) := by
  have hmax := fmt.maxFiniteFracField_lt_two_pow
  unfold maxFinite
  generalize 2 ^ fmt.fracWidth = F at hfraction hmax ⊢
  rcases Nat.lt_trichotomy exponent fmt.maxFiniteExpField with h | h | h
  · have : (exponent + 1) * F ≤ fmt.maxFiniteExpField * F := Nat.mul_le_mul_right F h
    have hexpand : (exponent + 1) * F = exponent * F + F := by ring
    constructor
    · intro _; exact Or.inl h
    · intro _; omega
  · subst h
    constructor
    · intro hle; exact Or.inr ⟨rfl, by omega⟩
    · rintro (h | ⟨_, h⟩) <;> omega
  · have : (fmt.maxFiniteExpField + 1) * F ≤ exponent * F := Nat.mul_le_mul_right F h
    have hexpand : (fmt.maxFiniteExpField + 1) * F = fmt.maxFiniteExpField * F + F := by ring
    constructor
    · intro hle; omega
    · rintro (h' | ⟨h', _⟩) <;> omega

/-- A `Bool.casesOn` on naturals is an `if`. -/
private theorem casesOn_eq_ite (c : Bool) (e t : Nat) :
    Bool.casesOn (motive := fun _ => Nat) c e t = if c then t else e := by
  cases c <;> rfl

/-- `pack` as a case distinction on its guard, the rounded significand and the range. -/
theorem pack_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign t mantissa guard special : Nat) :
    pack fmt mode sign zeroSign t mantissa guard special =
      if guard ≠ 0 then special
      else if mantissa = 0 then zeroWord fmt (decide (zeroSign ≠ 0))
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        sign * 2 ^ signPos fmt + (t * 2 ^ fmt.fracWidth + mantissa)
      else roundOverflowWord fmt mode (decide (zeroSign ≠ 0)) := by
  unfold pack packRare maxFiniteSucc
  simp only [casesOn_eq_ite, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq',
    Nat.shiftLeft_eq, Nat.ble_eq, Nat.beq_eq]
  by_cases hg : guard = 0
  · subst hg
    by_cases hM : mantissa = 0
    · subst hM
      have hnot : ¬ (t * 2 ^ fmt.fracWidth + (maxFinite fmt + 1) ≤ maxFinite fmt) := by omega
      by_cases hz : zeroSign = 0 <;> simp [hnot, hz]
    · have h1 : 1 - mantissa + 0 = 0 := by omega
      by_cases hle : t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt
      · simp [h1, hle, hM]
      · by_cases hz : zeroSign = 0 <;> simp [h1, hle, hM, hz]
  · have hnot : ¬ (t * 2 ^ fmt.fracWidth + mantissa +
        (1 - mantissa + guard) * (maxFinite fmt + 1) ≤ maxFinite fmt) := by
      have : maxFinite fmt + 1 ≤ (1 - mantissa + guard) * (maxFinite fmt + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    simp [hnot, hg]

/-- The encoding of a packed subnormal significand `mantissa ≤ 2 ^ fracWidth`. -/
theorem packRoundedSubnormal_bits (fmt : FloatFormat) (negative : Bool) (mantissa : Nat)
    (hmantissa : mantissa ≤ 2 ^ fmt.fracWidth) :
    (Model.packRoundedSubnormal fmt negative (Model.zero fmt negative) mantissa).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else (if negative then 2 ^ signPos fmt else 0) + mantissa := by
  have hone : 1 < 2 ^ fmt.expWidth :=
    Nat.one_lt_two_pow (by have := fmt.expWidth_ge_two; omega)
  unfold Model.packRoundedSubnormal
  simp only [beq_iff_eq, Model.pow2_eq_two_pow, ge_iff_le]
  by_cases h0 : mantissa = 0
  · simp [h0, zeroWord_eq]
  · simp only [h0, ite_false]
    by_cases hfull : 2 ^ fmt.fracWidth ≤ mantissa
    · have heq : mantissa = 2 ^ fmt.fracWidth := by omega
      rw [ite_eq_left hfull, toNatBits_ofFields fmt negative 1 0 hone (Nat.two_pow_pos _), heq]
      simp
    · rw [ite_eq_right hfull,
        toNatBits_ofFields fmt negative 0 mantissa (Nat.two_pow_pos _) (by omega)]
      simp

/--
The encoding of a packed normal significand `2 ^ fracWidth ≤ mantissa ≤ 2 ^ (fracWidth + 1)`
whose exponent field before the rounding carry is `t + 1`, with any overflow result.
-/
theorem packRoundedNormal_bits (fmt : FloatFormat) (negative : Bool) (overflow : Model fmt)
    (t mantissa : Nat) (total : Int) (htotal : total = (t : Int) + 1 - fmt.exponentBias)
    (hlow : 2 ^ fmt.fracWidth ≤ mantissa) (hhigh : mantissa ≤ 2 ^ (fmt.fracWidth + 1)) :
    (Model.packRoundedNormal fmt negative overflow total mantissa).toNatBits =
      if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else overflow.toNatBits := by
  have hsplit := Nat.two_pow_succ fmt.fracWidth
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hexpMax := fmt.maxFiniteExpField_lt_two_pow
  subst htotal
  unfold Model.packRoundedNormal
  simp only [Model.pow2_eq_two_pow, beq_iff_eq, FloatFormat.maxNormalExponent,
    Int.ofNat_eq_natCast, gt_iff_lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  by_cases hcarry : mantissa = 2 ^ (fmt.fracWidth + 1)
  · -- The rounding carry moves to the next exponent with a zero fraction.
    have hword : t * 2 ^ fmt.fracWidth + mantissa = (t + 2) * 2 ^ fmt.fracWidth + 0 := by
      rw [hcarry, hsplit]; ring
    have hiff := le_maxFinite_iff fmt (t + 2) 0 hpos
    simp only [hcarry, ite_true]
    rw [← hcarry, hword]
    by_cases hover : t + 2 ≤ fmt.maxFiniteExpField
    · have hle : (t + 2) * 2 ^ fmt.fracWidth + 0 ≤ maxFinite fmt := hiff.2 (by omega)
      have h1 : ¬ ((fmt.maxFiniteExpField : Int) - fmt.exponentBias <
          (t : Int) + 1 - fmt.exponentBias + 1) := by omega
      have henc : ((t : Int) + 1 - fmt.exponentBias + 1 + fmt.exponentBias).toNat = t + 2 := by
        omega
      rw [ite_eq_right h1, henc, ite_eq_left hle]
      have h2 : ¬ (fmt.maxFiniteExpField < t + 2 ∨
          t + 2 = fmt.maxFiniteExpField ∧
            fmt.maxFiniteFracField < 2 ^ fmt.fracWidth - 2 ^ fmt.fracWidth) := by omega
      rw [ite_eq_right h2, Nat.sub_self,
        toNatBits_ofFields fmt negative (t + 2) 0 (by omega) hpos]
    · have hnle : ¬ ((t + 2) * 2 ^ fmt.fracWidth + 0 ≤ maxFinite fmt) := fun h => by
        rcases hiff.1 h with h | ⟨h, _⟩ <;> omega
      have h1 : (fmt.maxFiniteExpField : Int) - fmt.exponentBias <
          (t : Int) + 1 - fmt.exponentBias + 1 := by omega
      rw [ite_eq_left h1, ite_eq_right hnle]
  · have hlt : mantissa - 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth := by omega
    have hword : t * 2 ^ fmt.fracWidth + mantissa =
        (t + 1) * 2 ^ fmt.fracWidth + (mantissa - 2 ^ fmt.fracWidth) := by
      have : (t + 1) * 2 ^ fmt.fracWidth = t * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by ring
      omega
    have hiff := le_maxFinite_iff fmt (t + 1) (mantissa - 2 ^ fmt.fracWidth) hlt
    simp only [hcarry, ite_false]
    rw [hword]
    by_cases hle : (t + 1) * 2 ^ fmt.fracWidth + (mantissa - 2 ^ fmt.fracWidth) ≤ maxFinite fmt
    · have hfields := hiff.1 hle
      have h1 : ¬ ((fmt.maxFiniteExpField : Int) - fmt.exponentBias <
          (t : Int) + 1 - fmt.exponentBias) := by omega
      have henc : ((t : Int) + 1 - fmt.exponentBias + fmt.exponentBias).toNat = t + 1 := by omega
      rw [ite_eq_right h1, henc, ite_eq_left hle]
      have h2 : ¬ (fmt.maxFiniteExpField < t + 1 ∨
          t + 1 = fmt.maxFiniteExpField ∧
            fmt.maxFiniteFracField < mantissa - 2 ^ fmt.fracWidth) := by omega
      rw [ite_eq_right h2,
        toNatBits_ofFields fmt negative (t + 1) (mantissa - 2 ^ fmt.fracWidth) (by omega) hlt]
    · rw [ite_eq_right hle]
      by_cases h1 : (fmt.maxFiniteExpField : Int) - fmt.exponentBias <
          (t : Int) + 1 - fmt.exponentBias
      · rw [ite_eq_left h1]
      · have henc : ((t : Int) + 1 - fmt.exponentBias + fmt.exponentBias).toNat = t + 1 := by
          omega
        have h2 : fmt.maxFiniteExpField < t + 1 ∨
            t + 1 = fmt.maxFiniteExpField ∧
              fmt.maxFiniteFracField < mantissa - 2 ^ fmt.fracWidth := by
          by_contra hcon
          exact hle (hiff.2 (by omega))
        rw [ite_eq_right h1, henc, ite_eq_left h2]

/-! ## The rounder computes the reference rounding in every direction -/

/--
Two quotients with the same value, from one identity between them: if
`num * 2 ^ A = mag * 2 ^ B * den` and the exponents balance, then
`(num * 2 ^ p) / (den * 2 ^ r) = (mag * 2 ^ q) / 2 ^ s` as a cross product.
-/
private theorem cross_of_balance {num den mag A B p s q r : Nat}
    (h : num * 2 ^ A = mag * 2 ^ B * den) (hbalance : B + p + s = q + r + A) :
    num * 2 ^ p * 2 ^ s = mag * 2 ^ q * (den * 2 ^ r) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos A)
  have hpow : 2 ^ B * 2 ^ p * 2 ^ s = 2 ^ q * 2 ^ r * 2 ^ A := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, hbalance]
  calc num * 2 ^ p * 2 ^ s * 2 ^ A = num * 2 ^ A * (2 ^ p * 2 ^ s) := by ring
    _ = mag * 2 ^ B * den * (2 ^ p * 2 ^ s) := by rw [h]
    _ = mag * den * (2 ^ B * 2 ^ p * 2 ^ s) := by ring
    _ = mag * den * (2 ^ q * 2 ^ r * 2 ^ A) := by rw [hpow]
    _ = mag * 2 ^ q * (den * 2 ^ r) * 2 ^ A := by ring

/--
The encoding of the policy rounding of a positive quotient `num / den` whose value is
`mag * 2 ^ (Ep - Em) * 2 ^ fmt.minSubnormalExponent` and whose leading bit is bit `L` of `mag`, in
the quantities `round` computes: `t` is the exponent field minus one (zero below the normal range)
and `mantissa` the magnitude in units of that exponent, rounded in the direction `mode`.
-/
theorem roundRatPolicy_bits (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (entropy : Nat)
    (negative : Bool) (num den : Nat) (hden : den ≠ 0) (mag L Ep Em : Nat)
    (hL1 : 2 ^ L ≤ mag) (hL2 : mag < 2 ^ (L + 1))
    (hlog : Numerics.RationalBinary.floorLog2 num den =
      (L : Int) + ((Ep : Int) - Em + fmt.minSubnormalExponent))
    (hscale : num * 2 ^ (Em + fmt.subnormalAlignExp) = mag * 2 ^ Ep * den)
    (t mantissa : Nat) (ht : t = L + 1 + Ep - (Em + fmt.fracWidth + 1))
    (hmantissa : mantissa = Model.Policy.roundQuot mode.toRoundingMode negative entropy
      (mag <<< (Ep - (t + Em))) (2 ^ (t + Em - Ep))) :
    (Model.Policy.roundRatGeneralOfDenNeZero fmt
        { rounding := mode.toRoundingMode, overflow := .native, underflow := .gradual }
        entropy negative num den hden).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else roundOverflowWord fmt mode negative := by
  have hmag : mag ≠ 0 := by have := Nat.two_pow_pos L; omega
  have hdenPos : 0 < den := Nat.pos_of_ne_zero hden
  have hnum : num ≠ 0 := by
    rintro rfl
    have hposRight : 0 < mag * 2 ^ Ep * den :=
      Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hmag) (Nat.two_pow_pos _)) hdenPos
    rw [Nat.zero_mul] at hscale
    omega
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hexpPos := fmt.maxFiniteExpField_pos
  have hfracMax := fmt.maxFiniteFracField_lt_two_pow
  have hbias := fmt.exponentBias_pos
  have hmaxge : 2 ^ fmt.fracWidth ≤ maxFinite fmt := by
    unfold maxFinite
    have : 1 * 2 ^ fmt.fracWidth ≤ fmt.maxFiniteExpField * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ hexpPos
    omega
  have hK : fmt.subnormalAlignExp = fmt.exponentBias + fmt.fracWidth - 1 := rfl
  have hoverflow : Model.Policy.overflowResult fmt .native mode.toRoundingMode negative =
      Model.directedOverflow fmt negative (mode.overflowRoundsMagnitudeUp negative) := by
    have hup : Model.Policy.overflowRoundsMagnitudeUp mode.toRoundingMode negative =
        mode.overflowRoundsMagnitudeUp negative := by
      cases mode <;> rfl
    rw [← hup]
    rfl
  unfold Model.Policy.roundRatGeneralOfDenNeZero
  simp only [beq_iff_eq, hnum, ite_false, hlog, hoverflow, Model.Policy.applyUnderflow,
    FloatFormat.maxNormalExponent, FloatFormat.minNormalExponent,
    FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast, gt_iff_lt,
    tinyRoundsMagnitudeUp?_toRoundingMode]
  by_cases hover : (fmt.maxFiniteExpField : Int) - fmt.exponentBias <
      (L : Int) + ((Ep : Int) - Em + (1 - fmt.exponentBias - fmt.fracWidth))
  · -- The leading bit is above the largest finite exponent.
    have ht' : fmt.maxFiniteExpField ≤ t := by omega
    have hsr : t + Em - Ep = L - fmt.fracWidth := by omega
    have hsl : Ep - (t + Em) = fmt.fracWidth - L := by omega
    have hlow : 2 ^ fmt.fracWidth ≤ mantissa := by
      rw [hmantissa, hsr, hsl]
      refine le_roundQuot mode negative entropy (Nat.two_pow_pos _) ?_
      rw [Nat.shiftLeft_eq, ← Nat.pow_add]
      by_cases h : fmt.fracWidth ≤ L
      · rw [show fmt.fracWidth - L = 0 by omega, Nat.pow_zero, Nat.mul_one,
          show fmt.fracWidth + (L - fmt.fracWidth) = L by omega]
        exact hL1
      · rw [show L - fmt.fracWidth = 0 by omega, Nat.add_zero]
        calc 2 ^ fmt.fracWidth = 2 ^ L * 2 ^ (fmt.fracWidth - L) := by
              rw [← Nat.pow_add]; congr 1; omega
          _ ≤ mag * 2 ^ (fmt.fracWidth - L) := Nat.mul_le_mul_right _ hL1
    have hM0 : mantissa ≠ 0 := by omega
    have hnle : ¬ (t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt) := by
      intro hle
      unfold maxFinite at hle
      have := Nat.mul_le_mul_right (2 ^ fmt.fracWidth) ht'
      omega
    rw [ite_eq_left hover, ite_eq_right hM0, ite_eq_right hnle]
    exact (roundOverflowWord_eq fmt mode negative).symm
  · rw [ite_eq_right hover]
    by_cases hsub : (L : Int) + ((Ep : Int) - Em + (1 - fmt.exponentBias - fmt.fracWidth)) <
        1 - fmt.exponentBias
    · -- Below the normal range the quantum is the least subnormal.
      have ht0 : t = 0 := by omega
      subst ht0
      rw [ite_eq_left hsub]
      have hbound : mag <<< (Ep - (0 + Em)) ≤ 2 ^ fmt.fracWidth * 2 ^ (0 + Em - Ep) := by
        rw [Nat.shiftLeft_eq, ← Nat.pow_add]
        calc mag * 2 ^ (Ep - (0 + Em)) ≤ 2 ^ (L + 1) * 2 ^ (Ep - (0 + Em)) :=
              Nat.mul_le_mul_right _ (le_of_lt hL2)
          _ = 2 ^ (L + 1 + (Ep - (0 + Em))) := (Nat.pow_add 2 _ _).symm
          _ ≤ 2 ^ (fmt.fracWidth + (0 + Em - Ep)) :=
              Nat.pow_le_pow_right (by decide) (by omega)
      have hMle : mantissa ≤ 2 ^ fmt.fracWidth := by
        rw [hmantissa]
        exact roundQuot_le mode negative entropy (Nat.two_pow_pos _) hbound
      have hfinish : ∀ fraction : Nat, mantissa = fraction →
          (Model.packRoundedSubnormal fmt negative (Model.zero fmt negative) fraction).toNatBits =
            if mantissa = 0 then zeroWord fmt negative
            else if 0 * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
              (if negative then 2 ^ signPos fmt else 0) + (0 * 2 ^ fmt.fracWidth + mantissa)
            else roundOverflowWord fmt mode negative := by
        intro fraction hM
        rw [packRoundedSubnormal_bits fmt negative _ (hM ▸ hMle), ← hM]
        by_cases hM0 : mantissa = 0
        · simp [hM0]
        · have hle : mantissa ≤ maxFinite fmt := by omega
          simp [hM0, hle]
      by_cases htiny : (L : Int) + ((Ep : Int) - Em + (1 - fmt.exponentBias - fmt.fracWidth)) +
          1 < 1 - fmt.exponentBias - fmt.fracWidth
      · -- Below half the least subnormal the direction alone decides.
        have hhalf : 2 * mag <<< (Ep - (0 + Em)) < 2 ^ (0 + Em - Ep) := by
          rw [show Ep - (0 + Em) = 0 by omega, Nat.shiftLeft_zero]
          calc 2 * mag < 2 * 2 ^ (L + 1) := by omega
            _ = 2 ^ (L + 2) := by rw [Nat.pow_succ 2 (L + 1)]; ring
            _ ≤ 2 ^ (0 + Em - Ep) := Nat.pow_le_pow_right (by decide) (by omega)
        have hshift0 : mag <<< (Ep - (0 + Em)) ≠ 0 := by simp [Nat.shiftLeft_eq, hmag]
        have hMval := roundQuot_tiny mode negative entropy hshift0 hhalf
        rw [← hmantissa] at hMval
        rw [ite_eq_left htiny]
        cases hdir : mode.roundsAwayFromZero negative
        · have hM0 : mantissa = 0 := by simpa [hdir] using hMval
          simp [hM0, zeroWord_eq]
        · have hM1 : mantissa = 1 := by simpa [hdir] using hMval
          have hone : 1 < 2 ^ fmt.fracWidth :=
            Nat.one_lt_two_pow (by have := fmt.fracWidth_pos; omega)
          have hle : 0 * 2 ^ fmt.fracWidth + 1 ≤ maxFinite fmt := by omega
          simp only [hM1]
          rw [toNatBits_ofFields fmt negative 0 1 (Nat.two_pow_pos _) hone,
            ite_eq_right (by decide : ¬ (1 = 0)), ite_eq_left hle]
      · rw [ite_eq_right htiny]
        refine hfinish _ ?_
        rw [hmantissa]
        refine roundQuot_eq_of_cross mode negative entropy (Nat.two_pow_pos _) hdenPos ?_
        have := cross_of_balance (p := fmt.exponentBias + fmt.fracWidth - 1)
          (s := 0 + Em - Ep) (q := Ep - (0 + Em)) (r := 0) hscale (by rw [hK]; omega)
        rw [Nat.pow_zero, Nat.mul_one] at this
        simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        exact this.symm
    · -- In the normal range `fracWidth` bits are kept below the leading one.
      have hsr : t + Em - Ep = L - fmt.fracWidth := by omega
      have hsl : Ep - (t + Em) = fmt.fracWidth - L := by lia
      rw [hsr, hsl] at hmantissa
      have hlow : 2 ^ fmt.fracWidth ≤ mantissa := by
        rw [hmantissa]
        refine le_roundQuot mode negative entropy (Nat.two_pow_pos _) ?_
        rw [Nat.shiftLeft_eq, ← Nat.pow_add]
        by_cases h : fmt.fracWidth ≤ L
        · rw [show fmt.fracWidth - L = 0 by omega, Nat.pow_zero, Nat.mul_one,
            show fmt.fracWidth + (L - fmt.fracWidth) = L by omega]
          exact hL1
        · rw [show L - fmt.fracWidth = 0 by omega, Nat.add_zero]
          calc 2 ^ fmt.fracWidth = 2 ^ L * 2 ^ (fmt.fracWidth - L) := by
                rw [← Nat.pow_add]; congr 1; omega
            _ ≤ mag * 2 ^ (fmt.fracWidth - L) := Nat.mul_le_mul_right _ hL1
      have hhigh : mantissa ≤ 2 ^ (fmt.fracWidth + 1) := by
        rw [hmantissa]
        refine roundQuot_le mode negative entropy (Nat.two_pow_pos _) ?_
        rw [Nat.shiftLeft_eq, ← Nat.pow_add]
        calc mag * 2 ^ (fmt.fracWidth - L) ≤ 2 ^ (L + 1) * 2 ^ (fmt.fracWidth - L) :=
              Nat.mul_le_mul_right _ (le_of_lt hL2)
          _ = 2 ^ (L + 1 + (fmt.fracWidth - L)) := (Nat.pow_add 2 _ _).symm
          _ ≤ 2 ^ (fmt.fracWidth + 1 + (L - fmt.fracWidth)) :=
              Nat.pow_le_pow_right (by decide) (by omega)
      have hM0 : mantissa ≠ 0 := by omega
      rw [ite_eq_right hsub, ite_eq_right hM0, roundOverflowWord_eq]
      have hrounded : ∀ scaledNum scaledDen : Nat, 0 < scaledDen →
          scaledNum * 2 ^ (L - fmt.fracWidth) = mag * 2 ^ (fmt.fracWidth - L) * scaledDen →
          Model.Policy.roundQuot mode.toRoundingMode negative entropy scaledNum scaledDen =
            mantissa := by
        intro scaledNum scaledDen hposDen hcross
        rw [hmantissa, Nat.shiftLeft_eq]
        exact roundQuot_eq_of_cross mode negative entropy hposDen (Nat.two_pow_pos _) hcross
      rcases hshift : ((fmt.fracWidth : Int) -
          ((L : Int) + ((Ep : Int) - Em + (1 - fmt.exponentBias - fmt.fracWidth)))) with a | a
      · have ha : (a : Int) = (fmt.fracWidth : Int) -
            ((L : Int) + ((Ep : Int) - Em + (1 - fmt.exponentBias - fmt.fracWidth))) := by
          rw [hshift]; rfl
        simp only [Nat.shiftLeft_eq']
        rw [hrounded (num <<< a) den hdenPos (by
          rw [Nat.shiftLeft_eq]
          have := cross_of_balance (p := a) (s := L - fmt.fracWidth) (q := fmt.fracWidth - L)
            (r := 0) hscale (by rw [hK]; omega)
          rw [Nat.pow_zero, Nat.mul_one] at this
          exact this)]
        exact packRoundedNormal_bits fmt negative _ t mantissa _ (by omega) hlow hhigh
      · simp only [Nat.shiftLeft_eq']
        rw [hrounded num (den <<< (a + 1)) (by rw [Nat.shiftLeft_eq]; positivity) (by
          rw [Nat.shiftLeft_eq]
          have := cross_of_balance (p := 0) (s := L - fmt.fracWidth) (q := fmt.fracWidth - L)
            (r := a + 1) hscale (by rw [hK]; lia)
          rw [Nat.pow_zero, Nat.mul_one] at this
          exact this)]
        exact packRoundedNormal_bits fmt negative _ t mantissa _ (by lia) hlow hhigh

/-- A zero significand rounds to the zero of its sign in every direction. -/
theorem roundDyadic_zero (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (exponent : Int) :
    Model.Internal.Directed.roundDyadic fmt mode ⟨negative, 0, exponent⟩ =
      Model.zero fmt negative := by
  rw [← Model.Policy.roundDyadicGeneral_toRoundingMode fmt mode 0,
    Model.Policy.roundDyadicGeneral_eq_roundRatGeneralOfDenNeZero]
  have hscaled : (Numerics.RationalBinary.scaleByPowerOfTwo 0 1 exponent).1 = 0 := by
    cases exponent <;> simp [Numerics.RationalBinary.scaleByPowerOfTwo]
  simp [Model.Policy.roundRatGeneralOfDenNeZero, hscaled, Model.Policy.applyUnderflow]

/--
The encoding of the reference rounding of a nonzero magnitude in the direction `mode`, in the
quantities `round` computes: `t` is the exponent field minus one (zero below the normal range) and
`mantissa` the magnitude in units of that exponent, rounded in the direction `mode`.
-/
theorem roundDyadic_bits (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (entropy : Nat)
    (negative : Bool) (mag Ep Em : Nat) (hmag : mag ≠ 0) (t mantissa : Nat)
    (ht : t = mag.log2 + 1 + Ep - (Em + fmt.fracWidth + 1))
    (hmantissa : mantissa = Model.Policy.roundQuot mode.toRoundingMode negative entropy
      (mag <<< (Ep - (t + Em))) (2 ^ (t + Em - Ep))) :
    (Model.Internal.Directed.roundDyadic fmt mode
        ⟨negative, mag, (Ep : Int) - Em + fmt.minSubnormalExponent⟩).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else roundOverflowWord fmt mode negative := by
  have hbias := fmt.exponentBias_pos
  rw [← Model.Policy.roundDyadicGeneral_toRoundingMode fmt mode entropy,
    Model.Policy.roundDyadicGeneral_eq_roundRatGeneralOfDenNeZero]
  dsimp only
  refine roundRatPolicy_bits fmt mode entropy negative _ _ _ mag mag.log2 Ep Em
    (Nat.log2_self_le hmag) Nat.lt_log2_self ?_ ?_ t mantissa ht hmantissa
  · have := Model.floorLog2_scaleByPowerOfTwo_den_one mag
      ((Ep : Int) - Em + fmt.minSubnormalExponent) hmag
    dsimp only at this
    rw [this, Int.ofNat_eq_natCast]
  · have hK : fmt.subnormalAlignExp = fmt.exponentBias + fmt.fracWidth - 1 := rfl
    rcases hexp : ((Ep : Int) - Em + fmt.minSubnormalExponent) with s | s
    · have hs : (s : Int) = (Ep : Int) - Em + fmt.minSubnormalExponent := by rw [hexp]; rfl
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast] at hs
      simp only [Numerics.RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
        Nat.mul_one]
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      rw [hK]; omega
    · have hs : ((s : Int) + 1) = -((Ep : Int) - Em + fmt.minSubnormalExponent) := by
        rw [hexp, Int.negSucc_eq]; omega
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast] at hs
      simp only [Numerics.RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
        Nat.one_mul]
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      rw [hK]; omega

/--
The nearest-even case of `roundDyadic_bits`, for `Model.roundDyadicGeneral` and with the rounded
significand written as a rounding shift.
-/
theorem roundDyadicGeneral_bits (fmt : FloatFormat) (negative : Bool) (mag Ep Em : Nat)
    (hmag : mag ≠ 0) (t mantissa : Nat)
    (ht : t = mag.log2 + 1 + Ep - (Em + fmt.fracWidth + 1))
    (hmantissa : mantissa = roundShiftRightEven (mag <<< (Ep - (t + Em))) (t + Em - Ep)) :
    (Model.roundDyadicGeneral fmt
        ⟨negative, mag, (Ep : Int) - Em + fmt.minSubnormalExponent⟩).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else overflowWord fmt negative := by
  rw [Model.roundDyadicGeneral_eq_roundDyadic]
  exact roundDyadic_bits fmt .nearest 0 negative mag Ep Em hmag t mantissa ht (by
    rw [hmantissa, roundShiftRightEven_eq_roundQuotientEven]
    exact (Model.Policy.roundQuot_nearest_eq_roundQuotientEven negative 0 _ _
      (Nat.two_pow_pos _).ne').symm)

/--
`round` computes the encoding of the reference rounding `Model.Internal.Directed.roundDyadic`,
for every format descriptor and every rounding direction.

`d` is the exact dyadic value: its significand is `mag < 2 ^ B`, its sign is `zeroSign`, and for a
nonzero magnitude its exponent is `Ep - Em + fmt.minSubnormalExponent` and `sign` agrees with
`zeroSign`. The guard is zero, so `special` is not used.
-/
theorem round_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (B sign zeroSign mag Ep Em special : Nat) (d : Numerics.Dyadic)
    (hmag : mag < 2 ^ B) (hsig : d.significand = mag)
    (hzero : zeroSign = signNat d.negative)
    (hexp : mag ≠ 0 → d.exponent = (Ep : Int) - Em + fmt.minSubnormalExponent)
    (hsign : mag ≠ 0 → sign = zeroSign) :
    round fmt mode B sign zeroSign mag Ep Em 0 special =
      (Model.Internal.Directed.roundDyadic fmt mode d).toNatBits := by
  obtain ⟨negative, significand, exponent⟩ := d
  dsimp only at hsig hzero hexp
  subst hsig
  have hzs : decide (zeroSign ≠ 0) = negative := by
    subst hzero
    cases negative <;> simp [signNat]
  unfold round
  rw [roundAt_def]
  unfold roundQuotient
  rw [bitLength_eq hmag]
  simp only [pack_eq, Nat.add_eq, Nat.sub_eq, div_def, mod_def, Nat.pow_eq, Nat.shiftLeft_eq',
    ne_eq, not_true_eq_false, ite_false, hzs]
  by_cases h0 : significand = 0
  · subst h0
    have hup : ∀ den : Nat, roundUp mode sign 0 0 den = 0 := by
      intro den
      unfold roundUp
      cases mode <;> simp [div_def]
    simp [roundDyadic_zero, hup, zeroWord_eq]
  · have hexp' := hexp h0
    have hsign' := hsign h0
    subst hexp'
    have hsw : sign = signNat negative := by rw [hsign', hzero]
    subst hsw
    have hsw2 : signNat negative * 2 ^ signPos fmt = if negative then 2 ^ signPos fmt else 0 := by
      cases negative <;> simp [signNat]
    simp only [h0, ite_false]
    rw [roundDyadic_bits fmt mode 0 negative significand Ep Em h0 _ _ rfl rfl,
      ← roundUp_eq mode negative 0 _ _ (Nat.two_pow_pos _), hsw2]

/-- A nonzero guard selects the caller's special result. -/
theorem round_guard (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (B sign zeroSign mag Ep Em guard special : Nat) (hguard : guard ≠ 0) :
    round fmt mode B sign zeroSign mag Ep Em guard special = special := by
  unfold round
  rw [roundAt_def]
  unfold roundQuotient
  simp only [pack_eq, ne_eq, hguard, not_false_eq_true, ite_true]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
