/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Compare

import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Tactic.Positivity

/-!
# Kernel path: the IEEE status of one rounding

`roundStatus fmt mode sign E Em w` is the status of delivering the word `w` for an exact dyadic
result, as one number: the five IEEE exception flags in its low bits (`decodeStatus`) and the
ternary value above them (`decodeTernary`). The exact result has the sign `sign` and the
magnitude `E * 2 ^ (fmt.minSubnormalExponent - Em - 2)`.

The function makes the comparisons that the reference `Model.dyadicRoundingStatus` and
`Model.dyadicTernary` make, on naturals: the exact magnitude against the overflow and underflow
thresholds of the format in the direction `mode`, and against the delivered value.
`roundStatus_eq` proves that the decoded flags and ternary value are the reference ones, for
every format descriptor, every rounding direction, every exact value and every delivered word.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- One when `b < a`. -/
def gtFlag (a b : Nat) : Nat :=
  Nat.sub 1 (Nat.sub 1 (Nat.sub a b))

/-- One when `b ≤ a`. -/
def geFlag (a b : Nat) : Nat :=
  Nat.sub 1 (Nat.sub b a)

/-- The significand of the largest finite value. -/
def maxSignificand (fmt : FloatFormat) : Nat :=
  2 ^ fmt.fracWidth + fmt.maxFiniteFracField

kernel_constant maxSignificand

/--
One when rounding the exact magnitude `E` with sign `sign` in the direction `mode` overflows:
`Model.dyadicRoundingOverflows` (`overflowFlag_eq`).
-/
def overflowFlag (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign E Em : Nat) : Nat :=
  (fun top =>
    (fun kmax kmid klim =>
      Model.IEEERoundingMode.casesOn (motive := fun _ => Nat) mode
        (gtFlag (Nat.add E (Nat.land (maxSignificand fmt) 1)) kmid)
        (geFlag E kmid)
        (geFlag E klim)
        (Nat.add (Nat.mul sign (geFlag E klim)) (Nat.mul (Nat.sub 1 sign) (gtFlag E kmax)))
        (Nat.add (Nat.mul sign (gtFlag E kmax)) (Nat.mul (Nat.sub 1 sign) (geFlag E klim)))
        (gtFlag E kmax))
      (Nat.shiftLeft (maxSignificand fmt) (Nat.succ top))
      (Nat.shiftLeft (Nat.succ (Nat.mul 2 (maxSignificand fmt))) top)
      (Nat.shiftLeft (Nat.succ (maxSignificand fmt)) (Nat.succ top)))
    (Nat.add Em fmt.maxFiniteExpField)

/--
One when the exact magnitude `E` with sign `sign` is tiny after rounding in the direction `mode`
by the threshold test of `Model.dyadicIsTinyAfterRounding`, which applies when the delivered
value is not a zero or a subnormal (`tinyFlag_eq`).
-/
def tinyFlag (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign E Em : Nat) : Nat :=
  (fun kmin kpred kmid =>
    Model.IEEERoundingMode.casesOn (motive := fun _ => Nat) mode
      (gtFlag kmid E)
      (gtFlag kmid E)
      (gtFlag kmin E)
      (Nat.add (Nat.mul (Nat.sub 1 sign) (geFlag kpred E)) (Nat.mul sign (gtFlag kmin E)))
      (Nat.add (Nat.mul sign (geFlag kpred E)) (Nat.mul (Nat.sub 1 sign) (gtFlag kmin E)))
      (geFlag kpred E))
    (Nat.shiftLeft (2 ^ fmt.fracWidth) (Nat.add Em 2))
    (Nat.shiftLeft (Nat.sub (Nat.mul 2 (2 ^ fmt.fracWidth)) 1) (Nat.succ Em))
    (Nat.shiftLeft (Nat.sub (Nat.mul 4 (2 ^ fmt.fracWidth)) 1) Em)

/--
The comparison of two signed magnitudes: `0` when `±X` is below `±Y`, `1` when they are equal
and `2` when it is above, where a sign of one means negative (`signedCompare_eq`).
-/
def signedCompare (sa X sb Y : Nat) : Nat :=
  (fun ka kb =>
    Nat.sub (Nat.add 1 (Nat.sub 1 (Nat.sub 1 (Nat.sub ka kb))))
      (Nat.sub 1 (Nat.sub 1 (Nat.sub kb ka))))
    (Nat.sub (Nat.add (Nat.add X Y) X) (Nat.mul (Nat.mul 2 sa) X))
    (Nat.sub (Nat.add (Nat.add X Y) Y) (Nat.mul (Nat.mul 2 sb) Y))

/--
The status of delivering the word `w` for the exact result with sign `sign` and magnitude
`E * 2 ^ (fmt.minSubnormalExponent - Em - 2)`, rounded in the direction `mode`: invalid `1`,
division by zero `2`, overflow `4`, underflow `8`, inexact `16`, and the ternary value times
`32` (`0` below the exact result, `1` equal, `2` above) (`roundStatus_eq`).
-/
def roundStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign E Em w : Nat) : Nat :=
  (fun sw uw over =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nonFinite fmt sw uw) 0)
      (Nat.add
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add over (infFlag fmt uw)) 0) 20 1)
        (Nat.mul 64 (Nat.sub 1 sign)))
      ((fun hw =>
          (fun cmp =>
            Nat.add (Nat.mul 32 cmp)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq over 0) 20
                ((fun inexact =>
                    Nat.add (Nat.mul 16 inexact)
                      (Nat.mul 8 (Nat.mul inexact
                        (Nat.sub 1 (Nat.sub 1
                          (Nat.add (Nat.sub 1 (Nat.shiftRight uw fmt.fracWidth))
                            (tinyFlag fmt mode sign E Em)))))))
                  (Nat.add (Nat.sub 1 cmp) (Nat.sub cmp 1)))))
            (signedCompare sw
              (Nat.shiftLeft (Nat.sub uw (Nat.shiftLeft hw fmt.fracWidth))
                (Nat.add (Nat.add hw Em) 2))
              sign E))
        (Nat.sub (Nat.shiftRight uw fmt.fracWidth) 1)))
    (Nat.shiftRight w (signPos fmt)) (Nat.land w (magnitudeMask fmt))
    (overflowFlag fmt mode sign E Em)

/-- The five IEEE exception flags of a status number. -/
def decodeStatus (code : Nat) : Numerics.IEEEStatus :=
  { invalid := Nat.beq (Nat.land code 1) 1
    divideByZero := Nat.beq (Nat.land (Nat.shiftRight code 1) 1) 1
    overflow := Nat.beq (Nat.land (Nat.shiftRight code 2) 1) 1
    underflow := Nat.beq (Nat.land (Nat.shiftRight code 3) 1) 1
    inexact := Nat.beq (Nat.land (Nat.shiftRight code 4) 1) 1 }

/-- The ternary value of a status number. -/
def decodeTernary (code : Nat) : Ordering :=
  (fun ternary =>
    Bool.casesOn (motive := fun _ => Ordering) (Nat.beq ternary 0)
      (Bool.casesOn (motive := fun _ => Ordering) (Nat.beq ternary 1) Ordering.gt Ordering.eq)
      Ordering.lt)
    (Nat.shiftRight code 5)

/-! ## Comparisons of dyadics as comparisons of naturals -/

/-- `gtFlag` is one exactly when its second argument is the smaller one. -/
theorem gtFlag_eq (a b : Nat) : gtFlag a b = if b < a then 1 else 0 := by
  unfold gtFlag
  simp only [Nat.sub_eq]
  split <;> omega

/-- `geFlag` is one exactly when its second argument is not the larger one. -/
theorem geFlag_eq (a b : Nat) : geFlag a b = if b ≤ a then 1 else 0 := by
  unfold geFlag
  simp only [Nat.sub_eq]
  split <;> omega

/-- The rational value of a dyadic, from its three fields. -/
theorem toRat_mk (negative : Bool) (significand : Nat) (exponent : Int) :
    Numerics.Dyadic.toRat ⟨negative, significand, exponent⟩ =
      (if negative then -1 else 1) * (significand : ℚ) * (2 : ℚ) ^ exponent := by
  unfold Numerics.Dyadic.toRat Numerics.Dyadic.signedSignificand
  cases negative <;> simp

/-- Two nonnegative dyadics on one scale compare as their magnitudes. -/
theorem cmpDyadic_eq_compare (a b : Numerics.Dyadic) (X Y : Nat) (c : Int)
    (ha : a.toRat = (X : ℚ) * (2 : ℚ) ^ c) (hb : b.toRat = (Y : ℚ) * (2 : ℚ) ^ c) :
    Model.cmpDyadic a b = compare X Y := by
  have hC : (0 : ℚ) < (2 : ℚ) ^ c := zpow_pos (by norm_num) c
  rw [Model.cmpDyadic_eq_cmpDyadicAligned,
    show Model.cmpDyadicAligned a b = Numerics.Dyadic.compare a b from rfl,
    Numerics.Dyadic.compare_eq_compare_toRat, ha, hb]
  apply compare_congr
  · rw [mul_lt_mul_iff_of_pos_right hC, Nat.cast_lt]
  · rw [mul_left_inj' hC.ne', Nat.cast_inj]

/-- `signedCompare` is the comparison of two signed dyadics on one scale. -/
theorem signedCompare_eq (a b : Numerics.Dyadic) (sa sb X Y : Nat) (c : Int)
    (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (ha : a.toRat = (if sa = 1 then -1 else 1) * (X : ℚ) * (2 : ℚ) ^ c)
    (hb : b.toRat = (if sb = 1 then -1 else 1) * (Y : ℚ) * (2 : ℚ) ^ c) :
    decodeOrdering (signedCompare sa X sb Y) = some (Model.cmpDyadic a b) := by
  have hC : (0 : ℚ) < (2 : ℚ) ^ c := zpow_pos (by norm_num) c
  have hkeys := compare_signed_eq_compare_keys (decide (sa = 1)) (decide (sb = 1)) X Y (X + Y)
    X Y ((2 : ℚ) ^ c) hC (by omega) (by omega) Iff.rfl Iff.rfl Iff.rfl Iff.rfl
  simp only [decide_eq_true_eq] at hkeys
  rw [Model.cmpDyadic_eq_cmpDyadicAligned,
    show Model.cmpDyadicAligned a b = Numerics.Dyadic.compare a b from rfl,
    Numerics.Dyadic.compare_eq_compare_toRat, ha, hb, hkeys]
  unfold signedCompare
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  have hka : X + Y + X - 2 * sa * X = if sa = 1 then X + Y - X else X + Y + X := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsa with h | h
    · subst h
      simp
    · subst h
      simp only [ite_true]
      omega
  have hkb : X + Y + Y - 2 * sb * Y = if sb = 1 then X + Y - Y else X + Y + Y := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsb with h | h
    · subst h
      simp
    · subst h
      simp only [ite_true]
      omega
  rw [hka, hkb]
  exact decodeOrdering_keys _ _

/-- The number of an ordering in a status number: `0` less, `1` equal, `2` greater. -/
def orderingCode : Ordering → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

/-- A code that decodes to an ordering is the number of that ordering. -/
theorem code_of_decodeOrdering {code : Nat} {ordering : Ordering}
    (h : decodeOrdering code = some ordering) : code = orderingCode ordering := by
  rcases code with _ | _ | _ | code
  · cases ordering <;> first | rfl | exact absurd h (by decide)
  · cases ordering <;> first | rfl | exact absurd h (by decide)
  · cases ordering <;> first | rfl | exact absurd h (by decide)
  · have h0 : Nat.beq (code + 1 + 1 + 1) 0 = false := rfl
    have h1 : Nat.beq (code + 1 + 1 + 1) 1 = false := rfl
    have h2 : Nat.beq (code + 1 + 1 + 1) 2 = false := rfl
    unfold decodeOrdering at h
    rw [h0, h1, h2] at h
    exact absurd (show (none : Option Ordering) = some ordering from h) (by simp)

/--
The number of a set of exception flags and a ternary value, which `decodeStatus` and
`decodeTernary` read back (`decodeStatus_statusCode`, `decodeTernary_statusCode`).
-/
def statusCode (status : Numerics.IEEEStatus) (ternary : Ordering) : Nat :=
  (if status.invalid then 1 else 0) + (if status.divideByZero then 2 else 0) +
    (if status.overflow then 4 else 0) + (if status.underflow then 8 else 0) +
    (if status.inexact then 16 else 0) + 32 * orderingCode ternary

/-- `decodeStatus` reads the flags of a status number back. -/
theorem decodeStatus_statusCode (status : Numerics.IEEEStatus) (ternary : Ordering) :
    decodeStatus (statusCode status ternary) = status := by
  obtain ⟨invalid, divideByZero, overflow, underflow, inexact⟩ := status
  cases invalid <;> cases divideByZero <;> cases overflow <;> cases underflow <;>
    cases inexact <;> cases ternary <;> decide +kernel

/-- `decodeTernary` reads the ternary value of a status number back. -/
theorem decodeTernary_statusCode (status : Numerics.IEEEStatus) (ternary : Ordering) :
    decodeTernary (statusCode status ternary) = ternary := by
  obtain ⟨invalid, divideByZero, overflow, underflow, inexact⟩ := status
  cases invalid <;> cases divideByZero <;> cases overflow <;> cases underflow <;>
    cases inexact <;> cases ternary <;> decide +kernel

/-- The flags of a status number depend on its five low bits only. -/
theorem decodeStatus_mod (code : Nat) : decodeStatus (code % 32) = decodeStatus code := by
  have h0 : code % 32 % 2 = code % 2 := by omega
  have h1 : code % 32 / 2 % 2 = code / 2 % 2 := by omega
  have h2 : code % 32 / 4 % 2 = code / 4 % 2 := by omega
  have h3 : code % 32 / 8 % 2 = code / 8 % 2 := by omega
  have h4 : code % 32 / 16 % 2 = code / 16 % 2 := by omega
  unfold decodeStatus
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 1 = 2 from rfl, show (2 : Nat) ^ 2 = 4 from rfl,
    show (2 : Nat) ^ 3 = 8 from rfl, show (2 : Nat) ^ 4 = 16 from rfl, h0, h1, h2, h3, h4]

/--
A status number has the flags `status` exactly when its five low bits are the number of
`status`. With this rule the kernel compares two numbers where it would compare two records
field by field.
-/
theorem decodeStatus_eq_iff (code : Nat) (status : Numerics.IEEEStatus) :
    decodeStatus code = status ↔ Nat.land code 31 = statusCode status .lt := by
  have hland : Nat.land code 31 = code % 32 := Nat.and_two_pow_sub_one_eq_mod code 5
  rw [hland, ← decodeStatus_mod code]
  have hlt : code % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize code % 32 = low at hlt
  obtain ⟨invalid, divideByZero, overflow, underflow, inexact⟩ := status
  have key : ∀ low : Fin 32, ∀ a b c d e : Bool,
      decodeStatus low.val = ⟨a, b, c, d, e⟩ ↔ low.val = statusCode ⟨a, b, c, d, e⟩ .lt := by
    decide +kernel
  exact key ⟨low, hlt⟩ invalid divideByZero overflow underflow inexact

/-- The value of a format constant with a clear sign, on the scale of a status computation. -/
private theorem toRat_constant (k : Numerics.Dyadic) (m h : Nat) (c : Int)
    (hnegative : k.negative = false) (hsig : k.significand = m)
    (hexp : k.exponent = (h : Int) + c) :
    k.toRat = ((m <<< h : ℕ) : ℚ) * (2 : ℚ) ^ c := by
  rw [toRat_of_fields k m h c hsig (fun _ => hexp), hnegative, Nat.shiftLeft_eq]
  simp

/-- The four tests that the status thresholds make on a comparison of naturals. -/
private theorem compare_tests (a b : Nat) :
    (compare a b == Ordering.gt) = decide (b < a) ∧
      (compare a b != Ordering.lt) = decide (b ≤ a) ∧
      (compare a b == Ordering.lt) = decide (a < b) ∧
      (compare a b != Ordering.gt) = decide (a ≤ b) := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [(compare_lt_iff_lt).2 h]
    simp [h, Nat.le_of_lt h, Nat.not_le_of_lt h, Nat.lt_asymm h]
  · subst h
    rw [(compare_eq_iff_eq).2 rfl]
    simp
  · rw [(compare_gt_iff_gt).2 h]
    simp [h, Nat.le_of_lt h, Nat.not_le_of_lt h, Nat.lt_asymm h]

/--
The rational value of a decoded finite value, on the scale of a status computation with the
offset `Em`: its sign, its significand shifted by its exponent field, and the scale.
-/
theorem decoded_toRat {fmt : FloatFormat} (x : Model fmt) (dx : Numerics.Dyadic)
    (hdx : Model.toDyadic? x = some dx) (Em : Nat) :
    dx.toRat =
      (if (if Model.signBit x then 1 else 0 : Nat) = 1 then -1 else 1) *
        (((if Model.expField x = 0 then Model.fracField x
            else 2 ^ fmt.fracWidth + Model.fracField x) <<<
          (Model.expField x - 1 + Em + 2) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) := by
  have hfinite : Model.isFinite x = true := by
    rw [← Model.toDyadic?_isSome_eq_isFinite, hdx]
    rfl
  obtain ⟨d, hd, hn, hs, he⟩ := toDyadic?_of_isFinite x hfinite
  obtain rfl : d = dx := Option.some.inj (hd.symm.trans hdx)
  rw [toRat_of_fields d _ (Model.expField x - 1 + Em + 2)
    (fmt.minSubnormalExponent - (Em : Int) - 2) hs (fun h => by
      rw [he (by rw [hs]; exact h)]
      push_cast
      omega), hn, Nat.shiftLeft_eq]
  cases Model.signBit x <;> simp

section Exact

variable (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (d : Numerics.Dyadic)
  (sign E Em : Nat)

/-- The magnitude of an exact result on the scale of its status computation. -/
theorem magnitude_toRat
    (hvalue : d.toRat = (if sign = 1 then -1 else 1) * (E : ℚ) *
      (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2)) :
    ({ d with negative := false } : Numerics.Dyadic).toRat =
      (E : ℚ) * (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) := by
  obtain ⟨negative, significand, exponent⟩ := d
  rw [toRat_mk] at hvalue ⊢
  have h1 : (0 : ℚ) ≤ (significand : ℚ) * (2 : ℚ) ^ exponent := by positivity
  have h2 : (0 : ℚ) ≤ (E : ℚ) * (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) := by
    positivity
  cases negative <;> by_cases hs : sign = 1 <;>
    simp only [hs, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul] at hvalue ⊢ <;>
    linarith

/-- A nonzero exact result has the sign that its status computation is given. -/
theorem negative_of_ne_zero
    (hvalue : d.toRat = (if sign = 1 then -1 else 1) * (E : ℚ) *
      (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2))
    (hE : E ≠ 0) : d.negative = decide (sign = 1) := by
  obtain ⟨negative, significand, exponent⟩ := d
  rw [toRat_mk] at hvalue
  have h1 : (0 : ℚ) ≤ (significand : ℚ) * (2 : ℚ) ^ exponent := by positivity
  have hpos : (0 : ℚ) < (E : ℚ) * (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) := by
    have : (0 : ℚ) < (E : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hE
    positivity
  cases negative <;> by_cases hs : sign = 1 <;>
    simp only [hs, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul] at hvalue <;>
    first | (exfalso; linarith) | simp [hs]

/-- `overflowFlag` is the reference overflow test of a rounding. -/
theorem overflowFlag_eq (hsign : sign ≤ 1)
    (hvalue : d.toRat = (if sign = 1 then -1 else 1) * (E : ℚ) *
      (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2)) :
    overflowFlag fmt mode sign E Em =
      if Model.dyadicRoundingOverflows fmt mode d then 1 else 0 := by
  have hmagnitude := magnitude_toRat fmt d sign E Em hvalue
  have hmax : (Model.maxFiniteDyadic fmt).toRat =
      ((maxSignificand fmt <<< (Em + fmt.maxFiniteExpField + 1) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) :=
    toRat_constant _ _ _ _ rfl
      (by simp [Model.maxFiniteDyadic, maxSignificand, Model.pow2_eq_two_pow]) (by
      simp only [Model.maxFiniteDyadic, FloatFormat.maxNormalExponent,
        FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
      push_cast
      omega)
  have hmid : (Model.overflowMidpoint fmt).toRat =
      (((2 * maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) :=
    toRat_constant _ _ _ _ rfl (by simp [Model.overflowMidpoint, Model.maxFiniteDyadic,
      maxSignificand, Model.pow2_eq_two_pow]) (by
      simp only [Model.overflowMidpoint, Model.maxFiniteDyadic, FloatFormat.maxNormalExponent,
        FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
      push_cast
      omega)
  have hlim : (Model.overflowLimit fmt).toRat =
      (((maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField + 1) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) :=
    toRat_constant _ _ _ _ rfl (by simp [Model.overflowLimit, Model.maxFiniteDyadic,
      maxSignificand, Model.pow2_eq_two_pow]) (by
      simp only [Model.overflowLimit, Model.maxFiniteDyadic, FloatFormat.maxNormalExponent,
        FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
      push_cast
      omega)
  have cmax := cmpDyadic_eq_compare _ _ _ _ _ hmagnitude hmax
  have cmid := cmpDyadic_eq_compare _ _ _ _ _ hmagnitude hmid
  have clim := cmpDyadic_eq_compare _ _ _ _ _ hmagnitude hlim
  have hodd : Model.maxFiniteMantissaOdd fmt = (maxSignificand fmt % 2 == 1) := by
    simp [Model.maxFiniteMantissaOdd, Model.maxFiniteDyadic, maxSignificand,
      Model.pow2_eq_two_pow]
  have hposMax : 0 < maxSignificand fmt <<< (Em + fmt.maxFiniteExpField + 1) := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos (by unfold maxSignificand; have := Nat.two_pow_pos fmt.fracWidth; omega)
      (Nat.two_pow_pos _)
  have hposLim : 0 < (maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField + 1) := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hnegative := negative_of_ne_zero fmt d sign E Em hvalue
  obtain ⟨tmax1, tmax2, -, -⟩ :=
    compare_tests E (maxSignificand fmt <<< (Em + fmt.maxFiniteExpField + 1))
  obtain ⟨-, tmid2, -, -⟩ :=
    compare_tests E ((2 * maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField))
  obtain ⟨-, tlim2, -, -⟩ :=
    compare_tests E ((maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField + 1))
  unfold overflowFlag Model.dyadicRoundingOverflows
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.succ_eq_add_one, Nat.shiftLeft_eq',
    Nat.land_eq, gtFlag_eq, geFlag_eq, Nat.and_one_is_mod]
  cases mode <;>
    simp only [Model.dyadicNearestEvenOverflows, Model.dyadicNearestAwayOverflows,
      Model.dyadicTruncationOverflows, Model.dyadicMagnitudeOverflows, cmax, cmid, clim, hodd,
      tmax1, tmid2, tlim2, decide_eq_true_eq]
  · -- nearest, ties to even
    have hparity : maxSignificand fmt % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases Nat.lt_trichotomy E ((2 * maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField))
      with h | h | h
    · rw [(compare_lt_iff_lt).2 h]
      have : ¬ (2 * maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField) <
          E + maxSignificand fmt % 2 := by omega
      simp [this]
    · rw [(compare_eq_iff_eq).2 h, ← h]
      by_cases hp : maxSignificand fmt % 2 = 1
      · simp [hp]
      · have : maxSignificand fmt % 2 = 0 := by omega
        simp [this]
    · rw [(compare_gt_iff_gt).2 h]
      have : (2 * maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField) <
          E + maxSignificand fmt % 2 := by omega
      simp [this]
  · -- up
    by_cases hE : E = 0
    · subst hE
      have h1 : ¬ (maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField + 1) ≤ 0 := by omega
      have h2 : ¬ maxSignificand fmt <<< (Em + fmt.maxFiniteExpField + 1) < 0 := by omega
      cases d.negative <;> simp [h1, h2]
    · rw [hnegative hE]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;> simp
  · -- down
    by_cases hE : E = 0
    · subst hE
      have h1 : ¬ (maxSignificand fmt + 1) <<< (Em + fmt.maxFiniteExpField + 1) ≤ 0 := by omega
      have h2 : ¬ maxSignificand fmt <<< (Em + fmt.maxFiniteExpField + 1) < 0 := by omega
      cases d.negative <;> simp [h1, h2]
    · rw [hnegative hE]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;> simp

/-- `tinyFlag` is zero or one. -/
theorem tinyFlag_le_one (hsign : sign ≤ 1) : tinyFlag fmt mode sign E Em ≤ 1 := by
  unfold tinyFlag
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, gtFlag_eq, geFlag_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;>
    cases mode <;> simp only [Nat.zero_mul, Nat.one_mul, Nat.sub_zero, Nat.sub_self,
      Nat.zero_add, Nat.add_zero] <;> split <;> omega

/--
`tinyFlag` is the reference tininess test of a rounding whose delivered value is not a zero or
a subnormal.
-/
theorem tinyFlag_eq (hsign : sign ≤ 1)
    (hvalue : d.toRat = (if sign = 1 then -1 else 1) * (E : ℚ) *
      (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2))
    (rounded : Model fmt) (hrounded : Model.isTinyAfterRounding rounded = false) :
    tinyFlag fmt mode sign E Em =
      if Model.dyadicIsTinyAfterRounding fmt mode d rounded then 1 else 0 := by
  have hmagnitude := magnitude_toRat fmt d sign E Em hvalue
  have hmin : (Model.minNormalDyadic fmt).toRat =
      ((2 ^ fmt.fracWidth <<< (Em + 2) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) :=
    toRat_constant _ _ _ _ rfl (by simp [Model.minNormalDyadic, Model.pow2_eq_two_pow]) (by
      simp only [Model.minNormalDyadic]
      push_cast
      omega)
  have hpred : (Model.underflowPredecessor fmt).toRat =
      (((2 * 2 ^ fmt.fracWidth - 1) <<< (Em + 1) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) :=
    toRat_constant _ _ _ _ rfl (by simp [Model.underflowPredecessor, Model.pow2_eq_two_pow]) (by
      simp only [Model.underflowPredecessor]
      push_cast
      omega)
  have hmid : (Model.underflowMidpoint fmt).toRat =
      (((4 * 2 ^ fmt.fracWidth - 1) <<< Em : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2) :=
    toRat_constant _ _ _ _ rfl (by simp [Model.underflowMidpoint, Model.pow2_eq_two_pow]) (by
      simp only [Model.underflowMidpoint]
      omega)
  have cmin := cmpDyadic_eq_compare _ _ _ _ _ hmagnitude hmin
  have cpred := cmpDyadic_eq_compare _ _ _ _ _ hmagnitude hpred
  have cmid := cmpDyadic_eq_compare _ _ _ _ _ hmagnitude hmid
  have hposMin : 0 < 2 ^ fmt.fracWidth <<< (Em + 2) := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hnegative := negative_of_ne_zero fmt d sign E Em hvalue
  obtain ⟨-, -, tmin3, -⟩ := compare_tests E (2 ^ fmt.fracWidth <<< (Em + 2))
  obtain ⟨-, -, -, tpred4⟩ := compare_tests E ((2 * 2 ^ fmt.fracWidth - 1) <<< (Em + 1))
  obtain ⟨-, -, tmid3, -⟩ := compare_tests E ((4 * 2 ^ fmt.fracWidth - 1) <<< Em)
  unfold tinyFlag Model.dyadicIsTinyAfterRounding
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.succ_eq_add_one, Nat.shiftLeft_eq',
    gtFlag_eq, geFlag_eq, hrounded, Bool.false_eq_true, ite_false]
  cases mode <;>
    simp only [Model.IEEERoundingMode.roundsAwayFromZero, cmin, cpred, cmid, tmin3, tpred4,
      tmid3, decide_eq_true_eq, ite_true]
  · -- up
    by_cases hE : E = 0
    · subst hE
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;>
        cases d.negative <;> simp [hposMin]
    · rw [hnegative hE]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;> simp
  · -- down
    by_cases hE : E = 0
    · subst hE
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;>
        cases d.negative <;> simp [hposMin]
    · rw [hnegative hE]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;> simp

/--
`roundStatus` computes the reference status and ternary value of a rounding: the decoded flags
are `Model.dyadicRoundingStatus` and the decoded ternary value is `Model.dyadicTernary`, for
every format descriptor, every rounding direction, every exact result `d` and every delivered
value `rounded`. The exact result has the sign `sign` and the magnitude
`E * 2 ^ (fmt.minSubnormalExponent - Em - 2)`, and an exact zero is delivered as a finite value.
-/
theorem roundStatus_eq (hsign : sign ≤ 1)
    (hvalue : d.toRat = (if sign = 1 then -1 else 1) * (E : ℚ) *
      (2 : ℚ) ^ (fmt.minSubnormalExponent - (Em : Int) - 2))
    (rounded : Model fmt) (hzero : E = 0 → Model.isFinite rounded = true) :
    decodeStatus (roundStatus fmt mode sign E Em rounded.toNatBits) =
        Model.dyadicRoundingStatus fmt mode d rounded ∧
      decodeTernary (roundStatus fmt mode sign E Em rounded.toNatBits) =
        Model.dyadicTernary d rounded := by
  have hfr := Model.fracField_lt_pow2 rounded
  have hover := overflowFlag_eq fmt mode d sign E Em hsign hvalue
  have hbeq : ∀ n : Nat, n ≠ 0 → Nat.beq n 0 = false := by
    intro n hn
    cases n
    · exact absurd rfl hn
    · rfl
  unfold roundStatus Model.dyadicRoundingStatus Model.dyadicTernary
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfr,
    fields_sub_shiftLeft, infFlag_eq, hover]
  generalize Model.dyadicRoundingOverflows fmt mode d = overflows
  by_cases hfinite : Model.isFinite rounded = true
  · -- A finite delivered value is decoded and compared with the exact result.
    obtain ⟨actual, hactual, -⟩ := toDyadic?_of_isFinite rounded hfinite
    have hdecoded : Model.finiteDyadic rounded hfinite = actual :=
      Model.finiteDyadic_eq_of_toDyadic hfinite hactual
    have hrat := decoded_toRat rounded actual hactual Em
    have hcompare := signedCompare_eq actual d _ sign _ E _
      (by split <;> omega) hsign hrat hvalue
    have hcode := code_of_decodeOrdering hcompare
    rw [nonFinite_eq_zero_of_isFinite rounded hfinite, hcode, show Nat.beq 0 0 = true from rfl]
    simp only [dite_eq_left hfinite, hdecoded, ← Model.cmpDyadic_swap actual d]
    generalize Model.cmpDyadic actual d = ordering
    by_cases htiny : Model.expField rounded = 0
    · have hspec : Model.dyadicIsTinyAfterRounding fmt mode d rounded = true := by
        simp [Model.dyadicIsTinyAfterRounding, Model.isTinyAfterRounding, hfinite, htiny]
      have hle := tinyFlag_le_one fmt mode sign E Em hsign
      have hflag : 1 - (1 - (1 - Model.expField rounded + tinyFlag fmt mode sign E Em)) = 1 := by
        omega
      rw [hspec, hflag]
      cases ordering <;> cases overflows <;> exact ⟨by decide +kernel, by decide +kernel⟩
    · have hrounded : Model.isTinyAfterRounding rounded = false := by
        simp [Model.isTinyAfterRounding, htiny]
      have hflag := tinyFlag_eq fmt mode d sign E Em hsign hvalue rounded hrounded
      have hfield : 1 - Model.expField rounded = 0 := by omega
      rw [hflag, hfield]
      cases ordering <;> cases overflows <;>
        cases Model.dyadicIsTinyAfterRounding fmt mode d rounded <;>
        exact ⟨by decide +kernel, by decide +kernel⟩
  · -- A delivered value that is not finite stands for an overflow.
    have hguard : nonFinite fmt (if Model.signBit rounded then 1 else 0)
        (Model.expField rounded * 2 ^ fmt.fracWidth + Model.fracField rounded) ≠ 0 := by
      intro h
      exact hfinite (isFinite_of_nonFinite_eq_zero rounded h)
    have hE : E ≠ 0 := fun h => hfinite (hzero h)
    rw [hbeq _ hguard, negative_of_ne_zero fmt d sign E Em hvalue hE]
    simp only [dite_eq_right hfinite]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsign with h | h <;> subst h <;>
      cases overflows <;> cases Model.isInfinite rounded <;>
      exact ⟨by decide +kernel, by decide +kernel⟩

end Exact

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
