/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Core
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Floats.Formats.P3109.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Range
public import FloatLib.Floats.Formats.P3109.Projection.Saturation
public meta import FloatLib.Tactic.KernelNotation
public import FloatLib.Tactic.KernelShape
public import FloatLib.Numerics.Kernel.ZProof
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal

/-!
# The kernel P3109 operations compute the P3109 operations

P3109 Interim Report v4.1 (14 September 2026), §§4.7 and 4.10, an unapproved draft. For every
valid descriptor (every width `K`, precision `P`, signedness and domain), every rounding mode
with every supplied random word, every saturation mode and every operand, the functions of
`KernelPath.Core` on encodings are the encodings of the reference operations:

* `toClosedRat_eq`: the class and the ratio read from a code are its exact closed value
  (§4.7.2);
* `projectRat_eq`: `project` is the code of the reference projection of a closed value given
  by its class and a ratio of natural numbers, with no normalization of the ratio (§4.7.3 to
  §4.7.6);
* `add_eq`, `mul_eq`, `div_eq`, `fma_eq`, `convert_eq`: the arithmetic of §4.10 with
  independent operand and destination descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109

/-! ## Descriptors, modes and closed values as natural numbers -/

/-- One for a signed format and zero for an unsigned one. -/
def sgOf (format : Format) : Nat :=
  match format.signedness with
  | .signed => 1
  | .unsigned => 0

/-- One for the extended domain and zero for the finite one. -/
def exOf (format : Format) : Nat :=
  match format.domain with
  | .extended => 1
  | .finite => 0

/-- The index of a rounding mode, in the order of `RoundingMode`. -/
def modeIndex : RoundingMode → Nat
  | .towardZero => 0
  | .up => 1
  | .down => 2
  | .nearestAway => 3
  | .nearest => 4
  | .toOdd => 5
  | .stochasticA _ => 6
  | .stochasticB _ => 7
  | .stochasticC _ => 8

/-- The width of the random word of a stochastic mode, and zero for the other modes. -/
def modeWidth : RoundingMode → Nat
  | .stochasticA random | .stochasticB random | .stochasticC random => random.width
  | _ => 0

/-- The value of the random word of a stochastic mode, and zero for the other modes. -/
def modeRandom : RoundingMode → Nat
  | .stochasticA random | .stochasticB random | .stochasticC random => random.toNat
  | _ => 0

/-- The index of a saturation mode: finite, propagate, none. -/
def satIndex : SaturationMode → Nat
  | .finite => 0
  | .propagate => 1
  | .none => 2

/-! The descriptor numbers are matches for the compiler; the kernel reads them as recursors. -/

kernel_shape sgOf
kernel_shape exOf
kernel_shape modeIndex
kernel_shape modeWidth
kernel_shape modeRandom
kernel_shape satIndex

/-- The closed value of a class and a signed ratio: class zero is `(-1) ^ s * n / d`, one `+∞`,
two `-∞`, and every other class NaN. -/
def closed (cls s n d : Nat) : NumericalValue Rat :=
  if cls = 0 then .finite ((if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat))
  else if cls = 1 then .infinity false
  else if cls = 2 then .infinity true
  else Arithmetic.nan

variable {format : Format}

/-! ## Descriptor quantities -/

/-- The kernel trailing-bit count is the descriptor's. -/
theorem trailingBits_eq (format : Format) :
    trailingBits format.precision = format.trailingBits := rfl

/-- The kernel exponent bias is the descriptor's. -/
theorem exponentBias_eq (format : Format) :
    exponentBias format.bitWidth format.precision (sgOf format) = format.exponentBias := by
  have hb := format.precision_bound
  unfold exponentBias Format.exponentBias Format.exponentBits sgOf
  kernel_notation
  cases hs : format.signedness <;> simp only [hs] at hb ⊢ <;> congr 2 <;> omega

/-- The kernel sign boundary is the descriptor's. -/
theorem signBoundary_eq (format : Format) :
    signBoundary format.bitWidth = format.signBoundary := by
  unfold signBoundary Format.signBoundary
  kernel_notation

/-- The kernel NaN code is the descriptor's. -/
theorem nanBits_eq (format : Format) :
    nanBits format.bitWidth (sgOf format) = format.nanBits := by
  unfold nanBits Format.nanBits sgOf
  rw [signBoundary_eq]
  kernel_notation
  cases hs : format.signedness <;> simp [Format.modulus]

/-- The kernel code of `+∞` is the descriptor's. -/
theorem positiveInfinityBits_eq (format : Format) :
    positiveInfinityBits format.bitWidth (sgOf format) = format.positiveInfinityBits := by
  unfold positiveInfinityBits Format.positiveInfinityBits sgOf
  rw [signBoundary_eq]
  kernel_notation
  cases hs : format.signedness <;> simp [Format.modulus]

/-- The kernel code of `-∞` is the descriptor's. -/
theorem negativeInfinityBits_eq (format : Format) :
    negativeInfinityBits format.bitWidth = format.negativeInfinityBits := by
  unfold negativeInfinityBits Format.negativeInfinityBits Format.modulus
  kernel_notation

/-- The kernel largest finite code is the descriptor's. -/
theorem maxFiniteBits_eq (format : Format) :
    maxFiniteBits format.bitWidth (sgOf format) (exOf format) = format.maxFiniteBits := by
  unfold maxFiniteBits Format.maxFiniteBits exOf
  rw [positiveInfinityBits_eq]
  kernel_notation
  cases hd : format.domain <;> simp

/-! ## Decoding -/

/-- A rational significand times a power of two, as a ratio of natural numbers. -/
theorem mul_zpow_eq_div (sig e C : Nat) :
    (sig : Rat) * (2 : Rat) ^ ((e : Int) - (C : Int)) =
      ((sig * 2 ^ (e - C) : Nat) : Rat) / ((2 ^ (C - e) : Nat) : Rat) := by
  by_cases h : C ≤ e
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hk : ((C + k : Nat) : Int) - (C : Int) = (k : Int) := by omega
    rw [hk, zpow_natCast, Nat.add_sub_cancel_left, Nat.sub_eq_zero_of_le (Nat.le_add_right C k)]
    push_cast
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le h)
    have hk : (e : Int) - ((e + k : Nat) : Int) = -(k : Int) := by omega
    rw [hk, zpow_neg, zpow_natCast, Nat.add_sub_cancel_left,
      Nat.sub_eq_zero_of_le (Nat.le_add_right e k)]
    push_cast
    simp [div_eq_mul_inv]

/--
P3109 interim report v4.1, §4.7.2: the value of a positive finite code is the ratio of the
    kernel numerator
and denominator of its fields, for every descriptor and every code.
-/
theorem decodePositiveFinite_toRat (format : Format) (m : Nat) :
    (format.decodePositiveFinite m).toRat =
      ((significandOf format.precision m *
          2 ^ (exponentOf format.precision m - (format.exponentBias + format.trailingBits)) :
        Nat) : Rat) /
      ((2 ^ (format.exponentBias + format.trailingBits - exponentOf format.precision m) : Nat) :
        Rat) := by
  have hT := format.trailingBits_add_one
  rw [← mul_zpow_eq_div]
  unfold significandOf exponentOf
  kernel_notation
  rw [trailingBits_eq]
  by_cases hrow : m / 2 ^ format.trailingBits = 0
  · by_cases hzero : m = 0
    · subst hzero
      simp
    · rw [format.decodePositiveFinite_of_biasedExponent_eq_zero m hzero hrow,
        Dyadic.toRat_mk_false, hrow, ite_eq_left rfl, Nat.add_zero,
        format.minimumQuantumExponent_eq]
      congr 2
      simp only [Format.minimumNormalExponent, Int.ofNat_eq_natCast]
      omega
  · rw [format.decodePositiveFinite_of_biasedExponent_ne_zero m hrow, Dyadic.toRat_mk_false,
      ite_eq_right hrow, Nat.add_comm]
    congr 2
    simp only [Int.ofNat_eq_natCast]
    generalize m / 2 ^ format.trailingBits = row at hrow ⊢
    omega

/-- The closed value of a nonnegative finite code, from its kernel fields. -/
theorem toRat_finite (format : Format) (m : Nat) :
    Arithmetic.toRat (.finite (format.decodePositiveFinite m)) =
      closed 0 0
        (significandOf format.precision m *
          2 ^ (exponentOf format.precision m - (format.exponentBias + format.trailingBits)))
        (2 ^ (format.exponentBias + format.trailingBits - exponentOf format.precision m)) := by
  simp [closed, Arithmetic.toRat, decodePositiveFinite_toRat]

/-- The closed value of a negative finite code, from its kernel fields. -/
theorem toRat_finite_neg (format : Format) (m : Nat) :
    Arithmetic.toRat (.finite (format.decodePositiveFinite m).neg) =
      closed 0 1
        (significandOf format.precision m *
          2 ^ (exponentOf format.precision m - (format.exponentBias + format.trailingBits)))
        (2 ^ (format.exponentBias + format.trailingBits - exponentOf format.precision m)) := by
  change NumericalValue.finite (format.decodePositiveFinite m).neg.toRat = _
  rw [Dyadic.neg_toRat, decodePositiveFinite_toRat]
  simp [closed, neg_div]

/--
P3109 interim report v4.1, §4.7.2: the exact closed value of a stored code is the closed value
    of its kernel
class, sign and ratio, for every descriptor and every code.
-/
theorem toClosedRat_eq (x : ExecFloat.P3109 format) :
    ExecFloat.P3109.toClosedRat x =
      closed (classOf format.bitWidth (sgOf format) (exOf format) x.toNatBits)
        (signOf format.bitWidth (sgOf format) x.toNatBits)
        (numeratorOf format.bitWidth format.precision (sgOf format) x.toNatBits)
        (denominatorOf format.bitWidth format.precision (sgOf format) x.toNatBits) := by
  unfold ExecFloat.P3109.toClosedRat
  rw [ExecFloat.P3109.decode_eq_format_decode]
  unfold Format.decode
  have ha : (ExecFloat.Codebook.toCode x).toNat = x.toNatBits := rfl
  rw [ha]
  generalize x.toNatBits = a
  have hboundary := format.one_lt_signBoundary
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  unfold classOf numeratorOf denominatorOf magnitudeOf signOf Format.decodeNat
  simp only [nanBits_eq, positiveInfinityBits_eq, negativeInfinityBits_eq, signBoundary_eq,
    exponentBias_eq, trailingBits_eq]
  kernel_notation
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]
  have hm := format.two_lt_modulus
  have e1 : format.signBoundary - 1 ≠ format.signBoundary := by omega
  have e2 : format.modulus - 1 ≠ format.signBoundary := by omega
  have e3 : format.modulus - 1 ≠ format.signBoundary - 1 := by omega
  have e4 : format.modulus - 2 ≠ format.modulus - 1 := by omega
  cases hs : format.signedness <;> cases hd : format.domain <;>
    simp only [sgOf, exOf, hs, hd, Format.nanBits, Format.positiveInfinityBits,
      Format.negativeInfinityBits]
  · by_cases h1 : a = format.signBoundary
    · simp [h1, closed, Arithmetic.toRat]
    · by_cases h2 : format.signBoundary < a
      · have h3 : format.signBoundary + 1 ≤ a := h2
        simp only [h1, h2, h3, ↓reduceIte, and_self, Nat.one_mul]
        exact toRat_finite_neg format _
      · have h3 : ¬format.signBoundary + 1 ≤ a := by omega
        simp only [h1, h2, h3, ↓reduceIte, and_false, Nat.zero_mul, Nat.sub_zero]
        exact toRat_finite format a
  · by_cases h1 : a = format.signBoundary
    · simp [h1, closed, Arithmetic.toRat]
    · by_cases h4 : a = format.signBoundary - 1
      · subst h4
        simp [e1, closed, Arithmetic.toRat]
      · by_cases h5 : a = format.modulus - 1
        · subst h5
          simp [e2, e3, closed, Arithmetic.toRat]
        · by_cases h2 : format.signBoundary < a
          · have h3 : format.signBoundary + 1 ≤ a := h2
            simp only [h1, h2, h3, h4, h5, ↓reduceIte, and_self, and_false,
              Nat.one_mul, Nat.one_ne_zero]
            exact toRat_finite_neg format _
          · have h3 : ¬format.signBoundary + 1 ≤ a := by omega
            simp only [h1, h2, h3, h4, h5, ↓reduceIte, and_false, Nat.zero_mul,
              Nat.sub_zero, Nat.one_ne_zero]
            exact toRat_finite format a
  · by_cases h1 : a = format.modulus - 1
    · simp [h1, closed, Arithmetic.toRat]
    · simp only [h1, ↓reduceIte, Nat.zero_ne_one, false_and, Nat.zero_mul, Nat.sub_zero]
      exact toRat_finite format a
  · by_cases h1 : a = format.modulus - 1
    · simp [h1, closed, Arithmetic.toRat]
    · by_cases h4 : a = format.modulus - 2
      · subst h4
        simp [e4, closed, Arithmetic.toRat]
      · simp only [h1, h4, ↓reduceIte, Nat.zero_ne_one, false_and, Nat.zero_mul, Nat.sub_zero,
          Nat.one_ne_zero]
        exact toRat_finite format a

end FloatLib.Floats.Formats.P3109.KernelPath
