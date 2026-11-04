/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Proof
public import FloatLib.Floats.Formats.P3109.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# P3109 representation proofs

Every validated P3109 descriptor defines an exact-width `NumericalSystem` and an `ExecFloat`
carrier, and these theorems connect their denotations to P3109 decoding. The proofs lean on
descriptor validation for the field-width, special-encoding, and storage conditions they need.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109

-- Unsigned dyadic denotations are the rational normal form for P3109 decoding.
attribute [simp] Dyadic.toRat_mk_false

namespace Format

/-- The stored trailing field and implicit leading bit make up the declared precision. -/
theorem trailingBits_add_one (format : Format) :
    format.trailingBits + 1 = format.precision :=
  Nat.sub_add_cancel format.precision_pos

/-- Integer form of `trailingBits_add_one`, used in exponent arithmetic. -/
theorem trailingBits_int (format : Format) :
    Int.ofNat format.trailingBits =
      Int.ofNat format.precision - 1 := by
  unfold trailingBits
  simpa using
    (Int.ofNat_sub
      (m := 1) (n := format.precision)
      (Nat.succ_le_iff.mpr format.precision_pos))

/-- Every P3109 descriptor has a positive encoded width. -/
theorem bitWidth_pos (format : Format) : 0 < format.bitWidth := by
  exact lt_trans (by decide) format.bitWidth_gt_two

/-- A signed descriptor carries the strict `P < K` requirement from P3109. -/
theorem precision_lt_bitWidth_of_signed
    (format : Format) (signed : format.signedness = .signed) :
    format.precision < format.bitWidth := by
  simpa [signed] using format.precision_bound

/-- Every descriptor satisfies `P ≤ K`: unsigned descriptors allow equality, and signed ones carry
the strict bound. -/
theorem precision_le_bitWidth (format : Format) :
    format.precision ≤ format.bitWidth := by
  cases hs : format.signedness with
  | signed => exact (format.precision_lt_bitWidth_of_signed hs).le
  | unsigned => simpa [hs] using format.precision_bound

/-- Every valid descriptor has a nonempty exponent field. -/
theorem exponentBits_pos (format : Format) :
    0 < format.exponentBits := by
  cases hs : format.signedness with
  | signed =>
      have hprecision := format.precision_lt_bitWidth_of_signed hs
      simp [exponentBits, hs]
      omega
  | unsigned =>
      simp [exponentBits, hs]

/-- Signed formats have the P3109 bias `2^(K-P-1)`. -/
theorem exponentBias_signed
    (format : Format) (signed : format.signedness = .signed) :
    format.exponentBias =
      2 ^ (format.bitWidth - format.precision - 1) := by
  simp [exponentBias, exponentBits, signed]

/-- Unsigned formats have the P3109 bias `2^(K-P)`. -/
theorem exponentBias_unsigned
    (format : Format) (unsigned : format.signedness = .unsigned) :
    format.exponentBias =
      2 ^ (format.bitWidth - format.precision) := by
  simp [exponentBias, exponentBits, unsigned]

/-- The signed/unsigned boundary lies strictly inside the `K`-bit code space. -/
theorem signBoundary_lt_modulus (format : Format) :
    format.signBoundary < format.modulus := by
  unfold signBoundary modulus
  exact Nat.pow_lt_pow_right (by decide)
    (Nat.sub_one_lt (Nat.ne_of_gt format.bitWidth_pos))

/-- The complete code-space size is twice the signed/unsigned boundary. -/
theorem modulus_eq_two_mul_signBoundary (format : Format) :
    format.modulus = 2 * format.signBoundary := by
  have hwidth : format.bitWidth - 1 + 1 = format.bitWidth :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt format.bitWidth_pos))
  unfold modulus signBoundary
  calc
    2 ^ format.bitWidth = 2 ^ (format.bitWidth - 1 + 1) := by rw [hwidth]
    _ = 2 ^ (format.bitWidth - 1) * 2 := Nat.pow_succ ..
    _ = 2 * 2 ^ (format.bitWidth - 1) := Nat.mul_comm _ _

/-- The boundary of the signed half of the code space is nonzero. -/
theorem signBoundary_pos (format : Format) :
    0 < format.signBoundary :=
  Nat.two_pow_pos _

/-- The signed boundary exceeds one, so code `1` lies strictly below it. -/
theorem one_lt_signBoundary (format : Format) :
    1 < format.signBoundary := by
  unfold signBoundary
  apply Nat.one_lt_two_pow
  have hwidth := format.bitWidth_gt_two
  omega

/--
At least three nonzero codes lie below the signed boundary, so at least two positive finite code
points do even when the code just below the boundary is positive infinity.
-/
theorem four_le_signBoundary (format : Format) :
    4 ≤ format.signBoundary := by
  have hwidth := format.bitWidth_gt_two
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ format.signBoundary := Nat.pow_le_pow_right (by decide) (by omega)

/-- Every valid P3109 format has more than two code points. -/
theorem two_lt_modulus (format : Format) :
    2 < format.modulus := by
  unfold modulus
  have hwidth : 1 < format.bitWidth := by
    have hvalid := format.bitWidth_gt_two
    omega
  simpa using Nat.pow_lt_pow_right (a := 2) (by decide) hwidth

/-- P3109's NaN code is never the all-zero code. -/
theorem nanBits_pos (format : Format) :
    0 < format.nanBits := by
  cases hs : format.signedness with
  | signed =>
      simpa [nanBits, hs] using format.signBoundary_pos
  | unsigned =>
      have hmodulus := format.two_lt_modulus
      simp [nanBits, hs]
      omega

/-- `positiveInfinityBits` is nonzero for every descriptor. -/
theorem positiveInfinityBits_pos (format : Format) :
    0 < format.positiveInfinityBits := by
  cases hs : format.signedness with
  | signed =>
      have hboundary := format.one_lt_signBoundary
      simp [positiveInfinityBits, hs]
      omega
  | unsigned =>
      have hmodulus := format.two_lt_modulus
      simp [positiveInfinityBits, hs]
      omega

/-- `negativeInfinityBits` is nonzero for every descriptor. -/
theorem negativeInfinityBits_pos (format : Format) :
    0 < format.negativeInfinityBits := by
  have hmodulus := format.two_lt_modulus
  simp [negativeInfinityBits]
  omega

/-- P3109's NaN code fits in the declared code space. -/
theorem nanBits_lt_modulus (format : Format) :
    format.nanBits < format.modulus := by
  cases hs : format.signedness with
  | signed =>
      simpa [nanBits, hs] using format.signBoundary_lt_modulus
  | unsigned =>
      have hmodulus : 0 < format.modulus := by
        exact Nat.two_pow_pos format.bitWidth
      simp [nanBits, hs]
      omega

/-- `positiveInfinityBits` fits in the declared code space for every descriptor. -/
theorem positiveInfinityBits_lt_modulus (format : Format) :
    format.positiveInfinityBits < format.modulus := by
  cases hs : format.signedness with
  | signed =>
      have hboundary := format.signBoundary_lt_modulus
      simp [positiveInfinityBits, hs]
      omega
  | unsigned =>
      have hmodulus := format.two_lt_modulus
      simp [positiveInfinityBits, hs]
      omega

/-- `negativeInfinityBits` fits in the declared code space for every descriptor. -/
theorem negativeInfinityBits_lt_modulus (format : Format) :
    format.negativeInfinityBits < format.modulus := by
  have hmodulus : 0 < format.modulus := by
    exact Nat.two_pow_pos format.bitWidth
  unfold negativeInfinityBits
  omega

/-- Positive infinity's code is never the midpoint code, which is the NaN code of a signed
descriptor. -/
theorem positiveInfinityBits_ne_signBoundary (format : Format) :
    format.positiveInfinityBits ≠ format.signBoundary := by
  have modulus_eq := format.modulus_eq_two_mul_signBoundary
  have boundary_large := format.four_le_signBoundary
  unfold positiveInfinityBits
  cases format.signedness <;> simp only <;> omega

/-- Negative infinity's code is never the midpoint code, which is the NaN code of a signed
descriptor. -/
theorem negativeInfinityBits_ne_signBoundary (format : Format) :
    format.negativeInfinityBits ≠ format.signBoundary := by
  have modulus_eq := format.modulus_eq_two_mul_signBoundary
  have boundary_large := format.one_lt_signBoundary
  unfold negativeInfinityBits
  rw [modulus_eq]
  omega

/-- The two infinity codes differ in every descriptor. -/
theorem negativeInfinityBits_ne_positiveInfinityBits (format : Format) :
    format.negativeInfinityBits ≠ format.positiveInfinityBits := by
  have modulus_eq := format.modulus_eq_two_mul_signBoundary
  have boundary_pos := format.signBoundary_pos
  unfold negativeInfinityBits positiveInfinityBits
  rw [modulus_eq]
  cases format.signedness <;> simp only <;> omega

/-- Positive infinity's code is distinct from the NaN code in every descriptor. -/
theorem positiveInfinityBits_ne_nanBits (format : Format) :
    format.positiveInfinityBits ≠ format.nanBits := by
  have modulus_large := format.two_lt_modulus
  have boundary_pos := format.signBoundary_pos
  unfold positiveInfinityBits nanBits
  cases format.signedness <;> simp only <;> omega

/-- The codebook of a descriptor denotes each code by the P3109 decoder. -/
@[simp, grind =] theorem codebook_denote (format : Format) :
    format.codebook.denote = format.decode := by
  unfold codebook
  rfl

/-- The generic numerical-system wrapper denotes each code by the P3109 decode function. -/
@[simp, grind =] theorem numericalSystem_denote
    (format : Format) (code : BitVec format.bitWidth) :
    format.numericalSystem.denote code = format.decode code := by
  unfold numericalSystem codebook
  rfl

/-- The all-zero positive finite code decodes to zero, the only one with a zero significand
(`decodePositiveFinite_significand_eq_zero_iff`). -/
@[simp] theorem decodePositiveFinite_zero (format : Format) :
    format.decodePositiveFinite 0 = .zero := by
  simp [decodePositiveFinite]

/-- A nonzero code in biased-exponent row zero follows the P3109 subnormal formula. -/
theorem decodePositiveFinite_of_biasedExponent_eq_zero
    (format : Format) (bits : Nat)
    (bits_ne_zero : bits ≠ 0)
    (biasedExponent_eq_zero :
      bits / 2 ^ format.trailingBits = 0) :
    format.decodePositiveFinite bits =
      {
        negative := false
        significand := bits % 2 ^ format.trailingBits
        exponent := format.minimumQuantumExponent
      } := by
  simp [decodePositiveFinite, bits_ne_zero, biasedExponent_eq_zero]

/-- A positive code outside biased-exponent row zero follows the P3109 normal formula. -/
theorem decodePositiveFinite_of_biasedExponent_ne_zero
    (format : Format) (bits : Nat)
    (biasedExponent_ne_zero :
      bits / 2 ^ format.trailingBits ≠ 0) :
    format.decodePositiveFinite bits =
      {
        negative := false
        significand :=
          2 ^ format.trailingBits + bits % 2 ^ format.trailingBits
        exponent :=
          Int.ofNat (bits / 2 ^ format.trailingBits) -
            Int.ofNat format.exponentBias + 1 - Int.ofNat format.precision
      } := by
  have bits_ne_zero : bits ≠ 0 := by
    rintro rfl
    simp at biasedExponent_ne_zero
  simp [decodePositiveFinite, bits_ne_zero, biasedExponent_ne_zero]

/-- Positive finite decoding has a zero significand if and only if the code is all zeros. -/
@[simp] theorem decodePositiveFinite_significand_eq_zero_iff
    (format : Format) (bits : Nat) :
    (format.decodePositiveFinite bits).significand = 0 ↔
      bits = 0 := by
  by_cases bits_eq_zero : bits = 0
  · simp [bits_eq_zero]
  have significand_ne_zero :
      (format.decodePositiveFinite bits).significand ≠ 0 := by
    by_cases biasedExponent_eq_zero :
        bits / 2 ^ format.trailingBits = 0
    · have trailingUnit_pos : 0 < 2 ^ format.trailingBits :=
        Nat.two_pow_pos _
      have bits_lt_trailingUnit :
          bits < 2 ^ format.trailingBits :=
        (Nat.div_eq_zero_iff.mp biasedExponent_eq_zero).resolve_left
          (ne_of_gt trailingUnit_pos)
      rw [format.decodePositiveFinite_of_biasedExponent_eq_zero
        bits bits_eq_zero biasedExponent_eq_zero]
      dsimp only
      rw [Nat.mod_eq_of_lt bits_lt_trailingUnit]
      exact bits_eq_zero
    · rw [format.decodePositiveFinite_of_biasedExponent_ne_zero
        bits biasedExponent_eq_zero]
      dsimp only
      exact ne_of_gt (Nat.add_pos_left (Nat.two_pow_pos _) _)
  simp [bits_eq_zero, significand_ne_zero]

/-- Positive finite decoding never introduces a negative sign. -/
@[simp] theorem decodePositiveFinite_negative
    (format : Format) (bits : Nat) :
    (format.decodePositiveFinite bits).negative = false := by
  unfold decodePositiveFinite
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- The minimum quantum sits `P - 1` binary places below the minimum normal exponent. -/
theorem minimumQuantumExponent_eq (format : Format) :
    format.minimumQuantumExponent =
      format.minimumNormalExponent - Int.ofNat format.trailingBits := by
  unfold minimumQuantumExponent minimumNormalExponent
  rw [format.trailingBits_int]
  omega

/-- A code in biased-exponent row zero denotes that many minimum quanta. -/
theorem decodePositiveFinite_toRat_of_lt
    (format : Format) (bits : Nat)
    (hbits : bits < 2 ^ format.trailingBits) :
    (format.decodePositiveFinite bits).toRat =
      (bits : Rat) * 2 ^ format.minimumQuantumExponent := by
  by_cases hzero : bits = 0
  · simp [hzero]
  rw [format.decodePositiveFinite_of_biasedExponent_eq_zero bits hzero
    (Nat.div_eq_of_lt hbits), Dyadic.toRat_mk_false, Nat.mod_eq_of_lt hbits]

/-- Rational value of a code written as trailing field plus a nonzero biased-exponent row. -/
theorem decodePositiveFinite_toRat_add_mul
    (format : Format) (trailing biasedExponent : Nat)
    (htrailing : trailing < 2 ^ format.trailingBits)
    (hbiased : biasedExponent ≠ 0) :
    (format.decodePositiveFinite
      (trailing + biasedExponent * 2 ^ format.trailingBits)).toRat =
      ((2 ^ format.trailingBits + trailing : Nat) : Rat) *
        2 ^ ((biasedExponent : Int) - format.exponentBias + 1 - format.precision) := by
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  have hdiv :
      (trailing + biasedExponent * 2 ^ format.trailingBits) / 2 ^ format.trailingBits =
        biasedExponent := by
    rw [Nat.add_mul_div_right _ _ hunit, Nat.div_eq_of_lt htrailing, Nat.zero_add]
  have hmod :
      (trailing + biasedExponent * 2 ^ format.trailingBits) % 2 ^ format.trailingBits =
        trailing := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htrailing]
  have hne : trailing + biasedExponent * 2 ^ format.trailingBits ≠ 0 := by
    have := Nat.mul_pos (Nat.pos_of_ne_zero hbiased) hunit
    omega
  rw [format.decodePositiveFinite_of_biasedExponent_ne_zero _
    (by rw [hdiv]; exact hbiased), Dyadic.toRat_mk_false, hdiv, hmod]
  rfl

/-- A code below the modulus survives the `BitVec` round trip, so its word decodes as that code. -/
theorem decode_ofNat_of_lt_modulus (format : Format) {bits : Nat} (h : bits < format.modulus) :
    format.decode (BitVec.ofNat format.bitWidth bits) = format.decodeNat bits := by
  rw [decode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bits < 2 ^ format.bitWidth from h)]

/-- The all-zero code denotes zero, and no other code does
(`significand_eq_zero_iff_of_decode_eq_finite`). -/
@[simp] theorem decode_zero (format : Format) :
    format.decode (BitVec.ofNat format.bitWidth 0) = .finite .zero := by
  cases hs : format.signedness <;>
    cases hd : format.domain <;>
    simp [decode, decodeNat, decodePositiveFinite, hs, hd,
      BitVec.toNat_ofNat, format.signBoundary_pos.ne,
      format.nanBits_pos.ne, format.positiveInfinityBits_pos.ne,
      format.negativeInfinityBits_pos.ne]

/-- Every signed or unsigned P3109 format decodes the P3109-specified NaN code as NaN. -/
@[simp] theorem decode_nanBits (format : Format) :
    format.decode (BitVec.ofNat format.bitWidth format.nanBits) =
      .exceptional (.nan) := by
  rw [format.decode_ofNat_of_lt_modulus format.nanBits_lt_modulus]
  cases hs : format.signedness <;>
    cases hd : format.domain <;>
    simp [decodeNat, hs, hd, nanBits]

/-- The NaN code is the only code that decodes to an exceptional value, so P3109 has one NaN. -/
theorem decode_eq_exceptional_iff (format : Format) (code : BitVec format.bitWidth)
    (exceptional : ExceptionalValue) :
    format.decode code = .exceptional exceptional ↔
      code.toNat = format.nanBits ∧ exceptional = .nan := by
  unfold decode decodeNat nanBits
  cases format.signedness <;> cases format.domain <;> simp only <;>
    split_ifs <;> simp_all [eq_comm]

/--
Only the all-zero code decodes to a finite value with a zero significand, so P3109 has one zero and
no negative zero.
-/
theorem significand_eq_zero_iff_of_decode_eq_finite (format : Format)
    (code : BitVec format.bitWidth) (value : Numerics.Dyadic)
    (hdecode : format.decode code = .finite value) :
    value.significand = 0 ↔ code.toNat = 0 := by
  unfold decode decodeNat at hdecode
  cases hs : format.signedness <;> cases hd : format.domain <;> simp only [hs, hd] at hdecode <;>
    split_ifs at hdecode <;> cases hdecode <;> simp [Numerics.Dyadic.neg] <;> omega

/-- Extended P3109 formats decode the P3109-specified positive-infinity code. -/
theorem decode_positiveInfinityBits
    (format : Format) (extended : format.domain = .extended) :
    format.decode (BitVec.ofNat format.bitWidth format.positiveInfinityBits) =
      .infinity false := by
  have hboundary := format.one_lt_signBoundary
  have hmodulus := format.two_lt_modulus
  rw [format.decode_ofNat_of_lt_modulus format.positiveInfinityBits_lt_modulus]
  cases hs : format.signedness with
  | signed =>
      have hnotNan :=
        format.positiveInfinityBits_ne_signBoundary
      simp [decodeNat, hs, extended, hnotNan]
  | unsigned =>
      have hnotNan :=
        format.positiveInfinityBits_ne_nanBits
      simp [decodeNat, hs, extended, hnotNan]

/-- Signed extended P3109 formats decode the P3109-specified negative-infinity code. -/
theorem decode_negativeInfinityBits
    (format : Format)
    (signed : format.signedness = .signed)
    (extended : format.domain = .extended) :
    format.decode (BitVec.ofNat format.bitWidth format.negativeInfinityBits) =
      .infinity true := by
  have hnotNan := format.negativeInfinityBits_ne_signBoundary
  have hnotPositiveInfinity := format.negativeInfinityBits_ne_positiveInfinityBits
  rw [format.decode_ofNat_of_lt_modulus format.negativeInfinityBits_lt_modulus]
  simp [decodeNat, signed, extended, hnotNan, hnotPositiveInfinity]

/-- A finite decoding is the positive-row formula, negated in the upper half of a signed format. -/
private theorem eq_of_decodeNat_eq_finite (format : Format) {bits : Nat} {exact : Numerics.Dyadic}
    (h : format.decodeNat bits = .finite exact) :
    exact = if format.signedness = .signed ∧ format.signBoundary < bits then
        (format.decodePositiveFinite (bits - format.signBoundary)).neg
      else format.decodePositiveFinite bits := by
  unfold decodeNat at h
  split at h <;> rename_i hs hd <;> simp only [hs, true_and, reduceCtorEq, false_and,
    ite_false] <;> split_ifs at h <;> simp_all

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

/-- Executable P3109 decoding is the descriptor's exact decoding function. -/
@[simp, grind =] theorem decode_eq_format_decode (value : ExecFloat.P3109 format) :
    decode value = format.decode (ExecFloat.Codebook.toCode value) := by
  change format.codebook.denote _ = _
  rw [Formats.P3109.Format.codebook_denote]

/-- The `zero` constructor decodes to zero, P3109's only zero
(`Format.significand_eq_zero_iff_of_decode_eq_finite`). -/
@[grind =] theorem decode_zero :
    decode (zero (format := format)) = .finite .zero := by
  rw [decode_eq_format_decode]
  exact format.decode_zero

/-- The `nan` constructor decodes to NaN, the format's only exceptional value
(`Format.decode_eq_exceptional_iff`). -/
@[grind =] theorem decode_nan :
    decode (nan (format := format)) = .exceptional (.nan) := by
  rw [decode_eq_format_decode]
  exact format.decode_nanBits

/-- In every extended format, `positiveInfinity` decodes to positive infinity. -/
@[grind =] theorem decode_positiveInfinity
    (extended : format.domain = .extended) :
    decode (positiveInfinity (format := format) extended) = .infinity false := by
  rw [decode_eq_format_decode]
  exact format.decode_positiveInfinityBits extended

/-- In signed extended formats, `negativeInfinity` decodes to negative infinity. -/
@[grind =] theorem decode_negativeInfinity
    (signed : format.signedness = .signed)
    (extended : format.domain = .extended) :
    decode (negativeInfinity (format := format) signed extended) = .infinity true := by
  rw [decode_eq_format_decode]
  exact format.decode_negativeInfinityBits signed extended

/-- A P3109 value reads as `q` if and only if it decodes to a finite dyadic with value `q`. -/
theorem toRat?_eq_some_iff (value : ExecFloat.P3109 format) (q : Rat) :
    toRat? value = some q ↔ ∃ exact, decode value = .finite exact ∧ exact.toRat = q := by
  unfold toRat?
  cases decode value <;> simp

/-- A P3109 value has no rational reading if and only if it decodes to NaN or an infinity. -/
theorem toRat?_eq_none_iff (value : ExecFloat.P3109 format) :
    toRat? value = none ↔ (decode value).isFinite = false := by
  unfold toRat?
  cases decode value <;> simp

/-- The `zero` constructor reads as the rational zero. -/
@[simp, grind =] theorem toRat?_zero :
    toRat? (zero (format := format)) = some 0 := by
  rw [toRat?, decode_zero]
  simp

/-- The `nan` constructor has no rational reading. -/
@[simp, grind =] theorem toRat?_nan :
    toRat? (nan (format := format)) = none := by
  rw [toRat?, decode_nan]
  rfl

/-- Positive infinity has no rational reading. -/
@[simp, grind =] theorem toRat?_positiveInfinity
    (extended : format.domain = .extended) :
    toRat? (positiveInfinity (format := format) extended) = none := by
  rw [toRat?, decode_positiveInfinity extended]
  rfl

/-- Negative infinity has no rational reading. -/
@[simp, grind =] theorem toRat?_negativeInfinity
    (signed : format.signedness = .signed)
    (extended : format.domain = .extended) :
    toRat? (negativeInfinity (format := format) signed extended) = none := by
  rw [toRat?, decode_negativeInfinity signed extended]
  rfl

/-- Natural-number construction reduces modulo `2^K`, where `K` is the encoded width. -/
@[simp, grind =] theorem toNatBits_ofNatBits (bits : Nat) :
    toNatBits (ofNatBits (format := format) bits) =
      bits % 2 ^ format.bitWidth :=
  ExecFloat.Codebook.toNatBits_ofNatBits bits

/--
A successful structured-field construction denotes the value its fields name: both fields are
within their widths, and the value is the positive finite code
`biasedExponent * 2 ^ trailingBits + trailing`, negated when `negative` is set.
-/
theorem decode_of_ofFiniteFields?_eq_some
    (negative : Bool) (biasedExponent trailing : Nat)
    (value : ExecFloat.P3109 format)
    (success : ofFiniteFields? (format := format) negative biasedExponent trailing = some value) :
    biasedExponent < 2 ^ format.exponentBits ∧ trailing < 2 ^ format.trailingBits ∧
      decode value = .finite
        (if negative then
          (format.decodePositiveFinite (biasedExponent * 2 ^ format.trailingBits + trailing)).neg
        else format.decodePositiveFinite (biasedExponent * 2 ^ format.trailingBits + trailing)) := by
  unfold ofFiniteFields? at success
  split at success
  · contradiction
  rename_i hsign
  have hsigned : negative = true → format.signedness = .signed := by
    intro hnegative
    cases h : format.signedness
    · rfl
    · exact absurd ⟨hnegative, h⟩ hsign
  split at success
  swap
  · contradiction
  rename_i hfields
  refine ⟨hfields.1, hfields.2, ?_⟩
  generalize hmagnitude : biasedExponent * 2 ^ format.trailingBits + trailing = magnitude at success ⊢
  have hlt : magnitude < 2 ^ format.exponentBits * 2 ^ format.trailingBits :=
    calc magnitude = biasedExponent * 2 ^ format.trailingBits + trailing := hmagnitude.symm
      _ < biasedExponent * 2 ^ format.trailingBits + 2 ^ format.trailingBits :=
          Nat.add_lt_add_left hfields.2 _
      _ = (biasedExponent + 1) * 2 ^ format.trailingBits := (Nat.succ_mul _ _).symm
      _ ≤ 2 ^ format.exponentBits * 2 ^ format.trailingBits :=
          Nat.mul_le_mul_right _ hfields.1
  have hT := format.trailingBits_add_one
  have hP := format.precision_le_bitWidth
  have hK := format.bitWidth_pos
  have hbound : (format.signedness = .signed → magnitude < format.signBoundary) ∧
      magnitude < format.modulus := by
    rw [← pow_add] at hlt
    cases hs : format.signedness with
    | signed =>
        have hPK := format.precision_lt_bitWidth_of_signed hs
        have hexp : format.exponentBits + format.trailingBits = format.bitWidth - 1 := by
          simp only [Formats.P3109.Format.exponentBits, hs]; omega
        rw [hexp] at hlt
        refine ⟨fun _ => hlt, hlt.trans format.signBoundary_lt_modulus⟩
    | unsigned =>
        have hexp : format.exponentBits + format.trailingBits = format.bitWidth := by
          simp only [Formats.P3109.Format.exponentBits, hs]; omega
        rw [hexp] at hlt
        exact ⟨fun h => absurd h (by simp), hlt⟩
  dsimp only at success
  have hbitsLt : (if negative = true then format.signBoundary + magnitude else magnitude) <
      format.modulus := by
    have := format.modulus_eq_two_mul_signBoundary
    cases negative with
    | false => exact hbound.2
    | true =>
        have := hbound.1 (hsigned rfl)
        simp only [ite_true]
        omega
  have hdecodeBits (bits : Nat) (h : bits < format.modulus) :
      ExecFloat.Codebook.decode (ExecFloat.Codebook.ofNatBits bits : ExecFloat.P3109 format) =
        format.decodeNat bits := by
    change decode _ = _
    rw [decode_eq_format_decode]
    exact format.decode_ofNat_of_lt_modulus h
  rw [hdecodeBits _ hbitsLt] at success
  cases hdecoded : format.decodeNat
      (if negative = true then format.signBoundary + magnitude else magnitude) with
  | infinity _ => simp [hdecoded] at success
  | exceptional _ => simp [hdecoded] at success
  | finite exact =>
      simp only [hdecoded, Option.some.injEq] at success
      subst success
      change ExecFloat.Codebook.decode _ = _
      rw [hdecodeBits _ hbitsLt, hdecoded,
        Formats.P3109.Format.eq_of_decodeNat_eq_finite format hdecoded]
      cases negative with
      | false =>
          have : ¬(format.signedness = .signed ∧ format.signBoundary < magnitude) := by
            rintro ⟨hs, h⟩
            exact absurd (hbound.1 hs) (by omega)
          simp [this]
      | true =>
          have hs := hsigned rfl
          have hpos : 0 < magnitude := by
            rcases Nat.eq_zero_or_pos magnitude with h0 | h0
            · subst h0
              have := hdecoded
              simp only [ite_true, Nat.add_zero] at this
              unfold Formats.P3109.Format.decodeNat at this
              rw [hs] at this
              cases hd : format.domain <;> simp [hd] at this
            · exact h0
          simp [hs, hpos]

/--
A successful structured-field construction denotes an ordinary finite value.

This is the elimination rule for `ofFiniteFields?`, so callers need not reason about the
descriptor's reserved code points after the constructor succeeds. The value itself is given by
`decode_of_ofFiniteFields?_eq_some`.
-/
theorem exists_decode_finite_of_ofFiniteFields?_eq_some
    (negative : Bool) (biasedExponent trailing : Nat)
    (value : ExecFloat.P3109 format)
    (success : ofFiniteFields? (format := format) negative biasedExponent trailing = some value) :
    ∃ exact, decode value = .finite exact :=
  ⟨_, (decode_of_ofFiniteFields?_eq_some negative biasedExponent trailing value success).2.2⟩

end FloatLib.Floats.ExecFloat.P3109
