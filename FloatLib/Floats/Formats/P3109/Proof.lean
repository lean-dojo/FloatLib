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

A validated P3109 descriptor defines an exact-width `NumericalSystem` and `ExecFloat` carrier.
These theorems connect their denotations to P3109 decoding. Descriptor validation supplies the
field-width, special-encoding, and storage conditions used by the proofs.
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

/-- An unsigned descriptor carries the `P ≤ K` requirement from P3109. -/
theorem precision_le_bitWidth_of_unsigned
    (format : Format) (unsigned : format.signedness = .unsigned) :
    format.precision ≤ format.bitWidth := by
  simpa [unsigned] using format.precision_bound

/-- The P3109 exponent field is nonempty for every valid descriptor. -/
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

/-- At least two positive finite code points lie below the signed boundary. -/
theorem one_lt_signBoundary (format : Format) :
    1 < format.signBoundary := by
  unfold signBoundary
  apply Nat.one_lt_two_pow
  have hwidth := format.bitWidth_gt_two
  omega

/-- Every valid P3109 format has more than two code points. -/
theorem two_lt_modulus (format : Format) :
    2 < format.modulus := by
  unfold modulus
  have hwidth : 1 < format.bitWidth := by
    have hvalid := format.bitWidth_gt_two
    omega
  simpa using Nat.pow_lt_pow_right (a := 2) (by decide) hwidth

/-- The single P3109 NaN code is never the all-zero code. -/
theorem nanBits_pos (format : Format) :
    0 < format.nanBits := by
  cases hs : format.signedness with
  | signed =>
      simpa [nanBits, hs] using format.signBoundary_pos
  | unsigned =>
      have hmodulus := format.two_lt_modulus
      simp [nanBits, hs]
      omega

/-- The extended-domain positive-infinity code is never the all-zero code. -/
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

/-- The signed extended-domain negative-infinity code is never the all-zero code. -/
theorem negativeInfinityBits_pos (format : Format) :
    0 < format.negativeInfinityBits := by
  have hmodulus := format.two_lt_modulus
  simp [negativeInfinityBits]
  omega

/-- The sole P3109 NaN code fits in the declared code space. -/
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

/-- The positive-infinity code, when active, fits in the declared code space. -/
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

/-- The negative-infinity code, when active, fits in the declared code space. -/
theorem negativeInfinityBits_lt_modulus (format : Format) :
    format.negativeInfinityBits < format.modulus := by
  have hmodulus : 0 < format.modulus := by
    exact Nat.two_pow_pos format.bitWidth
  unfold negativeInfinityBits
  omega

/-- In a signed descriptor, positive infinity is distinct from the midpoint NaN code. -/
theorem positiveInfinityBits_ne_signBoundary_of_signed
    (format : Format) (signed : format.signedness = .signed) :
    format.positiveInfinityBits ≠ format.signBoundary := by
  have boundary_large := format.one_lt_signBoundary
  simp [positiveInfinityBits, signed]
  omega

/-- In a signed descriptor, negative infinity is distinct from the midpoint NaN code. -/
theorem negativeInfinityBits_ne_signBoundary_of_signed
    (format : Format) (_signed : format.signedness = .signed) :
    format.negativeInfinityBits ≠ format.signBoundary := by
  have modulus_eq := format.modulus_eq_two_mul_signBoundary
  have boundary_large := format.one_lt_signBoundary
  unfold negativeInfinityBits
  rw [modulus_eq]
  omega

/-- The two infinity codes are distinct in every signed descriptor. -/
theorem negativeInfinityBits_ne_positiveInfinityBits_of_signed
    (format : Format) (signed : format.signedness = .signed) :
    format.negativeInfinityBits ≠ format.positiveInfinityBits := by
  have modulus_eq := format.modulus_eq_two_mul_signBoundary
  have boundary_pos := format.signBoundary_pos
  unfold negativeInfinityBits positiveInfinityBits
  simp only [signed]
  rw [modulus_eq]
  omega

/-- In an unsigned descriptor, positive infinity is distinct from the terminal NaN code. -/
theorem positiveInfinityBits_ne_nanBits_of_unsigned
    (format : Format) (unsigned : format.signedness = .unsigned) :
    format.positiveInfinityBits ≠ format.nanBits := by
  have modulus_large := format.two_lt_modulus
  simp [positiveInfinityBits, nanBits, unsigned]
  omega

/-- The generic numerical-system wrapper denotes exactly the P3109 decode function. -/
@[simp, grind =] theorem numericalSystem_denote
    (format : Format) (code : BitVec format.bitWidth) :
    format.numericalSystem.denote code = format.decode code :=
  rfl

/-- The all-zero positive finite code decodes to the unique P3109 zero. -/
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
    (bits_ne_zero : bits ≠ 0)
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
  simp [decodePositiveFinite, bits_ne_zero, biasedExponent_ne_zero]

/-- Positive finite decoding has zero significand exactly at the all-zero code. -/
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
        bits bits_eq_zero biasedExponent_eq_zero]
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
  rw [format.decodePositiveFinite_of_biasedExponent_ne_zero _ hne
    (by rw [hdiv]; exact hbiased), Dyadic.toRat_mk_false, hdiv, hmod]
  rfl

/-- The all-zero code denotes P3109's unique zero. -/
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
  have hnan := format.nanBits_lt_modulus
  have hnan' : format.nanBits < 2 ^ format.bitWidth := by
    simpa [modulus] using hnan
  simp only [decode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnan']
  cases hs : format.signedness <;>
    cases hd : format.domain <;>
    simp [decodeNat, hs, hd, nanBits]

/-- Extended P3109 formats decode the P3109-specified positive-infinity code. -/
theorem decode_positiveInfinityBits
    (format : Format) (extended : format.domain = .extended) :
    format.decode (BitVec.ofNat format.bitWidth format.positiveInfinityBits) =
      .infinity false := by
  have hcode := format.positiveInfinityBits_lt_modulus
  have hcode' : format.positiveInfinityBits < 2 ^ format.bitWidth := by
    simpa [modulus] using hcode
  have hboundary := format.one_lt_signBoundary
  have hmodulus := format.two_lt_modulus
  simp only [decode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcode']
  cases hs : format.signedness with
  | signed =>
      have hnotNan :=
        format.positiveInfinityBits_ne_signBoundary_of_signed hs
      simp [decodeNat, hs, extended, hnotNan]
  | unsigned =>
      have hnotNan :=
        format.positiveInfinityBits_ne_nanBits_of_unsigned hs
      simp [decodeNat, hs, extended, hnotNan]

/-- Signed extended P3109 formats decode the P3109-specified negative-infinity code. -/
theorem decode_negativeInfinityBits
    (format : Format)
    (signed : format.signedness = .signed)
    (extended : format.domain = .extended) :
    format.decode (BitVec.ofNat format.bitWidth format.negativeInfinityBits) =
      .infinity true := by
  have hcode := format.negativeInfinityBits_lt_modulus
  have hcode' : format.negativeInfinityBits < 2 ^ format.bitWidth := by
    simpa [modulus] using hcode
  have hnotNan :=
    format.negativeInfinityBits_ne_signBoundary_of_signed signed
  have hnotPositiveInfinity :=
    format.negativeInfinityBits_ne_positiveInfinityBits_of_signed signed
  simp [decode, decodeNat, signed, extended, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hcode', hnotNan, hnotPositiveInfinity]

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

/-- The user-facing zero constructor denotes P3109's unique finite zero. -/
@[grind =] theorem decode_zero :
    decode (zero (format := format)) = .finite .zero := by
  change format.decode (BitVec.ofNat format.bitWidth 0) = .finite .zero
  exact format.decode_zero

/-- The user-facing NaN constructor denotes the format's sole exceptional NaN value. -/
@[grind =] theorem decode_nan :
    decode (nan (format := format)) = .exceptional (.nan) := by
  change format.decode (BitVec.ofNat format.bitWidth format.nanBits) =
    .exceptional (.nan)
  exact format.decode_nanBits

/-- The positive-infinity constructor has its advertised meaning in every extended format. -/
@[grind =] theorem decode_positiveInfinity
    (extended : format.domain = .extended) :
    decode (positiveInfinity (format := format) extended) = .infinity false := by
  change format.decode
      (BitVec.ofNat format.bitWidth format.positiveInfinityBits) = .infinity false
  exact format.decode_positiveInfinityBits extended

/-- The negative-infinity constructor has its advertised meaning in signed extended formats. -/
@[grind =] theorem decode_negativeInfinity
    (signed : format.signedness = .signed)
    (extended : format.domain = .extended) :
    decode (negativeInfinity (format := format) signed extended) = .infinity true := by
  change format.decode
      (BitVec.ofNat format.bitWidth format.negativeInfinityBits) = .infinity true
  exact format.decode_negativeInfinityBits signed extended

/-- Natural-number construction reduces modulo `2^K`, where `K` is the encoded width. -/
@[simp, grind =] theorem toNatBits_ofNatBits (bits : Nat) :
    toNatBits (ofNatBits (format := format) bits) =
      bits % 2 ^ format.bitWidth :=
  ExecFloat.Codebook.toNatBits_ofNatBits bits

/-- Executable P3109 decoding is definitionally the descriptor's exact decoding function. -/
@[simp, grind =] theorem decode_eq_format_decode (value : ExecFloat.P3109 format) :
    decode value = format.decode (ExecFloat.Codebook.toCode value) :=
  rfl

private theorem exists_decode_finite_of_checked_candidate_eq_some
    (candidate value : ExecFloat.P3109 format)
    (success :
      (match ExecFloat.Codebook.decode candidate with
      | .finite _ => some candidate
      | .infinity _ | .exceptional _ => none) = some value) :
    ∃ exact, decode value = .finite exact := by
  cases decoded : ExecFloat.Codebook.decode candidate with
  | finite exact =>
      simp [decoded] at success
      subst value
      exact ⟨exact, decoded⟩
  | infinity negative => simp [decoded] at success
  | exceptional exceptional => simp [decoded] at success

/--
A successful structured-field construction is guaranteed to denote an ordinary finite value.

This theorem is the elimination rule for `ofFiniteFields?`: callers need not reason about the
descriptor's reserved code points after the constructor succeeds.
-/
theorem exists_decode_finite_of_ofFiniteFields?_eq_some
    (negative : Bool) (biasedExponent trailing : Nat)
    (value : ExecFloat.P3109 format)
    (success : ofFiniteFields? (format := format) negative biasedExponent trailing = some value) :
    ∃ exact, decode value = .finite exact := by
  unfold ofFiniteFields? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;>
    exact exists_decode_finite_of_checked_candidate_eq_some _ _ success

end FloatLib.Floats.ExecFloat.P3109
