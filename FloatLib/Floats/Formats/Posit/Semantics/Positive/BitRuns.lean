/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Decode
public import FloatLib.Numerics.Bitwise
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify

/-!
# Fixed-width bit runs in positive Posit encodings

Representation lemmas describe bit runs in the nonnegative half of a Posit Standard encoding.
Exact-width leading runs are reduced to `Nat.log2`; a run of one bits is reduced to the
leading-zero run of the fixed-width complement using mathlib's `BitVec` complement theorems; and
equal or ordered regime prefixes are related to the remaining encoded tail.

These facts are independent of the storage carrier. Tail-order and rounding proofs use them
alongside native execution backends.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
Exact rational value of the posit word with unsigned code `code`.

Codes in `[0, format.signMaskNat)` are the nonnegative finite posits. The function is total on
naturals: it first reduces the code modulo the format's modulus, then maps zero and NaR to zero
and other words to their signed rational value.
-/
@[inline] def nonnegativeRatAt (format : Format) (code : Nat) : Rat :=
  match decodeExact (ofNatBits (format := format) code) with
  | .zero => 0
  | .finite fields => fields.toRat
  | .nar => 0

/-- A positive code below the sign mask takes the finite branch of exact posit decoding. -/
theorem nonnegativeRatAt_of_pos_lt_signMask
    (format : Format) {code : Nat}
    (hpos : 0 < code) (hcode : code < format.signMaskNat) :
    nonnegativeRatAt format code =
      (ofNatBits (format := format) code).decodeFields.toRat := by
  let value := ofNatBits (format := format) code
  have hcodeModulus : code < format.modulus :=
    hcode.trans format.signMaskNat_lt_modulus
  have hvalueCode : value.toNatBits = code :=
    toNatBits_ofNatBits_of_lt code hcodeModulus
  have hzero : value.isZero = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hvalue := (isZero_eq_true_iff value).mp htrue
    have hbits := congrArg toNatBits hvalue
    rw [hvalueCode, zero_toNatBits] at hbits
    omega
  have hnar : value.isNaR = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hvalue := (isNaR_eq_true_iff value).mp htrue
    have hbits := congrArg toNatBits hvalue
    rw [hvalueCode, nar_toNatBits] at hbits
    omega
  simp [nonnegativeRatAt, decodeExact, value,
    hzero, hnar]

/-! ## Fixed-width bit runs -/

/--
For a positive value bounded by `2 ^ width`, the leading-zero run is the width minus its binary
length.
-/
theorem countLeadingRun_false_eq_log2
    (value width : Nat) (hpos : 0 < value) (hlt : value < 2 ^ width) :
    countLeadingRun value width false =
      width - (Nat.log2 value + 1) := by
  induction width generalizing value with
  | zero =>
      simp at hlt
      omega
  | succ width inductionHypothesis =>
      have htopBound : value < 2 ^ (width + 1) := by
        simpa using hlt
      cases htop : value.testBit width with
      | false =>
          rw [countLeadingRun]
          simp only [htop]
          simp
          have hnotLower : ¬2 ^ width ≤ value := by
            intro hlower
            have htrue :=
              (Nat.testBit_eq_true_iff_two_pow_le_of_lt htopBound).2 hlower
            rw [htop] at htrue
            contradiction
          have hlower : value < 2 ^ width :=
            Nat.lt_of_not_ge hnotLower
          rw [inductionHypothesis value hpos hlower]
          have hlogLt : Nat.log2 value < width := by
            rw [Nat.log2_eq_log_two]
            exact Nat.log_lt_of_lt_pow hpos.ne' hlower
          omega
      | true =>
          rw [countLeadingRun]
          simp only [htop]
          simp
          have hlower : 2 ^ width ≤ value :=
            (Nat.testBit_eq_true_iff_two_pow_le_of_lt htopBound).1 htop
          have hlog : Nat.log2 value = width :=
            (Nat.log2_eq_iff hpos.ne').2
              ⟨hlower, by simpa using hlt⟩
          omega

/-- Reducing modulo `2 ^ width` preserves every inspected bit below `width`. -/
private theorem testBit_mod_twoPow
    (value index width : Nat) (hindex : index < width) :
    (value % 2 ^ width).testBit index = value.testBit index := by
  have hgap : 0 < width - index :=
    Nat.sub_pos_of_lt hindex
  have hpow :
      2 ^ width = 2 ^ (width - index) * 2 ^ index := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdvd : 2 ∣ 2 ^ (width - index) := by
    rw [show width - index = (width - index - 1) + 1 by omega,
      Nat.pow_succ]
    simp
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow,
    Nat.one_and_eq_mod_two]
  rw [hpow, Nat.mod_mul_left_div_self]
  rw [← Nat.mod_mod_of_dvd (value / 2 ^ index) hdvd]

/-- A leading-run scan depends only on the low `width` bits being scanned. -/
theorem countLeadingRun_mod_twoPow
    (value width : Nat) (bit : Bool) :
    countLeadingRun value width bit =
      countLeadingRun (value % 2 ^ width) width bit := by
  induction width generalizing value bit with
  | zero =>
      rfl
  | succ width inductionHypothesis =>
      rw [countLeadingRun, countLeadingRun]
      rw [testBit_mod_twoPow value width (width + 1) (by omega)]
      congr 1
      rw [inductionHypothesis value bit]
      rw [inductionHypothesis (value % 2 ^ (width + 1)) bit]
      have hdvd : 2 ^ width ∣ 2 ^ (width + 1) := by
        rw [Nat.pow_succ]
        exact dvd_mul_right _ _
      rw [Nat.mod_mod_of_dvd value hdvd]

/-- Fixed-width subtraction from the all-ones word flips every bit in range. -/
private theorem testBit_fixedComplement
    (value index width : Nat)
    (hvalue : value < 2 ^ width)
    (hindex : index < width) :
    (2 ^ width - 1 - value).testBit index =
      !value.testBit index := by
  let bits := BitVec.ofNat width value
  have hbits : bits.toNat = value := by
    simp [bits, Nat.mod_eq_of_lt hvalue]
  have hnot :
      (~~~bits).toNat = 2 ^ width - 1 - value := by
    simp [hbits]
  rw [← hnot, ← hbits]
  change (~~~bits)[index] = !bits[index]
  exact BitVec.getElem_not hindex

/-- Complementary bit streams have complementary leading runs. -/
theorem countLeadingRun_true_eq_false_of_testBit_flip
    (left right width : Nat)
    (hflip : ∀ index, index < width →
      right.testBit index = !left.testBit index) :
    countLeadingRun left width true =
      countLeadingRun right width false := by
  induction width generalizing left right with
  | zero =>
      rfl
  | succ width inductionHypothesis =>
      have htop := hflip width (by omega)
      cases hleft : left.testBit width with
      | false =>
          have hright : right.testBit width = true := by
            simpa [hleft] using htop
          simp [countLeadingRun, hleft, hright]
      | true =>
          have hright : right.testBit width = false := by
            simpa [hleft] using htop
          simp only [countLeadingRun, hleft, hright]
          simp
          rw [inductionHypothesis left right]
          exact fun index hindex => hflip index (by omega)

/--
A leading-one run is the leading-zero run of the complement inside the same fixed width.
-/
theorem countLeadingRun_true_eq_fixedComplement
    (value width : Nat) (hvalue : value < 2 ^ width) :
    countLeadingRun value width true =
      countLeadingRun (2 ^ width - 1 - value) width false := by
  apply countLeadingRun_true_eq_false_of_testBit_flip
  intro index hindex
  exact testBit_fixedComplement value index width hvalue hindex

/-- The all-zero word has a zero-bit run occupying the complete inspected width. -/
@[simp] theorem countLeadingRun_zero_false (width : Nat) :
    countLeadingRun 0 width false = width := by
  induction width with
  | zero =>
      rfl
  | succ width inductionHypothesis =>
      simp [countLeadingRun, inductionHypothesis, Nat.add_comm]

/--
Within a fixed width, increasing an unsigned word can only shorten its leading-zero run.
-/
theorem countLeadingRun_false_anti
    {left right width : Nat}
    (hle : left ≤ right)
    (hright : right < 2 ^ width) :
    countLeadingRun right width false ≤
      countLeadingRun left width false := by
  have hleft : left < 2 ^ width :=
    lt_of_le_of_lt hle hright
  by_cases hleftZero : left = 0
  · subst left
    rw [countLeadingRun_zero_false]
    exact countLeadingRun_le _ _ _
  · have hleftPos : 0 < left :=
      Nat.pos_of_ne_zero hleftZero
    have hrightPos : 0 < right :=
      lt_of_lt_of_le hleftPos hle
    rw [countLeadingRun_false_eq_log2
      right width hrightPos hright]
    rw [countLeadingRun_false_eq_log2
      left width hleftPos hleft]
    have hlog : Nat.log2 left ≤ Nat.log2 right := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right hle
    omega

/--
Within a fixed width, increasing an unsigned word can only lengthen its leading-one run.
-/
theorem countLeadingRun_true_mono
    {left right width : Nat}
    (hle : left ≤ right)
    (hright : right < 2 ^ width) :
    countLeadingRun left width true ≤
      countLeadingRun right width true := by
  have hleft : left < 2 ^ width :=
    lt_of_le_of_lt hle hright
  rw [countLeadingRun_true_eq_fixedComplement left width hleft]
  rw [countLeadingRun_true_eq_fixedComplement right width hright]
  apply countLeadingRun_false_anti
  · omega
  · have hpower : 0 < 2 ^ width :=
      Nat.two_pow_pos width
    omega

/-- The binary length of `2 * value + 1` is one more than that of a positive `value`. -/
private theorem log2_two_mul_add_one
    {value : Nat} (hpos : 0 < value) :
    Nat.log2 (2 * value + 1) =
      Nat.log2 value + 1 := by
  apply (Nat.log2_eq_iff (by omega)).2
  have hlower := Nat.log2_self_le hpos.ne'
  have hupper := Nat.lt_log2_self (n := value)
  constructor
  · rw [Nat.pow_succ]
    omega
  · rw [show Nat.log2 value + 1 + 1 =
      (Nat.log2 value + 1) + 1 by omega,
      Nat.pow_succ]
    omega

/--
Appending a low zero bit to a positive bounded word preserves its leading regime run.

For the all-ones word the appended zero becomes the first terminator, and the run length is again
unchanged.
-/
theorem countLeadingRun_two_mul
    {value width : Nat} (hpos : 0 < value)
    (hbound : value < 2 ^ width) :
    countLeadingRun (2 * value) (width + 1)
        ((2 * value).testBit width) =
      countLeadingRun value width
        (value.testBit (width - 1)) := by
  have hwidth : 0 < width := by
    by_contra hzero
    have : width = 0 := by omega
    subst width
    simp at hbound
    omega
  have hdoubleBound :
      2 * value < 2 ^ (width + 1) := by
    rw [Nat.pow_succ]
    omega
  have htop :
      (2 * value).testBit width =
        value.testBit (width - 1) := by
    rw [show width = (width - 1) + 1 by omega,
      Nat.testBit_succ]
    norm_num
  rw [htop]
  cases hbit :
      value.testBit (width - 1) with
  | false =>
      rw [countLeadingRun_false_eq_log2
        value width hpos hbound]
      rw [countLeadingRun_false_eq_log2
        (2 * value) (width + 1)
          (by omega) hdoubleBound]
      rw [Nat.log2_two_mul hpos.ne']
      omega
  | true =>
      rw [countLeadingRun_true_eq_fixedComplement
        value width hbound]
      rw [countLeadingRun_true_eq_fixedComplement
        (2 * value) (width + 1) hdoubleBound]
      let complement :=
        2 ^ width - 1 - value
      have hnewComplement :
          2 ^ (width + 1) - 1 - 2 * value =
            2 * complement + 1 := by
        dsimp [complement]
        rw [Nat.pow_succ]
        omega
      rw [hnewComplement]
      change
        countLeadingRun (2 * complement + 1)
            (width + 1) false =
          countLeadingRun complement width false
      by_cases hcomplementZero :
          complement = 0
      · rw [hcomplementZero]
        rw [countLeadingRun_false_eq_log2
          1 (width + 1) (by decide)
            (Nat.one_lt_two_pow (by omega))]
        rw [show Nat.log2 1 = 0 by decide,
          countLeadingRun_zero_false]
        omega
      · have hcomplementPos : 0 < complement :=
          Nat.pos_of_ne_zero hcomplementZero
        have hcomplementBound :
            complement < 2 ^ width := by
          dsimp [complement]
          have hpower := Nat.two_pow_pos width
          omega
        have hnewBound :
            2 * complement + 1 <
              2 ^ (width + 1) := by
          rw [Nat.pow_succ]
          omega
        rw [countLeadingRun_false_eq_log2
          complement width
            hcomplementPos hcomplementBound]
        rw [countLeadingRun_false_eq_log2
          (2 * complement + 1) (width + 1)
            (by omega) hnewBound]
        rw [log2_two_mul_add_one
          hcomplementPos]
        omega

/-- The regime bit of a nonnegative code is the top bit of its payload. -/
theorem regimeBit_ofNatBits (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    (ofNatBits (format := format) code).regimeBit =
      code.testBit (format.payloadBits - 1) := by
  unfold regimeBit
  rw [magnitudeBits_ofNatBits_of_lt_signMask format code hcode]

/--
The regime bit of a nonnegative code is set exactly when the code is at least the code of one.
-/
theorem regimeBit_ofNatBits_eq_true_iff (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    (ofNatBits (format := format) code).regimeBit = true ↔
      format.oneCodeNat ≤ code := by
  rw [regimeBit_ofNatBits format hcode]
  have hpayload := format.payloadBits_pos
  exact Nat.testBit_eq_true_iff_two_pow_le_of_lt
    (by rw [Nat.sub_add_cancel hpayload]; exact hcode)

/-- The regime run of a nonnegative code is the leading run of its top payload bit. -/
theorem regimeRunLength_ofNatBits (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    (ofNatBits (format := format) code).regimeRunLength =
      countLeadingRun code format.payloadBits
        (code.testBit (format.payloadBits - 1)) := by
  unfold regimeRunLength
  rw [regimeBit_ofNatBits format hcode,
    magnitudeBits_ofNatBits_of_lt_signMask format code hcode]

/--
Unsigned code order below the sign mask induces nondecreasing signed regime values.

Below the code of one, leading-zero runs shorten as codes rise; at and above it, leading-one runs
lengthen.
-/
theorem regimeValue_ofNatBits_le_of_le
    (format : Format) {left right : Nat}
    (hle : left ≤ right)
    (hright : right < format.signMaskNat) :
    (ofNatBits (format := format) left).regimeValue ≤
      (ofNatBits (format := format) right).regimeValue := by
  have hleft : left < format.signMaskNat := lt_of_le_of_lt hle hright
  have hleftPos := regimeRunLength_pos (ofNatBits (format := format) left)
  have hrightPos := regimeRunLength_pos (ofNatBits (format := format) right)
  have hleftOne := regimeBit_ofNatBits_eq_true_iff format hleft
  have hrightOne := regimeBit_ofNatBits_eq_true_iff format hright
  unfold regimeValue
  rw [regimeRunLength_ofNatBits format hleft, regimeRunLength_ofNatBits format hright,
    regimeBit_ofNatBits format hleft, regimeBit_ofNatBits format hright] at *
  cases hleftBit : left.testBit (format.payloadBits - 1) <;>
    cases hrightBit : right.testBit (format.payloadBits - 1) <;>
      simp only [hleftBit, hrightBit] at *
  · exact neg_le_neg (Int.ofNat_le.mpr (countLeadingRun_false_anti hle hright))
  · simp
    omega
  · simp at hleftOne hrightOne
    omega
  · simp
    exact countLeadingRun_true_mono hle hright

/--
Two decoded words have the same regime value exactly when both the regime bit and run length
agree.

The positivity of every regime run separates the negative zero-run regimes from the nonnegative
one-run regimes.
-/
theorem regimeValue_eq_iff (left right : Model format) :
    left.regimeValue = right.regimeValue ↔
      left.regimeBit = right.regimeBit ∧
        left.regimeRunLength = right.regimeRunLength := by
  have hleftPos := regimeRunLength_pos left
  have hrightPos := regimeRunLength_pos right
  unfold regimeValue
  cases left.regimeBit <;> cases right.regimeBit <;> simp <;> omega

/-- A bounded word has a full leading-zero run exactly when the word is zero. -/
private theorem countLeadingRun_false_eq_width_iff
    {value width : Nat} (hvalue : value < 2 ^ width) :
    countLeadingRun value width false = width ↔ value = 0 := by
  constructor
  · intro hrun
    by_contra hzero
    have hpos : 0 < value :=
      Nat.pos_of_ne_zero hzero
    rw [countLeadingRun_false_eq_log2
      value width hpos hvalue] at hrun
    have hlogLt : Nat.log2 value < width := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_of_lt_pow hpos.ne' hvalue
    omega
  · rintro rfl
    exact countLeadingRun_zero_false width

/--
Discarding the low bits after a leading-zero regime's one-bit terminator leaves the fixed
prefix `1`.
-/
private theorem div_twoPow_after_false_run
    {value width : Nat} (hpos : 0 < value)
    (hlt : value < 2 ^ width) :
    value /
        2 ^ (width - countLeadingRun value width false - 1) =
      1 := by
  have hrun :=
    countLeadingRun_false_eq_log2 value width hpos hlt
  have hlogLt : Nat.log2 value < width := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow hpos.ne' hlt
  have htrailing :
      width - countLeadingRun value width false - 1 =
        Nat.log2 value := by
    omega
  rw [htrailing]
  apply Nat.div_eq_of_lt_le
  · simpa using Nat.log2_self_le hpos.ne'
  · have hupper := Nat.lt_log2_self (n := value)
    simpa [Nat.pow_succ, Nat.mul_comm] using hupper

/--
For a leading-one regime, division after its terminator leaves the fixed all-ones-then-zero
prefix. The complement's logarithm is exactly the number of remaining low bits.
-/
private theorem div_twoPow_after_true_run
    {value width : Nat} (hvalue : value < 2 ^ width)
    (hcomplement : 0 < 2 ^ width - 1 - value) :
    value / 2 ^ Nat.log2 (2 ^ width - 1 - value) =
      2 ^ (width - Nat.log2 (2 ^ width - 1 - value)) -
        2 := by
  let complement := 2 ^ width - 1 - value
  let trailing := Nat.log2 complement
  have hcomplementBound : complement < 2 ^ width := by
    dsimp [complement]
    have hpower := Nat.two_pow_pos width
    omega
  have htrailingLt : trailing < width := by
    dsimp [trailing]
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow
      hcomplement.ne' hcomplementBound
  have hwidthSubPos : 0 < width - trailing :=
    Nat.sub_pos_of_lt htrailingLt
  have hprefixPower : 2 ≤ 2 ^ (width - trailing) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (width - trailing) :=
        Nat.pow_le_pow_right (by decide) hwidthSubPos
  have hpower :
      2 ^ (width - trailing) * 2 ^ trailing =
        2 ^ width := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdecomposition :
      value + complement = 2 ^ width - 1 := by
    dsimp [complement]
    omega
  have hcomplementLower :
      2 ^ trailing ≤ complement := by
    dsimp [trailing]
    exact Nat.log2_self_le hcomplement.ne'
  have hcomplementUpper :
      complement < 2 ^ (trailing + 1) := by
    dsimp [trailing]
    exact Nat.lt_log2_self
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, hpower]
    have hdouble :
        2 * 2 ^ trailing = 2 ^ (trailing + 1) := by
      rw [Nat.pow_succ]
      omega
    rw [hdouble]
    omega
  · have hsuccessor :
        2 ^ (width - trailing) - 2 + 1 =
          2 ^ (width - trailing) - 1 := by
      omega
    rw [hsuccessor]
    have hupperProduct :
        (2 ^ (width - trailing) - 1) *
            2 ^ trailing =
          2 ^ width - 2 ^ trailing := by
      rw [Nat.sub_mul, hpower, one_mul]
    rw [hupperProduct]
    omega

/--
Dividing a bounded magnitude by its trailing-field modulus leaves a prefix that depends only on the
regime bit and run length.

A zero-bit regime with a terminator leaves the prefix `1`; a one-bit regime with a terminator
leaves the all-ones-then-zero prefix `2 ^ (run + 1) - 2`. Without a terminator the whole magnitude
survives: it is `0` for the zero word and `2 ^ payloadBits - 1` for the all-ones word.
-/
private theorem magnitudeBits_div_twoPow_trailingBits (value : Model format)
    (hbound : value.magnitudeBits < 2 ^ format.payloadBits) :
    value.magnitudeBits / 2 ^ value.trailingBits =
      if value.regimeBit then
        (if value.regimeRunLength < format.payloadBits then
          2 ^ (value.regimeRunLength + 1) - 2
        else 2 ^ format.payloadBits - 1)
      else (if value.regimeRunLength < format.payloadBits then 1 else 0) := by
  have hrunLe := regimeRunLength_le_payload value
  cases hbit : value.regimeBit with
  | false =>
    have hrun : value.regimeRunLength =
        countLeadingRun value.magnitudeBits format.payloadBits false := by
      simp [regimeRunLength, hbit]
    by_cases hzero : value.magnitudeBits = 0
    · have hfull : value.regimeRunLength = format.payloadBits := by
        rw [hrun, hzero]
        exact countLeadingRun_zero_false _
      simp [hzero, hfull]
    · have hlt : value.regimeRunLength < format.payloadBits := by
        have hne : value.regimeRunLength ≠ format.payloadBits := fun h =>
          hzero ((countLeadingRun_false_eq_width_iff hbound).mp (hrun.symm.trans h))
        omega
      have htrailing : value.trailingBits =
          format.payloadBits - value.regimeRunLength - 1 := by
        simp [trailingBits, hasRegimeTerminator, hlt]
      rw [ite_eq_right Bool.false_ne_true, ite_eq_left hlt, htrailing, hrun]
      exact div_twoPow_after_false_run (Nat.pos_of_ne_zero hzero) hbound
  | true =>
    have hpower := Nat.two_pow_pos format.payloadBits
    have hrun : value.regimeRunLength =
        countLeadingRun (2 ^ format.payloadBits - 1 - value.magnitudeBits)
          format.payloadBits false := by
      unfold regimeRunLength
      rw [hbit]
      exact countLeadingRun_true_eq_fixedComplement _ _ hbound
    by_cases hzero : 2 ^ format.payloadBits - 1 - value.magnitudeBits = 0
    · have hfull : value.regimeRunLength = format.payloadBits := by
        rw [hrun, hzero]
        exact countLeadingRun_zero_false _
      have htrailing : value.trailingBits = 0 := by
        simp [trailingBits, hasRegimeTerminator, hfull]
      have hmagnitude : value.magnitudeBits = 2 ^ format.payloadBits - 1 := by
        omega
      simp [hfull, htrailing, hmagnitude]
    · have hpos := Nat.pos_of_ne_zero hzero
      have hlog := countLeadingRun_false_eq_log2 _ format.payloadBits hpos (by omega)
      have hlogLt : Nat.log2 (2 ^ format.payloadBits - 1 - value.magnitudeBits) <
          format.payloadBits := by
        rw [Nat.log2_eq_log_two]
        exact Nat.log_lt_of_lt_pow hzero (by omega)
      have hlt : value.regimeRunLength < format.payloadBits := by
        omega
      have htrailing : value.trailingBits =
          Nat.log2 (2 ^ format.payloadBits - 1 - value.magnitudeBits) := by
        simp [trailingBits, hasRegimeTerminator, hlt]
        omega
      rw [ite_eq_left rfl, ite_eq_left hlt, htrailing, div_twoPow_after_true_run hbound hpos]
      congr 2
      omega

/--
Equal regimes have equal trailing widths and equal high-bit prefixes.

The second conclusion says that division by the trailing-field modulus leaves the same regime
prefix in both magnitudes. It is the representation lemma that turns unsigned code order into
strict order of the low exponent/fraction fields.
-/
theorem trailingBits_eq_and_prefix_eq_of_regimeValue_eq
    (left right : Model format)
    (hleftBound :
      left.magnitudeBits < 2 ^ format.payloadBits)
    (hrightBound :
      right.magnitudeBits < 2 ^ format.payloadBits)
    (hregime : left.regimeValue = right.regimeValue) :
    left.trailingBits = right.trailingBits ∧
      left.magnitudeBits / 2 ^ left.trailingBits =
        right.magnitudeBits / 2 ^ right.trailingBits := by
  obtain ⟨hbit, hrun⟩ := (regimeValue_eq_iff left right).mp hregime
  refine ⟨?_, ?_⟩
  · unfold trailingBits hasRegimeTerminator
    rw [hrun]
  · rw [magnitudeBits_div_twoPow_trailingBits left hleftBound,
      magnitudeBits_div_twoPow_trailingBits right hrightBound, hbit, hrun]

end FloatLib.Floats.Formats.Posit.Model
