/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Special

/-!
# Kernel path: casts between binary descriptors

`cast src dst mode a` is the encoding in `dst` of the value that the word `a` encodes in `src`,
rounded in the direction `mode`. `cast_eq_spec` proves it equal to the encoding of the reference
`Model.cast src dst x mode`, for every pair of format descriptors, every rounding direction and
every value:

* a finite value is rounded once into `dst` (`round`), or its word is shifted when the two
  descriptors differ only by a wider destination fraction (`widens`), as the reference does;
* an infinity becomes the overflow result of `dst`: an infinity, the NaN of a finite-with-NaN
  encoding, or the largest finite value of a fully finite encoding;
* a NaN becomes the NaN of `dst` with the source sign and, between IEEE encodings, the source
  payload when it fits (`nanWord`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Whether the fields of a finite value of `src` are also its fields in `dst`, up to a wider
fraction: equal exponent width, bias and encoding, and a fraction at least as wide.
-/
def widens (src dst : FloatFormat) : Bool :=
  decide (src.expWidth = dst.expWidth ∧ src.exponentBias = dst.exponentBias ∧
    src.encoding = dst.encoding ∧ src.fracWidth ≤ dst.fracWidth)

/-- Mask of the payload of a NaN: the fraction bits below the quiet bit of an IEEE encoding. -/
def payloadMask (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .ieee => 2 ^ (fmt.fracWidth - 1) - 1
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => 0

kernel_constant payloadMask

/--
Encoding of the NaN of `fmt` with sign `sign` and payload `payload`, `Model.propagatedNaN`
(`nanWord_eq`). A payload that does not fit below the quiet bit is dropped.
-/
def nanWord (fmt : FloatFormat) (sign payload : Nat) : Nat :=
  match fmt.encoding with
  | .ieee =>
      Nat.add (Nat.mul sign (2 ^ signPos fmt))
        (Nat.add (fmt.expAllOnesNat * 2 ^ fmt.fracWidth + 2 ^ (fmt.fracWidth - 1))
          (Nat.mul payload
            (Nat.sub 1 (Nat.sub 1 (Nat.sub (2 ^ (fmt.fracWidth - 1)) payload)))))
  | .finiteMaxNaN =>
      Nat.add (Nat.mul sign (2 ^ signPos fmt))
        (fmt.expAllOnesNat * 2 ^ fmt.fracWidth + fmt.fracMaskNat)
  | .finiteUnsignedZero | .finite => invalidWord fmt

kernel_constant nanWord

/--
The cast of a word of `src` that is not finite: a NaN gives `nanWord` with its sign and payload,
an infinity the overflow result of `dst` with its sign.
-/
def castSpecial (src dst : FloatFormat) (a : Nat) : Nat :=
  (fun sa ua =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanFlag src sa ua) 0)
      (nanWord dst sa (Nat.land a (payloadMask src)))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa 0)
        (overflowWord dst true) (overflowWord dst false)))
    (Nat.shiftRight a (signPos src)) (Nat.land a (magnitudeMask src))

kernel_constant castSpecial

/--
Encoding in `dst` of the value that `a` encodes in `src`, rounded in the direction `mode`
(`cast_eq_spec`).
-/
def cast (src dst : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun sa ua =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq
        (Nat.add (Nat.sub ua (maxFinite src)) (Nat.mul (negZeroNaN src) (Nat.sub sa ua))) 0)
      (castSpecial src dst a)
      (Bool.casesOn (motive := fun _ => Nat) (widens src dst)
        ((fun ha =>
            round dst mode (Nat.succ src.fracWidth) sa sa
              (Nat.sub ua (Nat.shiftLeft ha src.fracWidth))
              (Nat.add ha (Nat.add dst.exponentBias dst.fracWidth))
              (Nat.add src.exponentBias src.fracWidth) 0 0)
          (Nat.sub (Nat.shiftRight ua src.fracWidth) 1))
        (Nat.shiftLeft a (Nat.sub dst.fracWidth src.fracWidth))))
    (Nat.shiftRight a (signPos src)) (Nat.land a (magnitudeMask src))

/-- `nanWord` is the encoding of `Model.propagatedNaN`, in every encoding. -/
theorem nanWord_eq (fmt : FloatFormat) (negative : Bool) (payload : Nat) :
    nanWord fmt (signNat negative) payload =
      (Model.propagatedNaN fmt negative payload).toNatBits := by
  have hfw := fmt.fracWidth_pos
  have hexp : fmt.expAllOnesNat < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat
    have := Nat.two_pow_pos fmt.expWidth
    omega
  have hquiet : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 1) + 2 ^ (fmt.fracWidth - 1) := by
    rw [← Nat.two_mul, ← Nat.pow_succ']
    congr 1
    omega
  have hsign : signNat negative * 2 ^ signPos fmt = if negative then 2 ^ signPos fmt else 0 := by
    cases negative <;> simp [signNat]
  have hpos := Nat.two_pow_pos (fmt.fracWidth - 1)
  unfold nanWord Model.propagatedNaN
  simp only [invalidWord_eq]
  unfold Model.invalidResult
  cases hencoding : fmt.encoding <;> simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  · rw [toNatBits_ofFields fmt _ _ _ hexp (by split <;> omega), hsign]
    by_cases hfit : payload < 2 ^ (fmt.fracWidth - 1)
    · have hone : 1 - (1 - (2 ^ (fmt.fracWidth - 1) - payload)) = 1 := by omega
      rw [hone, Nat.mul_one, ite_eq_left hfit]
      omega
    · have hzero : 1 - (1 - (2 ^ (fmt.fracWidth - 1) - payload)) = 0 := by omega
      rw [hzero, Nat.mul_zero, ite_eq_right hfit]
      omega
  · rw [toNatBits_ofFields fmt _ _ _ hexp
      (by unfold FloatFormat.fracMaskNat; have := Nat.two_pow_pos fmt.fracWidth; omega), hsign]

/-- The payload of a NaN is its fraction below the quiet bit, read off its word. -/
theorem payload_eq {fmt : FloatFormat} (x : Model fmt) (hnan : Model.isNaN x = true) :
    x.toNatBits &&& payloadMask fmt = Model.nanPayload x := by
  have hfw := fmt.fracWidth_pos
  have hf := Model.fracField_lt_pow2 x
  unfold payloadMask Model.nanPayload Model.payloadOfNaNField Model.isSignaling
  cases hencoding : fmt.encoding <;> simp only [Nat.and_zero]
  have hieee : Model.IEEE.isNaN x = true := by simpa [Model.isNaN, hencoding] using hnan
  have hquiet : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hmod : x.toNatBits % 2 ^ (fmt.fracWidth - 1) =
      Model.fracField x % 2 ^ (fmt.fracWidth - 1) := by
    rw [toNatBits_eq_fields]
    have hsp : 2 ^ signPos fmt = 2 ^ (fmt.fracWidth - 1) * (2 * 2 ^ fmt.expWidth) := by
      unfold signPos
      rw [Nat.add_comm, Nat.pow_add, hquiet]
      ring
    have hfields : Model.expField x * 2 ^ fmt.fracWidth =
        2 ^ (fmt.fracWidth - 1) * (2 * Model.expField x) := by
      rw [hquiet]
      ring
    rw [hfields]
    cases Model.signBit x
    · simp only [Bool.false_eq_true, ite_false, Nat.zero_add, Nat.mul_add_mod]
    · simp only [ite_true]
      rw [hsp, Nat.mul_add_mod, Nat.mul_add_mod]
  rw [Nat.and_two_pow_sub_one_eq_mod, hmod, Model.IEEE.isSignaling, hieee, Bool.true_and,
    Model.and_quietBit_eq_zero_iff]
  cases hbit : (Model.fracField x).testBit (fmt.fracWidth - 1)
  · have hlt : Model.fracField x < 2 ^ (fmt.fracWidth - 1) := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      by_cases hi' : i = fmt.fracWidth - 1
      · rw [hi']
        exact hbit
      · exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hf (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [Bool.not_false, ite_true]
    exact Nat.mod_eq_of_lt hlt
  · have hge : 2 ^ (fmt.fracWidth - 1) ≤ Model.fracField x := Nat.ge_two_pow_of_testBit hbit
    have hlog : Nat.log2 (Model.fracField x) = fmt.fracWidth - 1 := by
      have hne : Model.fracField x ≠ 0 := by
        have := Nat.two_pow_pos (fmt.fracWidth - 1)
        omega
      rw [Nat.log2_eq_iff hne]
      refine ⟨hge, ?_⟩
      rw [show fmt.fracWidth - 1 + 1 = fmt.fracWidth by omega]
      exact hf
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, hlog]
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_eq_of_lt (by omega)

/-- A finite value that does not widen field by field is rounded once, in every direction. -/
theorem cast_of_finite {src dst : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model src)
    (d : Numerics.Dyadic) (hd : Model.toDyadic? x = some d) (hwidens : widens src dst = false) :
    Model.cast src dst x mode = Model.Internal.Directed.roundDyadic dst mode d := by
  have hnan := Model.isNaN_eq_false_of_toDyadic?_some hd
  have hinf := Model.isInfinite_eq_false_of_toDyadic?_some hd
  have hnot : ¬ (src.expWidth = dst.expWidth ∧ src.exponentBias = dst.exponentBias ∧
      src.encoding = dst.encoding ∧ src.fracWidth ≤ dst.fracWidth) :=
    of_decide_eq_false hwidens
  have hne : src ≠ dst := by
    rintro rfl
    exact hnot ⟨rfl, rfl, rfl, le_rfl⟩
  rw [← Model.Internal.Directed.cast_eq]
  cases mode
  all_goals
    simp only [Model.Internal.Directed.cast, Model.Internal.Nearest.cast, hnan, hinf,
      Bool.false_eq_true, dite_false, hne]
    split
    · next he =>
      split
      · next hb =>
        split
        · next hencoding =>
          split
          · next hf => exact (hnot ⟨he, hb, hencoding, hf⟩).elim
          · simp [Model.finiteDyadic, hd, Model.Internal.Directed.roundDyadic]
        · simp [Model.finiteDyadic, hd, Model.Internal.Directed.roundDyadic]
      · simp [Model.finiteDyadic, hd, Model.Internal.Directed.roundDyadic]
    · simp [Model.finiteDyadic, hd, Model.Internal.Directed.roundDyadic]

/-- `castSpecial` computes the encoding of the reference cast of a value that is not finite. -/
theorem castSpecial_eq {src dst : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model src)
    (hfinite : Model.isFinite x = false) :
    castSpecial src dst x.toNatBits = (Model.cast src dst x mode).toNatBits := by
  unfold castSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, nanFlag_eq]
  cases hnan : Model.isNaN x
  · have hinf : Model.isInfinite x = true := by
      cases hinf : Model.isInfinite x
      · rw [Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnan hinf] at hfinite
        exact absurd hfinite (by decide)
      · rfl
    have hcast : Model.cast src dst x mode = Model.nativeOverflow dst (Model.signBit x) := by
      cases mode <;>
        simp [Model.cast, Model.Internal.Directed.cast, Model.Internal.Nearest.cast, hnan, hinf]
    rw [hcast]
    simp only [overflowWord_eq]
    cases Model.signBit x <;> rfl
  · rw [Model.cast_of_isNaN x hnan mode, ← nanWord_eq, payload_eq x hnan]
    cases Model.signBit x <;> rfl

/--
`cast` computes the encoding of the reference cast `Model.cast src dst x mode`, for every pair
of format descriptors, every rounding direction and every value.
-/
theorem cast_eq_spec {src dst : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model src) :
    cast src dst mode x.toNatBits = (Model.cast src dst x mode).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  unfold cast
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft]
  by_cases hguard :
      Model.expField x * 2 ^ src.fracWidth + Model.fracField x - maxFinite src +
        negZeroNaN src * ((if Model.signBit x then 1 else 0) -
          (Model.expField x * 2 ^ src.fracWidth + Model.fracField x)) = 0
  · have hfinite := isFinite_of_nonFinite_eq_zero x hguard
    obtain ⟨d, hd, hn, hs, he⟩ := toDyadic?_of_isFinite x hfinite
    rw [hguard]
    cases hwidens : widens src dst
    · change round dst mode _ _ _ _ _ _ 0 0 = _
      rw [cast_of_finite mode x d hd hwidens]
      refine round_eq dst mode (src.fracWidth + 1) _ _ _ _ _ _ d (decoded_significand_lt x) hs
        (by rw [hn]; rfl) ?_ (fun _ => rfl)
      intro hne
      rw [he (by rw [hs]; exact hne)]
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      push_cast
      omega
    · obtain ⟨hexp, hbias, hencoding, hfrac⟩ := of_decide_eq_true hwidens
      change x.toNatBits <<< (dst.fracWidth - src.fracWidth) = _
      rw [Model.cast_eq_widenExact_of_compatibleWidening x hexp hbias hencoding hfrac hfinite mode]
      have hexponent : Model.expField x < 2 ^ dst.expWidth := by
        rw [← hexp]
        exact Model.expField_lt_pow2 x
      obtain ⟨k, hk⟩ : ∃ k, dst.fracWidth = src.fracWidth + k :=
        ⟨dst.fracWidth - src.fracWidth, by omega⟩
      have hfraction : Model.fracField x <<< (dst.fracWidth - src.fracWidth) <
          2 ^ dst.fracWidth := by
        rw [hk, Nat.add_sub_cancel_left, Nat.shiftLeft_eq, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right hfx (Nat.two_pow_pos k)
      have hsignPos : signPos dst = signPos src + k := by
        unfold signPos
        omega
      change _ = (Model.ofFields dst (Model.signBit x) (Model.expField x)
        (Model.fracField x <<< (dst.fracWidth - src.fracWidth))).toNatBits
      rw [toNatBits_ofFields dst _ _ _ hexponent hfraction, toNatBits_eq_fields x, hsignPos, hk,
        Nat.add_sub_cancel_left]
      simp only [Nat.shiftLeft_eq, Nat.pow_add]
      cases Model.signBit x
      · simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
        ring
      · simp only [ite_true]
        ring
  · have hfinite : Model.isFinite x = false := by
      cases h : Model.isFinite x
      · rfl
      · have hg := nonFinite_eq_zero_of_isFinite x h
        unfold nonFinite at hg
        simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hg
        exact absurd hg hguard
    have hbeq : ∀ n : Nat, n ≠ 0 → Nat.beq n 0 = false := by
      intro n hn
      cases n
      · exact absurd rfl hn
      · rfl
    rw [hbeq _ hguard]
    exact castSpecial_eq mode x hfinite

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
