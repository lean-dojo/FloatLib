/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Direct.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.TwoWordMul.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Division.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Fma.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Division.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Sqrt.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.FmaWord.Proof

/-!
# Correctness of direct storage-word arithmetic

Each direct operation equals the word operation it replaces, so it inherits that operation's
refinement of the specification. For binary64, an accepted word-kernel result is the one-word
view of the result the model dispatcher returns: the dispatcher tries the same one-word kernel
first, and `NativeSmallWordAdd.addFinite?_ofWord` relates the kernel on models to the kernel on
storage words. Two-word codes follow the same pattern through the `NativePair` kernels and
`NativePair.toWords`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat

namespace Backend

private theorem model_eq_of_toNatBits {format : FloatFormat} {x y : Model format}
    (h : x.toNatBits = y.toNatBits) : x = y := by
  rw [← Model.ofNatBits_toNatBits x, ← Model.ofNatBits_toNatBits y, h]

/-- The model value of a `word64` code is the one-word view of its stored word. -/
theorem decode_word64 {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (value : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    ModelCodec.decode (Model := Model format) (plan := StoragePlan.word64 hw) value =
      Model.NativeSmallWord.ofWord value.raw.1 := by
  apply model_eq_of_toNatBits
  rw [Model.NativeSmallWord.toNatBits_ofWord, Nat.mod_eq_of_lt value.raw.2]
  rfl

/-- Binary64 addition returns an accepted one-word sum unchanged. -/
private theorem addWord_eq_of_addFinite? {format : FloatFormat}
    (h64 : FloatFormat.IsBinary64 format)
    {x y s : Model format}
    (h : Model.NativeSmallWordAdd.addFinite? x y false = some s) :
    Model.AddBackend.word x y = s := by
  have h32 : ¬FloatFormat.IsBinary32 format := by
    rw [FloatFormat.eq_binary64_of_isBinary64 h64]; decide
  unfold Model.AddBackend.word
  simp only [h32, dite_false, h]
  rw [dite_eq_left_of_eq_true (eq_true h64)]

/-- Binary64 subtraction returns an accepted one-word difference unchanged. -/
private theorem subWord_eq_of_addFinite? {format : FloatFormat}
    (h64 : FloatFormat.IsBinary64 format)
    {x y s : Model format}
    (h : Model.NativeSmallWordAdd.addFinite? x y true = some s) :
    Model.AddBackend.subWord x y = s := by
  have h32 : ¬FloatFormat.IsBinary32 format := by
    rw [FloatFormat.eq_binary64_of_isBinary64 h64]; decide
  unfold Model.AddBackend.subWord
  simp only [h32, dite_false, h]
  rw [dite_eq_left_of_eq_true (eq_true h64)]

/-- Addition on stored binary64 words is word addition. -/
theorem binary64Add_eq {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (h64 : FloatFormat.IsBinary64 format)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    binary64Add hw left right = wordAdd left right := by
  unfold binary64Add
  split
  · rename_i bits hbits
    apply ModelCodec.decode_injective
      (F := Family format (Code (.word64 hw)) (.word64 hw)) (Model := Model format)
      (plan := StoragePlan.word64 hw)
    have hk := Model.NativeSmallWordAdd.addFinite?_ofWord hw left.raw.2 right.raw.2 false
    simp only [hbits, Option.map_some] at hk
    rw [wordAdd, ModelCodec.decode_liftBinary, decode_word64 hw left, decode_word64 hw right,
      addWord_eq_of_addFinite? h64 hk]
    rfl
  · rfl

/-- Subtraction on stored binary64 words is word subtraction. -/
theorem binary64Sub_eq {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (h64 : FloatFormat.IsBinary64 format)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    binary64Sub hw left right = wordSub left right := by
  unfold binary64Sub
  split
  · rename_i bits hbits
    apply ModelCodec.decode_injective
      (F := Family format (Code (.word64 hw)) (.word64 hw)) (Model := Model format)
      (plan := StoragePlan.word64 hw)
    have hk := Model.NativeSmallWordAdd.addFinite?_ofWord hw left.raw.2 right.raw.2 true
    simp only [hbits, Option.map_some] at hk
    rw [wordSub, ModelCodec.decode_liftBinary, decode_word64 hw left, decode_word64 hw right,
      subWord_eq_of_addFinite? h64 hk]
    rfl
  · rfl

/-- Binary64 multiplication returns an accepted two-word normal product unchanged. -/
private theorem mulWord_eq_of_mulNormal? {format : FloatFormat}
    (h64 : FloatFormat.IsBinary64 format)
    {x y s : Model format}
    (h : Model.NativeTwoWordMul.mulNormal? x y = some s) :
    Model.MulBackend.word x y = s := by
  have h32 : ¬FloatFormat.IsBinary32 format := by
    rw [FloatFormat.eq_binary64_of_isBinary64 h64]; decide
  unfold Model.MulBackend.word
  simp only [h32, dite_false, h]
  rw [dite_eq_left_of_eq_true (eq_true h64)]

/-- Multiplication on stored binary64 words is word multiplication. -/
theorem binary64Mul_eq {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (h64 : FloatFormat.IsBinary64 format)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    binary64Mul hw left right = wordMul left right := by
  unfold binary64Mul
  split
  · rename_i bits hbits
    apply ModelCodec.decode_injective
      (F := Family format (Code (.word64 hw)) (.word64 hw)) (Model := Model format)
      (plan := StoragePlan.word64 hw)
    have hk := Model.NativeTwoWordMul.mulNormal?_ofWord (fmt := format) left.raw.2 right.raw.2
    simp only [hbits, Option.map_some] at hk
    rw [wordMul, ModelCodec.decode_liftBinary, decode_word64 hw left, decode_word64 hw right,
      mulWord_eq_of_mulNormal? h64 hk]
    rfl
  · rfl

/-- For binary64 the one-word view and the native binary64 view of a word agree. -/
theorem ofWord_eq_ofUInt64 (bits : UInt64) :
    Model.NativeSmallWord.ofWord (fmt := FloatFormat.binary64) bits =
      Model.NativeBinary64.ofUInt64 bits := by
  apply model_eq_of_toNatBits
  rw [Model.NativeSmallWord.toNatBits_ofWord,
    Nat.mod_eq_of_lt (lt_of_lt_of_eq (UInt64.toNat_lt_size bits) (by decide))]
  rfl

/-- Binary64 division returns an accepted normal quotient unchanged. -/
private theorem divWord_eq_of_divNormal? {x y q : Model FloatFormat.binary64}
    (h : Model.NativeBinary64.divNormal? x y = some q) :
    Model.DivBackend.word x y = q := by
  have h32 : ¬FloatFormat.IsBinary32 FloatFormat.binary64 := by decide
  have h64 : FloatFormat.IsBinary64 FloatFormat.binary64 := by decide
  unfold Model.DivBackend.word
  simp only [h32, dite_false]
  rw [dite_eq_left_of_eq_true (eq_true h64)]
  simp [Model.NativeBinary64.divFinite?, h]

/-- Division on stored binary64 words is word division. -/
theorem binary64Div_eq {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (h64 : FloatFormat.IsBinary64 format)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    binary64Div hw left right = wordDiv left right := by
  obtain rfl := FloatFormat.eq_binary64_of_isBinary64 h64
  unfold binary64Div
  split
  · rename_i bits hbits
    apply ModelCodec.decode_injective
      (F := Family FloatFormat.binary64 (Code (.word64 hw)) (.word64 hw))
      (Model := Model FloatFormat.binary64) (plan := StoragePlan.word64 hw)
    have hk : Model.NativeBinary64.divNormal? (Model.NativeBinary64.ofUInt64 left.raw.1)
        (Model.NativeBinary64.ofUInt64 right.raw.1) =
          some (Model.NativeBinary64.ofUInt64 bits) := by
      simp only [Model.NativeBinary64.divNormal?, Model.NativeBinary64.toUInt64_ofUInt64, hbits,
        Option.map_some]
    rw [wordDiv, ModelCodec.decode_liftBinary, decode_word64 hw left, decode_word64 hw right,
      ofWord_eq_ofUInt64, ofWord_eq_ofUInt64, divWord_eq_of_divNormal? hk]
    change Model.NativeSmallWord.ofWord bits = _
    rw [ofWord_eq_ofUInt64]
  · rfl

/-- Binary64 fused multiply-add returns an accepted normal result unchanged. -/
private theorem fmaWord_eq_of_fmaNormal? {x y z q : Model FloatFormat.binary64}
    (h : Model.NativeBinary64.fmaNormal? x y z = some q) :
    Model.FmaBackend.word x y z = q := by
  have h32 : ¬FloatFormat.IsBinary32 FloatFormat.binary64 := by decide
  have h64 : FloatFormat.IsBinary64 FloatFormat.binary64 := by decide
  unfold Model.FmaBackend.word
  simp only [h32, dite_false]
  rw [dite_eq_left_of_eq_true (eq_true h64)]
  simp [Model.NativeBinary64.fmaFinite?, h]

/-- Fused multiply-add on stored binary64 words is word fused multiply-add. -/
theorem binary64Fma_eq {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (h64 : FloatFormat.IsBinary64 format)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    binary64Fma hw left right addend = wordFma left right addend := by
  obtain rfl := FloatFormat.eq_binary64_of_isBinary64 h64
  unfold binary64Fma
  split
  · rename_i bits hbits
    apply ModelCodec.decode_injective
      (F := Family FloatFormat.binary64 (Code (.word64 hw)) (.word64 hw))
      (Model := Model FloatFormat.binary64) (plan := StoragePlan.word64 hw)
    have hk : Model.NativeBinary64.fmaNormal? (Model.NativeBinary64.ofUInt64 left.raw.1)
        (Model.NativeBinary64.ofUInt64 right.raw.1) (Model.NativeBinary64.ofUInt64 addend.raw.1) =
          some (Model.NativeBinary64.ofUInt64 bits) := by
      simp only [Model.NativeBinary64.fmaNormal?, Model.NativeBinary64.toUInt64_ofUInt64, hbits,
        Option.map_some]
    rw [wordFma, ModelCodec.decode_liftTernary, decode_word64 hw left, decode_word64 hw right,
      decode_word64 hw addend, ofWord_eq_ofUInt64, ofWord_eq_ofUInt64, ofWord_eq_ofUInt64,
      fmaWord_eq_of_fmaNormal? hk]
    change Model.NativeSmallWord.ofWord bits = _
    rw [ofWord_eq_ofUInt64]
  · rfl

/-! ## Two-word carriers -/

/-- The model value of a `pair` code has the code's two words as its encoding. -/
theorem toNatBits_decode_pair {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (value : FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle)
      value).toNatBits = value.raw.1.toNat :=
  BitVec.toNat_ofNatLT _ _

/-- Splitting the model value of a `pair` code returns the code's two words. -/
theorem toWords_decode_pair {format : FloatFormat} (hpair : Model.NativePair.Eligible format)
    (hgt : 64 < format.bitWidth) (hle : format.bitWidth ≤ 128)
    (value : FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    Model.NativePair.toWords
        (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) value) =
      value.raw.1 := by
  apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
  rw [Model.NativePair.toWords_toNat hpair, toNatBits_decode_pair]

/-- A packed kernel result decodes to the model value the model kernel builds from its words. -/
theorem decode_pairCode {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (words : FloatLib.Numerics.FixedWord.UInt128) :
    ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle)
        (FloatLib.Floats.ExecFloat.ofRaw (F := Family format (Code (.pair hgt hle)) (.pair hgt hle))
          (pairCode hgt hle words)) =
      Model.NativePair.ofWords format words := by
  apply model_eq_of_toNatBits
  rw [toNatBits_decode_pair]
  unfold Model.NativePair.ofWords Model.toNatBits Model.ofBits
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, UInt64.toNat_toBitVec]
  rw [← Nat.shiftLeft_add_eq_or_of_lt words.lo.toNat_lt, Nat.shiftLeft_eq]
  unfold FloatLib.Numerics.FixedWord.UInt128.toNat
  change words.lo.toNat + (words.hi &&& pairHighMask format).toNat * 2 ^ 64 = _
  have hsplit : 2 ^ format.bitWidth = 2 ^ 64 * 2 ^ (format.bitWidth - 64) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmod : (words.hi.toNat * 2 ^ 64 + words.lo.toNat) % 2 ^ 64 = words.lo.toNat := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt words.lo.toNat_lt]
  have hdiv : (words.hi.toNat * 2 ^ 64 + words.lo.toNat) / 2 ^ 64 = words.hi.toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt words.lo.toNat_lt, Nat.zero_add]
  rw [UInt64.toNat_and, pairHighMask_toNat format hle, Nat.and_two_pow_sub_one_eq_mod, hsplit,
    Nat.mod_mul, hmod, hdiv, Nat.mul_comm]

private theorem not_binary32_of_pair {format : FloatFormat}
    (hpair : Model.NativePair.Eligible format) : ¬FloatFormat.IsBinary32 format := by
  intro h32
  have hfrac := hpair.2.1
  rw [FloatFormat.eq_binary32_of_isBinary32 h32] at hfrac
  exact absurd hfrac (by decide)

private theorem not_binary64_of_pair {format : FloatFormat}
    (hpair : Model.NativePair.Eligible format) : ¬FloatFormat.IsBinary64 format := by
  intro h64
  have hfrac := hpair.2.1
  rw [FloatFormat.eq_binary64_of_isBinary64 h64] at hfrac
  exact absurd hfrac (by decide)

/-- Two-word addition returns an accepted finite sum unchanged. -/
private theorem addWord_eq_of_pairAddFinite? {format : FloatFormat}
    (hpair : Model.NativePair.Eligible format) {x y s : Model format}
    (h : Model.NativePair.addFinite? x y = some s) :
    Model.AddBackend.word x y = s := by
  rw [Model.AddBackend.word, dite_eq_right (not_binary32_of_pair hpair),
    dite_eq_right (not_binary64_of_pair hpair), dite_eq_left hpair, h]

/-- Two-word subtraction returns an accepted finite difference unchanged. -/
private theorem subWord_eq_of_pairSubFinite? {format : FloatFormat}
    (hpair : Model.NativePair.Eligible format) {x y s : Model format}
    (h : Model.NativePair.subFinite? x y = some s) :
    Model.AddBackend.subWord x y = s := by
  rw [Model.AddBackend.subWord, dite_eq_right (not_binary32_of_pair hpair),
    dite_eq_right (not_binary64_of_pair hpair), dite_eq_left hpair, h]

/-- Addition on stored two-word codes is word addition. -/
theorem pairAdd_eq {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (hpair : Model.NativePair.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    pairAdd hgt hle left right = wordAdd left right := by
  unfold pairAdd
  split
  · rename_i words hwords
    apply ModelCodec.decode_injective
      (F := Family format (Code (.pair hgt hle)) (.pair hgt hle)) (Model := Model format)
      (plan := StoragePlan.pair hgt hle)
    have hk :
        Model.NativePair.addFinite?
            (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) left)
            (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) right) =
          some (Model.NativePair.ofWords format words) := by
      apply Model.NativePair.addFinite?_of_words
      rw [toWords_decode_pair hpair, toWords_decode_pair hpair]
      exact hwords
    rw [wordAdd, ModelCodec.decode_liftBinary, addWord_eq_of_pairAddFinite? hpair hk,
      decode_pairCode]
  · rfl

/-- Subtraction on stored two-word codes is word subtraction. -/
theorem pairSub_eq {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (hpair : Model.NativePair.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    pairSub hgt hle left right = wordSub left right := by
  unfold pairSub
  split
  · rename_i words hwords
    apply ModelCodec.decode_injective
      (F := Family format (Code (.pair hgt hle)) (.pair hgt hle)) (Model := Model format)
      (plan := StoragePlan.pair hgt hle)
    have hk :
        Model.NativePair.subFinite?
            (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) left)
            (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) right) =
          some (Model.NativePair.ofWords format words) := by
      apply Model.NativePair.subFinite?_of_words
      rw [toWords_decode_pair hpair, toWords_decode_pair hpair]
      exact hwords
    rw [wordSub, ModelCodec.decode_liftBinary, subWord_eq_of_pairSubFinite? hpair hk,
      decode_pairCode]
  · rfl

/-- Two-word multiplication returns an accepted normal product unchanged. -/
private theorem mulWord_eq_of_pairMulNormal? {format : FloatFormat}
    (hpair : Model.NativePair.Eligible format) {x y s : Model format}
    (h : Model.NativePair.mulNormalLimb? x y = some s) :
    Model.MulBackend.word x y = s := by
  unfold Model.MulBackend.word
  simp only [not_binary32_of_pair hpair, not_binary64_of_pair hpair, dite_false]
  rw [dite_eq_left_of_eq_true (eq_true hpair)]
  simp [h]

/-- Multiplication on stored two-word codes is word multiplication. -/
theorem pairMul_eq {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (hpair : Model.NativePair.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    pairMul hgt hle left right = wordMul left right := by
  unfold pairMul
  split
  · rename_i words hwords
    apply ModelCodec.decode_injective
      (F := Family format (Code (.pair hgt hle)) (.pair hgt hle)) (Model := Model format)
      (plan := StoragePlan.pair hgt hle)
    have hk := Model.NativePair.mulNormalLimb?.eq_1
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) left)
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) right)
    rw [toWords_decode_pair hpair, toWords_decode_pair hpair, hwords, Option.map_some] at hk
    rw [wordMul, ModelCodec.decode_liftBinary, mulWord_eq_of_pairMulNormal? hpair hk,
      decode_pairCode]
  · rfl

/-- Two-word division returns an accepted normal quotient unchanged. -/
private theorem divWord_eq_of_pairDivNormal? {format : FloatFormat}
    (hpair : Model.NativePair.Eligible format) {x y q : Model format}
    (h : Model.NativePair.divNormal? x y = some q) :
    Model.DivBackend.word x y = q := by
  unfold Model.DivBackend.word
  simp only [not_binary32_of_pair hpair, not_binary64_of_pair hpair, dite_false]
  rw [dite_eq_left_of_eq_true (eq_true hpair)]
  simp [h]

/-- Division on stored two-word codes is word division. -/
theorem pairDiv_eq {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (hpair : Model.NativePair.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    pairDiv hgt hle left right = wordDiv left right := by
  unfold pairDiv
  split
  · rename_i words hwords
    apply ModelCodec.decode_injective
      (F := Family format (Code (.pair hgt hle)) (.pair hgt hle)) (Model := Model format)
      (plan := StoragePlan.pair hgt hle)
    have hk := Model.NativePair.divNormal?.eq_1
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) left)
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) right)
    rw [toWords_decode_pair hpair, toWords_decode_pair hpair, hwords, Option.map_some] at hk
    rw [wordDiv, ModelCodec.decode_liftBinary, divWord_eq_of_pairDivNormal? hpair hk,
      decode_pairCode]
  · rfl

/-- Square root of a stored two-word code implements the configured square-root specification. -/
theorem pairSqrt_eq_spec {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (hpair : Model.NativePair.Eligible format)
    (value : FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    pairSqrt hgt hle value = Spec.sqrt value := by
  unfold pairSqrt
  split
  · rename_i words hwords
    apply ModelCodec.decode_injective
      (F := Family format (Code (.pair hgt hle)) (.pair hgt hle)) (Model := Model format)
      (plan := StoragePlan.pair hgt hle)
    have hk := Model.NativePair.sqrtNormal?_of_words hpair
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) value) words
      (by rw [toWords_decode_pair hpair]; exact hwords)
    rw [Spec.sqrt, ModelCodec.decode_liftUnary, decode_pairCode]
    exact Model.NativePair.sqrtNormal_refines hpair _ _ hk
  · exact fixedLimbSqrt_eq_spec value

/-- Fused multiply-add on stored two-word codes implements the configured FMA specification. -/
theorem pairFma_eq_spec {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (hpair : Model.NativePair.Eligible format)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    pairFma hgt hle left right addend = Spec.fma left right addend := by
  unfold pairFma
  split
  · rename_i words hwords
    apply ModelCodec.decode_injective
      (F := Family format (Code (.pair hgt hle)) (.pair hgt hle)) (Model := Model format)
      (plan := StoragePlan.pair hgt hle)
    have hk := Model.NativePair.fmaFiniteWords_refines hpair
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) left)
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) right)
      (ModelCodec.decode (Model := Model format) (plan := StoragePlan.pair hgt hle) addend) words
      (by rw [toWords_decode_pair hpair, toWords_decode_pair hpair, toWords_decode_pair hpair]
          exact hwords)
    rw [Spec.fma, ModelCodec.decode_liftTernary, decode_pairCode,
      ← Model.FmaBackend.generic_eq_spec]
    simp [Model.FmaBackend.generic, Model.FiniteKernel.fmaRuntimeFlat_eq,
      Model.FiniteKernel.fmaRuntime_eq, hk]
  · exact fixedLimbFma_eq_spec left right addend

/-! ## Plan dispatch -/

/-- Direct addition is word addition on every plan. -/
theorem directAdd_eq {format : FloatFormat} {plan : StoragePlan format}
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    directAdd left right = wordAdd left right := by
  cases plan with
  | word64 hw =>
      simp only [directAdd]
      split
      · rename_i h64; exact binary64Add_eq hw h64 left right
      · rfl
  | pair hgt hle =>
      simp only [directAdd]
      split
      · rename_i hpair; exact pairAdd_eq hgt hle hpair left right
      · rfl
  | _ => rfl

/-- Direct subtraction is word subtraction on every plan. -/
theorem directSub_eq {format : FloatFormat} {plan : StoragePlan format}
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    directSub left right = wordSub left right := by
  cases plan with
  | word64 hw =>
      simp only [directSub]
      split
      · rename_i h64; exact binary64Sub_eq hw h64 left right
      · rfl
  | pair hgt hle =>
      simp only [directSub]
      split
      · rename_i hpair; exact pairSub_eq hgt hle hpair left right
      · rfl
  | _ => rfl

/-- Direct multiplication is word multiplication on every plan. -/
theorem directMul_eq {format : FloatFormat} {plan : StoragePlan format}
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    directMul left right = wordMul left right := by
  cases plan with
  | pair hgt hle =>
      simp only [directMul]
      split
      · rename_i hpair; exact pairMul_eq hgt hle hpair left right
      · rfl
  | _ => rfl

/-- Direct division is word division on every plan. -/
theorem directDiv_eq {format : FloatFormat} {plan : StoragePlan format}
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    directDiv left right = wordDiv left right := by
  cases plan with
  | pair hgt hle =>
      simp only [directDiv]
      split
      · rename_i hpair; exact pairDiv_eq hgt hle hpair left right
      · rfl
  | _ => rfl

end Backend

end FloatLib.Floats.Formats.BinaryInterchange.Configured
