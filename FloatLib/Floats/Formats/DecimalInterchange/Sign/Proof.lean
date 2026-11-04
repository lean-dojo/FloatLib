/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sign.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Codec.BitsProof

/-!
# Bit preservation and datum semantics of decimal sign operations

Changing the sign of a decimal word touches only the sign bit, so every payload bit survives,
noncanonical words included. For every codec, decoding commutes with sign replacement, negation,
absolute value, and sign copying. The exact value of a negated datum (`Datum.negate_toRat?`) is
proved in `Arithmetic.Proof`, which doesn't depend on the codecs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Datum

/-- Setting the sign of any datum, NaNs and infinities included, makes its sign bit the requested
one. -/
@[simp] theorem isSignMinus_withSign (s : Bool) (d : Datum) :
    (d.withSign s).isSignMinus = s := by cases d <;> rfl

/-- Setting a datum's sign to its own sign bit leaves it unchanged. -/
@[simp] theorem withSign_isSignMinus (d : Datum) :
    d.withSign d.isSignMinus = d := by cases d <;> rfl

/-- Only the last sign replacement matters. -/
@[simp] theorem withSign_withSign (s t : Bool) (d : Datum) :
    (d.withSign s).withSign t = d.withSign t := by cases d <;> rfl

/-- Negation flips the sign bit and nothing else, also on NaNs, whose signaling bit and payload are
kept. -/
theorem negate_eq_withSign (d : Datum) :
    d.negate = d.withSign (!d.isSignMinus) := by cases d <;> rfl

/-- Negating a datum twice gives it back, for every datum including NaNs. -/
@[simp] theorem negate_negate (d : Datum) : d.negate.negate = d := by
  cases d <;> simp [negate]

/-- Changing the sign does not affect validity in a format. -/
@[simp] theorem withSign_valid (f : Format) (s : Bool) (d : Datum) :
    (d.withSign s).Valid f ↔ d.Valid f := by cases d <;> rfl

/-- Changing the sign never quiets a signaling NaN or makes a datum signaling. -/
@[simp] theorem withSign_isSNaN (s : Bool) (d : Datum) :
    (d.withSign s).isSNaN = d.isSNaN := by cases d <;> rfl

/-- Negation does not affect validity in a format. -/
@[simp] theorem negate_valid (f : Format) (d : Datum) : d.negate.Valid f ↔ d.Valid f := by
  cases d <;> rfl

/-- Negation is an involution, so it moves across an equation of datums. -/
theorem negate_eq_iff_eq_negate {d e : Datum} : d.negate = e ↔ d = e.negate := by
  constructor <;> rintro rfl <;> simp

end Datum

namespace Bits

/-- The stored sign bit of a word after sign replacement is the requested sign. -/
@[simp] theorem negative_withSign (f : Format) (s : Bool) (w : BitVec f.bitWidth) :
    negative f (withSign f s w) = s :=
  negative_pack f s _ (payload_lt f w)

/-- All bits below the sign are unchanged, even for noncanonical words. -/
@[simp] theorem payload_withSign (f : Format) (s : Bool) (w : BitVec f.bitWidth) :
    payload f (withSign f s w) = payload f w :=
  payload_pack f s _ (payload_lt f w)

/-- A word is rebuilt from its sign bit and the bits below it, with nothing lost. -/
theorem pack_negative_payload (f : Format) (w : BitVec f.bitWidth) :
    pack f (negative f w) (payload f w) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat f _ _ (payload_lt f w)]
  have hw := w.isLt
  rw [← f.twice_signBase] at hw
  have hb := f.signBase_pos
  have hd : w.toNat / f.signBase < 2 :=
    (Nat.div_lt_iff_lt_mul hb).2 hw
  have heq := Nat.mod_add_div w.toNat f.signBase
  have hcases : w.toNat / f.signBase = 0 ∨ w.toNat / f.signBase = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hd)
  rcases hcases with h | h <;> rw [h] at heq <;> simp [negative, payload, h] <;>
    omega

/-- Rewriting a word's sign bit with its own value leaves every bit unchanged. -/
@[simp] theorem withSign_negative (f : Format) (w : BitVec f.bitWidth) :
    withSign f (negative f w) w = w := pack_negative_payload f w

/-- On stored words, only the last sign replacement matters. -/
@[simp] theorem withSign_withSign (f : Format) (s t : Bool) (w : BitVec f.bitWidth) :
    withSign f t (withSign f s w) = withSign f t w := by
  simp only [withSign, payload_pack f s _ (payload_lt f w)]

/-- Negating a stored word twice restores every bit, including in noncanonical encodings. -/
@[simp] theorem negate_negate (f : Format) (w : BitVec f.bitWidth) :
    negate f (negate f w) = w := by
  simp [negate]

/-- Stored-word absolute value is idempotent. -/
@[simp] theorem abs_abs (f : Format) (w : BitVec f.bitWidth) :
    abs f (abs f w) = abs f w := by simp [abs]

/-- Copying a word's own sign onto it leaves every bit unchanged. -/
@[simp] theorem copySign_self (f : Format) (w : BitVec f.bitWidth) :
    copySign f w w = w := withSign_negative f w

end Bits

namespace Codec

/-- Decoding sign replacement preserves the coefficient, quantum and NaN metadata.
This holds for every codec and every word, without a canonicality hypothesis. -/
theorem decode_withSign (codec : Codec) (f : Format) (s : Bool)
    (w : BitVec f.bitWidth) :
    codec.decode f (Bits.withSign f s w) = (codec.decode f w).withSign s := by
  simp only [decode, Bits.negative_withSign, Bits.payload_withSign]
  split_ifs <;> rfl

/-- For every codec, the decoded datum's sign is the stored sign bit, for all words including NaNs
and noncanonical encodings. -/
theorem decode_isSignMinus (codec : Codec) (f : Format) (w : BitVec f.bitWidth) :
    (codec.decode f w).isSignMinus = Bits.negative f w := by
  simp only [decode]
  split_ifs <;> rfl

/-- For every codec and word, decoding the bitwise negation gives the negated datum. -/
theorem decode_negate (codec : Codec) (f : Format) (w : BitVec f.bitWidth) :
    codec.decode f (Bits.negate f w) = (codec.decode f w).negate := by
  rw [Bits.negate, decode_withSign, Datum.negate_eq_withSign, decode_isSignMinus]

/-- For every codec and word, decoding the bitwise absolute value gives the datum's absolute value.
-/
theorem decode_abs (codec : Codec) (f : Format) (w : BitVec f.bitWidth) :
    codec.decode f (Bits.abs f w) = (codec.decode f w).abs :=
  decode_withSign codec f false w

/-- For every codec and pair of words, decoding the bitwise sign copy gives the datum-level sign
copy. -/
theorem decode_copySign (codec : Codec) (f : Format) (x y : BitVec f.bitWidth) :
    codec.decode f (Bits.copySign f x y) =
      (codec.decode f x).copySign (codec.decode f y) := by
  rw [Bits.copySign, decode_withSign, Datum.copySign, decode_isSignMinus]

end Codec
end FloatLib.Floats.Formats.DecimalInterchange
