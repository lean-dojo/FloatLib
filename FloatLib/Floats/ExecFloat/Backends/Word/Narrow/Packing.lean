/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Native binary32 field-packing identities

Extracting and repacking a native binary32 word loses nothing, and this module proves it, along with
the native form of quieting a NaN. Executable field operations live in `Narrow.Base.Runtime`.
Addition and fused multiply-add proofs share these bit-level identities, which don't depend on
either arithmetic operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Bit `i` of the 32-bit mask `2 ^ n - 1` is set exactly below `n`. -/
private theorem lowMask_getLsbD (n i : Nat) (hn : n ≤ 32) :
    (BitVec.ofNat 32 (2 ^ n - 1)).getLsbD i = decide (i < n) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    exact Nat.testBit_two_pow_sub_one n i
  · have : ¬i < n := by omega
    simp [hi, this]

private theorem fractionMask_getLsbD (i : Nat) :
    (8388607#32 : BitVec 32).getLsbD i = decide (i < 23) :=
  lowMask_getLsbD 23 i (by decide)

private theorem exponentMask_getLsbD (i : Nat) :
    (255#32 : BitVec 32).getLsbD i = decide (i < 8) :=
  lowMask_getLsbD 8 i (by decide)

private theorem signMask_getLsbD (i : Nat) :
    (2147483648#32 : BitVec 32).getLsbD i = decide (i = 31) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    change (2 ^ 31).testBit i = decide (i = 31)
    simpa [eq_comm] using (Nat.testBit_two_pow (n := 31) (m := i))
  · have : i ≠ 31 := by omega
    simp [hi, this]

/-- Repacking the fields extracted from a native binary32 word returns the original word. -/
theorem mkBits_fields (bits : UInt32) :
    mkBits (signBit bits) (expField bits).toNat (fracField bits).toNat = bits := by
  have hsignBit : bits.toBitVec.getLsbD 31 = signBit bits := by
    unfold signBit
    by_cases hsign : bits &&& 0x80000000 = 0
    · have h := congrArg (fun x : UInt32 => x.toBitVec.getLsbD 31) hsign
      rw [hsign]
      simpa [UInt32.toBitVec_and, BitVec.getLsbD_ofNat] using h
    · simp only [bne_iff_ne.mpr hsign]
      by_contra hbit
      apply hsign
      apply UInt32.toBitVec_inj.1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases heq : i = 31
      · subst i
        simpa [UInt32.toBitVec_and, signMask_getLsbD] using hbit
      · simp [UInt32.toBitVec_and, signMask_getLsbD, heq]
  simp only [mkBits, UInt32.ofNat_toNat]
  unfold expField fracField
  apply UInt32.toBitVec_inj.1
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight, apply_ite UInt32.toBitVec]
  norm_num
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hsignWord :
      (if signBit bits = true then 2147483648#32 else 0#32).getLsbD i =
        (signBit bits && decide (i = 31)) := by
    cases signBit bits <;> simp [signMask_getLsbD]
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, hsignWord]
  by_cases hlow : i < 23
  · have hfraction : (8388607#32 : BitVec 32)[i] = true := by
      rw [← BitVec.getLsbD_eq_getElem hi, fractionMask_getLsbD]
      simp [hlow]
    have hne : i ≠ 31 := by omega
    simp [hlow, hi, hfraction, hne]
  · by_cases hmid : i < 31
    · have hindex : 23 + (i - 23) = i := by omega
      have hexponent : i - 23 < 8 := by omega
      have hexponentMask : (255#32 : BitVec 32)[i - 23] = true := by
        rw [← BitVec.getLsbD_eq_getElem (by omega), exponentMask_getLsbD]
        simp [hexponent]
      have hfraction : (8388607#32 : BitVec 32)[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem hi, fractionMask_getLsbD]
        simp [hlow]
      have hne : i ≠ 31 := by omega
      simp [hlow, hi, hindex, hexponentMask, hfraction, hne]
    · have heq : i = 31 := by omega
      subst i
      simp only [decide_true, Bool.and_true]
      rw [hsignBit]
      simp

/-- Setting the native quiet-NaN bit agrees with setting the generic binary32 quiet bit. -/
theorem ofUInt32_or_quietBit (x : Value) :
    ofUInt32 (toUInt32 x ||| 0x00400000) =
      Model.ofBits (x.bits ||| FloatFormat.quietBit FloatFormat.binary32) := by
  cases x
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
