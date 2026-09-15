/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word16.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Backend.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Native.Instances

/-!
# Correctness of the fixed `UInt16` posit backend

Each monomorphic `UInt16` operation first agrees with the shared carrier-generic packed kernel,
then inherits that kernel's proof against the representation-independent specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Word16

open FloatLib.Numerics

variable {format : Format}

/-! ## Addition and subtraction -/

/-- Fixed `UInt16` addition refines configured posit addition. -/
theorem add_eq_spec
    (width_le : format.bits ≤ 16)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word16 width_le)) (.word16 width_le))) :
    add width_le left right = Spec.add left right := by
  refine Eq.trans ?_
    (storedNativeWordAdd_eq_spec (le_trans width_le (by decide)) left right)
  apply FloatLib.Floats.ExecFloat.ext
  simpa only [add, addRaw, storedNativeWordAdd, NativeCode.word,
    NativeCode.pack, NativeCode.toUInt64, word16NativeCode,
    FloatLib.Floats.ExecFloat.raw_ofRaw, FixedWords.uint16Carrier,
    StaticStorage.Word16Code.ofNat] using
    FixedWords.addCode_eq FixedWords.uint16Carrier
      width_le left.raw right.raw

/-- Fixed `UInt16` subtraction refines configured posit subtraction. -/
theorem sub_eq_spec
    (width_le : format.bits ≤ 16)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word16 width_le)) (.word16 width_le))) :
    sub width_le left right = Spec.sub left right := by
  refine Eq.trans ?_
    (storedNativeWordSub_eq_spec (le_trans width_le (by decide)) left right)
  apply FloatLib.Floats.ExecFloat.ext
  simpa only [sub, subRaw, storedNativeWordSub, NativeCode.word,
    NativeCode.pack, NativeCode.toUInt64, word16NativeCode,
    FloatLib.Floats.ExecFloat.raw_ofRaw, FixedWords.uint16Carrier,
    StaticStorage.Word16Code.ofNat] using
    FixedWords.subCode_eq FixedWords.uint16Carrier
      width_le left.raw right.raw

/-! ## Multiplication and division -/

/-- Fixed `UInt16` multiplication refines configured posit multiplication. -/
theorem mul_eq_spec
    (width_le : format.bits ≤ 16)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word16 width_le)) (.word16 width_le))) :
    mul width_le left right = Spec.mul left right := by
  refine Eq.trans ?_
    (storedNativeWordMul_eq_spec (le_trans width_le (by decide)) left right)
  apply FloatLib.Floats.ExecFloat.ext
  simpa only [mul, mulRaw, storedNativeWordMul, NativeCode.word,
    NativeCode.pack, NativeCode.toUInt64, word16NativeCode,
    FloatLib.Floats.ExecFloat.raw_ofRaw, FixedWords.uint16Carrier,
    StaticStorage.Word16Code.ofNat] using
    FixedWords.mulCode_eq FixedWords.uint16Carrier
      width_le left.raw right.raw

/-- Fixed `UInt16` division refines configured posit division. -/
theorem div_eq_spec
    (width_le : format.bits ≤ 16)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word16 width_le)) (.word16 width_le))) :
    div width_le left right = Spec.div left right := by
  refine Eq.trans ?_
    (storedNativeWordDiv_eq_spec (le_trans width_le (by decide)) left right)
  apply FloatLib.Floats.ExecFloat.ext
  simpa only [div, divRaw, storedNativeWordDiv, NativeCode.word,
    NativeCode.pack, NativeCode.toUInt64, word16NativeCode,
    FloatLib.Floats.ExecFloat.raw_ofRaw, FixedWords.uint16Carrier,
    StaticStorage.Word16Code.ofNat] using
    FixedWords.divCode_eq FixedWords.uint16Carrier
      width_le left.raw right.raw

/-! ## Square root and fused multiply-add -/

/-- Fixed `UInt16` square root refines configured posit square root. -/
theorem sqrt_eq_spec
    (width_le : format.bits ≤ 16)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word16 width_le)) (.word16 width_le))) :
    sqrt width_le value = Spec.sqrt value := by
  refine Eq.trans ?_
    (storedNativeWordSqrt_eq_spec (le_trans width_le (by decide)) value)
  apply FloatLib.Floats.ExecFloat.ext
  simpa only [sqrt, sqrtRaw, storedNativeWordSqrt, NativeCode.word,
    NativeCode.pack, NativeCode.toUInt64, word16NativeCode,
    FloatLib.Floats.ExecFloat.raw_ofRaw, FixedWords.uint16Carrier,
    StaticStorage.Word16Code.ofNat] using
    FixedWords.sqrtCode_eq FixedWords.uint16Carrier width_le value.raw

/-- Fixed `UInt16` FMA refines configured posit FMA. -/
theorem fma_eq_spec
    (width_le : format.bits ≤ 16)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word16 width_le)) (.word16 width_le))) :
    fma width_le left right addend = Spec.fma left right addend := by
  refine Eq.trans ?_
    (storedNativeWordFma_eq_spec
      (le_trans width_le (by decide)) left right addend)
  apply FloatLib.Floats.ExecFloat.ext
  simpa only [fma, fmaRaw, storedNativeWordFma, NativeCode.word,
    NativeCode.pack, NativeCode.toUInt64, word16NativeCode,
    FloatLib.Floats.ExecFloat.raw_ofRaw, FixedWords.uint16Carrier,
    StaticStorage.Word16Code.ofNat] using
    FixedWords.fmaCode_eq FixedWords.uint16Carrier
      width_le left.raw right.raw addend.raw

end FloatLib.Floats.Formats.Posit.Configured.Backend.Word16
