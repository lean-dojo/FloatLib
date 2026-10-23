/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Sqrt.Runtime

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Executable word-specialized square-root dispatch

Executable square-root kernels and their format dispatcher live here. Correctness theorems are in
`SqrtWord.Proof`, so runtime-only clients do not load the native refinement proofs.

Binary32 and binary64 use their native paths, other one-word IEEE formats use the shared word
kernel, and every remaining format uses the general implementation. All of these implement one
square-root specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace SqrtBackend

/--
Width-generic compiled square root.

The outer cases handle NaN payloads, infinities, signed zeros and negative inputs. Positive
finite nonzero values use the compact decoder and checked model square root. Their classification
proof makes the finite decoder total, so this path needs no fallback.
-/
@[specialize fmt] def generic {fmt : FloatFormat}
    (x : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN1 x) fun hnan =>
    let hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
    if hxInf : isInf x then
      if signBit x then invalidResult fmt else nativeOverflow fmt false
    else if hxZero : isZero x then
      x
    else if hxSign : signBit x then
      invalidResult fmt
    else
      let hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN
          (Bool.eq_false_of_not_eq_true hxInf)
      FiniteSqrt.sqrtPositiveRuntime x hfinite
        (Bool.eq_false_of_not_eq_true hxZero)
        (Bool.eq_false_of_not_eq_true hxSign)

/--
One-word square root with native finite-field decoding.

The outer cases match `SqrtBackend.generic`. Only the positive finite kernel changes: it becomes
the one-word root of `NativeSmallWordSqrt` where the format allows it. Eligibility and
classification evidence are erased, so compiled code keeps the native field kernel without an
impossible fallback.
-/
@[inline] def smallWord {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN1 x) fun hnan =>
    let hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
    if hxInf : isInf x then
      if signBit x then invalidResult fmt else nativeOverflow fmt false
    else if hxZero : isZero x then
      x
    else if hxSign : signBit x then
      invalidResult fmt
    else
      let hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN
          (Bool.eq_false_of_not_eq_true hxInf)
      NativeSmallWordSqrt.sqrtPositive heligible x hfinite
        (Bool.eq_false_of_not_eq_true hxZero)
        (Bool.eq_false_of_not_eq_true hxSign)

/--
Word-specialized compiled implementation of `sqrt`.

Binary32 uses the checked `UInt32`/`UInt64` backend. Binary64 uses the two-limb restoring
kernel. Other eligible one-word IEEE formats use native storage decoding and, when the radicand
fits one word, the one-word root. Remaining formats use `SqrtBackend.generic`. The dispatcher is
specialized on the descriptor, as described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def word {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    Eq.mpr hcarrier (NativeBinary32.sqrt x32)
  else if h64 : FloatFormat.IsBinary64 fmt then
    let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    let hcarrier := congrArg Model hfmt
    let x64 : NativeBinary64.Value := Eq.mp hcarrier x
    Eq.mpr hcarrier (NativeBinary64.sqrt x64)
  else if heligible : NativeSmallWord.StorageEligible fmt then
    smallWord heligible x
  else
    generic x

end SqrtBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
