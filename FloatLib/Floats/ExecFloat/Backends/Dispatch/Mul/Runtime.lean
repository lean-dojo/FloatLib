/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.TwoWordMul.Runtime

/-!
# Executable multiplication backends

The generic path computes exact finite products and owns the complete exceptional-value policy.
The dispatcher opportunistically uses native binary32 or binary64, fixed-pair limbs, and
parameterized one- or two-word kernels when their structural capabilities apply.

Every specialized routine is partial by design: a declined case is handled by the one exact
generic implementation. `Mul.Proof` establishes that successful fast paths and the baseline all
implement the same public specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace MulBackend

/--
Width-generic compiled multiplication.

Finite operands use the compact scale kernel; exceptional operands retain the public NaN and
infinity policy.
-/
@[specialize fmt] def generic {fmt : FloatFormat}
    (x y : Model fmt) : Model fmt :=
  match FiniteKernel.mulRuntime? x y with
  | some product => product
  | none =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isZero y then
              invalidResult fmt
            else
              nativeOverflow fmt (signBit x != signBit y)
          else if isInf y then
            if isZero x then
              invalidResult fmt
            else
              nativeOverflow fmt (signBit x != signBit y)
          else
            invalidResult fmt

/--
Word-specialized compiled implementation of `mul`.

Each specialized kernel is selected by a structural capability and returns only a partial fast
result. Binary32 uses the checked narrow backend. Binary64 first tries the parameterized two-word
normal-product kernel, whose `64 x 64 -> 128` product and machine-word finishing stage suit its
53-bit significands, and falls back to its fixed multiword kernel. Eligible pair layouts use the
four-limb product kernel. Other conventional IEEE formats use
parameterized one- and two-word normal-product kernels. After the binary64 candidate chain is
exhausted, and on every other declined route,
`generic` supplies the result. The dispatcher is specialized on the descriptor, as described in
`Dispatch.Add.Runtime`.
-/
@[specialize fmt] def word {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    let y32 : NativeBinary32.Value := Eq.mp hcarrier y
    match NativeBinary32.mulFiniteImpl? x32 y32 with
    | some product => Eq.mpr hcarrier product
    | none => generic x y
  else if h64 : FloatFormat.IsBinary64 fmt then
    match NativeTwoWordMul.mulNormal? x y with
    | some product => product
    | none =>
        let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
        let hcarrier := congrArg Model hfmt
        let x64 : NativeBinary64.Value := Eq.mp hcarrier x
        let y64 : NativeBinary64.Value := Eq.mp hcarrier y
        match NativeBinary64.mulNormalLimb? x64 y64 with
        | some product => Eq.mpr hcarrier product
        | none => generic x y
  else if _hpair : NativePair.Eligible fmt then
    match NativePair.mulNormalLimb? x y with
    | some product => product
    | none => generic x y
  else if _heligible : NativeSmallWordMul.Eligible fmt then
    let product := NativeSmallWordMul.mulNormalWord x y
    if product == NativeSmallWordMul.declineWord then
      generic x y
    else
      NativeSmallWord.ofWord product
  else if _htwoWord : NativeTwoWordMul.Eligible fmt then
    match NativeTwoWordMul.mulNormal? x y with
    | some product => product
    | none => generic x y
  else
    generic x y

end MulBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
