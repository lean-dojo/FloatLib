/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Addition.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Addition.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Subtraction.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Runtime

/-!
# Executable addition and subtraction backends

The generic path handles exact finite arithmetic and the descriptor's exceptional-value policy.
The word dispatcher first tries a kernel justified by structural capabilities (native binary32 or
binary64, a fixed pair of limbs, the one-word `UInt64` kernel for small IEEE formats, or reusable
small-word storage for the remaining one-word formats) and returns to that generic path when the
specialization declines.

The `@[specialize fmt]` annotation exposes descriptor-dependent tests to specialization at
closed-format call sites. The choice of kernel depends only on the descriptor; operand-dependent
acceptance checks remain in the selected kernels. A runtime descriptor is checked on each call.

Refinement theorems live in `Add.Proof`, so runtime clients can import this module separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace AddBackend

/--
Width-generic compiled addition.

Finite operands use the compact component decoder; exceptional operands retain the public NaN and
infinity policy.
-/
@[specialize fmt] def generic {fmt : FloatFormat}
    (x y : Model fmt) : Model fmt :=
  match FiniteKernel.addRuntime? x y with
  | some sum => sum
  | none =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isInf y then
              if signBit x == signBit y then x else invalidResult fmt
            else
              x
          else if isInf y then
            y
          else
            invalidResult fmt

/--
Non-table implementation of addition.

Specialized kernels are selected by structural capabilities. Binary32 finite operands use the
checked native-word backend. Binary64 first tries the one-word `UInt64` kernel of
`NativeSmallWordAdd`, whose capacity contract admits its 53-bit significands, and falls back to its
fixed-format chain for wide alignment shifts and boundary results. Eligible two-word layouts use
their fixed-limb and width-generic finite chain. Every other IEEE format with at most 30 exponent
and 61 fraction bits adds entirely in `UInt64` through `NativeSmallWordAdd`; the remaining one-word
IEEE formats use the shared native-storage decoder before the compiled component kernel. Every
decline and every exceptional case enters the single exact `generic` baseline here.
-/
@[specialize fmt] def word {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    let y32 : NativeBinary32.Value := Eq.mp hcarrier y
    match NativeBinary32.addFiniteImpl? x32 y32 with
    | some sum => Eq.mpr hcarrier sum
    | none => generic x y
  else if h64 : FloatFormat.IsBinary64 fmt then
    match NativeSmallWordAdd.addFinite? x y false with
    | some sum => sum
    | none =>
        let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
        let hcarrier := congrArg Model hfmt
        let x64 : NativeBinary64.Value := Eq.mp hcarrier x
        let y64 : NativeBinary64.Value := Eq.mp hcarrier y
        match NativeBinary64.addFiniteFastImpl? x64 y64 with
        | some sum => Eq.mpr hcarrier sum
        | none => generic x y
  else if _hpair : NativePair.Eligible fmt then
    match NativePair.addFinite? x y with
    | some sum => sum
    | none => generic x y
  else if _heligible : NativeSmallWordAdd.Eligible fmt then
    match NativeSmallWordAdd.addFinite? x y false with
    | some sum => sum
    | none => generic x y
  else if _hstorage : NativeSmallWord.StorageEligible fmt then
    match NativeSmallWordFinite.addFinite? x y with
    | some sum => sum
    | none => generic x y
  else
    generic x y

/--
Non-table implementation of subtraction.

Binary32 enters its checked native backend directly; binary64 first tries the one-word `UInt64`
kernel with the right sign toggled in the storage word and then its fixed-format chain. Eligible
two-word layouts use their fixed-limb and width-generic finite subtraction chain. Every other
one-word IEEE format with at most 30 exponent and 61 fraction bits subtracts through
`NativeSmallWordAdd`; the remaining one-word formats use the shared native decoder on the negated
operand. Exceptional cases enter exact generic addition with the negated right operand.
-/
@[specialize fmt] def subWord {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    let y32 : NativeBinary32.Value := Eq.mp hcarrier y
    match NativeBinary32.addFiniteImpl? x32 (NativeBinary32.negate y32) with
    | some difference => Eq.mpr hcarrier difference
    | none => generic x (neg y)
  else if h64 : FloatFormat.IsBinary64 fmt then
    match NativeSmallWordAdd.addFinite? x y true with
    | some difference => difference
    | none =>
        let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
        let hcarrier := congrArg Model hfmt
        let x64 : NativeBinary64.Value := Eq.mp hcarrier x
        let y64 : NativeBinary64.Value := Eq.mp hcarrier y
        match NativeBinary64.subFiniteFastImpl? x64 y64 with
        | some difference => Eq.mpr hcarrier difference
        | none => generic x (neg y)
  else if _hpair : NativePair.Eligible fmt then
    match NativePair.subFinite? x y with
    | some difference => difference
    | none => generic x (neg y)
  else if _heligible : NativeSmallWordAdd.Eligible fmt then
    match NativeSmallWordAdd.addFinite? x y true with
    | some difference => difference
    | none => generic x (neg y)
  else if _hstorage : NativeSmallWord.StorageEligible fmt then
    match NativeSmallWordFinite.addFinite? x (neg y) with
    | some difference => difference
    | none => generic x (neg y)
  else
    generic x (neg y)

end AddBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
