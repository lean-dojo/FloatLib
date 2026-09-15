/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Runtime

/-!
# Native finite decoding for one-word formats

A flat `UInt64` field decoder serves every conventional IEEE format covered by
`NativeSmallWord.StorageEligible`. The executable operations have refinements in `Finite.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordFinite

open NativeSmallWord

/-- Decode the finite significand, including the implicit bit for normal values. -/
@[inline] def finiteMantissa
    (fmt : FloatFormat) (exponent fraction : UInt64) : UInt64 :=
  if exponent == 0 then fraction else fraction ||| hiddenBit fmt

/--
Decode a finite value through native storage fields.

An all-ones exponent returns `none`; zeros, subnormals, and normals retain the exact compact
component representation used by `FiniteKernel`.
-/
@[inline] def decode? {fmt : FloatFormat}
    (x : Model fmt) : Option FiniteKernel.Components :=
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  if exponent == NativeSmallWord.exponentMask fmt then
    none
  else
    let fraction := NativeSmallWord.fractionField fmt bits
    some {
      sign := NativeSmallWord.signField fmt bits
      exponent := exponent.toNat
      mantissa := (finiteMantissa fmt exponent fraction).toNat }

/--
Native-storage finite addition through the compiled unsigned-scale component kernel.

The body names `FiniteKernel.addComponentsImpl` rather than the exact-dyadic `addComponents`.
The two are proved equal in `Kernel.Proof`, but a runtime module cannot import that proof, so
naming the compiled kernel here is what keeps the exact-dyadic body out of generated code.
-/
@[inline] def addFinite? {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  match decode? x, decode? y with
  | some dx, some dy => some <| FiniteKernel.addComponentsImpl fmt dx dy
  | _, _ => none

/--
Native-storage finite FMA through the compiled unsigned-scale component kernel.

As for `addFinite?`, the body names `FiniteKernel.fmaComponentsImpl`, the compiled twin of the
exact `fmaComponents`, because the equality between them is proved in a module this runtime cannot
import.
-/
@[inline] def fmaFinite? {fmt : FloatFormat}
    (x y z : Model fmt) : Option (Model fmt) :=
  match decode? x, decode? y, decode? z with
  | some dx, some dy, some dz =>
      some <| FiniteKernel.fmaComponentsImpl fmt dx dy dz
  | _, _, _ => none

/-- Native-storage positive square root using the shared compact finite kernel. -/
@[inline] def sqrtPositive? {fmt : FloatFormat}
    (x : Model fmt) : Option (Model fmt) :=
  match decode? x with
  | none => none
  | some value => FiniteSqrt.sqrtComponents? fmt value

/--
Native-storage square root for an input already proved positive, finite, and nonzero.

The proofs state the exact contract of the unchecked field kernel and are erased by compilation.
The implementation keeps the one-word decoder and enters the same descriptor-generic square-root
kernel used by the arbitrary-width path.
-/
@[inline] def sqrtPositive {fmt : FloatFormat}
    (_heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt)
    (_hfinite : isFinite x = true)
    (_hnonzero : isZero x = false)
    (_hpositive : signBit x = false) : Model fmt :=
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  let fraction := NativeSmallWord.fractionField fmt bits
  let mantissa := finiteMantissa fmt exponent fraction
  FiniteSqrt.sqrtPositiveDyadic fmt mantissa.toNat
    (FiniteKernel.dyadicExponent fmt exponent.toNat)

end Model.NativeSmallWordFinite
end FloatLib.Floats.Formats.BinaryInterchange
