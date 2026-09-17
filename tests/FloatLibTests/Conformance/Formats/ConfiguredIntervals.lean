/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval
public import FloatLib.Numerics.Enclosure.Interval.Real

/-!
# Configured interval conformance

These checks exercise endpoint-type inference, model parity, exact encoding round trips,
and whole-range fallback. The same API is used for tiny finite and IEEE formats, binary16,
binary32, and binary64. Symbolic enclosure checks retain their finiteness hypotheses.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.ConfiguredIntervals

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open ExecFloat.Binary (Interval)

/-- Endpoint types determine all interval representation parameters. -/
def enclose (lo hi : ExecFloat.Binary 8 23) := Interval.ofBounds lo hi

/-- A downstream theorem can use the constructor without naming a storage plan or codec. -/
example (lo hi : ExecFloat.Binary 8 23) : (enclose lo hi).ValidExtended :=
  Interval.validExtended_ofBounds lo hi (by decide)

section Generic

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]

local notation "Bounds" => Interval (format := format) (plan := plan) (code := code)

/-- Encoding round trips include arbitrary signed zeros and NaN payloads. -/
example (I : Bounds) : Interval.ofModel I.toModel = I := Interval.ofModel_toModel I

/-- Multiplication uses exactly the model's directed corner operations. -/
example (I J : Bounds) :
    (I.mul J).toModel = Model.Interval.mul I.toModel J.toModel := Interval.toModel_mul I J

/-- Every storage plan shares the real enclosure theorem, with no backend assumptions. -/
example (I J : Bounds) (hformat : format.isIEEE = true)
    (hI : I.Valid) (hJ : J.Valid) {x y : ℝ} (hx : I.RealMem x) (hy : J.RealMem y) :
    (I.add J).ERealMem ((x + y : ℝ) : EReal) :=
  Interval.add_sound I J hformat hI hJ hx hy

/-- An activation can consume the product enclosure even when multiplication overflows. -/
example (I J : Bounds) (hformat : format.isIEEE = true)
    (hI : I.Valid) (hJ : J.Valid) {x y : ℝ} (hx : I.RealMem x) (hy : J.RealMem y) :
    (I.mul J).relu.ERealMem ((max (x * y) 0 : ℝ) : EReal) :=
  Interval.relu_sound_extended (I.mul J) (Interval.mul_validExtended I J hformat)
    (Interval.mul_sound I J hformat hI hJ hx hy)

/-- Finite-only addition exposes the range assumptions needed to avoid saturation. -/
example (I J : Bounds) (hformat : format.encoding = .finite)
    (hlo : |Model.toReal (ExecFloat.Binary.toModel I.lo) +
      Model.toReal (ExecFloat.Binary.toModel J.lo)| ≤ Model.toReal (Model.posMaxFinite format))
    (hhi : |Model.toReal (ExecFloat.Binary.toModel I.hi) +
      Model.toReal (ExecFloat.Binary.toModel J.hi)| ≤ Model.toReal (Model.posMaxFinite format))
    {x y : ℝ} (hx : I.RealMem x) (hy : J.RealMem y) : (I.add J).RealMem (x + y) :=
  Interval.add_sound_of_encoding_finite I J hformat hlo hhi hx hy

end Generic

/-- The shared binary adapter computes through the same generic API as decimal and posit. -/
example :
    let I := FloatLib.Numerics.Interval.point (1 : ExecFloat.Binary 5 10)
    let J := FloatLib.Numerics.Interval.point (2 : ExecFloat.Binary 5 10)
    ((FloatLib.Numerics.Interval.add? ExecFloat.Binary.intervalRounding I J).map
      (fun K => (ExecFloat.Binary.toRat? K.lo, ExecFloat.Binary.toRat? K.hi))) =
      some (some 3, some 3) := by
  decide +kernel

/-- A finite-only binary adapter reports failure when the real enclosure cannot fit. -/
example :
    let I := FloatLib.Numerics.Interval.point
      (ExecFloat.Binary.maxFinite false : ExecFloat.Binary 3 2 .finite)
    (FloatLib.Numerics.Interval.add? ExecFloat.Binary.intervalRounding I I).isNone = true := by
  decide +kernel

/-- Rationally executed binary bounds enclose products of arbitrary real inputs. -/
example (I J K : FloatLib.Numerics.Interval (ExecFloat.Binary 8 23))
    (h : FloatLib.Numerics.Interval.mul? ExecFloat.Binary.intervalRounding I J = some K)
    {x y : ℝ} (hx : I.ContainsReal ExecFloat.Binary.toRat? x)
    (hy : J.ContainsReal ExecFloat.Binary.toRat? y) :
    K.ContainsReal ExecFloat.Binary.toRat? (x * y) :=
  FloatLib.Numerics.Interval.containsReal_mul? ExecFloat.Binary.intervalRounding h hx hy

/-- Small finite-only formats use maximal finite values, not imaginary infinity encodings. -/
example :
    let lo : ExecFloat.Binary 3 2 .finite := ExecFloat.Binary.maxFinite true
    let hi : ExecFloat.Binary 3 2 .finite := ExecFloat.Binary.maxFinite false
    let I := Interval.ofBounds hi lo
    (ExecFloat.Binary.toNatBits I.lo, ExecFloat.Binary.toNatBits I.hi) =
      (ExecFloat.Binary.toNatBits lo, ExecFloat.Binary.toNatBits hi) := by
  decide +kernel

/-- Binary16 interval addition rounds the two bounds independently. -/
example :
    let I := Interval.ofBounds (1 : ExecFloat.Binary 5 10) 2
    let J := Interval.ofBounds (3 : ExecFloat.Binary 5 10) 4
    let result := I.add J
    (ExecFloat.Binary.toRat? result.lo, ExecFloat.Binary.toRat? result.hi) =
      (some 4, some 6) := by
  decide +kernel

/-- Binary32 division through zero conservatively returns both infinities. -/
example :
    let I := Interval.point (1 : ExecFloat.Binary 8 23)
    let J := Interval.ofBounds (-1 : ExecFloat.Binary 8 23) 1
    let result := I.div J
    (ExecFloat.Binary.isInfinite result.lo, ExecFloat.Binary.signBit result.lo,
      ExecFloat.Binary.isInfinite result.hi, ExecFloat.Binary.signBit result.hi) =
      (true, true, true, false) := by
  decide +kernel

/-- Binary64 square roots retain exact representable endpoint results. -/
example :
    let result := (Interval.ofBounds (1 : ExecFloat.Binary 11 52) 4).sqrt
    (ExecFloat.Binary.toRat? result.lo, ExecFloat.Binary.toRat? result.hi) =
      (some 1, some 2) := by
  decide +kernel

/-- Point intervals preserve the sign bit of negative zero. -/
example :
    let I := Interval.point (ExecFloat.Binary.zero true : ExecFloat.Binary 8 23)
    (ExecFloat.Binary.toNatBits I.lo, ExecFloat.Binary.toNatBits I.hi) =
      (0x80000000, 0x80000000) := by
  decide +kernel

/-- Raw point construction and conversion preserve signaling-NaN payload bits. -/
example :
    let I := Interval.point (ExecFloat.Binary.ofNatBits 0x7f800123 : ExecFloat.Binary 8 23)
    (ExecFloat.Binary.toNatBits I.lo, ExecFloat.Binary.toNatBits I.hi) =
      (0x7f800123, 0x7f800123) := by
  decide +kernel

/-- Checked construction rejects NaN endpoints and returns the whole range. -/
example :
    let nan : ExecFloat.Binary 5 10 := ExecFloat.Binary.canonicalNaN
    let I := Interval.ofBounds nan 1
    (ExecFloat.Binary.toNatBits I.lo, ExecFloat.Binary.toNatBits I.hi) =
      (0xfc00, 0x7c00) := by
  decide +kernel

/-- The zero-times-infinity corner is indeterminate, so it cannot narrow the result. -/
example :
    let zero := Interval.point (0 : ExecFloat.Binary 5 10)
    let infinite := Interval.point (ExecFloat.Binary.infinity false : ExecFloat.Binary 5 10)
    let result := zero.mul infinite
    (ExecFloat.Binary.toNatBits result.lo, ExecFloat.Binary.toNatBits result.hi) =
      (0xfc00, 0x7c00) := by
  decide +kernel

end FloatLibTests.Conformance.Formats.ConfiguredIntervals
