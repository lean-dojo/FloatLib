/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Directed rounding of exact dyadics

This module rounds an exact signed dyadic into a binary format under each `IEEERoundingMode`.
Rounding toward zero, toward positive and toward negative share one pair of magnitude rounders,
`roundDyadicMagnitudeDown` and `roundDyadicMagnitudeUp`, and the sign of the value picks which
one runs. Nearest-even delegates to `Model.roundDyadic`.

Two more rounders come from the same pieces. `roundDyadicAway` (MPFR's `MPFR_RNDA`) always rounds
the magnitude up. `roundDyadicNearestAway` (IEEE 754-2019 `roundTiesToAway`) is nearest-even
except at an exact tie on the format's grid, which `dyadicIsGridTie` detects and which then rounds
away from zero.

Overflow follows `directedOverflow`. A magnitude carried upward becomes the format's native
overflow value, and one carried downward becomes the largest finite value. In
`Rounding.Policy.Runtime`, the policy entry point `Policy.roundDyadic` delegates to
`Internal.Directed.roundDyadic` for the six directions with native overflow and gradual
underflow. `Policy.roundDyadicGeneral` is an independent rational core, and
`Rounding.Policy.Agreement` proves that it agrees with these rounders.

Every threshold comes from `FloatFormat`. Because the magnitude helpers need a positive mantissa,
the signed entry points handle zero before choosing one.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Directed rounding of exact dyadics -/

/-- Round an exact positive magnitude downward, attaching `sign` to the result. -/
def roundDyadicMagnitudeDown (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let leading := Nat.log2 mantissa
  let totalExponent := Int.ofNat leading + exponent
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  if totalExponent > maxNormal then
    maxFinite fmt sign
  else if totalExponent < minSubnormal then
    zero fmt sign
  else if totalExponent < minNormal then
    let fraction :=
      match exponent - minSubnormal with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => Nat.shiftRight mantissa (shift + 1)
    if fraction == 0 then zero fmt sign else ofFields fmt sign 0 fraction
  else
    let roundedMantissa :=
      if leading ≥ precision then
        Nat.shiftRight mantissa (leading - precision)
      else
        Nat.shiftLeft mantissa (precision - leading)
    let encodedExponent := Int.toNat (totalExponent + Int.ofNat fmt.exponentBias)
    let fraction := roundedMantissa - pow2 precision
    if encodedExponent > fmt.maxFiniteExpField ||
        (encodedExponent == fmt.maxFiniteExpField &&
          fraction > fmt.maxFiniteFracField) then
      maxFinite fmt sign
    else
      ofFields fmt sign encodedExponent fraction

/-- Round an exact positive magnitude upward, attaching `sign` to the result. -/
def roundDyadicMagnitudeUp (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let leading := Nat.log2 mantissa
  let totalExponent := Int.ofNat leading + exponent
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  if totalExponent > maxNormal then
    nativeOverflow fmt sign
  else if totalExponent < minSubnormal then
    ofFields fmt sign 0 1
  else if totalExponent < minNormal then
    let fraction :=
      match exponent - minSubnormal with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => Numerics.shiftRightCeil mantissa (shift + 1)
    packRoundedSubnormal fmt sign (ofFields fmt sign 0 1) fraction
  else
    let roundedMantissa :=
      if leading ≥ precision then
        Numerics.shiftRightCeil mantissa (leading - precision)
      else
        Nat.shiftLeft mantissa (precision - leading)
    packRoundedNormal fmt sign (nativeOverflow fmt sign) totalExponent roundedMantissa

/-- Round a positive exact dyadic toward negative infinity. -/
@[inline] def roundDyadicPosDown
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  roundDyadicMagnitudeDown fmt false mantissa exponent

/-- Round a positive exact dyadic toward positive infinity. -/
@[inline] def roundDyadicPosUp
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  roundDyadicMagnitudeUp fmt false mantissa exponent

/-- Round an exact dyadic toward negative infinity. -/
def roundDyadicDown (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else if value.negative then
    roundDyadicMagnitudeUp fmt true value.significand value.exponent
  else
    roundDyadicMagnitudeDown fmt false value.significand value.exponent

/-- Round an exact dyadic toward positive infinity. -/
def roundDyadicUp (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else if value.negative then
    roundDyadicMagnitudeDown fmt true value.significand value.exponent
  else
    roundDyadicMagnitudeUp fmt false value.significand value.exponent

/-- Round an exact dyadic toward zero. -/
def roundDyadicTowardZero (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundDyadicMagnitudeDown fmt value.negative value.significand value.exponent

/--
Round an exact dyadic away from zero, MPFR's `MPFR_RNDA`.

The magnitude rounds up and keeps its sign, so a nonzero value below the least subnormal becomes
that subnormal and a magnitude carried past the largest finite value becomes the native overflow
value.
-/
def roundDyadicAway (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundDyadicMagnitudeUp fmt value.negative value.significand value.exponent

/--
Whether an exact dyadic lies halfway between two adjacent values of the binary grid of `fmt`, with
gradual underflow and no upper exponent bound.

If the leading bit has exponent `L`, the grid spacing is
`2^(max fmt.minSubnormalExponent (L - fmt.fracWidth))`, the spacing `roundDyadic` rounds to. The
value is a tie when the bits below that spacing are one half of it, as `Numerics.shiftRightIsTie`
tests. Zero is never a tie, and neither is a magnitude below half the least subnormal, whose
guard bit is clear. The grid continues past the largest finite value, so the midpoint between
that value and the next grid value is a tie, and so are ties in binades above the finite range.
-/
def dyadicIsGridTie (fmt : FloatFormat) (value : Numerics.Dyadic) : Bool :=
  match value.exponent -
      max fmt.minSubnormalExponent
        ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth) with
  | .ofNat _ => false
  | .negSucc shift => Numerics.shiftRightIsTie value.significand (shift + 1)

/-- Zero is never a grid tie. -/
@[simp] theorem dyadicIsGridTie_zero (fmt : FloatFormat) (sign : Bool) (exponent : Int) :
    dyadicIsGridTie fmt { negative := sign, significand := 0, exponent := exponent } = false := by
  unfold dyadicIsGridTie
  split <;> simp [Numerics.shiftRightIsTie]

/--
Round an exact dyadic to nearest with ties away from zero, IEEE 754-2019 `roundTiesToAway`.

Off a grid tie the nearer neighbour is unique and this is nearest-even rounding, `roundDyadic`. At
a tie both neighbours are equally near and the magnitude rounds up, as `roundDyadicAway`
computes. So overflow and underflow behave as in nearest-even rounding, with two exceptions. A
tie at the overflow midpoint overflows whatever the parity of the largest finite significand, and
the midpoint between zero and the least subnormal rounds to that subnormal.
-/
def roundDyadicNearestAway (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if dyadicIsGridTie fmt value then roundDyadicAway fmt value else roundDyadic fmt value

namespace Internal.Directed

/--
Round an exact dyadic in the direction `mode`, the rounding step of every directed kernel.
Nearest-even is `Model.roundDyadic`.
-/
@[inline] def roundDyadic (fmt : FloatFormat) (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) : Model fmt :=
  match mode with
  | .nearest => Model.roundDyadic fmt value
  | .nearestAway => roundDyadicNearestAway fmt value
  | .towardZero => roundDyadicTowardZero fmt value
  | .up => roundDyadicUp fmt value
  | .down => roundDyadicDown fmt value
  | .away => roundDyadicAway fmt value

end Internal.Directed

/-! ## Sticky folding of low bits

Every directed rounder reads a magnitude only down to the bit below its guard bit, so a sticky
quotient that keeps `fracWidth + 2` bits below the leading one rounds like the magnitude. Compiled
directed addition and FMA use this to round `addDyadicForRounding` instead of the exact sum.
-/

/-- Below the normal range a sticky quotient by `2 ^ discard` lands on the same subnormal shift. -/
private theorem subnormalShift_of_shiftRightJam (fmt : FloatFormat) (magnitude : Nat)
    (exponent : Int) (discard : Nat) (hleading : discard + fmt.fracWidth + 2 ≤ magnitude.log2)
    (hsub : Int.ofNat magnitude.log2 + exponent < fmt.minNormalExponent) :
    ∃ n : Nat, 1 ≤ n ∧ exponent + discard - fmt.minSubnormalExponent = Int.negSucc n ∧
      exponent - fmt.minSubnormalExponent = Int.negSucc (n + discard) := by
  have hbelow : exponent + discard - fmt.minSubnormalExponent ≤ -3 := by
    simp only [FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast] at hsub ⊢
    omega
  refine ⟨(fmt.minSubnormalExponent - exponent - discard).toNat - 1, by omega, ?_, ?_⟩ <;>
    rw [Int.negSucc_eq] <;> push_cast <;> omega

/-- Downward magnitude rounding of a sticky quotient that keeps `fracWidth + 2` bits. -/
theorem roundDyadicMagnitudeDown_shiftRightJam (fmt : FloatFormat) (sign : Bool)
    (magnitude : Nat) (exponent : Int) (discard : Nat)
    (hleading : discard + fmt.fracWidth + 2 ≤ magnitude.log2) :
    roundDyadicMagnitudeDown fmt sign (Numerics.shiftRightJam magnitude discard)
        (exponent + discard) =
      roundDyadicMagnitudeDown fmt sign magnitude exponent := by
  have hlog := Numerics.log2_shiftRightJam magnitude discard
  have htotal : Int.ofNat (magnitude.log2 - discard) + (exponent + discard) =
      Int.ofNat magnitude.log2 + exponent := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hnormal : Nat.shiftRight (Numerics.shiftRightJam magnitude discard)
      (magnitude.log2 - discard - fmt.fracWidth) =
        Nat.shiftRight magnitude (magnitude.log2 - fmt.fracWidth) := by
    have := Numerics.roundShiftRight_shiftRightJam .down magnitude discard
      (magnitude.log2 - fmt.fracWidth) (by omega)
    rwa [show magnitude.log2 - fmt.fracWidth - discard =
      magnitude.log2 - discard - fmt.fracWidth by omega] at this
  unfold roundDyadicMagnitudeDown
  simp only [hlog, htotal, ge_iff_le, show fmt.fracWidth ≤ magnitude.log2 - discard by omega,
    show fmt.fracWidth ≤ magnitude.log2 by omega, ite_true, hnormal]
  by_cases hover : Int.ofNat magnitude.log2 + exponent > fmt.maxNormalExponent
  · simp only [hover, ite_true]
  simp only [hover, ite_false]
  by_cases htiny : Int.ofNat magnitude.log2 + exponent < fmt.minSubnormalExponent
  · simp only [htiny, ite_true]
  simp only [htiny, ite_false]
  by_cases hsub : Int.ofNat magnitude.log2 + exponent < fmt.minNormalExponent
  · obtain ⟨n, hn, hjam, hexact⟩ :=
      subnormalShift_of_shiftRightJam fmt magnitude exponent discard hleading hsub
    have hshift := Numerics.roundShiftRight_shiftRightJam .down magnitude discard
      (n + discard + 1) (by omega)
    rw [show n + discard + 1 - discard = n + 1 by omega] at hshift
    simp only [hsub, ite_true, hjam, hexact]
    simp only [Numerics.roundShiftRight_down] at hshift
    rw [hshift]
  · simp only [hsub, ite_false]

/-- Upward magnitude rounding of a sticky quotient that keeps `fracWidth + 2` bits. -/
theorem roundDyadicMagnitudeUp_shiftRightJam (fmt : FloatFormat) (sign : Bool)
    (magnitude : Nat) (exponent : Int) (discard : Nat)
    (hleading : discard + fmt.fracWidth + 2 ≤ magnitude.log2) :
    roundDyadicMagnitudeUp fmt sign (Numerics.shiftRightJam magnitude discard)
        (exponent + discard) =
      roundDyadicMagnitudeUp fmt sign magnitude exponent := by
  have hlog := Numerics.log2_shiftRightJam magnitude discard
  have htotal : Int.ofNat (magnitude.log2 - discard) + (exponent + discard) =
      Int.ofNat magnitude.log2 + exponent := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hnormal : Numerics.shiftRightCeil (Numerics.shiftRightJam magnitude discard)
      (magnitude.log2 - discard - fmt.fracWidth) =
        Numerics.shiftRightCeil magnitude (magnitude.log2 - fmt.fracWidth) := by
    have := Numerics.roundShiftRight_shiftRightJam .up magnitude discard
      (magnitude.log2 - fmt.fracWidth) (by omega)
    rwa [show magnitude.log2 - fmt.fracWidth - discard =
      magnitude.log2 - discard - fmt.fracWidth by omega] at this
  unfold roundDyadicMagnitudeUp
  simp only [hlog, htotal, ge_iff_le, show fmt.fracWidth ≤ magnitude.log2 - discard by omega,
    show fmt.fracWidth ≤ magnitude.log2 by omega, ite_true, hnormal]
  by_cases hover : Int.ofNat magnitude.log2 + exponent > fmt.maxNormalExponent
  · simp only [hover, ite_true]
  simp only [hover, ite_false]
  by_cases htiny : Int.ofNat magnitude.log2 + exponent < fmt.minSubnormalExponent
  · simp only [htiny, ite_true]
  simp only [htiny, ite_false]
  by_cases hsub : Int.ofNat magnitude.log2 + exponent < fmt.minNormalExponent
  · obtain ⟨n, hn, hjam, hexact⟩ :=
      subnormalShift_of_shiftRightJam fmt magnitude exponent discard hleading hsub
    have hshift := Numerics.roundShiftRight_shiftRightJam .up magnitude discard
      (n + discard + 1) (by omega)
    rw [show n + discard + 1 - discard = n + 1 by omega] at hshift
    simp only [hsub, ite_true, hjam, hexact]
    simp only [Numerics.roundShiftRight_up] at hshift
    rw [hshift]
  · simp only [hsub, ite_false]

/-- A sticky quotient that keeps `fracWidth + 2` bits is a grid tie exactly when the magnitude is. -/
theorem dyadicIsGridTie_shiftRightJam (fmt : FloatFormat) (sign : Bool) (magnitude : Nat)
    (exponent : Int) (discard : Nat) (hleading : discard + fmt.fracWidth + 2 ≤ magnitude.log2) :
    dyadicIsGridTie fmt
        { negative := sign
          significand := Numerics.shiftRightJam magnitude discard
          exponent := exponent + discard } =
      dyadicIsGridTie fmt { negative := sign, significand := magnitude, exponent } := by
  have hlog := Numerics.log2_shiftRightJam magnitude discard
  unfold dyadicIsGridTie
  simp only [hlog]
  have hspacing : max fmt.minSubnormalExponent
      (((magnitude.log2 - discard : Nat) : Int) + (exponent + discard) - fmt.fracWidth) =
        max fmt.minSubnormalExponent ((magnitude.log2 : Int) + exponent - fmt.fracWidth) := by
    congr 1
    omega
  rw [hspacing]
  generalize hspacingDef :
    max fmt.minSubnormalExponent ((magnitude.log2 : Int) + exponent - fmt.fracWidth) = spacing
  have hle : (magnitude.log2 : Int) + exponent - fmt.fracWidth ≤ spacing := by
    rw [← hspacingDef]
    exact le_max_right _ _
  obtain ⟨n, hjam, hexact⟩ : ∃ n : Nat, exponent + discard - spacing = Int.negSucc n ∧
      exponent - spacing = Int.negSucc (n + discard) :=
    ⟨(spacing - exponent - discard).toNat - 1, by rw [Int.negSucc_eq]; omega,
      by rw [Int.negSucc_eq]; push_cast; omega⟩
  have hn : 1 ≤ n := by
    rw [Int.negSucc_eq] at hjam
    omega
  rw [hjam, hexact]
  dsimp only
  rw [← Numerics.shiftRightIsTie_shiftRightJam magnitude discard (n + discard + 1) (by omega),
    show n + discard + 1 - discard = n + 1 by omega]

namespace Internal.Directed

/--
Directed rounding in every IEEE direction cannot tell a sticky quotient that keeps
`fracWidth + 2` bits from the magnitude it folds.
-/
theorem roundDyadic_shiftRightJam (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (magnitude : Nat) (exponent : Int) (discard : Nat)
    (hleading : discard + fmt.fracWidth + 2 ≤ magnitude.log2) :
    Internal.Directed.roundDyadic fmt mode
        { negative := sign
          significand := Numerics.shiftRightJam magnitude discard
          exponent := exponent + discard } =
      Internal.Directed.roundDyadic fmt mode
        { negative := sign, significand := magnitude, exponent } := by
  have hpos : magnitude ≠ 0 := by
    rintro rfl
    simp at hleading
  have hjam : Numerics.shiftRightJam magnitude discard ≠ 0 :=
    Numerics.shiftRightJam_ne_zero magnitude discard
      ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.log2_self_le hpos))
  cases mode <;>
    simp only [Internal.Directed.roundDyadic, roundDyadicNearestAway, roundDyadicTowardZero,
      roundDyadicUp, roundDyadicDown, roundDyadicAway, beq_iff_eq, hpos, hjam, ite_false,
      Model.roundDyadic_shiftRightJam fmt sign magnitude exponent discard hleading,
      dyadicIsGridTie_shiftRightJam fmt sign magnitude exponent discard hleading,
      roundDyadicMagnitudeDown_shiftRightJam fmt _ magnitude exponent discard hleading,
      roundDyadicMagnitudeUp_shiftRightJam fmt _ magnitude exponent discard hleading]

/-- Directed rounding cannot tell `addDyadicForRounding (fmt.fracWidth + 3)` from the exact sum. -/
theorem roundDyadic_addDyadicForRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (a b : Numerics.Dyadic) :
    Internal.Directed.roundDyadic fmt mode (addDyadicForRounding (fmt.fracWidth + 3) a b) =
      Internal.Directed.roundDyadic fmt mode (Model.addDyadic a b) := by
  rcases addDyadicForRounding_eq (fmt.fracWidth + 3) a b with h | ⟨discard, -, hlog, h⟩
  · rw [h]
  · rw [h, roundDyadic_shiftRightJam _ _ _ _ _ _ (by omega)]

end Internal.Directed

end Model
end FloatLib.Floats.Formats.BinaryInterchange
