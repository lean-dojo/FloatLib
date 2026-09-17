/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core
public import FloatLib.Numerics.Quantization.Affine.Real

/-!
# Executable affine quantization and real rounding

The rational nearest-even kernel and the real nearest-even specification choose exactly the
same integer, including negative inputs and half-way ties. Consequently, executable affine
quantization agrees with real affine quantization before and after saturation, and exact
reconstruction commutes with the rational-to-real embedding.

The rounding-independent API lives in `Numerics.Quantization.Affine.Real`. This module also
specializes its order, round-trip, and error theorems to the existing Flocq rounding contracts.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

open Numerics Numerics.Quantization

/-- Rational nearest-even execution agrees exactly with real nearest-even rounding. -/
theorem nearestEven_ratCast (x : ℚ) : nearestEven (x : ℝ) = roundRatEven x := by
  rw [roundRatEven_eq_floor_ceil]
  by_cases hint : x.floor = x.ceil
  · have hx : x = (x.floor : ℚ) :=
      le_antisymm (by simpa [← hint] using (Rat.le_ceil (x := x))) (Rat.floor_le x)
    rw [ite_eq_left hint]
    rw [hx, Rat.cast_intCast]
    exact ValidRnd.id _
  · rw [ite_eq_right hint]
    have hstep : x.ceil = x.floor + 1 := by
      have hlo : x.floor ≤ x.ceil := by
        exact_mod_cast (Rat.floor_le x).trans (Rat.le_ceil (x := x))
      have hhi : x.ceil ≤ x.floor + 1 :=
        Rat.ceil_le_iff.mpr (Rat.lt_floor_add_one x).le
      omega
    have hbelow : (x : ℝ) - (x.floor : ℝ) < 1 / 2 ↔
        x - (x.floor : ℚ) < (x.ceil : ℚ) - x := by
      rw [hstep]
      have hcast : (x : ℝ) - (x.floor : ℝ) < 1 / 2 ↔
          x - (x.floor : ℚ) < 1 / 2 := by
        simpa using (Rat.cast_lt (K := ℝ) (p := x - (x.floor : ℚ)) (q := 1 / 2))
      rw [hcast]
      push_cast
      constructor <;> intro h <;> linarith
    have habove : (x : ℝ) - (x.floor : ℝ) > 1 / 2 ↔
        (x.ceil : ℚ) - x < x - (x.floor : ℚ) := by
      rw [hstep]
      have hcast : (x : ℝ) - (x.floor : ℝ) > 1 / 2 ↔
          x - (x.floor : ℚ) > 1 / 2 := by
        simpa using (Rat.cast_lt (K := ℝ) (p := 1 / 2) (q := x - (x.floor : ℚ)))
      rw [hcast]
      push_cast
      constructor <;> intro h <;> linarith
    have hfloor : ⌊(x : ℝ)⌋ = x.floor := Rat.floor_cast x
    simp only [nearestEven, hfloor, hbelow, habove, Int.even_iff, hstep]

/-- A Flocq-valid integer rounder gives monotone affine quantization. -/
theorem affine_quantize_monotone (q : RealAffineQuantizer) (rnd : ℝ → ℤ) [ValidRnd rnd] :
    Monotone (q.quantize rnd) :=
  q.quantize_monotone (fun _ _ h ↦ ValidRnd.monotone _ _ h)

/-- Any Flocq-valid rounder preserves in-range stored codes under reconstruction and rounding. -/
theorem affine_quantize_dequantize (q : RealAffineQuantizer) (rnd : ℝ → ℤ) [ValidRnd rnd]
    {code : ℤ} (hlo : q.qmin ≤ code) (hhi : code ≤ q.qmax) :
    q.quantize rnd (q.dequantize code) = code :=
  q.quantize_dequantize (fun n ↦ ValidRnd.id n) hlo hhi

/-- Without saturation, every valid nearest rounder reconstructs within half a grid step. -/
theorem affine_dequantize_quantize_error_le_half (q : RealAffineQuantizer) (rnd : ℝ → ℤ)
    [ValidRndToNearest rnd] (x : ℝ)
    (hlo : q.qmin ≤ q.rawCode rnd x) (hhi : q.rawCode rnd x ≤ q.qmax) :
    |q.roundedValue rnd x - x| ≤ q.scale / 2 := by
  apply q.dequantize_quantize_error_le_half rnd x _ hlo hhi
  simpa only [one_div] using ValidRndToNearest.abs_sub_le_half (rnd := rnd) (x / q.scale)

/-- Saturated rational execution and real nearest-even affine quantization return the same code. -/
theorem affine_toReal_quantize (q : AffineQuantizer) (x : ℚ) :
    q.toReal.quantize nearestEven (x : ℝ) = q.quantize x :=
  q.toReal_quantize nearestEven nearestEven_ratCast x

/-- Exact reconstruction agrees after the complete nearest-even quantization operation. -/
theorem affine_toReal_roundedValue (q : AffineQuantizer) (x : ℚ) :
    q.toReal.roundedValue nearestEven (x : ℝ) = (q.roundedValue x : ℝ) :=
  q.toReal_roundedValue nearestEven nearestEven_ratCast x

end FloatLib.Floats.Formats.Flocq
