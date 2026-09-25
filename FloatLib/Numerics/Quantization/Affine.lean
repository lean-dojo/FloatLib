/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public import FloatLib.Numerics.Core.Proof
public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Quantization.Deterministic
public import FloatLib.Numerics.Quantization.Saturating

/-!
# Executable affine rational quantization

For a positive rational scale `s`, zero point `z`, and integer code interval
`[qmin, qmax]`, this module executes nearest-even affine quantization:

```text
quantize x   = clamp (roundEven (x / s) + z)
dequantize k = s * (k - z)
```

Exact rational parameters keep the scalar kernel executable and make its mathematical denotation
independent of host floating-point behavior. Downstream tensor libraries can lift the scalar
operation pointwise without introducing a second quantization semantics.

The reconstruction equation is Jacob et al., "Quantization and Training of Neural Networks for
Efficient Integer-Arithmetic-Only Inference," CVPR 2018, §2.1, Eq. (1), p. 2706,
doi:10.1109/CVPR.2018.00286. The nearest-even tie rule is this kernel's policy; Eq. (1) specifies
the affine reconstruction map. Ties are resolved on `x / s`, before adding the zero point.
This parameter record permits any integer zero point. Exact zero has a code in the stored interval
precisely when `qmin ≤ zeroPoint ≤ qmax`, as required by the paper's code-range convention.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization

/-- Parameters of a bounded nearest-even affine quantizer. -/
structure AffineQuantizer where
  /-- Exact distance between adjacent reconstructed values. -/
  scale : ℚ
  /-- Integer code representing zero when it lies in the code range. -/
  zeroPoint : ℤ
  /-- Smallest stored code. -/
  qmin : ℤ
  /-- Largest stored code. -/
  qmax : ℤ
  /-- A quantization scale is strictly positive. -/
  scale_pos : 0 < scale
  /-- The code interval is nonempty. -/
  codeRange : qmin ≤ qmax

namespace AffineQuantizer

/-- Saturate an integer to the quantizer's code interval, using the shared saturating clamp. -/
@[inline] def clampCode (q : AffineQuantizer) (code : ℤ) : ℤ :=
  Saturating.clamp q.qmin q.qmax code

/-- Integer code before saturation. -/
@[inline] def rawCode (q : AffineQuantizer) (x : ℚ) : ℤ :=
  roundRatEven (x / q.scale) + q.zeroPoint

/-- Quantize an exact rational and saturate the result to the stored code interval. -/
@[inline] def quantize (q : AffineQuantizer) (x : ℚ) : ℤ :=
  q.clampCode (q.rawCode x)

/-- Reconstruct the exact rational denoted by an integer code. -/
@[inline] def dequantize (q : AffineQuantizer) (code : ℤ) : ℚ :=
  q.scale * ((code - q.zeroPoint : ℤ) : ℚ)

/-- Mathematical value produced by executable affine quantization. -/
@[inline] def roundedValue (q : AffineQuantizer) (x : ℚ) : ℚ :=
  q.dequantize (q.quantize x)

/-- Saturation always returns a valid code. -/
theorem clampCode_mem (q : AffineQuantizer) (code : ℤ) :
    q.qmin ≤ q.clampCode code ∧ q.clampCode code ≤ q.qmax :=
  ⟨Saturating.lower_le_clamp _ _ _, Saturating.clamp_le_upper q.codeRange⟩

/-- Saturation fixes a code already inside the representable interval. -/
@[simp, grind =] theorem clampCode_eq_self (q : AffineQuantizer) {code : ℤ}
    (hlo : q.qmin ≤ code) (hhi : code ≤ q.qmax) :
    q.clampCode code = code :=
  Saturating.clamp_eq_self hlo hhi

/-- Every quantized scalar lies in the declared code interval. -/
theorem quantize_mem (q : AffineQuantizer) (x : ℚ) :
    q.qmin ≤ q.quantize x ∧ q.quantize x ≤ q.qmax :=
  q.clampCode_mem _

/-- Dequantizing the zero point gives exact zero. -/
@[simp, grind =] theorem dequantize_zeroPoint (q : AffineQuantizer) :
    q.dequantize q.zeroPoint = 0 := by
  simp [dequantize]

/-- Every in-range integer code survives an executable quantize/dequantize round trip. -/
@[simp, grind =] theorem quantize_dequantize (q : AffineQuantizer) {code : ℤ}
    (hlo : q.qmin ≤ code) (hhi : code ≤ q.qmax) :
    q.quantize (q.dequantize code) = code := by
  have hscale : q.scale ≠ 0 := ne_of_gt q.scale_pos
  have hscaled :
      q.dequantize code / q.scale = ((code - q.zeroPoint : ℤ) : ℚ) := by
    simp [dequantize, hscale]
  rw [quantize, rawCode, hscaled, roundRatEven_intCast]
  simp only [Int.sub_add_cancel]
  exact q.clampCode_eq_self hlo hhi

/-- Before saturation, reconstruction differs from the input by at most half a quantization step. -/
theorem dequantize_rawCode_error_le (q : AffineQuantizer) (x : ℚ) :
    |q.dequantize (q.rawCode x) - x| ≤ q.scale / 2 := by
  have hscale : q.scale ≠ 0 := ne_of_gt q.scale_pos
  have hround := roundRatEven_error_le_half (x / q.scale)
  have hrewrite :
      q.dequantize (q.rawCode x) - x =
        q.scale * ((roundRatEven (x / q.scale) : ℚ) - x / q.scale) := by
    simp only [dequantize, rawCode, Int.cast_sub, Int.cast_add]
    field_simp
    ring
  rw [hrewrite, abs_mul, abs_of_pos q.scale_pos]
  calc
    q.scale * |(roundRatEven (x / q.scale) : ℚ) - x / q.scale| ≤
        q.scale * ((1 : ℚ) / 2) :=
      mul_le_mul_of_nonneg_left hround q.scale_pos.le
    _ = q.scale / 2 := by ring

/-- The half-step bound survives saturation whenever clipping is inactive. -/
theorem dequantize_quantize_error_le (q : AffineQuantizer) (x : ℚ)
    (hlo : q.qmin ≤ q.rawCode x) (hhi : q.rawCode x ≤ q.qmax) :
    |q.roundedValue x - x| ≤ q.scale / 2 := by
  rw [roundedValue, quantize, q.clampCode_eq_self hlo hhi]
  exact q.dequantize_rawCode_error_le x

/-! ## General numerical-system view -/

/--
An integer code in the quantizer's closed storage interval.

Using Mathlib's interval subtype keeps range reasoning interoperable and avoids a project-local
proof-carrying record for the standard `qmin ≤ value ≤ qmax` invariant.
-/
abbrev StoredCode (q : AffineQuantizer) :=
  Set.Icc q.qmin q.qmax

/-- Store the executable quantization result together with its erased range proof. -/
@[inline] def quantizeCode (q : AffineQuantizer) (x : ℚ) : StoredCode q :=
  let bounds := q.quantize_mem x
  ⟨q.quantize x, bounds⟩

/-- Numerical system whose codes denote their exact affine reconstruction. -/
def numericalSystem (q : AffineQuantizer) : NumericalSystem :=
  NumericalSystem.ofFinite
    (fun code : StoredCode q ↦ q.dequantize code.1)

/-- An affine-quantized code with an erased proof of its complete denotation. -/
abbrev At (q : AffineQuantizer) (value : NumericalValue ℚ) :=
  (numericalSystem q).At value

/-- An affine-quantized code with an erased proof of its reconstructed rational value. -/
abbrev AtFinite (q : AffineQuantizer) (value : ℚ) :=
  (numericalSystem q).AtFinite value

/-- Representation in the affine system is equality with exact dequantization. -/
@[simp, grind =] theorem numericalSystem_represents_iff (q : AffineQuantizer) (code : StoredCode q)
    (x : ℚ) :
    (numericalSystem q).Represents code x ↔ q.dequantize code.1 = x := by
  simp [numericalSystem]

/--
Executable quantization is a quantizer onto its own reconstructed value.

Since `roundedValue` is `dequantize` after `quantize`, this is the definitional contract used by
generic `QuantizerOn` automation. The error bound when clipping is inactive is
`dequantize_quantize_error_le`.
-/
theorem quantizeCode_quantizerOn_roundedValue (q : AffineQuantizer) :
    Operation.QuantizerOn (numericalSystem q) q.quantizeCode q.roundedValue
      (fun _ => True) := by
  intro x _
  exact (numericalSystem_represents_iff q _ _).2 rfl

/-- The numerical-system view inherits the inactive-saturation half-step guarantee. -/
theorem numericalSystem_quantize_error_le (q : AffineQuantizer) (x : ℚ)
    (hlo : q.qmin ≤ q.rawCode x) (hhi : q.rawCode x ≤ q.qmax) :
    ∃ reconstructed : ℚ,
      (numericalSystem q).Represents (q.quantizeCode x) reconstructed ∧
      |reconstructed - x| ≤ q.scale / 2 := by
  refine ⟨q.roundedValue x, ?_, q.dequantize_quantize_error_le x hlo hhi⟩
  exact q.quantizeCode_quantizerOn_roundedValue x trivial

end AffineQuantizer

end FloatLib.Numerics.Quantization
