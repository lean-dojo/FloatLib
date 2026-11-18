/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.Block.Binary
public import FloatLib.Numerics.Quantization.Block.Coded

/-!
# Codecs of the general scalar formats

The executable scalar formats that every block format can use for its elements and its scales:

* `Codec.ofFormat fmt` stores a rational in any binary descriptor with nearest-even rounding and
  the descriptor's own overflow policy: an FP8 overflow is its NaN or infinity word, and a fully
  finite encoding (E2M1, E2M3, E3M2) saturates. `Codec.ofFormat fmt (saturate := true)` clips to
  the finite range first, which is the SAT conversion of OCP MX for FP8 and the clamp NVFP4
  implementations apply to E4M3 scales.
* `Codec.int` stores a rational as the nearest integer, ties to even, with no bound.
* `Codec.exponent` stores a positive rational as the exponent of the largest power of two not
  above it, with no bound.

The codecs of the OCP element formats and of E8M0 are in `OCP.MX.Standard`.

`ofFormat_round_eq_grid`: for an IEEE descriptor and a rational inside its finite range, the
codec stores the real nearest-even grid rounding `Rounding.grid fmt`.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.3 and 6.3; NVIDIA, Pretraining
Large Language Models with NVFP4 (2025), Appendix B.1–B.3.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

namespace Codec

/-- Exact value of a binary word: its dyadic value with the sign of zero, or its infinity or NaN
class. -/
def decodeModel {fmt : FloatFormat} (word : Model fmt) : NumericalValue SignedRat :=
  ((Model.exactNumericalSystem fmt).denote word).map SignedRat.ofDyadic

/-- A signed zero word has rational value zero. -/
theorem finiteValue_decodeModel_zero (fmt : FloatFormat) (sign : Bool) :
    finiteValue (decodeModel (Model.zero fmt sign)) = 0 := by
  simp [decodeModel, Model.exactNumericalSystem, Model.toDyadic?_zero, finiteValue]

/-- Largest finite value of a descriptor, as a rational. -/
def maxFinite (fmt : FloatFormat) : ℚ :=
  (Model.toRat? (Model.posMaxFinite fmt)).getD 0

/-- Clip a signed rational to magnitude at most `bound`. A value inside the bound, and its sign of
zero, is unchanged. -/
def clip (bound : ℚ) (s : SignedRat) : SignedRat :=
  if bound < |s.value| then SignedRat.ofRat (if s.value < 0 then -bound else bound) else s

/-- Nearest-even rounding of a signed rational into a binary descriptor. -/
def roundModel (fmt : FloatFormat) (s : SignedRat) : Model fmt :=
  Model.roundRat fmt s.negative s.value.num.natAbs s.value.den

private theorem value_roundModel (fmt : FloatFormat) (s : SignedRat) :
    finiteValue (decodeModel (roundModel fmt s)) =
      finiteValue (decodeModel (roundModel fmt (SignedRat.ofRat s.value))) := by
  by_cases h : s.value = 0
  · simp only [roundModel, h, SignedRat.value_ofRat, Rat.num_zero, Int.natAbs_zero,
      Model.roundRat_num_zero _ _ _ (Nat.ne_of_gt (Rat.den_pos _)), finiteValue_decodeModel_zero]
  · rw [SignedRat.ofRat_value_of_ne_zero h]

/--
A binary descriptor as a codec, with nearest-even rounding. With `saturate` the input is clipped
to the finite range first. Without it the descriptor's own overflow policy applies.
-/
@[reducible] def ofFormat (fmt : FloatFormat) (saturate : Bool := false) : Codec where
  Code := Model fmt
  decode := decodeModel
  encode s := roundModel fmt (if saturate then clip (maxFinite fmt) s else s)
  value_encode s := by
    cases saturate
    · exact value_roundModel fmt s
    · change finiteValue (decodeModel (roundModel fmt (clip (maxFinite fmt) s))) =
        finiteValue (decodeModel (roundModel fmt
          (clip (maxFinite fmt) (SignedRat.ofRat s.value))))
      by_cases h : s.value = 0
      · by_cases hM : maxFinite fmt < 0
        · have h1 : clip (maxFinite fmt) s = SignedRat.ofRat (maxFinite fmt) := by
            simp [clip, h, hM]
          have h2 : clip (maxFinite fmt) (SignedRat.ofRat s.value) =
              SignedRat.ofRat (maxFinite fmt) := by
            simp [clip, h, hM]
          rw [h1, h2]
        · have h1 : clip (maxFinite fmt) s = s := by simp [clip, h, hM]
          have h2 : clip (maxFinite fmt) (SignedRat.ofRat s.value) =
              SignedRat.ofRat s.value := by
            simp [clip, h, hM]
          rw [h1, h2]
          exact value_roundModel fmt s
      · rw [SignedRat.ofRat_value_of_ne_zero h]

/-- The rational value of a binary word is its real value. A word with no finite value has the
value zero on both sides. -/
theorem cast_finiteValue_decodeModel {fmt : FloatFormat} (word : Model fmt) :
    ((finiteValue (decodeModel word) : ℚ) : ℝ) = Model.toReal word := by
  rw [← Model.cast_toRat_eq_toReal]
  congr 1
  simp only [decodeModel, Model.exactNumericalSystem, Model.toRat?]
  cases h : Model.toDyadic? word with
  | some d => simp [finiteValue]
  | none =>
    by_cases hinf : Model.isInfinite word <;> simp [finiteValue, hinf]

/--
The codec of an IEEE descriptor is the real nearest-even grid rounding on the rationals inside
the descriptor's finite range. Outside it the stored word is an infinity, which has no value.
-/
theorem ofFormat_round_eq_grid (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (q : ℚ)
    (hq : |(q : ℝ)| ≤ Model.toReal (Model.posMaxFinite fmt)) :
    (((ofFormat fmt).rounding.round q : ℚ) : ℝ) = (Rounding.grid fmt).round (q : ℝ) := by
  have hsign : decide (q < 0) = decide (q.num < 0) := decide_eq_decide.mpr Rat.num_neg.symm
  have hword : roundModel fmt (SignedRat.ofRat q) = Model.ofRat fmt q := by
    change Model.roundRat fmt (decide (q < 0)) q.num.natAbs q.den =
      Model.roundRat fmt (decide (q.num < 0)) q.num.natAbs q.den
    rw [hsign]
  change ((finiteValue (decodeModel (roundModel fmt (SignedRat.ofRat q))) : ℚ) : ℝ) =
    Model.roundAt fmt (q : ℝ)
  rw [hword, cast_finiteValue_decodeModel,
    Model.toReal_ofRat_eq_roundAt q hfmt (Model.isFinite_ofRat q hfmt hq)]

/-- Unbounded integers: a rational is stored as the nearest integer, ties to even. -/
@[reducible] def int : Codec where
  Code := Int
  decode n := .finite (SignedRat.ofRat n)
  encode s := roundRatEven s.value
  value_encode _ := rfl

/-- Unbounded powers of two stored as exponents: a positive rational is stored as the exponent of
the largest power of two not above it. -/
@[reducible] def exponent : Codec where
  Code := Int
  decode e := .finite (SignedRat.ofRat ((2 : ℚ) ^ e))
  encode s := Int.log 2 s.value
  value_encode _ := rfl

/-- The integer codec rounds to the nearest integer, ties to even. -/
@[simp] theorem int_rounding_round (q : ℚ) : int.rounding.round q = (roundRatEven q : ℚ) := by
  simp [rounding, value, finiteValue]

/-- The exponent codec rounds a rational down to a power of two. -/
@[simp] theorem exponent_rounding_round (q : ℚ) :
    exponent.rounding.round q = (2 : ℚ) ^ Int.log 2 q := by
  simp [rounding, value, finiteValue]

end Codec

end FloatLib.Floats.Formats.Block
