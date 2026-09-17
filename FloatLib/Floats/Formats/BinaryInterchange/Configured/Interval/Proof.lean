/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Configured interval correctness

Packing and decoding are inverse on complete endpoint encodings, including signed zeros and NaNs.
Every configured operation decodes to the existing model operation. Soundness and validity are
transported from `Model.Interval`, retaining its format and finiteness hypotheses.

In particular, arithmetic soundness starts from finite valid intervals and concludes membership
in extended-real bounds: overflow is permitted. Totalized real decoding alone is not a sound
interpretation of infinite or NaN endpoints.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary.Interval

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => FloatLib.Floats.ExecFloat (Configured.Family format code plan)
local notation "Bounds" => Interval (format := format) (plan := plan) (code := code)

/-- Decoding packed bounds preserves every endpoint bit. -/
@[simp] theorem toModel_ofModel (I : Model.Interval format) :
    toModel (ofModel (plan := plan) (code := code) I) = I := by
  cases I
  simp [toModel, ofModel]

/-- Repacking decoded bounds is lossless. -/
@[simp] theorem ofModel_toModel (I : Bounds) : ofModel I.toModel = I := by
  cases I
  simp [toModel, ofModel]

/-- Model equality determines configured interval equality. -/
theorem toModel_injective : Function.Injective (toModel (plan := plan) (code := code)) :=
  Function.LeftInverse.injective ofModel_toModel

/-- Membership agrees with the exact model order. -/
@[simp] theorem mem_iff (I : Bounds) (x : Value) :
    x ∈ I ↔ Binary.toModel x ∈ I.toModel := Iff.rfl

/-- Packing model bounds preserves finite validity. -/
@[simp] theorem valid_ofModel_iff (I : Model.Interval format) :
    Valid (ofModel (plan := plan) (code := code) I) ↔ Model.Interval.Valid I := by
  simp [Valid]

/-- Packing model bounds preserves extended validity. -/
@[simp] theorem validExtended_ofModel_iff (I : Model.Interval format) :
    ValidExtended (ofModel (plan := plan) (code := code) I) ↔ Model.Interval.ValidExtended I := by
  simp [ValidExtended]

/-- Point construction commutes with decoding. -/
@[simp] theorem toModel_point (x : Value) :
    toModel (point x) = Model.Interval.point (Binary.toModel x) := by
  simp [point]

/-- The configured whole range has exactly the model's endpoints. -/
@[simp] theorem toModel_whole :
    toModel (whole (format := format) (plan := plan) (code := code)) =
      Model.Interval.whole format := by
  simp [whole]

/-- Checked construction commutes with decoding. -/
@[simp] theorem toModel_ofBounds (lo hi : Value) :
    toModel (ofBounds lo hi) = Model.Interval.ofBounds (Binary.toModel lo) (Binary.toModel hi) := by
  simp [ofBounds]

/-- Configured hull decodes to the model operation. -/
@[simp] theorem toModel_hull (I J : Bounds) :
    toModel (hull I J) = Model.Interval.hull I.toModel J.toModel := by
  simp [hull]

/-- Configured add decodes to the model operation. -/
@[simp] theorem toModel_add (I J : Bounds) :
    toModel (add I J) = Model.Interval.add I.toModel J.toModel := by
  simp [add]

/-- Configured sub decodes to the model operation. -/
@[simp] theorem toModel_sub (I J : Bounds) :
    toModel (sub I J) = Model.Interval.sub I.toModel J.toModel := by
  simp [sub]

/-- Configured mul decodes to the model operation. -/
@[simp] theorem toModel_mul (I J : Bounds) :
    toModel (mul I J) = Model.Interval.mul I.toModel J.toModel := by
  simp [mul]

/-- Configured div decodes to the model operation. -/
@[simp] theorem toModel_div (I J : Bounds) :
    toModel (div I J) = Model.Interval.div I.toModel J.toModel := by
  simp [div]

/-- Configured neg decodes to the model operation. -/
@[simp] theorem toModel_neg (I : Bounds) :
    toModel (neg I) = Model.Interval.neg I.toModel := by
  simp [neg]

/-- Configured inv decodes to the model operation. -/
@[simp] theorem toModel_inv (I : Bounds) :
    toModel (inv I) = Model.Interval.inv I.toModel := by
  simp [inv]

/-- Configured relu decodes to the model operation. -/
@[simp] theorem toModel_relu (I : Bounds) :
    toModel (relu I) = Model.Interval.relu I.toModel := by
  simp [relu]

/-- Configured abs decodes to the model operation. -/
@[simp] theorem toModel_abs (I : Bounds) :
    toModel (abs I) = Model.Interval.abs I.toModel := by
  simp [abs]

/-- Configured sqrt decodes to the model operation. -/
@[simp] theorem toModel_sqrt (I : Bounds) :
    toModel (sqrt I) = Model.Interval.sqrt I.toModel := by
  simp [sqrt]

noncomputable section

/-- Real membership in decoded bounds; meaningful as an interval interpretation under `Valid`. -/
abbrev RealMem (I : Bounds) (x : ℝ) : Prop := Model.Interval.RealMem I.toModel x

/-- Extended-real membership, permitting infinite endpoints under `ValidExtended`. -/
abbrev ERealMem (I : Bounds) (x : EReal) : Prop := Model.Interval.ERealMem I.toModel x

/-- Finite validity implies extended validity. -/
theorem Valid.validExtended {I : Bounds} (hI : Valid I) : ValidExtended I :=
  Model.Interval.Valid.validExtended hI

/-- Finite endpoint interpretations agree after embedding a real number into `EReal`. -/
theorem eRealMem_coe_iff_of_valid {I : Bounds} (hI : Valid I) (x : ℝ) :
    ERealMem I (x : EReal) ↔ RealMem I x :=
  Model.Interval.eRealMem_coe_iff_of_valid hI x

/-- A finite value gives a valid point interval. -/
theorem valid_point_of_isFinite (x : Value) (hx : Binary.isFinite x = true) :
    Valid (point x) := by
  simpa [Valid] using Model.Interval.valid_point_of_isFinite (Binary.toModel x) hx

/-- A non-NaN value gives an extended-valid point interval, including at infinity. -/
theorem validExtended_point_of_isNaN_eq_false (x : Value) (hx : Binary.isNaN x = false) :
    ValidExtended (point x) := by
  simpa [ValidExtended] using
    Model.Interval.validExtended_point_of_isNaN_eq_false (Binary.toModel x) hx

/-- The full IEEE range is extended-valid. -/
theorem validExtended_whole (hformat : format.isIEEE = true) :
    ValidExtended (whole (format := format) (plan := plan) (code := code)) := by
  simpa [ValidExtended] using Model.Interval.validExtended_whole format hformat

/-- The full IEEE range contains every extended real. -/
theorem eRealMem_whole (hformat : format.isIEEE = true) (x : EReal) :
    ERealMem (whole (format := format) (plan := plan) (code := code)) x := by
  simpa [ERealMem] using Model.Interval.eRealMem_whole format hformat x

/-- Checked IEEE bounds are extended-valid even when the supplied pair is unordered. -/
theorem validExtended_ofBounds (lo hi : Value) (hformat : format.isIEEE = true) :
    ValidExtended (ofBounds lo hi) := by
  simpa [ValidExtended] using
    Model.Interval.validExtended_ofBounds (Binary.toModel lo) (Binary.toModel hi) hformat

/-- Outward-rounded add encloses the exact real result, including overflow. -/
theorem add_sound (I J : Bounds) (hformat : format.isIEEE = true)
    (hI : Valid I) (hJ : Valid J) {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) :
    ERealMem (add I J) ((x + y : ℝ) : EReal) := by
  simpa [ERealMem] using
    Model.Interval.add_sound I.toModel J.toModel hformat hI hJ hx hy

/-- IEEE add returns ordered, non-NaN bounds, even for indeterminate input endpoints. -/
theorem add_validExtended (I J : Bounds) (hformat : format.isIEEE = true) :
    ValidExtended (add I J) := by
  simpa [ValidExtended] using Model.Interval.add_validExtended I.toModel J.toModel hformat

/-- Outward-rounded sub encloses the exact real result, including overflow. -/
theorem sub_sound (I J : Bounds) (hformat : format.isIEEE = true)
    (hI : Valid I) (hJ : Valid J) {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) :
    ERealMem (sub I J) ((x - y : ℝ) : EReal) := by
  simpa [ERealMem] using
    Model.Interval.sub_sound I.toModel J.toModel hformat hI hJ hx hy

/-- IEEE sub returns ordered, non-NaN bounds, even for indeterminate input endpoints. -/
theorem sub_validExtended (I J : Bounds) (hformat : format.isIEEE = true) :
    ValidExtended (sub I J) := by
  simpa [ValidExtended] using Model.Interval.sub_validExtended I.toModel J.toModel hformat

/-- Outward-rounded mul encloses the exact real result, including overflow. -/
theorem mul_sound (I J : Bounds) (hformat : format.isIEEE = true)
    (hI : Valid I) (hJ : Valid J) {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) :
    ERealMem (mul I J) ((x * y : ℝ) : EReal) := by
  simpa [ERealMem] using
    Model.Interval.mul_sound I.toModel J.toModel hformat hI hJ hx hy

/-- IEEE mul returns ordered, non-NaN bounds, even for indeterminate input endpoints. -/
theorem mul_validExtended (I J : Bounds) (hformat : format.isIEEE = true) :
    ValidExtended (mul I J) := by
  simpa [ValidExtended] using Model.Interval.mul_validExtended I.toModel J.toModel hformat

/-- Outward-rounded div encloses the exact real result, including overflow. -/
theorem div_sound (I J : Bounds) (hformat : format.isIEEE = true)
    (hI : Valid I) (hJ : Valid J) {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) :
    ERealMem (div I J) ((x / y : ℝ) : EReal) := by
  simpa [ERealMem] using
    Model.Interval.div_sound I.toModel J.toModel hformat hI hJ hx hy

/-- IEEE div returns ordered, non-NaN bounds, even for indeterminate input endpoints. -/
theorem div_validExtended (I J : Bounds) (hformat : format.isIEEE = true) :
    ValidExtended (div I J) := by
  simpa [ValidExtended] using Model.Interval.div_validExtended I.toModel J.toModel hformat

/-- The neg image encloses every represented real, permitting infinite bounds. -/
theorem neg_sound_extended (I : Bounds) (hI : ValidExtended I)
    {x : ℝ} (hx : ERealMem I (x : EReal)) :
    ERealMem (neg I) ((-x : ℝ) : EReal) := by
  simpa [ERealMem] using Model.Interval.neg_sound_extended I.toModel hI hx

/-- The neg image preserves extended validity in every format. -/
theorem neg_validExtended (I : Bounds) (hI : ValidExtended I) :
    ValidExtended (neg I) := by
  simpa [ValidExtended] using Model.Interval.neg_validExtended I.toModel hI

/-- The relu image encloses every represented real, permitting infinite bounds. -/
theorem relu_sound_extended (I : Bounds) (hI : ValidExtended I)
    {x : ℝ} (hx : ERealMem I (x : EReal)) :
    ERealMem (relu I) ((max x 0 : ℝ) : EReal) := by
  simpa [ERealMem] using Model.Interval.relu_sound_extended I.toModel hI hx

/-- The relu image preserves extended validity in every format. -/
theorem relu_validExtended (I : Bounds) (hI : ValidExtended I) :
    ValidExtended (relu I) := by
  simpa [ValidExtended] using Model.Interval.relu_validExtended I.toModel hI

/-- The abs image encloses every represented real, permitting infinite bounds. -/
theorem abs_sound_extended (I : Bounds) (hI : ValidExtended I)
    {x : ℝ} (hx : ERealMem I (x : EReal)) :
    ERealMem (abs I) ((|x| : ℝ) : EReal) := by
  simpa [ERealMem] using Model.Interval.abs_sound_extended I.toModel hI hx

/-- The abs image preserves extended validity in every format. -/
theorem abs_validExtended (I : Bounds) (hI : ValidExtended I) :
    ValidExtended (abs I) := by
  simpa [ValidExtended] using Model.Interval.abs_validExtended I.toModel hI

/-- Reciprocal soundness includes zero: the whole-range fallback encloses the totalized result. -/
theorem inv_sound (I : Bounds) (hformat : format.isIEEE = true) (hI : Valid I)
    {x : ℝ} (hx : RealMem I x) : ERealMem (inv I) ((1 / x : ℝ) : EReal) := by
  simpa [ERealMem] using Model.Interval.inv_sound I.toModel hformat hI hx

/-- IEEE reciprocal returns extended-valid bounds. -/
theorem inv_validExtended (I : Bounds) (hformat : format.isIEEE = true) :
    ValidExtended (inv I) := by
  simpa [ValidExtended, Model.Interval.inv] using
    Model.Interval.div_validExtended
      (Model.Interval.point (Model.posOne format)) I.toModel hformat

/-- Directed square root encloses the real square root on nonnegative finite input bounds. -/
theorem sqrt_sound (I : Bounds) (hformat : format.isIEEE = true) (hI : Valid I)
    (hnonnegative : 0 ≤ Model.toReal (Binary.toModel I.lo))
    {x : ℝ} (hx : RealMem I x) :
    ERealMem (sqrt I) ((Real.sqrt x : ℝ) : EReal) := by
  simpa [ERealMem] using Model.Interval.sqrt_sound I.toModel hformat hI hnonnegative hx

/-- Directed square root preserves extended validity on nonnegative finite input bounds. -/
theorem sqrt_validExtended (I : Bounds) (hformat : format.isIEEE = true) (hI : Valid I)
    (hnonnegative : 0 ≤ Model.toReal (Binary.toModel I.lo)) :
    ValidExtended (sqrt I) := by
  simpa [ValidExtended] using
    Model.Interval.sqrt_validExtended I.toModel hformat hI hnonnegative

end
end FloatLib.Floats.ExecFloat.Binary.Interval
