/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Finite

/-!
# Configured interval enclosures for finite-only encodings

Finite-only formats saturate on overflow. Unlike an IEEE interval with infinite endpoints,
their whole range cannot enclose every real number. These theorems transport the existing
model results with explicit range hypotheses on the exact endpoint calculations.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary.Interval

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Bounds" => Interval (format := format) (plan := plan) (code := code)

section

/-- Finite-only addition encloses a sum when the exact endpoint sums fit in the format. -/
theorem add_sound_of_encoding_finite (I J : Bounds) (hformat : format.encoding = .finite)
    (hloRange : |Model.toReal (Binary.toModel I.lo) + Model.toReal (Binary.toModel J.lo)| ≤
      Model.toReal (Model.posMaxFinite format))
    (hhiRange : |Model.toReal (Binary.toModel I.hi) + Model.toReal (Binary.toModel J.hi)| ≤
      Model.toReal (Model.posMaxFinite format))
    {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) : RealMem (add I J) (x + y) := by
  simpa [RealMem] using
    Model.Interval.add_sound_of_encoding_finite I.toModel J.toModel hformat hloRange hhiRange hx hy

/-- Finite-only subtraction encloses a difference when its endpoint differences fit in range. -/
theorem sub_sound_of_encoding_finite (I J : Bounds) (hformat : format.encoding = .finite)
    (hloRange : |Model.toReal (Binary.toModel I.lo) - Model.toReal (Binary.toModel J.hi)| ≤
      Model.toReal (Model.posMaxFinite format))
    (hhiRange : |Model.toReal (Binary.toModel I.hi) - Model.toReal (Binary.toModel J.lo)| ≤
      Model.toReal (Model.posMaxFinite format))
    {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) : RealMem (sub I J) (x - y) := by
  simpa [RealMem] using
    Model.Interval.sub_sound_of_encoding_finite I.toModel J.toModel hformat hloRange hhiRange hx hy

/-- Finite-only multiplication encloses a product when all four exact corner products fit. -/
theorem mul_sound_of_encoding_finite (I J : Bounds) (hformat : format.encoding = .finite)
    (h00 : |Model.toReal (Binary.toModel I.lo) * Model.toReal (Binary.toModel J.lo)| ≤
      Model.toReal (Model.posMaxFinite format))
    (h01 : |Model.toReal (Binary.toModel I.lo) * Model.toReal (Binary.toModel J.hi)| ≤
      Model.toReal (Model.posMaxFinite format))
    (h10 : |Model.toReal (Binary.toModel I.hi) * Model.toReal (Binary.toModel J.lo)| ≤
      Model.toReal (Model.posMaxFinite format))
    (h11 : |Model.toReal (Binary.toModel I.hi) * Model.toReal (Binary.toModel J.hi)| ≤
      Model.toReal (Model.posMaxFinite format))
    {x y : ℝ} (hx : RealMem I x) (hy : RealMem J y) : RealMem (mul I J) (x * y) := by
  simpa [RealMem] using
    Model.Interval.mul_sound_of_encoding_finite I.toModel J.toModel hformat h00 h01 h10 h11 hx hy

end
end FloatLib.Floats.ExecFloat.Binary.Interval
