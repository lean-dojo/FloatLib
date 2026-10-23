/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Invalid flags for adjacency and number-preferring extrema

`nextUp`, `nextDown`, `minimumNumber`, and `maximumNumber` deliver a value without a status. With
`status := true` they add the `invalid` indicator required for a signaling NaN operand by IEEE
754-2019 (§5.3.1 for the adjacent-value operations, §9.6 for the number-preferring selections).
This module proves that the value is unchanged, that `invalid` is raised exactly for a signaling
operand, and that no other indicator is set.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- `nextUp` with `status := true` delivers the value of `nextUp`. -/
@[simp] theorem value_nextUp {fmt : FloatFormat} (x : Model fmt) :
    (nextUp x (status := true)).value = nextUp x :=
  rfl

/-- `nextUp` raises `invalid` exactly for a signaling NaN input. -/
@[simp] theorem nextUp_invalid {fmt : FloatFormat} (x : Model fmt) :
    (nextUp x (status := true)).status.invalid = isSNaN x := by
  cases h : isSNaN x <;> simp [nextUp, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `nextUp` raises no indicator other than `invalid`. -/
theorem nextUp_status_eq {fmt : FloatFormat} (x : Model fmt) :
    (nextUp x (status := true)).status = { invalid := isSNaN x } := by
  cases h : isSNaN x <;> simp [nextUp, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `nextDown` with `status := true` delivers the value of `nextDown`. -/
@[simp] theorem value_nextDown {fmt : FloatFormat} (x : Model fmt) :
    (nextDown x (status := true)).value = nextDown x :=
  rfl

/-- `nextDown` raises `invalid` exactly for a signaling NaN input. -/
@[simp] theorem nextDown_invalid {fmt : FloatFormat} (x : Model fmt) :
    (nextDown x (status := true)).status.invalid = isSNaN x := by
  cases h : isSNaN x <;> simp [nextDown, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `nextDown` raises no indicator other than `invalid`. -/
theorem nextDown_status_eq {fmt : FloatFormat} (x : Model fmt) :
    (nextDown x (status := true)).status = { invalid := isSNaN x } := by
  cases h : isSNaN x <;> simp [nextDown, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `minimumNumber` with `status := true` delivers the value of `minimumNumber`. -/
@[simp] theorem value_minimumNumber {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumber x y (status := true)).value = minimumNumber x y :=
  rfl

/-- `minimumNumber` raises `invalid` exactly when an operand is a signaling NaN. -/
@[simp] theorem minimumNumber_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumber x y (status := true)).status.invalid = (isSNaN x || isSNaN y) := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [minimumNumber, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `minimumNumber` raises no indicator other than `invalid`. -/
theorem minimumNumber_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumber x y (status := true)).status = { invalid := isSNaN x || isSNaN y } := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [minimumNumber, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `maximumNumber` with `status := true` delivers the value of `maximumNumber`. -/
@[simp] theorem value_maximumNumber {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumber x y (status := true)).value = maximumNumber x y :=
  rfl

/-- `maximumNumber` raises `invalid` exactly when an operand is a signaling NaN. -/
@[simp] theorem maximumNumber_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumber x y (status := true)).status.invalid = (isSNaN x || isSNaN y) := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [maximumNumber, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

/-- `maximumNumber` raises no indicator other than `invalid`. -/
theorem maximumNumber_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumber x y (status := true)).status = { invalid := isSNaN x || isSNaN y } := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [maximumNumber, outcomeWithInvalid, h, Numerics.IEEEStatus.clear]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
