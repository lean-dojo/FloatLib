/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Invalid flags for adjacency and number-preferring extrema

`nextUp`, `nextDown`, `minimumNumber`, and `maximumNumber` deliver a value without a status. Their
`*WithStatus` forms add the `invalid` indicator required for a signaling NaN operand by IEEE 754-2019
(§5.3.1 for the adjacent-value operations, §9.6 for the number-preferring selections). This module
proves that the value is unchanged and that `invalid` is raised exactly for a signaling operand;
no other indicator is ever set.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- The status form of `nextUp` delivers exactly `nextUp`. -/
@[simp] theorem nextUpWithStatus_value {fmt : FloatFormat} (x : Model fmt) :
    (nextUpWithStatus x).value = nextUp x :=
  rfl

/-- `nextUpWithStatus` raises `invalid` exactly for a signaling NaN input. -/
@[simp] theorem nextUpWithStatus_invalid {fmt : FloatFormat} (x : Model fmt) :
    (nextUpWithStatus x).status.invalid = isSNaN x := by
  cases h : isSNaN x <;> simp [nextUpWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- `nextUpWithStatus` raises no indicator other than `invalid`. -/
theorem nextUpWithStatus_status_eq {fmt : FloatFormat} (x : Model fmt) :
    (nextUpWithStatus x).status = { invalid := isSNaN x } := by
  cases h : isSNaN x <;> simp [nextUpWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- The status form of `nextDown` delivers exactly `nextDown`. -/
@[simp] theorem nextDownWithStatus_value {fmt : FloatFormat} (x : Model fmt) :
    (nextDownWithStatus x).value = nextDown x :=
  rfl

/-- `nextDownWithStatus` raises `invalid` exactly for a signaling NaN input. -/
@[simp] theorem nextDownWithStatus_invalid {fmt : FloatFormat} (x : Model fmt) :
    (nextDownWithStatus x).status.invalid = isSNaN x := by
  cases h : isSNaN x <;> simp [nextDownWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- `nextDownWithStatus` raises no indicator other than `invalid`. -/
theorem nextDownWithStatus_status_eq {fmt : FloatFormat} (x : Model fmt) :
    (nextDownWithStatus x).status = { invalid := isSNaN x } := by
  cases h : isSNaN x <;> simp [nextDownWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- The status form of `minimumNumber` delivers exactly `minimumNumber`. -/
@[simp] theorem minimumNumberWithStatus_value {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumberWithStatus x y).value = minimumNumber x y :=
  rfl

/-- `minimumNumberWithStatus` raises `invalid` exactly when an operand is a signaling NaN. -/
@[simp] theorem minimumNumberWithStatus_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumberWithStatus x y).status.invalid = (isSNaN x || isSNaN y) := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [minimumNumberWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- `minimumNumberWithStatus` raises no indicator other than `invalid`. -/
theorem minimumNumberWithStatus_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumberWithStatus x y).status = { invalid := isSNaN x || isSNaN y } := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [minimumNumberWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- The status form of `maximumNumber` delivers exactly `maximumNumber`. -/
@[simp] theorem maximumNumberWithStatus_value {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumberWithStatus x y).value = maximumNumber x y :=
  rfl

/-- `maximumNumberWithStatus` raises `invalid` exactly when an operand is a signaling NaN. -/
@[simp] theorem maximumNumberWithStatus_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumberWithStatus x y).status.invalid = (isSNaN x || isSNaN y) := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [maximumNumberWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

/-- `maximumNumberWithStatus` raises no indicator other than `invalid`. -/
theorem maximumNumberWithStatus_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumberWithStatus x y).status = { invalid := isSNaN x || isSNaN y } := by
  cases h : (isSNaN x || isSNaN y) <;>
    simp [maximumNumberWithStatus, outcomeWithInvalid, h, IEEEStatus.clear]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
