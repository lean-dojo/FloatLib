/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Invalid flags for adjacency and extrema

`nextUp`, `nextDown`, `minimum`, `maximum`, `minimumNumber` and `maximumNumber` deliver a value
without a status. With `status := true` they add the `invalid` indicator that IEEE 754-2019
requires for a signaling NaN operand (§5.3.1 for the adjacent-value operations, §6.2 and §9.6 for
the selections). We prove that the value is unchanged, that `invalid` is raised if and only if an
operand is signaling, and that no other indicator is set.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- An outcome built by `outcomeWithInvalid` raises `invalid` for its condition and nothing else. -/
private theorem outcomeWithInvalid_status {fmt : FloatFormat} (value : Model fmt)
    (invalid : Bool) :
    (outcomeWithInvalid value invalid).status = { invalid := invalid } := by
  cases invalid <;> simp [outcomeWithInvalid, Numerics.IEEEStatus.clear]

/-- `nextUp` with `status := true` delivers the value of `nextUp`. -/
@[simp] theorem value_nextUp {fmt : FloatFormat} (x : Model fmt) :
    (nextUp x (status := true)).value = nextUp x :=
  rfl

/-- `nextUp` raises `invalid` just when its input is a signaling NaN. -/
@[simp] theorem nextUp_invalid {fmt : FloatFormat} (x : Model fmt) :
    (nextUp x (status := true)).status.invalid = isSNaN x := by
  simp [nextUp, outcomeWithInvalid_status]

/-- `nextUp` raises no indicator other than `invalid`. -/
theorem nextUp_status_eq {fmt : FloatFormat} (x : Model fmt) :
    (nextUp x (status := true)).status = { invalid := isSNaN x } := by
  simp [nextUp, outcomeWithInvalid_status]

/-- `nextDown` with `status := true` delivers the value of `nextDown`. -/
@[simp] theorem value_nextDown {fmt : FloatFormat} (x : Model fmt) :
    (nextDown x (status := true)).value = nextDown x :=
  rfl

/-- `nextDown` raises `invalid` just when its input is a signaling NaN. -/
@[simp] theorem nextDown_invalid {fmt : FloatFormat} (x : Model fmt) :
    (nextDown x (status := true)).status.invalid = isSNaN x := by
  simp [nextDown, outcomeWithInvalid_status]

/-- `nextDown` raises no indicator other than `invalid`. -/
theorem nextDown_status_eq {fmt : FloatFormat} (x : Model fmt) :
    (nextDown x (status := true)).status = { invalid := isSNaN x } := by
  simp [nextDown, outcomeWithInvalid_status]

/-- `minimum` with `status := true` delivers the value of `minimum`. -/
@[simp] theorem value_minimum {fmt : FloatFormat} (x y : Model fmt) :
    (minimum x y (status := true)).value = minimum x y :=
  rfl

/-- `minimum` raises `invalid` just when an operand is a signaling NaN. -/
@[simp] theorem minimum_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (minimum x y (status := true)).status.invalid = (isSNaN x || isSNaN y) := by
  simp [minimum, outcomeWithInvalid_status]

/-- `minimum` raises no indicator other than `invalid`. -/
theorem minimum_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (minimum x y (status := true)).status = { invalid := isSNaN x || isSNaN y } := by
  simp [minimum, outcomeWithInvalid_status]

/-- `maximum` with `status := true` delivers the value of `maximum`. -/
@[simp] theorem value_maximum {fmt : FloatFormat} (x y : Model fmt) :
    (maximum x y (status := true)).value = maximum x y :=
  rfl

/-- `maximum` raises `invalid` just when an operand is a signaling NaN. -/
@[simp] theorem maximum_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (maximum x y (status := true)).status.invalid = (isSNaN x || isSNaN y) := by
  simp [maximum, outcomeWithInvalid_status]

/-- `maximum` raises no indicator other than `invalid`. -/
theorem maximum_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (maximum x y (status := true)).status = { invalid := isSNaN x || isSNaN y } := by
  simp [maximum, outcomeWithInvalid_status]

/-- `minimumNumber` with `status := true` delivers the value of `minimumNumber`. -/
@[simp] theorem value_minimumNumber {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumber x y (status := true)).value = minimumNumber x y :=
  rfl

/-- `minimumNumber` raises `invalid` just when an operand is a signaling NaN. -/
@[simp] theorem minimumNumber_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumber x y (status := true)).status.invalid = (isSNaN x || isSNaN y) := by
  simp [minimumNumber, outcomeWithInvalid_status]

/-- `minimumNumber` raises no indicator other than `invalid`. -/
theorem minimumNumber_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (minimumNumber x y (status := true)).status = { invalid := isSNaN x || isSNaN y } := by
  simp [minimumNumber, outcomeWithInvalid_status]

/-- `maximumNumber` with `status := true` delivers the value of `maximumNumber`. -/
@[simp] theorem value_maximumNumber {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumber x y (status := true)).value = maximumNumber x y :=
  rfl

/-- `maximumNumber` raises `invalid` just when an operand is a signaling NaN. -/
@[simp] theorem maximumNumber_invalid {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumber x y (status := true)).status.invalid = (isSNaN x || isSNaN y) := by
  simp [maximumNumber, outcomeWithInvalid_status]

/-- `maximumNumber` raises no indicator other than `invalid`. -/
theorem maximumNumber_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    (maximumNumber x y (status := true)).status = { invalid := isSNaN x || isSNaN y } := by
  simp [maximumNumber, outcomeWithInvalid_status]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
