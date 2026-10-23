/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Executable binary comparisons

Comparison first handles NaNs and signed infinities, then compares finite values through their
exact dyadic denotations. This gives every `FloatFormat` one numerical order without assuming a
particular storage width or relying on host floating-point comparison.

NaNs are unordered. The minimum and maximum operations apply their NaN-selection and
signed-zero rules around the same comparator. Both the deprecated IEEE 754-2008 `minNum`/`maxNum`
and the IEEE 754-2019 `minimumNumber`/`maximumNumber` operations are provided, and they differ
only in how a signaling NaN operand is treated.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Numerical ordering once both operands are known not to be NaNs.

Infinity is ordered by sign. Every remaining bit pattern is finite, so comparison uses the exact
dyadics extracted from those classification proofs.
-/
def compareNonNaN {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) : Ordering :=
  if hxInf : isInf x then
    if isInf y then
      if signBit x == signBit y then .eq
      else if signBit x then .lt else .gt
    else
      if signBit x then .lt else .gt
  else if hyInf : isInf y then
    if signBit y then .gt else .lt
  else
    let hxFinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hxNaN
        (Bool.eq_false_of_not_eq_true hxInf)
    let hyFinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hyNaN
        (Bool.eq_false_of_not_eq_true hyInf)
    cmpDyadic (finiteDyadic x hxFinite) (finiteDyadic y hyFinite)

/--
IEEE numerical comparison: `none` if either operand is a NaN (unordered), otherwise the ordering.

Infinities are ordered first by sign, and finite values are compared through `cmpDyadic`.
-/
def compare {fmt : FloatFormat} (x y : Model fmt) : Option Ordering :=
  if hnan : isNaN x || isNaN y then
    none
  else
    let hnotNaN :=
      Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hnan)
    some (compareNonNaN x y hnotNaN.1 hnotNaN.2)

/-- Strict IEEE order, `compare x y = some .lt`. It fails when either operand is a NaN. -/
def lt {fmt : FloatFormat} (x y : Model fmt) : Prop :=
  compare x y = some .lt

/-- Weak IEEE order, `compare x y` is `some .lt` or `some .eq`. It fails for a NaN operand. -/
def le {fmt : FloatFormat} (x y : Model fmt) : Prop :=
  match compare x y with
  | some .lt => True
  | some .eq => True
  | _ => False

/-- `le` is decided by the executable comparison. -/
instance {fmt : FloatFormat} (x y : Model fmt) : Decidable (le x y) :=
  match h : compare x y with
  | some .lt => isTrue (by simp [le, h])
  | some .eq => isTrue (by simp [le, h])
  | some .gt => isFalse (by simp [le, h])
  | none => isFalse (by simp [le, h])

/-- IEEE `minimum`, with NaNs selected by `chooseNaN2` and `minimum(-0,+0) = -0`. -/
def minimum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN2 x y) fun hnan =>
    let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
    match compareNonNaN x y hnotNaN.1 hnotNaN.2 with
    | .lt => x
    | .gt => y
    | .eq =>
        if isZero x && isZero y then
          zero fmt (signBit x || signBit y)
        else
          x

/-- IEEE `maximum`, with NaNs selected by `chooseNaN2` and `maximum(-0,+0) = +0`. -/
def maximum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN2 x y) fun hnan =>
    let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
    match compareNonNaN x y hnotNaN.1 hnotNaN.2 with
    | .lt => y
    | .gt => x
    | .eq =>
        if isZero x && isZero y then
          zero fmt (signBit x && signBit y)
        else
          x

/--
IEEE 754-2008 `minNum`, deprecated by IEEE 754-2019 in favor of `minimumNumber`.

A signaling NaN takes priority and propagates as a quiet NaN. Otherwise, a lone quiet NaN is
ignored, two quiet NaNs select the left operand after quieting, and two numbers use `minimum`,
including its `minNum(-0, +0) = -0` rule.
-/
def minNum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isSNaN x then quietNaN x
  else if isSNaN y then quietNaN y
  else if isNaN x then
    if isNaN y then quietNaN x else y
  else if isNaN y then
    x
  else
    minimum x y

/--
IEEE 754-2008 `maxNum`, deprecated by IEEE 754-2019 in favor of `maximumNumber`.

A signaling NaN takes priority and propagates as a quiet NaN. Otherwise, a lone quiet NaN is
ignored, two quiet NaNs select the left operand after quieting, and two numbers use `maximum`,
including its `maxNum(-0, +0) = +0` rule.
-/
def maxNum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isSNaN x then quietNaN x
  else if isSNaN y then quietNaN y
  else if isNaN x then
    if isNaN y then quietNaN x else y
  else if isNaN y then
    x
  else
    maximum x y

/--
Quiet NaN delivered when both operands of `minimumNumber` or `maximumNumber` are NaNs.

The signaling operand is preferred, then the left operand, matching `chooseNaN2`.
-/
@[inline] def bothNaNNumber {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if !isSNaN x && isSNaN y then quietNaN y else quietNaN x

namespace Internal.Value

/--
IEEE 754-2019 §9.6 `minimumNumber`, the kernel of `Model.minimumNumber x y`.

If exactly one operand is a NaN, quiet or signaling, the other operand is returned, so a signaling
NaN is not propagated. When both operands are NaNs the result is a quiet NaN chosen by
`bothNaNNumber`. On two numbers this is `minimum`, so `minimumNumber(-0, +0) = -0`. The invalid
signal owed to a signaling operand is reported by `Model.minimumNumber x y (status := true)` in
`Operations.Runtime`, since the value alone carries no status.
-/
def minimumNumber {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isNaN x then
    if isNaN y then bothNaNNumber x y else y
  else if isNaN y then
    x
  else
    minimum x y

/--
IEEE 754-2019 §9.6 `maximumNumber`, the kernel of `Model.maximumNumber x y`.

If exactly one operand is a NaN, quiet or signaling, the other operand is returned, so a signaling
NaN is not propagated. When both operands are NaNs the result is a quiet NaN chosen by
`bothNaNNumber`. On two numbers this is `maximum`, so `maximumNumber(-0, +0) = +0`. The invalid
signal owed to a signaling operand is reported by `Model.maximumNumber x y (status := true)` in
`Operations.Runtime`.
-/
def maximumNumber {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isNaN x then
    if isNaN y then bothNaNNumber x y else y
  else if isNaN y then
    x
  else
    maximum x y

end Internal.Value

end Model

end FloatLib.Floats.Formats.BinaryInterchange
