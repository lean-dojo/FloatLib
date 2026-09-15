/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime

/-!
# Format-generic executable floating-point intervals

Closed executable intervals have `Model fmt` endpoints, an endpoint order, and
format-independent constructors. Outward-rounded arithmetic and activation ranges live in later
modules.

The executable layer is separate from soundness theorems so applications can choose an exact
real, extended-real, or format-model interpretation without changing the interval representation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- A closed executable interval with both endpoints in `fmt`. -/
structure Interval (fmt : FloatFormat) where
  /-- Lower endpoint. -/
  lo : Model fmt
  /-- Upper endpoint. -/
  hi : Model fmt
  deriving DecidableEq, Repr

namespace Interval

/-- Membership using the numerical order of `Model`; NaNs are unordered. -/
def mem {fmt : FloatFormat} (I : Interval fmt) (x : Model fmt) : Prop :=
  Model.le I.lo x ∧ Model.le x I.hi

/-- Enable `x ∈ I` for format-generic executable intervals. -/
instance {fmt : FloatFormat} : Membership (Model fmt) (Interval fmt) where
  mem I x := Interval.mem I x

/-- Unfold membership into lower- and upper-endpoint comparisons. -/
@[simp] theorem mem_iff {fmt : FloatFormat} (I : Interval fmt) (x : Model fmt) :
    x ∈ I ↔ Model.le I.lo x ∧ Model.le x I.hi :=
  Iff.rfl

/--
An interval is valid when both endpoints are finite and ordered.

For formats with infinity, `whole` is intentionally not valid under this finite-endpoint
predicate. For finite formats, `whole` uses the two maximal finite endpoints and is valid.
-/
def Valid {fmt : FloatFormat} (I : Interval fmt) : Prop :=
  Model.isFinite I.lo = true ∧
    Model.isFinite I.hi = true ∧
    Model.le I.lo I.hi

/--
An interval is extended-valid when both endpoints are non-NaN and are ordered.

Unlike `Valid`, this predicate permits infinite endpoints. It is the closure invariant for
outward-rounded IEEE operations: a finite input interval may produce an infinite endpoint on
overflow without ceasing to denote an ordered interval.
-/
def ValidExtended {fmt : FloatFormat} (I : Interval fmt) : Prop :=
  Model.isNaN I.lo = false ∧
    Model.isNaN I.hi = false ∧
    Model.le I.lo I.hi

/-- Degenerate interval `[x, x]`. -/
@[inline] def point {fmt : FloatFormat} (x : Model fmt) : Interval fmt :=
  ⟨x, x⟩

/-- Smallest endpoint hull containing both input intervals, with IEEE NaN propagation. -/
@[inline] def hull {fmt : FloatFormat} (A B : Interval fmt) : Interval fmt :=
  { lo := Model.minimum A.lo B.lo
    hi := Model.maximum A.hi B.hi }

/-- Minimum of four values, grouped to match the interval corner operations. -/
@[inline] def minOfFour {fmt : FloatFormat} (a b c d : Model fmt) : Model fmt :=
  Model.minimum (Model.minimum a b) (Model.minimum c d)

/-- Maximum of four values, grouped to match the interval corner operations. -/
@[inline] def maxOfFour {fmt : FloatFormat} (a b c d : Model fmt) : Model fmt :=
  Model.maximum (Model.maximum a b) (Model.maximum c d)

/--
Conservative interval spanning the complete numerical range of `fmt`.

Formats with infinity use `[-∞, +∞]`; formats without infinity use their two maximal finite
endpoints.
-/
@[inline] def whole (fmt : FloatFormat) : Interval fmt :=
  ⟨Model.infinityOrMaxFinite fmt true,
    Model.infinityOrMaxFinite fmt false⟩

/-- Executable `x ≤ y`; unordered comparisons return `false`. -/
@[inline] def leB {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  match Model.compare x y with
  | some .lt | some .eq => true
  | some .gt | none => false

/--
Build an enclosure from ordered, non-NaN endpoints, or use the whole range.

The candidate pair is kept only when `leB lo hi` holds. It is replaced by `whole fmt` when either
endpoint is a NaN (so the comparison is unordered) and also when `lo > hi` numerically, which can
happen when a caller supplies reversed bounds. An indeterminate expression such as `0 * ∞`
can instead produce NaN endpoints. Indeterminate endpoint
calculations cannot justify a narrower bound; for formats with infinity the fallback encloses
every real number and permits interval arithmetic to compose.
-/
@[inline] def ofBounds {fmt : FloatFormat} (lo hi : Model fmt) : Interval fmt :=
  if leB lo hi then ⟨lo, hi⟩ else whole fmt

/-- Whether the represented endpoint range contains numerical zero. -/
@[inline] def containsZero {fmt : FloatFormat} (I : Interval fmt) : Bool :=
  leB I.lo (Model.zero fmt false) && leB (Model.zero fmt true) I.hi

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
