/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Core

/-!
# Semantic membership for arbitrary-format executable intervals

`RealMem` interprets a finite-endpoint interval as a closed interval in `ℝ`. `ERealMem`
interprets its endpoints in `EReal`, so outward-rounded operations remain meaningful when a result
overflows to an infinity. Meaningful endpoint interpretations require `Valid` or `ValidExtended`;
the totalized decoders alone do not exclude NaN endpoints.

The executable interval carrier remains independent of these interpretations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

noncomputable section

/-- Membership in the real interval denoted by the decoded endpoints. -/
def RealMem {fmt : FloatFormat} (I : Interval fmt) (x : ℝ) : Prop :=
  toReal I.lo ≤ x ∧ x ≤ toReal I.hi

/-- Membership in the extended-real interval denoted by the decoded endpoints. -/
def ERealMem {fmt : FloatFormat} (I : Interval fmt) (x : EReal) : Prop :=
  toEReal I.lo ≤ x ∧ x ≤ toEReal I.hi

/-- Real membership unfolds to the two endpoint inequalities. -/
@[simp] theorem realMem_iff {fmt : FloatFormat} (I : Interval fmt) (x : ℝ) :
    RealMem I x ↔ toReal I.lo ≤ x ∧ x ≤ toReal I.hi :=
  Iff.rfl

/-- Extended-real membership unfolds to the two endpoint inequalities. -/
@[simp] theorem eRealMem_iff {fmt : FloatFormat} (I : Interval fmt) (x : EReal) :
    ERealMem I x ↔ toEReal I.lo ≤ x ∧ x ≤ toEReal I.hi :=
  Iff.rfl

/-- The lower endpoint of a valid interval is finite. -/
theorem Valid.lo_isFinite {fmt : FloatFormat} {I : Interval fmt} (hI : Valid I) :
    isFinite I.lo = true :=
  hI.1

/-- The upper endpoint of a valid interval is finite. -/
theorem Valid.hi_isFinite {fmt : FloatFormat} {I : Interval fmt} (hI : Valid I) :
    isFinite I.hi = true :=
  hI.2.1

/-- The endpoints of a valid interval are ordered by executable comparison. -/
theorem Valid.ordered {fmt : FloatFormat} {I : Interval fmt} (hI : Valid I) :
    Model.le I.lo I.hi :=
  hI.2.2

/-- The lower endpoint of an extended-valid interval is not a NaN. -/
theorem ValidExtended.lo_isNaN_eq_false
    {fmt : FloatFormat} {I : Interval fmt} (hI : ValidExtended I) :
    isNaN I.lo = false :=
  hI.1

/-- The upper endpoint of an extended-valid interval is not a NaN. -/
theorem ValidExtended.hi_isNaN_eq_false
    {fmt : FloatFormat} {I : Interval fmt} (hI : ValidExtended I) :
    isNaN I.hi = false :=
  hI.2.1

/-- The endpoints of an extended-valid interval are ordered numerically. -/
theorem ValidExtended.ordered
    {fmt : FloatFormat} {I : Interval fmt} (hI : ValidExtended I) :
    Model.le I.lo I.hi :=
  hI.2.2

/-- Every finite valid interval is extended-valid. -/
theorem Valid.validExtended
    {fmt : FloatFormat} {I : Interval fmt} (hI : Valid I) :
    ValidExtended I := by
  exact
    ⟨isNaN_eq_false_of_isFinite_eq_true I.lo hI.lo_isFinite,
      isNaN_eq_false_of_isFinite_eq_true I.hi hI.hi_isFinite,
      hI.ordered⟩

/-- An extended-valid interval is finite-valid once both endpoints are known to be finite. -/
theorem ValidExtended.valid_of_isFinite
    {fmt : FloatFormat} {I : Interval fmt} (hI : ValidExtended I)
    (hlo : isFinite I.lo = true) (hhi : isFinite I.hi = true) :
    Valid I :=
  ⟨hlo, hhi, hI.ordered⟩

/--
For a valid interval, embedding real membership into `EReal` preserves membership exactly.
-/
theorem eRealMem_coe_iff_of_valid
    {fmt : FloatFormat} {I : Interval fmt} (hI : Valid I) (x : ℝ) :
    ERealMem I (x : EReal) ↔ RealMem I x := by
  simp only [ERealMem, RealMem,
    toEReal_eq_coe_toReal_of_isFinite I.lo hI.lo_isFinite,
    toEReal_eq_coe_toReal_of_isFinite I.hi hI.hi_isFinite,
    EReal.coe_le_coe_iff]

end

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
