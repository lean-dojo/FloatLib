/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Core

/-!
# Extended-real semantics of interval endpoint selection

IEEE `minimum` and `maximum` agree with lattice `min` and `max` on non-NaN values. This module
lifts that contract through the four-corner selectors used by executable interval multiplication
and division.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

noncomputable section

namespace Interval

/-- Extended-real semantics of the four-way minimum on non-NaN inputs. -/
theorem toEReal_minOfFour_eq
    {fmt : FloatFormat} (a b c d : Model fmt)
    (haNaN : isNaN a = false) (hbNaN : isNaN b = false)
    (hcNaN : isNaN c = false) (hdNaN : isNaN d = false) :
    toEReal (minOfFour a b c d) =
      min (min (toEReal a) (toEReal b)) (min (toEReal c) (toEReal d)) := by
  have habNaN :=
    isNaN_minimum_eq_false_of_isNaN_eq_false a b haNaN hbNaN
  have hcdNaN :=
    isNaN_minimum_eq_false_of_isNaN_eq_false c d hcNaN hdNaN
  unfold minOfFour
  rw [toEReal_minimum_eq_min (minimum a b) (minimum c d) habNaN hcdNaN,
    toEReal_minimum_eq_min a b haNaN hbNaN,
    toEReal_minimum_eq_min c d hcNaN hdNaN]

/-- Extended-real semantics of the four-way maximum on non-NaN inputs. -/
theorem toEReal_maxOfFour_eq
    {fmt : FloatFormat} (a b c d : Model fmt)
    (haNaN : isNaN a = false) (hbNaN : isNaN b = false)
    (hcNaN : isNaN c = false) (hdNaN : isNaN d = false) :
    toEReal (maxOfFour a b c d) =
      max (max (toEReal a) (toEReal b)) (max (toEReal c) (toEReal d)) := by
  have habNaN :=
    isNaN_maximum_eq_false_of_isNaN_eq_false a b haNaN hbNaN
  have hcdNaN :=
    isNaN_maximum_eq_false_of_isNaN_eq_false c d hcNaN hdNaN
  unfold maxOfFour
  rw [toEReal_maximum_eq_max (maximum a b) (maximum c d) habNaN hcdNaN,
    toEReal_maximum_eq_max a b haNaN hbNaN,
    toEReal_maximum_eq_max c d hcNaN hdNaN]

/--
Pointwise upper bounds on four non-NaN values bound their executable four-way minimum.
-/
theorem toEReal_minOfFour_le_of_le
    {fmt : FloatFormat} (a b c d : Model fmt)
    (haNaN : isNaN a = false) (hbNaN : isNaN b = false)
    (hcNaN : isNaN c = false) (hdNaN : isNaN d = false)
    {a' b' c' d' : EReal}
    (ha : toEReal a ≤ a') (hb : toEReal b ≤ b')
    (hc : toEReal c ≤ c') (hd : toEReal d ≤ d') :
    toEReal (minOfFour a b c d) ≤ min (min a' b') (min c' d') := by
  rw [toEReal_minOfFour_eq a b c d haNaN hbNaN hcNaN hdNaN]
  exact min_le_min (min_le_min ha hb) (min_le_min hc hd)

/--
Pointwise lower bounds on four non-NaN values bound their executable four-way maximum.
-/
theorem le_toEReal_maxOfFour_of_le
    {fmt : FloatFormat} (a b c d : Model fmt)
    (haNaN : isNaN a = false) (hbNaN : isNaN b = false)
    (hcNaN : isNaN c = false) (hdNaN : isNaN d = false)
    {a' b' c' d' : EReal}
    (ha : a' ≤ toEReal a) (hb : b' ≤ toEReal b)
    (hc : c' ≤ toEReal c) (hd : d' ≤ toEReal d) :
    max (max a' b') (max c' d') ≤ toEReal (maxOfFour a b c d) := by
  rw [toEReal_maxOfFour_eq a b c d haNaN hbNaN hcNaN hdNaN]
  exact max_le_max (max_le_max ha hb) (max_le_max hc hd)

end Interval
end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
