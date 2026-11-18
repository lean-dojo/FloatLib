/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Formats

/-!
# ULP Conditions for Standard Formats

The generic theorem that ULPs are representable asks that the format not flush the selected ULP to
zero. FIX, positive-precision FLX, and positive-precision FLT all qualify, and the witnesses here
make the theorem available for each of these standard families.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Fixed-point exponent selection preserves ULP representability. -/
theorem expNotFlushToZero_fix (emin : ℤ) : ExpNotFlushToZero (fixExp emin) where
  ulp_exponent := by simp [fixExp]

/-- Positive-precision unbounded floats preserve ULP representability. -/
theorem expNotFlushToZero_flx (prec : ℤ) (hprec : 0 < prec) :
    ExpNotFlushToZero (flxExp prec) where
  ulp_exponent := by
    intro e
    simp only [flxExp, tsub_le_iff_right, sub_add_cancel, Order.add_one_le_iff, sub_lt_self_iff]
    linarith

/-- Positive-precision lower-bounded floats preserve ULP representability. -/
theorem expNotFlushToZero_flt (emin prec : ℤ) (hprec : 0 < prec) :
    ExpNotFlushToZero (fltExp emin prec) where
  ulp_exponent := by
    intro e
    simp only [fltExp]
    apply max_le
    · linarith
    · exact le_max_right _ _

end FloatLib.Floats.Formats.Flocq
