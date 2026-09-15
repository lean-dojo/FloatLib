/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Format.Formats
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-!
# ULP Conditions for Standard Formats

FIX, positive-precision FLX, and positive-precision FLT do not flush the selected ULP to zero.
These witnesses make the generic ULP representability theorem available for each standard family.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Fixed-point exponent selection preserves ULP representability. -/
abbrev fixNotFlushToZero (emin : ℤ) : ExpNotFlushToZero (fixExp emin) where
  ulpExponent := by simp [fixExp]

/-- Positive-precision unbounded floats preserve ULP representability. -/
abbrev flxNotFlushToZero (prec : ℤ) (hprec : 0 < prec) :
    ExpNotFlushToZero (flxExp prec) where
  ulpExponent := by
    intro e
    simp [flxExp]
    linarith

/-- Positive-precision lower-bounded floats preserve ULP representability. -/
abbrev fltNotFlushToZero (emin prec : ℤ) (hprec : 0 < prec) :
    ExpNotFlushToZero (fltExp emin prec) where
  ulpExponent := by
    intro e
    simp only [fltExp]
    apply max_le
    · have hprecOne : 1 ≤ prec := by linarith
      linarith
    · exact le_max_right _ _

end FloatLib.Floats.Formats.Flocq
