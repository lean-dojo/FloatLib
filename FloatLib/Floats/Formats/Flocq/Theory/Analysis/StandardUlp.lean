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

The generic theorem that ULPs are representable asks that the format not flush the selected ULP to
zero. FIX, positive-precision FLX, and positive-precision FLT all qualify, and the witnesses here
make the theorem available for each of these standard families.
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
