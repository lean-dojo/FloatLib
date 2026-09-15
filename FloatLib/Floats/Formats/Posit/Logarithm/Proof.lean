/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Logarithm.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Proof
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Correct rounding of base-two and base-ten posit logarithms

The inverse relation between logarithm and exponentiation transfers every exact boundary
comparison to the rational-power kernel. The resulting theorem includes rational logarithms,
irrational logarithms, exact ties, signed saturation, and invalid argument domains.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Logarithm

/-- Inverse power comparisons have exactly the real-logarithm ordering. -/
theorem compareTarget_eq_real (base argument candidate : Rat) (degree : Nat)
    (hbase : 1 < base) (hargument : 0 < argument) :
    compareTarget base argument candidate degree =
      cmp (Real.logb (base : ℝ) (argument : ℝ)) (candidate : ℝ) := by
  have hbaseReal : (1 : ℝ) < base := by exact_mod_cast hbase
  have hargumentReal : (0 : ℝ) < argument := by exact_mod_cast hargument
  rw [compareTarget, FloatLib.Numerics.RationalPower.compareWithEnclosure_eq_real
    base candidate argument degree (by linarith), cmp_swap]
  simp only [cmp, cmpUsing,
    Real.logb_lt_iff_lt_rpow hbaseReal hargumentReal,
    Real.lt_logb_iff_rpow_lt hbaseReal hargumentReal]

/-- A positive rational argument is rounded according to its exact signed real logarithm. -/
theorem roundRat_eq_real (format : Format) (base argument : Rat)
    (hbase : 1 < base) (hargument : 0 < argument) :
    roundRat format base argument =
      RealRounding.round format (Real.logb (base : ℝ) (argument : ℝ)) := by
  rw [roundRat, if_neg (not_le_of_gt hargument)]
  exact ComparisonRounding.roundSigned_eq_real format _ _
    (fun candidate => compareTarget_eq_real base argument candidate _ hbase hargument)

/-- Nonpositive logarithm arguments are rejected before real logarithm evaluation. -/
theorem roundRat_eq_nar (format : Format) (base argument : Rat) (hargument : argument ≤ 0) :
    roundRat format base argument = nar format := by
  simp [roundRat, hargument]

/-- NaR propagates through every logarithm and exact-offset logarithm. -/
@[simp] theorem apply_nar {format : Format} (base offset : Rat) :
    apply base offset (nar format) = nar format := by
  simp [apply]

/-- Exact offset formation and logarithm evaluation are fused into one final rounding. -/
theorem apply_eq_real {format : Format} (base offset : Rat) (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hbase : 1 < base) (hargument : 0 < q + offset) :
    apply base offset value =
      RealRounding.round format (Real.logb (base : ℝ) ((q : ℝ) + (offset : ℝ))) := by
  simp only [apply, hvalue]
  simpa only [Rat.cast_add] using roundRat_eq_real format base (q + offset) hbase hargument

/-- An invalid exact-offset argument yields NaR. -/
theorem apply_eq_nar {format : Format} (base offset : Rat) (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hargument : q + offset ≤ 0) :
    apply base offset value = nar format := by
  simp only [apply, hvalue]
  exact roundRat_eq_nar format base (q + offset) hargument

end Logarithm

variable {format : Format}

/-- Base-two logarithm has the signed real rounding required by the Posit Standard. -/
theorem log2_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : 0 < q) :
    log2 value = RealRounding.round format (Real.logb 2 (q : ℝ)) := by
  simpa [log2] using
    Logarithm.apply_eq_real 2 0 value hvalue (by norm_num) (by simpa using hq)

/-- Base-ten logarithm has the signed real rounding required by the Posit Standard. -/
theorem log10_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : 0 < q) :
    log10 value = RealRounding.round format (Real.logb 10 (q : ℝ)) := by
  simpa [log10] using
    Logarithm.apply_eq_real 10 0 value hvalue (by norm_num) (by simpa using hq)

/-- The base-two `Plus1` operation rounds the exact logarithm of `1 + x` once. -/
theorem log2Plus1_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : -1 < q) :
    log2Plus1 value = RealRounding.round format (Real.logb 2 (1 + (q : ℝ))) := by
  simpa [log2Plus1, add_comm] using
    Logarithm.apply_eq_real 2 1 value hvalue (by norm_num) (by linarith)

/-- The base-ten `Plus1` operation rounds the exact logarithm of `1 + x` once. -/
theorem log10Plus1_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : -1 < q) :
    log10Plus1 value = RealRounding.round format (Real.logb 10 (1 + (q : ℝ))) := by
  simpa [log10Plus1, add_comm] using
    Logarithm.apply_eq_real 10 1 value hvalue (by norm_num) (by linarith)

/-- Base-two logarithm propagates NaR. -/
@[simp] theorem log2_nar : log2 (nar format) = nar format := Logarithm.apply_nar _ _
/-- Base-ten logarithm propagates NaR. -/
@[simp] theorem log10_nar : log10 (nar format) = nar format := Logarithm.apply_nar _ _
/-- Base-two `Plus1` propagates NaR. -/
@[simp] theorem log2Plus1_nar : log2Plus1 (nar format) = nar format := Logarithm.apply_nar _ _
/-- Base-ten `Plus1` propagates NaR. -/
@[simp] theorem log10Plus1_nar : log10Plus1 (nar format) = nar format := Logarithm.apply_nar _ _

/-- Base-two logarithm rejects zero and negative finite inputs. -/
theorem log2_eq_nar_of_nonpos (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ 0) : log2 value = nar format :=
  Logarithm.apply_eq_nar 2 0 value hvalue (by simpa using hq)

/-- Base-ten logarithm rejects zero and negative finite inputs. -/
theorem log10_eq_nar_of_nonpos (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ 0) : log10 value = nar format :=
  Logarithm.apply_eq_nar 10 0 value hvalue (by simpa using hq)

/-- Base-two `Plus1` rejects finite inputs at or below `-1`. -/
theorem log2Plus1_eq_nar_of_le_neg_one (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ -1) : log2Plus1 value = nar format :=
  Logarithm.apply_eq_nar 2 1 value hvalue (by linarith)

/-- Base-ten `Plus1` rejects finite inputs at or below `-1`. -/
theorem log10Plus1_eq_nar_of_le_neg_one (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ -1) : log10Plus1 value = nar format :=
  Logarithm.apply_eq_nar 10 1 value hvalue (by linarith)

end FloatLib.Floats.Formats.Posit.Model
