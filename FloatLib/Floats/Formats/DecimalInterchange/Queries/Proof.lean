/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Sign.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity

/-!
# Numerical classification, cohorts and stored canonicality

Zero, normal, and subnormal classification agrees with exact rational magnitudes and is
preserved within a cohort. For a fixed encoding and format, canonical words are equal exactly
when they decode to the same complete datum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem Format.minNormal_pos (f : Format) : 0 < f.minNormal := by
  unfold Format.minNormal
  positivity

namespace Datum

theorem finiteValue_abs (s : Bool) (c : Nat) (q : Int) :
    |finiteValue s c q| = (c : ℚ) * (10 : ℚ) ^ q := by
  have h : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q := by positivity
  cases s <;>
    simp only [finiteValue, Bool.false_eq_true, ↓reduceIte, one_mul,
      neg_mul, abs_neg, abs_of_nonneg h]

theorem finiteValue_eq_zero_iff (s : Bool) (c : Nat) (q : Int) :
    finiteValue s c q = 0 ↔ c = 0 := by
  have hp : (10 : ℚ) ^ q ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
  cases s <;> simp [finiteValue, hp]

/-- The zero predicate agrees with exact rational semantics, at every quantum. -/
theorem isZero_iff (d : Datum) : d.isZero = true ↔ d.toRat? = some 0 := by
  cases d with
  | finite s c q =>
      simp only [toRat?_eq]
      change (c == 0) = true ↔ some (finiteValue s c q) = some 0
      simp only [beq_iff_eq, Option.some.injEq, finiteValue_eq_zero_iff]
  | infinity s => simp [isZero, toRat?]
  | nan s t p => simp [isZero, toRat?]

/-- Normality is a numerical threshold test, independent of sign and cohort. -/
theorem isNormal_iff (f : Format) (d : Datum) :
    d.isNormal f = true ↔ ∃ x : ℚ, d.toRat? = some x ∧ f.minNormal ≤ |x| := by
  cases d with
  | finite s c q =>
      simp only [toRat?_eq]
      change decide (f.minNormal ≤ (c : ℚ) * (10 : ℚ) ^ q) = true ↔
        ∃ x : ℚ, some (finiteValue s c q) = some x ∧ f.minNormal ≤ |x|
      simp only [Option.some.injEq, exists_eq_left', finiteValue_abs, decide_eq_true_eq]
  | infinity s => simp [isNormal, toRat?]
  | nan s t p => simp [isNormal, toRat?]

theorem isSubnormal_iff (f : Format) (d : Datum) :
    d.isSubnormal f = true ↔
      ∃ x : ℚ, d.toRat? = some x ∧ x ≠ 0 ∧ |x| < f.minNormal := by
  cases d with
  | finite s c q =>
      simp only [toRat?_eq]
      change decide (c ≠ 0 ∧ (c : ℚ) * (10 : ℚ) ^ q < f.minNormal) = true ↔
        ∃ x : ℚ, some (finiteValue s c q) = some x ∧ x ≠ 0 ∧ |x| < f.minNormal
      simp only [Option.some.injEq, exists_eq_left', finiteValue_abs, decide_eq_true_eq,
        ne_eq, finiteValue_eq_zero_iff]
  | infinity s => simp [isSubnormal, toRat?]
  | nan s t p => simp [isSubnormal, toRat?]

theorem sameCohort_isNormal (f : Format) {x y : Datum} (h : x.SameCohort y) :
    x.isNormal f = y.isNormal f := by
  cases x <;> cases y <;> simp only [SameCohort] at h
  · simp only [isNormal, h.2]
  · rfl

theorem sameCohort_isSubnormal (f : Format) {x y : Datum} (h : x.SameCohort y) :
    x.isSubnormal f = y.isSubnormal f := by
  cases x <;> cases y <;> simp only [SameCohort] at h
  · rename_i s c q t d r
    have hz : c = 0 ↔ d = 0 := by
      have hc : (c : ℚ) * (10 : ℚ) ^ q = 0 ↔ c = 0 := by
        simpa only [finiteValue, Bool.false_eq_true, ↓reduceIte, one_mul] using
          finiteValue_eq_zero_iff false c q
      have hd : (d : ℚ) * (10 : ℚ) ^ r = 0 ↔ d = 0 := by
        simpa only [finiteValue, Bool.false_eq_true, ↓reduceIte, one_mul] using
          finiteValue_eq_zero_iff false d r
      rw [← hc, ← hd, h.2]
    simp only [isSubnormal, h.2, ne_eq, hz]
  · rfl

/-- The finite classes exhaust zero, normal and subnormal values. -/
theorem finite_classification (f : Format) (s : Bool) (c : Nat) (q : Int) :
    let d := Datum.finite s c q
    (d.isZero || d.isNormal f || d.isSubnormal f) = true := by
  dsimp [isZero, isNormal, isSubnormal]
  by_cases hc : c = 0 <;>
    by_cases hm : f.minNormal ≤ (c : ℚ) * (10 : ℚ) ^ q <;>
      simp [hc, hm, lt_of_not_ge]

theorem classify_zero_iff (f : Format) (d : Datum) :
    (d.classify f = .negativeZero ∨ d.classify f = .positiveZero) ↔ d.isZero = true := by
  cases d with
  | finite s c q =>
      cases s <;> by_cases hc : c = 0 <;>
        by_cases hm : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;>
          simp [classify, isZero, hc, hm]
  | infinity s => cases s <;> simp [classify, isZero]
  | nan s t p => cases t <;> simp [classify, isZero]

theorem classify_normal_iff (f : Format) (d : Datum) :
    (d.classify f = .negativeNormal ∨ d.classify f = .positiveNormal) ↔
      d.isNormal f = true := by
  cases d with
  | finite s c q =>
      have hp := f.minNormal_pos
      cases s <;> by_cases hc : c = 0 <;>
        by_cases hm : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;>
          simp_all [classify, isNormal, not_le]
  | infinity s => cases s <;> simp [classify, isNormal]
  | nan s t p => cases t <;> simp [classify, isNormal]

theorem classify_subnormal_iff (f : Format) (d : Datum) :
    (d.classify f = .negativeSubnormal ∨ d.classify f = .positiveSubnormal) ↔
      d.isSubnormal f = true := by
  cases d with
  | finite s c q =>
      cases s <;> by_cases hc : c = 0 <;>
        by_cases hm : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;>
          simp [classify, isSubnormal, hc, hm]
  | infinity s => cases s <;> simp [classify, isSubnormal]
  | nan s t p => cases t <;> simp [classify, isSubnormal]

theorem classify_signalingNaN_iff (f : Format) (d : Datum) :
    d.classify f = .signalingNaN ↔ d.isSignaling = true := by
  cases d with
  | finite s c q =>
      cases s <;> by_cases hc : c = 0 <;>
        by_cases hm : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;>
          simp [classify, isSignaling, hc, hm]
  | infinity s => cases s <;> simp [classify, isSignaling]
  | nan s t p => cases t <;> simp [classify, isSignaling]

theorem classify_infinite_iff (f : Format) (d : Datum) :
    (d.classify f = .negativeInfinity ∨ d.classify f = .positiveInfinity) ↔
      d.isInfinite = true := by
  cases d with
  | finite s c q =>
      cases s <;> by_cases hc : c = 0 <;>
        by_cases hm : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;>
          simp [classify, isInfinite, hc, hm]
  | infinity s => cases s <;> simp [classify, isInfinite]
  | nan s t p => cases t <;> simp [classify, isInfinite]

theorem classify_nan_iff (f : Format) (d : Datum) :
    (d.classify f = .signalingNaN ∨ d.classify f = .quietNaN) ↔ d.isNaN = true := by
  cases d with
  | finite s c q =>
      cases s <;> by_cases hc : c = 0 <;>
        by_cases hm : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;>
          simp [classify, isNaN, hc, hm]
  | infinity s => cases s <;> simp [classify, isNaN]
  | nan s t p => cases t <;> simp [classify, isNaN]

@[simp] theorem sameQuantum_self (x : Datum) : x.sameQuantum x = true := by
  cases x <;> simp [sameQuantum]

theorem sameQuantum_comm (x y : Datum) : x.sameQuantum y = y.sameQuantum x := by
  cases x <;> cases y <;> simp [sameQuantum, eq_comm]

theorem sameQuantum_trans {x y z : Datum}
    (hxy : x.sameQuantum y = true) (hyz : y.sameQuantum z = true) :
    x.sameQuantum z = true := by
  cases x <;> cases y <;> cases z <;> simp_all [sameQuantum]

end Datum

namespace Encoding

/-- Re-encoding always produces a canonical word, including on redundant input. -/
@[simp] theorem isCanonical_canonicalize (encoding : Encoding) (f : Format)
    (w : BitVec f.bitWidth) :
    encoding.isCanonical f (encoding.canonicalize f w) = true := by
  simp [isCanonical, canonicalize_idempotent]

/-- Two canonical encodings in the same encoding and format are equal precisely
when they decode to the same complete datum. -/
theorem eq_iff_decode_eq (encoding : Encoding) (f : Format)
    {x y : BitVec f.bitWidth} (hx : encoding.isCanonical f x = true)
    (hy : encoding.isCanonical f y = true) :
    x = y ↔ encoding.decode f x = encoding.decode f y := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have hx' : encoding.canonicalize f x = x := of_decide_eq_true hx
    have hy' : encoding.canonicalize f y = y := of_decide_eq_true hy
    rw [← hx', ← hy']
    exact congrArg (encoding.codec.encode f) h

end Encoding
end FloatLib.Floats.Formats.DecimalInterchange
