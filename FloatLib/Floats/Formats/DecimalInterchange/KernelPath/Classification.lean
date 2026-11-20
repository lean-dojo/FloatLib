/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Runtime

/-!
# Kernel path of the decimal classification

`Datum.isNormal`, `Datum.isSubnormal` and `Datum.classify` (IEEE 754-2019 §5.7.2) compare the
rational magnitude of a finite datum with the least normal magnitude of the format. On the
fields of the datum that comparison is a comparison of digit counts: a nonzero coefficient `c`
at the quantum exponent `q` is below the least normal magnitude exactly when its digits end
below the precision of the least quantum (`tiny_eq`, from `scaled_lt_minNormal_iff`).

`isNormal_eq`, `isSubnormal_eq` and `classify_eq`, tagged `@[kernel_optimize]`, state the three
operations with that test, for every decimal format and every datum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

/--
Whether the nonzero coefficient `c` at the quantum exponent `q` is below the least normal
magnitude of `f` (`tiny_eq`): its digit count and the offset of `q` from the least quantum are
compared with the precision.
-/
def tiny (f : Format) (c : Nat) (q : Int) : Bool :=
  offsets q f.bias fun above below =>
    Nat.ble (Nat.succ (Nat.add (decimalLength c) above))
      (Nat.add (Nat.succ (Nat.mul 3 f.declets)) below)

/-- Kernel form of `Datum.isNormal` (`isNormal_eq`). -/
def isNormal (f : Format) (x : Datum) : Bool :=
  Datum.casesOn (motive := fun _ => Bool) x
    (fun _ c q => Bool.casesOn (motive := fun _ => Bool) (Nat.beq c 0) (!tiny f c q) false)
    (fun _ => false) (fun _ _ _ => false)

/-- Kernel form of `Datum.isSubnormal` (`isSubnormal_eq`). -/
def isSubnormal (f : Format) (x : Datum) : Bool :=
  Datum.casesOn (motive := fun _ => Bool) x
    (fun _ c q => Bool.casesOn (motive := fun _ => Bool) (Nat.beq c 0) (tiny f c q) false)
    (fun _ => false) (fun _ _ _ => false)

/-- Kernel form of `Datum.classify` (`classify_eq`). -/
def classify (f : Format) (x : Datum) : Class :=
  Datum.casesOn (motive := fun _ => Class) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Class) (Nat.beq c 0)
        (Bool.casesOn (motive := fun _ => Class) (tiny f c q)
          (Bool.casesOn (motive := fun _ => Class) s .positiveNormal .negativeNormal)
          (Bool.casesOn (motive := fun _ => Class) s .positiveSubnormal .negativeSubnormal))
        (Bool.casesOn (motive := fun _ => Class) s .positiveZero .negativeZero))
    (fun s => Bool.casesOn (motive := fun _ => Class) s .positiveInfinity .negativeInfinity)
    (fun _ t _ => Bool.casesOn (motive := fun _ => Class) t .quietNaN .signalingNaN)

/--
`tiny` decides whether a nonzero finite magnitude is below the least normal magnitude of the
format.
-/
theorem tiny_eq (f : Format) {c : Nat} (hc : c ≠ 0) (q : Int) :
    tiny f c q = decide ((c : ℚ) * (10 : ℚ) ^ q < f.minNormal) := by
  unfold tiny
  rw [offsets_eq, decimalLength_eq hc, Bool.eq_iff_iff, decide_eq_true_iff,
    scaled_lt_minNormal_iff f hc (e := q) (a := (q + f.bias).toNat)
      (b := (-(q + f.bias)).toNat) (by omega) (by omega),
    Nat.ble_eq]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one, Format.precision]
  omega

/-- A test of a coefficient against zero, as a Boolean. -/
theorem beq_zero_eq_decide (c : Nat) : Nat.beq c 0 = decide (c = 0) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

/-- `Datum.isSubnormal` is its kernel form, for every decimal format and every datum. -/
@[kernel_optimize] theorem isSubnormal_eq (f : Format) (x : Datum) :
    x.isSubnormal f = isSubnormal f x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change decide (c ≠ 0 ∧ (c : ℚ) * (10 : ℚ) ^ q < f.minNormal) = _
  unfold isSubnormal
  simp only [beq_zero_eq_decide]
  by_cases hc : c = 0
  · simp [hc]
  · simp [hc, tiny_eq f hc]

/-- `Datum.isNormal` is its kernel form, for every decimal format and every datum. -/
@[kernel_optimize] theorem isNormal_eq (f : Format) (x : Datum) :
    x.isNormal f = isNormal f x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change decide (f.minNormal ≤ (c : ℚ) * (10 : ℚ) ^ q) = _
  unfold isNormal
  simp only [beq_zero_eq_decide]
  by_cases hc : c = 0
  · simp [hc, f.minNormal_pos]
  · by_cases htiny : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal
    · simp [hc, tiny_eq f hc, htiny, not_le.mpr htiny]
    · simp [hc, tiny_eq f hc, htiny, not_lt.mp htiny]

/-- `Datum.classify` is its kernel form, for every decimal format and every datum. -/
@[kernel_optimize] theorem classify_eq (f : Format) (x : Datum) :
    x.classify f = classify f x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩
  · unfold Datum.classify classify
    simp only [beq_zero_eq_decide]
    by_cases hc : c = 0
    · cases s <;> simp [hc]
    · by_cases htiny : (c : ℚ) * (10 : ℚ) ^ q < f.minNormal <;> cases s <;>
        simp [hc, tiny_eq f hc, htiny]
  · cases s <;> rfl
  · cases t <;> rfl

/-! ## Kernel shapes -/

kernel_shape tiny
kernel_shape isNormal
kernel_shape isSubnormal
kernel_shape classify

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
