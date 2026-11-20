/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite

/-!
# Contracts of the augmented arithmetic operations

For a conventional IEEE descriptor (`fmt.isIEEE = true`, any width) and all operands:

* `toReal_augmentedAddition_head`, `toReal_augmentedMultiplication_head`: a finite head denotes
  the exact sum or product rounded to nearest with ties toward zero (`roundTiesTowardZeroAt`).
* `toReal_augmentedAddition_add`: with a finite head, head and tail of a sum add up to the exact
  sum, the tail is finite and no flag is raised. This is the error-free transformation
  of IEEE 754-2019 §9.5, for every tie rule's representable error (`add_round_error_generic`).
* `toReal_augmentedSubtraction_sub`: the same for a difference.
* `toReal_augmentedMultiplication_tail`: a finite tail of a product denotes the error of the
  head rounded the same way, and `augmentedMultiplication_inexact_iff`: `inexact` is raised
  exactly when head and tail do not add up to the exact product.
* `augmentedAddition_of_isFinite_head_eq_false`,
`augmentedMultiplication_of_isFinite_head_eq_false`:
  finite operands whose head is not finite overflowed: the tail is the head, and the flags are
  `overflow` and `inexact`.

For every descriptor:

* `augmentedAddition_of_isFinite_eq_false`, `augmentedMultiplication_of_isFinite_eq_false`: an
  operand that is not finite gives the special value of `add` or `mul` as head and as tail, with
  its flags.

The first group is proved once for the shared kernel `Internal.Status.augmented`
(`toReal_augmented_head`, `toReal_augmented_tail`, `augmented_inexact_iff`,
`augmented_status_of_isFinite`, `augmented_of_isFinite_head_eq_false`,
`isFinite_augmented_tail_of_abs_le`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- Exact dyadic subtraction agrees with subtraction in the real semantics. -/
theorem Dyadic.toReal_sub (a b : Numerics.Dyadic) :
    (Numerics.Dyadic.sub a b).toReal = a.toReal - b.toReal := by
  rw [← Numerics.Dyadic.cast_toRat, Numerics.Dyadic.sub_toRat]
  simp

/-- A grid value is within the finite range exactly when its magnitude does not overflow. -/
private theorem dyadicMagnitudeOverflows_eq_false_iff (d : Numerics.Dyadic) :
    dyadicMagnitudeOverflows fmt d = false ↔ |d.toReal| ≤ toReal (posMaxFinite fmt) := by
  unfold dyadicMagnitudeOverflows
  rw [beq_eq_false_iff_ne, Ne, cmpDyadic_gt_iff, not_lt, Dyadic.toReal_magnitude,
    Dyadic.toReal_maxFiniteDyadic]

/--
The head of a nonzero exact result is finite exactly when its grid value does not overflow, and
then it denotes the real rounded to nearest with ties toward zero.
-/
private theorem roundDyadicTiesTowardZero_facts (hfmt : fmt.isIEEE = true)
    (exact : Numerics.Dyadic) :
    (dyadicMagnitudeOverflows fmt (tiesTowardZeroGrid fmt exact) = false →
        isFinite (roundDyadicTiesTowardZero fmt exact) = true ∧
          toReal (roundDyadicTiesTowardZero fmt exact) =
            roundTiesTowardZeroAt fmt exact.toReal) ∧
      (dyadicMagnitudeOverflows fmt (tiesTowardZeroGrid fmt exact) = true →
        isFinite (roundDyadicTiesTowardZero fmt exact) = false) := by
  constructor
  · intro hrange
    have hfinite : isFinite (roundDyadicTiesTowardZero fmt exact) = true :=
      isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt _
        ((dyadicMagnitudeOverflows_eq_false_iff _).1 hrange)
    exact ⟨hfinite, toReal_roundDyadicTiesTowardZero fmt hfmt exact hfinite⟩
  · intro hover
    by_contra hnot
    have hfinite : isFinite (roundDyadicTiesTowardZero fmt exact) = true := by
      cases h : isFinite (roundDyadicTiesTowardZero fmt exact)
      · exact absurd h hnot
      · rfl
    have hbound := abs_toReal_le_posMaxFinite_of_isFinite _ hfinite
    rw [toReal_roundDyadicTiesTowardZero fmt hfmt exact hfinite,
      roundTiesTowardZeroAt_dyadic] at hbound
    rw [(dyadicMagnitudeOverflows_eq_false_iff _).2 hbound] at hover
    exact Bool.false_ne_true hover

namespace Internal.Status

/--
The four branches of the kernel: a zero result, an overflowing head, an exact error and a rounded
error, each with the outcome it delivers.
-/
private theorem augmented_cases (fmt : FloatFormat) (exact : Numerics.Dyadic)
    (zeroNegative : Bool) :
    (exact.significand = 0 ∧
        augmented fmt exact zeroNegative =
          { head := zero fmt zeroNegative, tail := zero fmt zeroNegative }) ∨
      (exact.significand ≠ 0 ∧
        dyadicMagnitudeOverflows fmt (tiesTowardZeroGrid fmt exact) = true ∧
        augmented fmt exact zeroNegative =
          { head := roundDyadicTiesTowardZero fmt exact
            tail := roundDyadicTiesTowardZero fmt exact
            status := { overflow := true, inexact := true } }) ∨
      (exact.significand ≠ 0 ∧
        dyadicMagnitudeOverflows fmt (tiesTowardZeroGrid fmt exact) = false ∧
        (Numerics.Dyadic.sub exact (tiesTowardZeroGrid fmt exact)).significand = 0 ∧
        augmented fmt exact zeroNegative =
          { head := roundDyadicTiesTowardZero fmt exact, tail := zero fmt exact.negative }) ∨
      (exact.significand ≠ 0 ∧
        dyadicMagnitudeOverflows fmt (tiesTowardZeroGrid fmt exact) = false ∧
        (Numerics.Dyadic.sub exact (tiesTowardZeroGrid fmt exact)).significand ≠ 0 ∧
        ∃ inexact : Bool,
          (inexact = true ↔
            (Numerics.Dyadic.sub exact (tiesTowardZeroGrid fmt exact)).toReal ≠
              (tiesTowardZeroGrid fmt
                (Numerics.Dyadic.sub exact (tiesTowardZeroGrid fmt exact))).toReal) ∧
          augmented fmt exact zeroNegative =
            { head := roundDyadicTiesTowardZero fmt exact
              tail := roundDyadicTiesTowardZero fmt
                (Numerics.Dyadic.sub exact (tiesTowardZeroGrid fmt exact))
              status := { underflow := inexact, inexact := inexact } }) := by
  by_cases hzero : exact.significand = 0
  · exact Or.inl ⟨hzero, by simp [augmented, hzero]⟩
  by_cases hover : dyadicMagnitudeOverflows fmt (tiesTowardZeroGrid fmt exact) = true
  · exact Or.inr (Or.inl ⟨hzero, hover, by
      simp [augmented, hzero, hover, roundDyadicTiesTowardZero]⟩)
  have hrange := Bool.eq_false_of_not_eq_true hover
  by_cases herror : (Numerics.Dyadic.sub exact (tiesTowardZeroGrid fmt exact)).significand = 0
  · exact Or.inr (Or.inr (Or.inl ⟨hzero, hrange, herror, by
      simp [augmented, hzero, hrange, herror, roundDyadicTiesTowardZero]⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨hzero, hrange, herror, _, ?_, by
      simp only [augmented, hzero, hrange, herror, roundDyadicTiesTowardZero, beq_iff_eq,
        ite_false, Bool.false_eq_true]
      rfl⟩))
    rw [bne_iff_ne, Ne, ← Dyadic.toReal_eq_zero_iff, Dyadic.toReal_sub, sub_eq_zero]

/-- A finite head of the kernel denotes the exact result rounded to nearest with ties toward
zero, in a conventional IEEE descriptor. -/
theorem toReal_augmented_head (hfmt : fmt.isIEEE = true) (exact : Numerics.Dyadic)
    (zeroNegative : Bool)
    (hfinite : isFinite (augmented fmt exact zeroNegative).head = true) :
    toReal (augmented fmt exact zeroNegative).head =
      roundTiesTowardZeroAt fmt exact.toReal := by
  rcases augmented_cases fmt exact zeroNegative with
    ⟨hzero, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [h, (Dyadic.toReal_eq_zero_iff exact).2 hzero, roundTiesTowardZeroAt_zero]
    exact toReal_zero fmt zeroNegative
  all_goals
    rw [h] at hfinite ⊢
    exact toReal_roundDyadicTiesTowardZero fmt hfmt exact hfinite

/--
Finite operands whose head is not finite overflowed, in a conventional IEEE descriptor: the tail
is the head, and the flags are `overflow` and `inexact`.
-/
theorem augmented_of_isFinite_head_eq_false (hfmt : fmt.isIEEE = true) (exact : Numerics.Dyadic)
    (zeroNegative : Bool)
    (hinfinite : isFinite (augmented fmt exact zeroNegative).head = false) :
    (augmented fmt exact zeroNegative).tail = (augmented fmt exact zeroNegative).head ∧
      (augmented fmt exact zeroNegative).status = { overflow := true, inexact := true } := by
  rcases augmented_cases fmt exact zeroNegative with
    ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, hrange, _, h⟩ | ⟨_, hrange, _, _, _, h⟩
  · rw [h] at hinfinite
    have hzero : isFinite (zero fmt zeroNegative) = true :=
      isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt zeroNegative)
    exact absurd (hinfinite.symm.trans hzero) (by decide)
  · rw [h]
    exact ⟨rfl, rfl⟩
  all_goals
    rw [h] at hinfinite
    exact absurd (hinfinite.symm.trans
      ((roundDyadicTiesTowardZero_facts hfmt exact).1 hrange).1) (by decide)

/--
A finite head raises neither `overflow`, `invalid` nor `divideByZero`, and `underflow` exactly
with `inexact`, in a conventional IEEE descriptor.
-/
theorem augmented_status_of_isFinite (hfmt : fmt.isIEEE = true) (exact : Numerics.Dyadic)
    (zeroNegative : Bool)
    (hfinite : isFinite (augmented fmt exact zeroNegative).head = true) :
    (augmented fmt exact zeroNegative).status =
      { underflow := (augmented fmt exact zeroNegative).status.inexact
        inexact := (augmented fmt exact zeroNegative).status.inexact } := by
  rcases augmented_cases fmt exact zeroNegative with
    ⟨_, h⟩ | ⟨_, hover, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [h]
  · rw [h] at hfinite
    exact absurd (hfinite.symm.trans
      ((roundDyadicTiesTowardZero_facts hfmt exact).2 hover)) (by decide)
  · rw [h]
  · rw [h]

/--
A finite tail of the kernel denotes the error of the head rounded to nearest with ties toward
zero, in a conventional IEEE descriptor.
-/
theorem toReal_augmented_tail (hfmt : fmt.isIEEE = true) (exact : Numerics.Dyadic)
    (zeroNegative : Bool)
    (hhead : isFinite (augmented fmt exact zeroNegative).head = true)
    (htail : isFinite (augmented fmt exact zeroNegative).tail = true) :
    toReal (augmented fmt exact zeroNegative).tail =
      roundTiesTowardZeroAt fmt
        (exact.toReal - toReal (augmented fmt exact zeroNegative).head) := by
  rw [toReal_augmented_head hfmt exact zeroNegative hhead]
  rcases augmented_cases fmt exact zeroNegative with
    ⟨hzero, h⟩ | ⟨_, hover, h⟩ | ⟨_, _, herror, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [h, (Dyadic.toReal_eq_zero_iff exact).2 hzero, roundTiesTowardZeroAt_zero, sub_zero,
      roundTiesTowardZeroAt_zero]
    exact toReal_zero fmt zeroNegative
  · rw [h] at hhead
    exact absurd (hhead.symm.trans
      ((roundDyadicTiesTowardZero_facts hfmt exact).2 hover)) (by decide)
  · have hreal := (Dyadic.toReal_eq_zero_iff _).2 herror
    rw [Dyadic.toReal_sub, ← roundTiesTowardZeroAt_dyadic] at hreal
    rw [h, hreal, roundTiesTowardZeroAt_zero]
    exact toReal_zero fmt exact.negative
  · rw [h] at htail ⊢
    rw [toReal_roundDyadicTiesTowardZero fmt hfmt _ htail, Dyadic.toReal_sub,
      ← roundTiesTowardZeroAt_dyadic]

/--
The kernel raises `inexact` exactly when a finite head and a finite tail do not add up to the
exact result, in a conventional IEEE descriptor.
-/
theorem augmented_inexact_iff (hfmt : fmt.isIEEE = true) (exact : Numerics.Dyadic)
    (zeroNegative : Bool)
    (hhead : isFinite (augmented fmt exact zeroNegative).head = true)
    (htail : isFinite (augmented fmt exact zeroNegative).tail = true) :
    (augmented fmt exact zeroNegative).status.inexact = true ↔
      toReal (augmented fmt exact zeroNegative).head +
          toReal (augmented fmt exact zeroNegative).tail ≠ exact.toReal := by
  rw [toReal_augmented_tail hfmt exact zeroNegative hhead htail,
    toReal_augmented_head hfmt exact zeroNegative hhead]
  rcases augmented_cases fmt exact zeroNegative with
    ⟨hzero, h⟩ | ⟨_, hover, h⟩ | ⟨_, _, herror, h⟩ | ⟨_, _, _, inexact, hinexact, h⟩
  · rw [h, (Dyadic.toReal_eq_zero_iff exact).2 hzero]
    simp
  · rw [h] at hhead
    exact absurd (hhead.symm.trans
      ((roundDyadicTiesTowardZero_facts hfmt exact).2 hover)) (by decide)
  · have hreal := (Dyadic.toReal_eq_zero_iff _).2 herror
    rw [Dyadic.toReal_sub, ← roundTiesTowardZeroAt_dyadic] at hreal
    rw [h, hreal, roundTiesTowardZeroAt_zero, add_zero]
    constructor
    · intro hfalse
      exact absurd hfalse Bool.false_ne_true
    · intro hne
      exact absurd (by linarith) hne
  · rw [h]
    change inexact = true ↔ _
    rw [hinexact, ← roundTiesTowardZeroAt_dyadic, Dyadic.toReal_sub,
      ← roundTiesTowardZeroAt_dyadic]
    constructor
    · intro hne heq
      exact hne (by linarith)
    · intro hne heq
      exact hne (by linarith)

/--
The tail of a finite head is finite whenever the rounded error of the head is within the finite
range, in a conventional IEEE descriptor.
-/
theorem isFinite_augmented_tail_of_abs_le (hfmt : fmt.isIEEE = true) (exact : Numerics.Dyadic)
    (zeroNegative : Bool)
    (hhead : isFinite (augmented fmt exact zeroNegative).head = true)
    (hbound : |roundTiesTowardZeroAt fmt
        (exact.toReal - toReal (augmented fmt exact zeroNegative).head)| ≤
      toReal (posMaxFinite fmt)) :
    isFinite (augmented fmt exact zeroNegative).tail = true := by
  rw [toReal_augmented_head hfmt exact zeroNegative hhead] at hbound
  rcases augmented_cases fmt exact zeroNegative with
    ⟨_, h⟩ | ⟨_, hover, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [h]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt zeroNegative)
  · rw [h] at hhead ⊢
    exact hhead
  · rw [h]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt exact.negative)
  · rw [h]
    refine isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt
      (tiesTowardZeroGrid fmt _) ?_
    rw [← roundTiesTowardZeroAt_dyadic, Dyadic.toReal_sub, ← roundTiesTowardZeroAt_dyadic]
    exact hbound

end Internal.Status

/-! ## Addition and subtraction -/

/-- A decoding failure of an operand that is not finite. -/
private theorem toDyadic?_eq_none_of_not_isFinite {x : Model fmt} (h : isFinite x = false) :
    toDyadic? x = none := by
  cases hd : toDyadic? x with
  | none => rfl
  | some d =>
      rw [isFinite_eq_true_of_toDyadic?_some hd] at h
      exact absurd h (by decide)

/--
An operand that is not finite gives the special value of `add` as head and as tail, with its
flags: a quiet NaN for a NaN operand or infinities of opposite signs, and the infinity otherwise.
-/
theorem augmentedAddition_of_isFinite_eq_false (x y : Model fmt)
    (h : isFinite x = false ∨ isFinite y = false) :
    augmentedAddition x y =
      { head := add x y, tail := add x y, status := (add x y (status := true)).status } := by
  have hspecial : augmentedAddition x y =
      Internal.Status.augmentedSpecial (add x y (status := true)) := by
    unfold augmentedAddition
    rcases h with h | h
    · rw [toDyadic?_eq_none_of_not_isFinite h]
    · rw [toDyadic?_eq_none_of_not_isFinite h]
      cases toDyadic? x <;> rfl
  rw [hspecial, Internal.Status.augmentedSpecial, value_add]

/--
A head that is the special value `special` whenever an operand is not finite, where a finite
`special` has finite operands: a finite head has finite operands.
-/
private theorem exists_toDyadic?_of_isFinite_head {x y head special : Model fmt}
    (hspecial : isFinite x = false ∨ isFinite y = false → head = special)
    (hoperands : isFinite special = true → isFinite x = true ∧ isFinite y = true)
    (hfinite : isFinite head = true) :
    ∃ dx dy, toDyadic? x = some dx ∧ toDyadic? y = some dy := by
  by_contra hnot
  have hbad : isFinite x = false ∨ isFinite y = false := by
    by_contra hboth
    rw [not_or, Bool.not_eq_false, Bool.not_eq_false] at hboth
    obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hboth.1
    obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hboth.2
    exact hnot ⟨dx, dy, hdx, hdy⟩
  rw [hspecial hbad] at hfinite
  obtain ⟨hx, hy⟩ := hoperands hfinite
  rcases hbad with hbad | hbad
  · rw [hx] at hbad; exact absurd hbad (by decide)
  · rw [hy] at hbad; exact absurd hbad (by decide)

/-- A finite head of a sum has finite operands, in a conventional IEEE descriptor. -/
private theorem isFinite_of_isFinite_augmentedAddition_head (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (hfinite : isFinite (augmentedAddition x y).head = true) :
    ∃ dx dy, toDyadic? x = some dx ∧ toDyadic? y = some dy :=
  exists_toDyadic?_of_isFinite_head
    (fun hbad => congrArg AugmentedOutcome.head (augmentedAddition_of_isFinite_eq_false x y hbad))
    (isFinite_of_isFinite_add hfmt) hfinite

/--
A finite head of `augmentedAddition` denotes the exact sum rounded to nearest with ties toward
zero, in a conventional IEEE descriptor.
-/
theorem toReal_augmentedAddition_head (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hfinite : isFinite (augmentedAddition x y).head = true) :
    toReal (augmentedAddition x y).head = roundTiesTowardZeroAt fmt (toReal x + toReal y) := by
  obtain ⟨dx, dy, hdx, hdy⟩ := isFinite_of_isFinite_augmentedAddition_head hfmt hfinite
  simp only [augmentedAddition, hdx, hdy] at hfinite ⊢
  rw [Internal.Status.toReal_augmented_head hfmt _ _ hfinite,
    toReal_addDyadic_of_toDyadic?_some hdx hdy]

/--
The error-free transformation of IEEE 754-2019 §9.5: with a finite head, head and tail of
`augmentedAddition` add up to the exact sum, the tail is finite, and no flag is raised, in a
conventional IEEE descriptor.
-/
theorem toReal_augmentedAddition_add (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hfinite : isFinite (augmentedAddition x y).head = true) :
    toReal (augmentedAddition x y).head + toReal (augmentedAddition x y).tail =
        toReal x + toReal y ∧
      isFinite (augmentedAddition x y).tail = true ∧ (augmentedAddition x y).status = {} := by
  obtain ⟨dx, dy, hdx, hdy⟩ := isFinite_of_isFinite_augmentedAddition_head hfmt hfinite
  have hx := toReal_genericFormat_of_isFinite x (isFinite_eq_true_of_toDyadic?_some hdx)
  have hy := toReal_genericFormat_of_isFinite y (isFinite_eq_true_of_toDyadic?_some hdy)
  have hexact := toReal_addDyadic_of_toDyadic?_some hdx hdy
  simp only [augmentedAddition, hdx, hdy] at hfinite ⊢
  have hhead := Internal.Status.toReal_augmented_head hfmt _ (dx.negative && dy.negative) hfinite
  rw [hexact] at hhead
  -- the error of the head is a value of the format, bounded by an operand
  have herror : GenericRepresentable binaryRadix (fexpOf fmt)
      (toReal x + toReal y - roundTiesTowardZeroAt fmt (toReal x + toReal y)) := by
    have h := add_round_error_generic (β := binaryRadix) (fexp := fexpOf fmt)
      (rnd := nearestChoice nearestTowardZeroChoice) hx hy
    have hneg := genericRepresentable_neg _ h
    rwa [neg_sub] at hneg
  have hnear := (round_toNearest_point (β := binaryRadix) (fexp := fexpOf fmt)
    (nearestChoice nearestTowardZeroChoice) (toReal x + toReal y)).2 (toReal x) hx
  have hbound : |toReal x + toReal y - roundTiesTowardZeroAt fmt (toReal x + toReal y)| ≤
      toReal (posMaxFinite fmt) := by
    have hy' := abs_toReal_le_posMaxFinite_of_isFinite y (isFinite_eq_true_of_toDyadic?_some hdy)
    have hstep : |toReal x - (toReal x + toReal y)| = |toReal y| := by
      rw [show toReal x - (toReal x + toReal y) = -toReal y by ring, abs_neg]
    rw [abs_sub_comm]
    exact (hnear.trans hstep.le).trans hy'
  have hround : roundTiesTowardZeroAt fmt
      (toReal x + toReal y - roundTiesTowardZeroAt fmt (toReal x + toReal y)) =
        toReal x + toReal y - roundTiesTowardZeroAt fmt (toReal x + toReal y) :=
    round_preserves_generic _ _ herror
  have htail : isFinite
      (Internal.Status.augmented fmt (addDyadic dx dy) (dx.negative &&
        dy.negative)).tail = true := by
    apply Internal.Status.isFinite_augmented_tail_of_abs_le hfmt _ _ hfinite
    rw [hexact, hhead, hround]
    exact hbound
  have htailReal := Internal.Status.toReal_augmented_tail hfmt _ _ hfinite htail
  rw [hexact, hhead, hround] at htailReal
  have hsum : toReal (Internal.Status.augmented fmt (addDyadic dx dy)
        (dx.negative && dy.negative)).head +
      toReal (Internal.Status.augmented fmt (addDyadic dx dy)
        (dx.negative && dy.negative)).tail = toReal x + toReal y := by
    rw [hhead, htailReal]
    ring
  refine ⟨hsum, htail, ?_⟩
  have hinexact : (Internal.Status.augmented fmt (addDyadic dx dy)
      (dx.negative && dy.negative)).status.inexact = false := by
    by_contra hne
    have := (Internal.Status.augmented_inexact_iff hfmt _ _ hfinite htail).1
      (by simpa using hne)
    exact this (by rw [hexact]; exact hsum)
  rw [Internal.Status.augmented_status_of_isFinite hfmt _ _ hfinite, hinexact]

/--
Finite operands whose sum has a head that is not finite overflowed, in a conventional IEEE
descriptor: the tail is the head, and the flags are `overflow` and `inexact`.
-/
theorem augmentedAddition_of_isFinite_head_eq_false (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hinfinite : isFinite (augmentedAddition x y).head = false) :
    (augmentedAddition x y).tail = (augmentedAddition x y).head ∧
      (augmentedAddition x y).status = { overflow := true, inexact := true } := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  simp only [augmentedAddition, hdx, hdy] at hinfinite ⊢
  exact Internal.Status.augmented_of_isFinite_head_eq_false hfmt _ _ hinfinite

/--
With a finite head, head and tail of `augmentedSubtraction` add up to the exact difference, in a
conventional IEEE descriptor.
-/
theorem toReal_augmentedSubtraction_sub (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hfinite : isFinite (augmentedSubtraction x y).head = true) :
    toReal (augmentedSubtraction x y).head + toReal (augmentedSubtraction x y).tail =
      toReal x - toReal y := by
  obtain ⟨_, dy, _, hdy⟩ := isFinite_of_isFinite_augmentedAddition_head hfmt hfinite
  have hy : isFinite y = true := by
    rw [← isFinite_neg]
    exact isFinite_eq_true_of_toDyadic?_some hdy
  rw [augmentedSubtraction, (toReal_augmentedAddition_add hfmt x (neg y) hfinite).1,
    toReal_neg y hy, sub_eq_add_neg]

/-! ## Multiplication -/

/--
An operand that is not finite gives the special value of `mul` as head and as tail, with its
flags: a quiet NaN for a NaN operand or zero times infinity, and the infinity otherwise.
-/
theorem augmentedMultiplication_of_isFinite_eq_false (x y : Model fmt)
    (h : isFinite x = false ∨ isFinite y = false) :
    augmentedMultiplication x y =
      { head := mul x y, tail := mul x y, status := (mul x y (status := true)).status } := by
  have hspecial : augmentedMultiplication x y =
      Internal.Status.augmentedSpecial (mul x y (status := true)) := by
    unfold augmentedMultiplication
    rcases h with h | h
    · rw [toDyadic?_eq_none_of_not_isFinite h]
    · rw [toDyadic?_eq_none_of_not_isFinite h]
      cases toDyadic? x <;> rfl
  rw [hspecial, Internal.Status.augmentedSpecial, value_mul]

/-- A finite head of a product has finite operands, in a conventional IEEE descriptor. -/
private theorem isFinite_of_isFinite_augmentedMultiplication_head (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (hfinite : isFinite (augmentedMultiplication x y).head = true) :
    ∃ dx dy, toDyadic? x = some dx ∧ toDyadic? y = some dy :=
  exists_toDyadic?_of_isFinite_head
    (fun hbad =>
      congrArg AugmentedOutcome.head (augmentedMultiplication_of_isFinite_eq_false x y hbad))
    (isFinite_of_isFinite_mul hfmt) hfinite

/--
A finite head of `augmentedMultiplication` denotes the exact product rounded to nearest with ties
toward zero, in a conventional IEEE descriptor.
-/
theorem toReal_augmentedMultiplication_head (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hfinite : isFinite (augmentedMultiplication x y).head = true) :
    toReal (augmentedMultiplication x y).head =
      roundTiesTowardZeroAt fmt (toReal x * toReal y) := by
  obtain ⟨dx, dy, hdx, hdy⟩ := isFinite_of_isFinite_augmentedMultiplication_head hfmt hfinite
  simp only [augmentedMultiplication, hdx, hdy] at hfinite ⊢
  rw [Internal.Status.toReal_augmented_head hfmt _ _ hfinite,
    toReal_mulDyadic_of_toDyadic?_some hdx hdy]

/--
A finite tail of `augmentedMultiplication` with a finite head denotes the error of the head
rounded to nearest with ties toward zero, in a conventional IEEE descriptor.
-/
theorem toReal_augmentedMultiplication_tail (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hhead : isFinite (augmentedMultiplication x y).head = true)
    (htail : isFinite (augmentedMultiplication x y).tail = true) :
    toReal (augmentedMultiplication x y).tail =
      roundTiesTowardZeroAt fmt
        (toReal x * toReal y - toReal (augmentedMultiplication x y).head) := by
  obtain ⟨dx, dy, hdx, hdy⟩ := isFinite_of_isFinite_augmentedMultiplication_head hfmt hhead
  simp only [augmentedMultiplication, hdx, hdy] at hhead htail ⊢
  rw [Internal.Status.toReal_augmented_tail hfmt _ _ hhead htail,
    toReal_mulDyadic_of_toDyadic?_some hdx hdy]

/--
`augmentedMultiplication` raises `inexact` exactly when a finite head and a finite tail do not
add up to the exact product, and then it raises `underflow` too, in a conventional IEEE
descriptor.
-/
theorem augmentedMultiplication_inexact_iff (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (hhead : isFinite (augmentedMultiplication x y).head = true)
    (htail : isFinite (augmentedMultiplication x y).tail = true) :
    ((augmentedMultiplication x y).status.inexact = true ↔
        toReal (augmentedMultiplication x y).head + toReal (augmentedMultiplication x y).tail ≠
          toReal x * toReal y) ∧
      (augmentedMultiplication x y).status =
        { underflow := (augmentedMultiplication x y).status.inexact
          inexact := (augmentedMultiplication x y).status.inexact } := by
  obtain ⟨dx, dy, hdx, hdy⟩ := isFinite_of_isFinite_augmentedMultiplication_head hfmt hhead
  simp only [augmentedMultiplication, hdx, hdy] at hhead htail ⊢
  refine ⟨?_, Internal.Status.augmented_status_of_isFinite hfmt _ _ hhead⟩
  rw [Internal.Status.augmented_inexact_iff hfmt _ _ hhead htail,
    toReal_mulDyadic_of_toDyadic?_some hdx hdy]

/--
Finite operands whose product has a head that is not finite overflowed, in a conventional IEEE
descriptor: the tail is the head, and the flags are `overflow` and `inexact`.
-/
theorem augmentedMultiplication_of_isFinite_head_eq_false (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : isFinite x = true) (hy : isFinite y = true)
    (hinfinite : isFinite (augmentedMultiplication x y).head = false) :
    (augmentedMultiplication x y).tail = (augmentedMultiplication x y).head ∧
      (augmentedMultiplication x y).status = { overflow := true, inexact := true } := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  simp only [augmentedMultiplication, hdx, hdy] at hinfinite ⊢
  exact Internal.Status.augmented_of_isFinite_head_eq_false hfmt _ _ hinfinite

end Model
end FloatLib.Floats.Formats.BinaryInterchange
