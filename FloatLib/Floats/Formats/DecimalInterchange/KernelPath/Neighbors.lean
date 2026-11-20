/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Quantum
public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Runtime

/-!
# Kernel path of decimal `nextUp` and `nextDown`

`Arithmetic.nextUp` (IEEE 754-2019 §5.3.1) first puts its operand on the finest quantum that
the precision and the exponent range allow, through the rounding `roundedPair` of an exact
rational value, and then steps to the neighbouring coefficient. For a nonzero finite datum of
the format that normalization rounds nothing (`roundedPair_of_fits`): the coefficient is
multiplied by a power of ten that its number of digits decides.

`nextUp` computes this on natural numbers: the quantum exponent as its offset above the least
quantum, the number of digits by `decimalLength`, and the two neighbours by comparisons of
natural numbers (`neighborAbove_eq`, `neighborBelow_eq`). A zero, a datum that is not in the
format, an infinity and a NaN are left to the specification. `nextUp_eq`, tagged
`@[kernel_optimize]`, proves the kernel form equal to `Arithmetic.nextUp` for every format and
datum. `Arithmetic.nextDown` is `nextUp` of the negated datum, negated, and is unfolded to it.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/--
Kernel form of `Arithmetic.neighborAbove` at the quantum `shift` above the least quantum
(`neighborAbove_eq`): the next coefficient, the least coefficient of full precision at the next
quantum when the coefficient is the largest, and `+∞` beyond the largest quantum.
-/
def neighborAbove (f : Format) (c shift : Nat) : Datum :=
  (fun full =>
    Bool.casesOn (motive := fun _ => Datum) (Nat.ble (Nat.add c 2) full)
      (Bool.casesOn (motive := fun _ => Datum)
        (Nat.ble (Nat.add shift 2) (Nat.mul 3 (Nat.pow 2 f.exponentBits)))
        (.infinity false)
        (.finite false (Nat.div full 10) (quantumAt (Nat.succ shift) f.bias)))
      (.finite false (Nat.succ c) (quantumAt shift f.bias)))
    (Nat.pow 10 (Nat.succ (Nat.mul 3 f.declets)))

/--
Kernel form of `Arithmetic.neighborBelow` at the quantum `shift` above the least quantum
(`neighborBelow_eq`): the previous coefficient, and below the least coefficient of full
precision the largest coefficient at the previous quantum, when there is one.
-/
def neighborBelow (f : Format) (c shift : Nat) : Datum :=
  (fun full =>
    Bool.casesOn (motive := fun _ => Datum)
      (Bool.and (Bool.not (Nat.beq shift 0)) (Nat.beq c (Nat.div full 10)))
      (.finite false (Nat.pred c) (quantumAt shift f.bias))
      (.finite false (Nat.pred full) (quantumAt (Nat.pred shift) f.bias)))
    (Nat.pow 10 (Nat.succ (Nat.mul 3 f.declets)))

/-- `neighborAbove` is `Arithmetic.neighborAbove` at the quantum exponent of the offset. -/
theorem neighborAbove_eq (f : Format) (c shift : Nat) :
    neighborAbove f c shift = Arithmetic.neighborAbove f c ((shift : Int) - f.bias) := by
  have hbound : 3 * 2 ^ f.exponentBits = f.exponentBound := rfl
  have hfull : 10 ^ (3 * f.declets + 1) = f.coefficientBound := (Format.coefficientBound_eq f).symm
  have hdiv : ∀ m n : Nat, Nat.div m n = m / n := fun _ _ => rfl
  unfold neighborAbove Arithmetic.neighborAbove Format.maxQuantum
  simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq, hdiv, Nat.succ_eq_add_one, hbound, hfull,
    coefficientBound_div_ten, quantumAt_eq, natBle_eq, casesOn_decide]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- `neighborBelow` is `Arithmetic.neighborBelow` at the quantum exponent of the offset. -/
theorem neighborBelow_eq (f : Format) (c shift : Nat) :
    neighborBelow f c shift = Arithmetic.neighborBelow f c ((shift : Int) - f.bias) := by
  have hfull : 10 ^ (3 * f.declets + 1) = f.coefficientBound := (Format.coefficientBound_eq f).symm
  have hdiv : ∀ m n : Nat, Nat.div m n = m / n := fun _ _ => rfl
  unfold neighborBelow Arithmetic.neighborBelow Format.minQuantum
  simp only [Nat.mul_eq, Nat.pow_eq, hdiv, Nat.succ_eq_add_one, Nat.pred_eq_sub_one, hfull,
    coefficientBound_div_ten, quantumAt_eq, natBeq_eq, ← decide_not, ← Bool.decide_and,
    casesOn_decide]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/--
`nextUp` of a nonzero finite datum of the format, on natural numbers (`nextUpValid_eq`): the
coefficient is scaled to the finest quantum, whose offset above the least quantum is the number
of digits plus the offset of the exponent less the precision, and the neighbour above is taken
for a positive datum and the negated neighbour below for a negative one.
-/
def nextUpValid (f : Format) (s : Bool) (c : Nat) (q : Int) : Outcome :=
  offsets q f.bias fun above _ =>
    (fun shift =>
      (fun coefficient =>
        ({ value := Bool.casesOn (motive := fun _ => Datum) s (neighborAbove f coefficient shift)
            (Datum.negate (neighborBelow f coefficient shift)) } : Outcome))
        (Nat.mul c (Nat.pow 10 (Nat.sub above shift))))
      (Nat.sub (Nat.add (decimalLength c) above) (Nat.succ (Nat.mul 3 f.declets)))

/--
`nextUpValid` is `Arithmetic.nextUp` on a nonzero coefficient within the precision at a
quantum exponent not below the least one.
-/
theorem nextUpValid_eq (f : Format) (s : Bool) {c : Nat} (hc : c ≠ 0) {q : Int}
    (hmin : f.minQuantum ≤ q) (hfits : c < f.coefficientBound) :
    Arithmetic.nextUp f (.finite s c q) = nextUpValid f s c q := by
  have hoffset : (((q + f.bias).toNat : Nat) : Int) = q + f.bias := by
    unfold Format.minQuantum at hmin
    omega
  have hpair := roundedPair_of_fits f .nearest false hc
    (by rwa [← f.coefficientBound_eq]) hoffset
  rw [nextUpValid, offsets_eq]
  simp only [Arithmetic.nextUp, hc, ↓reduceIte, hpair, neighborAbove_eq, neighborBelow_eq,
    decimalLength_eq hc, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one]
  cases s <;> rfl

/--
Kernel form of `Arithmetic.nextUp` (`nextUp_eq`): `nextUpValid` for a nonzero finite datum of
the format. A zero, a finite datum outside the format, an infinity and a NaN are left to the
specification.
-/
def nextUp (f : Format) (x : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Outcome) (Bool.and (fits f c q) (Bool.not (Nat.beq c 0)))
        (Arithmetic.nextUp f x) (nextUpValid f s c q))
    (fun _ => Arithmetic.nextUp f x) (fun _ _ _ => Arithmetic.nextUp f x)

/-- IEEE 754-2019 §5.3.1 `nextUp` on decimal data is its kernel form, for every format and datum. -/
@[kernel_optimize] theorem nextUp_eq (f : Format) (x : Datum) :
    Arithmetic.nextUp f x = nextUp f x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change _ = Bool.casesOn (motive := fun _ => Outcome)
    (Bool.and (fits f c q) (Bool.not (Nat.beq c 0)))
    (Arithmetic.nextUp f (.finite s c q)) (nextUpValid f s c q)
  cases hvalid : fits f c q
  · rfl
  · rcases c with _ | c
    · rfl
    · rw [fits_eq, decide_eq_true_iff] at hvalid
      exact nextUpValid_eq f s (Nat.succ_ne_zero c) hvalid.1 hvalid.2.2

/-! ## Kernel shapes -/

kernel_shape neighborAbove
kernel_shape neighborBelow
kernel_shape nextUpValid
kernel_shape nextUp

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath

/-
`nextDown` is `nextUp` of the negated datum, negated: `float_decide` unfolds it, and the rule of
`nextUp` applies.
-/
attribute [kernel_optimize unfold] FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.nextDown
