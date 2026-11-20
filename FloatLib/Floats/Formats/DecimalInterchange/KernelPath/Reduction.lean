/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Runtime

/-!
# Kernel path of the decimal reductions

`Arithmetic.sum`, `sumAbs`, `sumSquare` and `dot` (IEEE 754-2019 §9.4) add their terms as exact
rational numbers and round the sum once. For finite operands the exact sum is an integer at the
least quantum exponent of the terms, so the kernel form keeps it as two natural numbers, the
sum of the positive and the sum of the negative terms at that exponent:

* `sumLoop` consumes the terms, given by their sign, coefficient and quantum exponent, and keeps
  the two sums, the least exponent and the sign that an exact zero sum has. `sumLoop_eq` proves
  that this state stands for the exact sum of the specification (`totalOf`) after every term.
* `deliverSum` rounds the difference of the two sums once with `KernelPath.project`
  (`deliverSum_eq`).
* `sum`, `sumAbs`, `sumSquare` and `dot` are the kernel forms: when every operand is finite the
  terms are collected (`collect`, `collectProducts`) and added by `sumLoop`; an array with an
  infinity or a NaN, and two arrays of different lengths, are left to the specification.
  `sum_eq`, `sumAbs_eq`, `sumSquare_eq` and `dot_eq`, tagged `@[kernel_optimize]`, prove them
  equal to the specification for every format, rounding direction and array.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics
open Arithmetic.Reduction (Term Total)

/-- The term of the specification with the sign, coefficient and quantum exponent `fields`. -/
def toTerm (fields : Bool × Nat × Int) : Term :=
  .finite fields.1 (Datum.finiteValue fields.1 fields.2.1 fields.2.2) fields.2.2

/--
The exact sum that a state of `sumLoop` stands for: nothing consumed yet, or the difference of
the sums of the positive and of the negative terms at the least quantum exponent, with the sign
of an exact zero sum.
-/
def totalOf (seen : Bool) (positive negative : Nat) (quantum : Int) (zero : Bool) : Total :=
  if seen then
    { value := ((positive : ℚ) - (negative : ℚ)) * (10 : ℚ) ^ quantum
      quantum := some quantum
      negative := some zero }
  else {}

/--
Add finite terms exactly: `positive` and `negative` are the sums of the positive and of the
negative terms consumed so far, as coefficients at `quantum`, the least quantum exponent so far,
and `zero` is the sign of an exact zero sum: the common sign of the terms, and after terms of
both signs the sign that the rounding direction gives a cancellation. `k` receives the final
state (`sumLoop_eq`).
-/
def sumLoop {α : Type} (mode : RoundingMode) (k : Bool → Nat → Nat → Int → Bool → α)
    (terms : List (Bool × Nat × Int)) : Bool → Nat → Nat → Int → Bool → α :=
  List.rec (motive := fun _ => Bool → Nat → Nat → Int → Bool → α) k
    (fun fields _ next seen positive negative quantum zero =>
      Bool.casesOn (motive := fun _ => α) seen
        (next true
          (Bool.casesOn (motive := fun _ => Nat) fields.1 fields.2.1 0)
          (Bool.casesOn (motive := fun _ => Nat) fields.1 0 fields.2.1)
          fields.2.2 fields.1)
        (gaps quantum fields.2.2 fun above below =>
          (fun scale term =>
            next true
              (Nat.add (Nat.mul positive scale)
                (Bool.casesOn (motive := fun _ => Nat) fields.1 term 0))
              (Nat.add (Nat.mul negative scale)
                (Bool.casesOn (motive := fun _ => Nat) fields.1 0 term))
              (Bool.casesOn (motive := fun _ => Int) (Nat.beq above 0) fields.2.2 quantum)
              (Bool.casesOn (motive := fun _ => Bool) (differ zero fields.1) zero (isDown mode)))
            (Nat.pow 10 above) (Nat.mul fields.2.1 (Nat.pow 10 below))))
    terms

/-- The first term of a sum, as a state. -/
theorem push_first (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    Total.push mode {} (toTerm (s, c, q)) =
      totalOf true (Bool.rec (motive := fun _ => Nat) c 0 s)
        (Bool.rec (motive := fun _ => Nat) 0 c s) q s := by
  cases s <;> simp [Total.push, totalOf, toTerm, Datum.finiteValue]

/-- A further term of a sum, as a state at the smaller of the two quantum exponents. -/
theorem push_next (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) (positive negative : Nat)
    (quantum : Int) (zero : Bool) :
    Total.push mode (totalOf true positive negative quantum zero) (toTerm (s, c, q)) =
      totalOf true
        (positive * 10 ^ (quantum - q).toNat +
          Bool.rec (motive := fun _ => Nat) (c * 10 ^ (q - quantum).toNat) 0 s)
        (negative * 10 ^ (quantum - q).toNat +
          Bool.rec (motive := fun _ => Nat) 0 (c * 10 ^ (q - quantum).toNat) s)
        (min quantum q) (Arithmetic.zeroSumSign mode zero s) := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  have hm : (10 : ℚ) ^ quantum =
      (10 : ℚ) ^ min quantum q * (10 : ℚ) ^ (quantum - q).toNat := by
    rw [← zpow_natCast (10 : ℚ) (quantum - q).toNat, ← zpow_add₀ hten]
    congr 1
    omega
  have hq : (10 : ℚ) ^ q = (10 : ℚ) ^ min quantum q * (10 : ℚ) ^ (q - quantum).toNat := by
    rw [← zpow_natCast (10 : ℚ) (q - quantum).toNat, ← zpow_add₀ hten]
    congr 1
    omega
  cases s <;> simp [Total.push, totalOf, toTerm, Datum.finiteValue, hm, hq] <;> ring

/--
`sumLoop` hands to its continuation a state that stands for the exact sum of the terms it
consumed, added to the sum that its starting state stands for.
-/
theorem sumLoop_eq {α : Type} (mode : RoundingMode) (k : Bool → Nat → Nat → Int → Bool → α)
    (deliver : Total → α)
    (hk : ∀ seen positive negative quantum zero,
      k seen positive negative quantum zero =
        deliver (totalOf seen positive negative quantum zero)) :
    ∀ (terms : List (Bool × Nat × Int)) (seen : Bool) (positive negative : Nat) (quantum : Int)
      (zero : Bool),
      sumLoop mode k terms seen positive negative quantum zero =
        deliver ((terms.map toTerm).foldl (Total.push mode)
          (totalOf seen positive negative quantum zero))
  | [], seen, positive, negative, quantum, zero => hk seen positive negative quantum zero
  | (s, c, q) :: rest, seen, positive, negative, quantum, zero => by
      have hleast : Bool.rec (motive := fun _ => Int) q quantum (Nat.beq (quantum - q).toNat 0) =
          min quantum q := by
        by_cases h : quantum ≤ q
        · have hzero : (quantum - q).toNat = 0 := by omega
          rw [hzero, min_eq_left h]
          rfl
        · obtain ⟨j, hj⟩ : ∃ j, (quantum - q).toNat = j + 1 := ⟨(quantum - q).toNat - 1, by omega⟩
          rw [hj, min_eq_right (by omega)]
          rfl
      cases seen
      · change sumLoop mode k rest true (Bool.rec (motive := fun _ => Nat) c 0 s)
          (Bool.rec (motive := fun _ => Nat) 0 c s) q s = _
        rw [sumLoop_eq mode k deliver hk rest, List.map_cons, List.foldl_cons]
        congr 2
        exact (push_first mode s c q).symm
      · change (gaps quantum q fun above below =>
          (fun scale term =>
            sumLoop mode k rest true
              (Nat.add (Nat.mul positive scale)
                (Bool.rec (motive := fun _ => Nat) term 0 s))
              (Nat.add (Nat.mul negative scale)
                (Bool.rec (motive := fun _ => Nat) 0 term s))
              (Bool.rec (motive := fun _ => Int) q quantum (Nat.beq above 0))
              (Bool.rec (motive := fun _ => Bool) zero (isDown mode) (differ zero s)))
            (Nat.pow 10 above) (Nat.mul c (Nat.pow 10 below))) = _
        have hzero : Bool.rec (motive := fun _ => Bool) zero (isDown mode) (differ zero s) =
            Arithmetic.zeroSumSign mode zero s := by
          cases zero <;> cases s <;> cases mode <;> rfl
        rw [gaps_eq]
        dsimp only
        rw [hleast, hzero, sumLoop_eq mode k deliver hk rest, List.map_cons, List.foldl_cons]
        congr 2
        exact (push_next mode s c q positive negative quantum zero).symm

/--
The outcome of a state of `sumLoop` (`deliverSum_eq`): `+0` for no term, and otherwise one
kernel projection of the difference of the two sums at the least quantum exponent, with the
sign of the larger sum, or the zero-sum sign when they are equal.
-/
def deliverSum (f : Format) (mode : RoundingMode) (seen : Bool) (positive negative : Nat)
    (quantum : Int) (zero : Bool) : Outcome :=
  Bool.casesOn (motive := fun _ => Outcome) seen
    (project f mode false 0 0)
    (Bool.casesOn (motive := fun _ => Outcome) (Nat.beq positive negative)
      (Bool.casesOn (motive := fun _ => Outcome) (Nat.ble negative positive)
        (project f mode true (Nat.sub negative positive) quantum)
        (project f mode false (Nat.sub positive negative) quantum))
      (project f mode zero 0 quantum))

/-- `deliverSum` is the specified delivery of the exact sum that the state stands for. -/
theorem deliverSum_eq (f : Format) (mode : RoundingMode) (seen : Bool) (positive negative : Nat)
    (quantum : Int) (zero : Bool) :
    deliverSum f mode seen positive negative quantum zero =
      (totalOf seen positive negative quantum zero).deliver f mode := by
  cases seen
  · change project f mode false 0 0 = DecimalInterchange.project f mode 0 0 false
    rw [← project_finiteValue f mode false false 0 0 (fun _ => rfl)]
    simp [Datum.finiteValue]
  · change Bool.casesOn (motive := fun _ => Outcome) (Nat.beq positive negative)
        (Bool.casesOn (motive := fun _ => Outcome) (Nat.ble negative positive)
          (project f mode true (Nat.sub negative positive) quantum)
          (project f mode false (Nat.sub positive negative) quantum))
        (project f mode zero 0 quantum) =
      DecimalInterchange.project f mode
        (((positive : ℚ) - (negative : ℚ)) * (10 : ℚ) ^ quantum) quantum zero
    rcases lt_trichotomy positive negative with h | h | h
    · have hbeq : Nat.beq positive negative = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        omega
      have hble : Nat.ble negative positive = false := by
        rw [← Bool.not_eq_true, Nat.ble_eq]
        omega
      rw [hbeq, hble]
      change project f mode true (negative - positive) quantum = _
      rw [← project_finiteValue f mode true zero (negative - positive) quantum
        (fun hzero => absurd hzero (by omega))]
      congr 1
      simp only [Datum.finiteValue, ↓reduceIte]
      push_cast [Nat.cast_sub h.le]
      ring
    · subst h
      have hbeq : Nat.beq positive positive = true := by rw [Nat.beq_eq]
      rw [hbeq]
      change project f mode zero 0 quantum = _
      rw [← project_finiteValue f mode zero zero 0 quantum (fun _ => rfl)]
      congr 1
      simp [Datum.finiteValue]
    · have hbeq : Nat.beq positive negative = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        omega
      have hble : Nat.ble negative positive = true := by
        rw [Nat.ble_eq]
        omega
      rw [hbeq, hble]
      change project f mode false (positive - negative) quantum = _
      rw [← project_finiteValue f mode false zero (positive - negative) quantum
        (fun hzero => absurd hzero (by omega))]
      congr 1
      simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte]
      push_cast [Nat.cast_sub h.le]
      ring

/-- The delivery of a sum of magnitudes is the delivery of the sum on a state of `sumLoop`. -/
theorem deliverMagnitude_totalOf (f : Format) (mode : RoundingMode) (seen : Bool)
    (positive negative : Nat) (quantum : Int) (zero : Bool) :
    (totalOf seen positive negative quantum zero).deliverMagnitude f mode =
      (totalOf seen positive negative quantum zero).deliver f mode := by
  cases seen <;> rfl

/--
The fields of the finite data of a list, each passed through `term`, or `none` when a datum of
the list is not finite (`collect_eq`).
-/
def collect (term : Bool → Nat → Int → Bool × Nat × Int) (values : List Datum) :
    Option (List (Bool × Nat × Int)) :=
  List.rec (motive := fun _ => Option (List (Bool × Nat × Int))) (some [])
    (fun x _ collected =>
      Datum.casesOn (motive := fun _ => Option (List (Bool × Nat × Int))) x
        (fun s c q =>
          Option.casesOn (motive := fun _ => Option (List (Bool × Nat × Int))) collected none
            (fun tail => some (term s c q :: tail)))
        (fun _ => none) (fun _ _ _ => none))
    values

/--
The fields that `collect` returns are the terms of the specification, for a term function of
the specification that agrees with `term` on finite data.
-/
theorem collect_eq (term : Bool → Nat → Int → Bool × Nat × Int) (spec : Datum → Term)
    (hterm : ∀ s c q, spec (.finite s c q) = toTerm (term s c q)) :
    ∀ (values : List Datum) (terms : List (Bool × Nat × Int)),
      collect term values = some terms → values.map spec = terms.map toTerm
  | [], terms, h => by
      obtain rfl : [] = terms := Option.some.inj h
      rfl
  | .finite s c q :: rest, terms, h => by
      cases htail : collect term rest with
      | none =>
          have hnone : collect term (.finite s c q :: rest) = none := by
            change Option.casesOn (motive := fun _ => Option (List (Bool × Nat × Int)))
              (collect term rest) none (fun tail => some (term s c q :: tail)) = none
            rw [htail]
          rw [hnone] at h
          exact absurd h (by simp)
      | some tail =>
          have hsome : collect term (.finite s c q :: rest) = some (term s c q :: tail) := by
            change Option.casesOn (motive := fun _ => Option (List (Bool × Nat × Int)))
              (collect term rest) none (fun tail => some (term s c q :: tail)) = _
            rw [htail]
          rw [hsome] at h
          obtain rfl : term s c q :: tail = terms := Option.some.inj h
          rw [List.map_cons, List.map_cons, hterm, collect_eq term spec hterm rest tail htail]
  | .infinity s :: rest, terms, h => absurd h (by
      change ¬ ((none : Option (List (Bool × Nat × Int))) = some terms)
      simp)
  | .nan s t p :: rest, terms, h => absurd h (by
      change ¬ ((none : Option (List (Bool × Nat × Int))) = some terms)
      simp)

/--
The exact sum of the finite data of an array, each passed through `term`, rounded once; an
array with a datum that is not finite gives `fallback`.
-/
def reduce (f : Format) (mode : RoundingMode) (term : Bool → Nat → Int → Bool × Nat × Int)
    (fallback : Outcome) (values : Array Datum) : Outcome :=
  Option.casesOn (motive := fun _ => Outcome) (collect term values.toList) fallback
    (fun terms => sumLoop mode (deliverSum f mode) terms false 0 0 0 false)

/-- Kernel form of `Arithmetic.sum` (`sum_eq`). -/
def sum (f : Format) (mode : RoundingMode) (values : Array Datum) : Outcome :=
  reduce f mode (fun s c q => (s, c, q)) (Arithmetic.sum f mode values) values

/-- Kernel form of `Arithmetic.sumAbs` (`sumAbs_eq`): every term with a positive sign. -/
def sumAbs (f : Format) (mode : RoundingMode) (values : Array Datum) : Outcome :=
  reduce f mode (fun _ c q => (false, c, q)) (Arithmetic.sumAbs f mode values) values

/--
Kernel form of `Arithmetic.sumSquare` (`sumSquare_eq`): the square of each coefficient at twice
its quantum exponent.
-/
def sumSquare (f : Format) (mode : RoundingMode) (values : Array Datum) : Outcome :=
  reduce f mode (fun _ c q => (false, Nat.mul c c, Int.add q q))
    (Arithmetic.sumSquare f mode values) values

/--
`reduce` is the specified delivery of the exact sum of the terms of the specification, when
`fallback` is that delivery and the term functions agree on finite data.
-/
theorem reduce_eq (f : Format) (mode : RoundingMode) (term : Bool → Nat → Int → Bool × Nat × Int)
    (spec : Datum → Term) (hterm : ∀ s c q, spec (.finite s c q) = toTerm (term s c q))
    (deliver : Total → Outcome)
    (hdeliver : ∀ seen positive negative quantum zero,
      deliverSum f mode seen positive negative quantum zero =
        deliver (totalOf seen positive negative quantum zero))
    (values : Array Datum) :
    reduce f mode term (deliver (Arithmetic.Reduction.total mode (values.toList.map spec)))
      values = deliver (Arithmetic.Reduction.total mode (values.toList.map spec)) := by
  unfold reduce
  cases hcollect : collect term values.toList with
  | none => rfl
  | some terms =>
      change sumLoop mode (deliverSum f mode) terms false 0 0 0 false = _
      rw [sumLoop_eq mode (deliverSum f mode) deliver hdeliver terms,
        collect_eq term spec hterm values.toList terms hcollect]
      rfl

/--
IEEE 754-2019 §9.4 `sum` on decimal data is its kernel form, for every format, rounding
direction and array.
-/
@[kernel_optimize] theorem sum_eq (f : Format) (mode : RoundingMode) (values : Array Datum) :
    Arithmetic.sum f mode values = sum f mode values :=
  (reduce_eq f mode (fun s c q => (s, c, q)) Term.ofDatum (fun _ _ _ => rfl)
    (fun total => total.deliver f mode) (deliverSum_eq f mode) values).symm

/--
IEEE 754-2019 §9.4 `sumAbs` on decimal data is its kernel form, for every format, rounding
direction and array.
-/
@[kernel_optimize] theorem sumAbs_eq (f : Format) (mode : RoundingMode) (values : Array Datum) :
    Arithmetic.sumAbs f mode values = sumAbs f mode values :=
  (reduce_eq f mode (fun _ c q => (false, c, q)) (fun x => (Term.ofDatum x).abs)
    (fun s c q => by
      change Term.finite false |Datum.finiteValue s c q| q = _
      rw [Datum.finiteValue_abs]
      simp [toTerm, Datum.finiteValue])
    (fun total => total.deliverMagnitude f mode)
    (fun seen positive negative quantum zero => by
      rw [deliverMagnitude_totalOf, deliverSum_eq]) values).symm

/--
IEEE 754-2019 §9.4 `sumSquare` on decimal data is its kernel form, for every format, rounding
direction and array.
-/
@[kernel_optimize] theorem sumSquare_eq (f : Format) (mode : RoundingMode)
    (values : Array Datum) :
    Arithmetic.sumSquare f mode values = sumSquare f mode values :=
  (reduce_eq f mode (fun _ c q => (false, Nat.mul c c, Int.add q q))
    (fun x => (Term.ofDatum x).mul (Term.ofDatum x))
    (fun s c q => by
      change Term.finite (s ^^ s) (Datum.finiteValue s c q * Datum.finiteValue s c q) (q + q) = _
      rw [finiteValue_mul, Bool.xor_self]
      rfl)
    (fun total => total.deliverMagnitude f mode)
    (fun seen positive negative quantum zero => by
      rw [deliverMagnitude_totalOf, deliverSum_eq]) values).symm

/--
The fields of the products of the finite data of two lists, pair by pair up to the shorter
list, or `none` when a datum of a pair is not finite (`collectProducts_eq`).
-/
def collectProducts (xs ys : List Datum) : Option (List (Bool × Nat × Int)) :=
  List.rec (motive := fun _ => List Datum → Option (List (Bool × Nat × Int)))
    (fun _ => some [])
    (fun x _ collect ys =>
      List.casesOn (motive := fun _ => Option (List (Bool × Nat × Int))) ys (some [])
        fun y rest =>
          Datum.casesOn (motive := fun _ => Option (List (Bool × Nat × Int))) x
            (fun sx cx qx =>
              Datum.casesOn (motive := fun _ => Option (List (Bool × Nat × Int))) y
                (fun sy cy qy =>
                  Option.casesOn (motive := fun _ => Option (List (Bool × Nat × Int)))
                    (collect rest) none
                    (fun tail => some ((differ sx sy, Nat.mul cx cy, Int.add qx qy) :: tail)))
                (fun _ => none) (fun _ _ _ => none))
            (fun _ => none) (fun _ _ _ => none))
    xs ys

/-- The fields that `collectProducts` returns are the product terms of the specification. -/
theorem collectProducts_eq :
    ∀ (xs ys : List Datum) (terms : List (Bool × Nat × Int)),
      collectProducts xs ys = some terms →
        List.zipWith (fun x y => (Term.ofDatum x).mul (Term.ofDatum y)) xs ys =
          terms.map toTerm
  | [], ys, terms, h => by
      obtain rfl : [] = terms := Option.some.inj h
      simp
  | x :: xs, [], terms, h => by
      obtain rfl : [] = terms := Option.some.inj h
      simp
  | .finite sx cx qx :: xs, .finite sy cy qy :: ys, terms, h => by
      cases htail : collectProducts xs ys with
      | none =>
          have hnone : collectProducts (.finite sx cx qx :: xs) (.finite sy cy qy :: ys) =
              none := by
            change Option.casesOn (motive := fun _ => Option (List (Bool × Nat × Int)))
              (collectProducts xs ys) none
              (fun tail => some ((differ sx sy, Nat.mul cx cy, Int.add qx qy) :: tail)) = none
            rw [htail]
          rw [hnone] at h
          exact absurd h (by simp)
      | some tail =>
          have hsome : collectProducts (.finite sx cx qx :: xs) (.finite sy cy qy :: ys) =
              some ((differ sx sy, Nat.mul cx cy, Int.add qx qy) :: tail) := by
            change Option.casesOn (motive := fun _ => Option (List (Bool × Nat × Int)))
              (collectProducts xs ys) none
              (fun tail => some ((differ sx sy, Nat.mul cx cy, Int.add qx qy) :: tail)) = _
            rw [htail]
          rw [hsome] at h
          obtain rfl : (differ sx sy, Nat.mul cx cy, Int.add qx qy) :: tail = terms :=
            Option.some.inj h
          rw [List.zipWith_cons_cons, List.map_cons, collectProducts_eq xs ys tail htail]
          congr 1
          change Term.finite (sx ^^ sy) (Datum.finiteValue sx cx qx * Datum.finiteValue sy cy qy)
            (qx + qy) = _
          rw [finiteValue_mul, ← differ_eq]
          rfl
  | .finite sx cx qx :: xs, .infinity sy :: ys, terms, h => absurd h (by
      change ¬ ((none : Option (List (Bool × Nat × Int))) = some terms)
      simp)
  | .finite sx cx qx :: xs, .nan sy ty py :: ys, terms, h => absurd h (by
      change ¬ ((none : Option (List (Bool × Nat × Int))) = some terms)
      simp)
  | .infinity sx :: xs, y :: ys, terms, h => absurd h (by
      change ¬ ((none : Option (List (Bool × Nat × Int))) = some terms)
      simp)
  | .nan sx tx px :: xs, y :: ys, terms, h => absurd h (by
      change ¬ ((none : Option (List (Bool × Nat × Int))) = some terms)
      simp)

/--
Kernel form of `Arithmetic.dot` (`dot_eq`): for two arrays of one length whose data are all
finite, the exact sum of the products of the coefficients at the sums of the quantum exponents,
rounded once. Every other case is the specification.
-/
def dot (f : Format) (mode : RoundingMode) (left right : Array Datum) :
    Except Numerics.ReductionError Outcome :=
  Option.casesOn (motive := fun _ => Except Numerics.ReductionError Outcome)
    (collectProducts left.toList right.toList) (Arithmetic.dot f mode left right)
    (fun terms =>
      Bool.casesOn (motive := fun _ => Except Numerics.ReductionError Outcome)
        (Nat.beq left.size right.size) (Arithmetic.dot f mode left right)
        (.ok (sumLoop mode (deliverSum f mode) terms false 0 0 0 false)))

/--
IEEE 754-2019 §9.4 `dot` on decimal data is its kernel form, for every format, rounding
direction and pair of arrays.
-/
@[kernel_optimize] theorem dot_eq (f : Format) (mode : RoundingMode) (left right : Array Datum) :
    Arithmetic.dot f mode left right = dot f mode left right := by
  unfold dot
  cases hcollect : collectProducts left.toList right.toList with
  | none => rfl
  | some terms =>
      cases hsize : Nat.beq left.size right.size with
      | false => rfl
      | true =>
          change _ = Except.ok (sumLoop mode (deliverSum f mode) terms false 0 0 0 false)
          rw [Nat.beq_eq] at hsize
          rw [sumLoop_eq mode (deliverSum f mode) (fun total => total.deliver f mode)
            (deliverSum_eq f mode) terms, ← collectProducts_eq _ _ terms hcollect,
            Arithmetic.dot, ite_eq_left hsize]
          rfl

/-! ## Kernel shapes -/

kernel_shape sumLoop
kernel_shape deliverSum
kernel_shape collect
kernel_shape reduce
kernel_shape sum
kernel_shape sumAbs
kernel_shape sumSquare
kernel_shape collectProducts
kernel_shape dot

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
