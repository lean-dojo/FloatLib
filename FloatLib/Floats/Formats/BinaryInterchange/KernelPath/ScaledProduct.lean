/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.FormatOf
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime

/-!
# The scaled products on encodings

IEEE 754-2019 §9.4 `scaledProd`, `scaledProdSum` and `scaledProdDiff` deliver a product with a
scale factor. The reference folds the factors into a `ProductState`, which keeps the exact
product of the finite factors apart from the NaNs and infinities, and finishes it by scaling
the product to the exponent of its leading bit and rounding once.

This module runs the same fold on lists of encodings. `factor source destination a` is the
factor that the word `a` is: its exact value `KernelPath.decode` when it is finite, and the
reference rule on the decoded word otherwise (`factor_eq`). `finishProduct` encodes the
finished state: for a nonzero product of finite factors it is `KernelPath.roundDyadic` of the
scaled product, with the scale factor, and the reference rule otherwise (`finishProduct_eq`).

`scaledProd` and `scaledProdOfSums` are the reductions on lists of encodings, and
`scaledProd_eq_spec` and `scaledProdOfSums_eq_spec` prove them equal to the reference
reductions with the product encoded, for all descriptors, every rounding direction and all
operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open Model.Reduction.Internal (Factor ProductState)

variable {source left right destination : FloatFormat}

/--
The factor that the word `a` of `source` is (`factor_eq`): its exact value when it is finite,
and the reference rule for a NaN or an infinity.
-/
def factor (source destination : FloatFormat) (a : Nat) : Factor destination :=
  Bool.casesOn (motive := fun _ => Factor destination) (Nat.beq (finiteCode source a) 1)
    (Factor.ofValue (Model.ofNatBits a : Model source))
    (.finite (decode source a))

/-- `factor` is the factor of the decoded word. -/
theorem factor_eq (x : Model source) :
    factor source destination x.toNatBits = Factor.ofValue x := by
  unfold factor
  rw [finiteCode_eq, Model.ofNatBits_toNatBits]
  cases hfinite : Model.isFinite x
  · rfl
  · exact (Factor.ofValue_of_toDyadic?_eq_some (toDyadic?_eq_decode x hfinite)).symm

/--
The exact sum of the factors that the words `a` of `left` and `b` of `right` are
(`factorSum_eq`): the exact sum of two finite words by `addExact`, and the reference rule
otherwise.
-/
def factorSum (left right destination : FloatFormat) (a b : Nat) : Factor destination :=
  Bool.casesOn (motive := fun _ => Factor destination) (bothFinite left right a b)
    (Factor.add (factor left destination a) (factor right destination b))
    (.finite (addExact (decode left a) (decode right b)))

/-- `factorSum` is the sum of the factors of the decoded words. -/
theorem factorSum_eq (x : Model left) (y : Model right) :
    factorSum left right destination x.toNatBits y.toNatBits =
      Factor.add (Factor.ofValue x) (Factor.ofValue y) := by
  unfold factorSum
  rw [bothFinite_eq, factor_eq, factor_eq]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · rw [Factor.ofValue_of_toDyadic?_eq_some (toDyadic?_eq_decode x hx),
        Factor.ofValue_of_toDyadic?_eq_some (toDyadic?_eq_decode y hy), addExact_eq]
      rfl

/--
The finished state with its product encoded (`finishProduct_eq`): for a nonzero product of
finite factors, one rounding of the product scaled to the exponent of its leading bit, with
that exponent as the scale factor, and the reference rule otherwise.
-/
def finishProduct (destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (state : ProductState destination) : ScaledProduct Nat :=
  Bool.casesOn (motive := fun _ => ScaledProduct Nat)
    (state.signalingNaN.isNone && state.quietNaN.isNone && !state.generatedInvalid &&
      !state.sawInfinity && !Nat.beq state.exact.significand 0)
    ((state.finish mode).map Model.toNatBits)
    ((fun scaled : Numerics.Dyadic =>
        { product := roundDyadic destination mode scaled
          scaleFactor :=
            Kernel.Z.add (Int.ofNat (Kernel.log2 state.exact.significand)) state.exact.exponent
          status :=
            { inexact := (Model.dyadicRoundingStatus destination mode scaled
                (Model.Internal.Directed.roundDyadic destination mode scaled)).inexact } })
      { state.exact with
        exponent := Kernel.Z.neg (Int.ofNat (Kernel.log2 state.exact.significand)) })

/-- `finishProduct` is the finished state of the reference with its product encoded. -/
theorem finishProduct_eq (mode : Model.IEEERoundingMode) (state : ProductState destination) :
    finishProduct destination mode state = (state.finish mode).map Model.toNatBits := by
  unfold finishProduct
  cases hfast : (state.signalingNaN.isNone && state.quietNaN.isNone &&
      !state.generatedInvalid && !state.sawInfinity && !Nat.beq state.exact.significand 0)
  · rfl
  · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
      beq_zero_eq] at hfast
    obtain ⟨⟨⟨⟨hsignaling, hquiet⟩, hinvalid⟩, hinfinity⟩, hzero⟩ := hfast
    unfold ProductState.finish
    simp only [hsignaling, hquiet, hinvalid, hinfinity, hzero, Bool.false_and, Bool.or_self,
      Bool.false_eq_true, ite_false, ScaledProduct.map, roundDyadic_eq, Kernel.log2_eq,
      Kernel.Z.add_eq, Kernel.Z.neg_eq, Int.ofNat_eq_natCast]

/--
The scaled product of the values that `words` encode in `source`, with the product encoded in
`destination` (`scaledProd_eq_spec`).
-/
def scaledProd (source destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (words : List Nat) : ScaledProduct Nat :=
  finishProduct destination mode
    (words.foldl (fun state a => state.push (factor source destination a)) {})

/-- The fold of the factors of encodings is the reference fold over the values. -/
theorem foldl_push_factor (values : List (Model source)) (state : ProductState destination) :
    (values.map Model.toNatBits).foldl
        (fun state a => state.push (factor source destination a)) state =
      values.foldl (fun state value => state.push (Factor.ofValue value)) state := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, factor_eq, ih]

/--
`scaledProd` computes `Model.scaledProd destination values mode` with its product encoded, for
every source and destination descriptor, every rounding direction and all operands.
-/
theorem scaledProd_eq_spec (mode : Model.IEEERoundingMode) (values : Array (Model source)) :
    scaledProd source destination mode (values.toList.map Model.toNatBits) =
      (Model.scaledProd destination values mode).map Model.toNatBits := by
  unfold scaledProd Model.scaledProd
  rw [finishProduct_eq, foldl_push_factor, Array.foldl_toList]

/--
The scaled product of the sums (`subtract := false`) or differences (`subtract := true`) of
the values that `as` encode in `left` and `bs` in `right`, with the product encoded in
`destination`, or the length mismatch (`scaledProdOfSums_eq_spec`).
-/
def scaledProdOfSums (left right destination : FloatFormat) (subtract : Bool)
    (mode : Model.IEEERoundingMode) (as bs : List Nat) :
    Except Numerics.ReductionError (ScaledProduct Nat) :=
  Bool.casesOn (motive := fun _ => Except Numerics.ReductionError (ScaledProduct Nat))
    (Nat.beq as.length bs.length)
    (.error (.lengthMismatch as.length bs.length))
    (.ok (finishProduct destination mode
      ((as.zip bs).foldl
        (fun state pair =>
          state.push
            (factorSum left right destination pair.1
              (Bool.casesOn (motive := fun _ => Nat) subtract pair.2 (neg right pair.2))))
        {})))

/-- The fold of the sums of factors of encodings is the reference fold over the values. -/
theorem foldl_push_sum (subtract : Bool) (pairs : List (Model left × Model right))
    (state : ProductState destination) :
    (pairs.map fun pair => (pair.1.toNatBits, pair.2.toNatBits)).foldl
        (fun state pair =>
          state.push
            (factorSum left right destination pair.1
              (Bool.casesOn (motive := fun _ => Nat) subtract pair.2 (neg right pair.2))))
        state =
      pairs.foldl
        (fun state pair =>
          state.push
            (Factor.add (Factor.ofValue pair.1)
              (Factor.ofValue (if subtract then Model.neg pair.2 else pair.2))))
        state := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
      congr 2
      cases subtract
      · exact factorSum_eq pair.1 pair.2
      · change factorSum left right destination pair.1.toNatBits
          (neg right pair.2.toNatBits) = _
        rw [neg_eq_spec, factorSum_eq]
        rfl

/--
`scaledProdOfSums` computes the reference reduction with its product encoded, for all
descriptors, both operations, every rounding direction and all operands.
-/
theorem scaledProdOfSums_eq_spec (subtract : Bool) (mode : Model.IEEERoundingMode)
    (xs : Array (Model left)) (ys : Array (Model right)) :
    scaledProdOfSums left right destination subtract mode (xs.toList.map Model.toNatBits)
        (ys.toList.map Model.toNatBits) =
      (Model.Reduction.Internal.scaledProdOfSums destination xs ys subtract mode).map
        (ScaledProduct.map Model.toNatBits) := by
  have hzip : (xs.toList.map Model.toNatBits).zip (ys.toList.map Model.toNatBits) =
      (xs.toList.zip ys.toList).map fun pair => (pair.1.toNatBits, pair.2.toNatBits) := by
    rw [List.zip_map]
    rfl
  unfold scaledProdOfSums Model.Reduction.Internal.scaledProdOfSums
  simp only [List.length_map, Array.length_toList]
  by_cases hsize : xs.size = ys.size
  · have hbeq : Nat.beq xs.size ys.size = true := Nat.beq_eq_true_eq _ _ ▸ hsize
    rw [ite_eq_left hsize, hbeq, finishProduct_eq, hzip, foldl_push_sum, ← Array.toList_zip,
      Array.foldl_toList]
    rfl
  · have hbeq : Nat.beq xs.size ys.size = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      exact hsize
    rw [ite_eq_right hsize, hbeq]
    rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
