/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Accumulation

/-!
# Error bounds for mixed-precision accumulation

Real-error decompositions and absolute bounds for `mulAcc` and `dotSequential`. Each step's bound
accounts for both input casts, multiplication, the cast to the accumulator, and addition. The dot
bound also includes the final output cast. The bounds assume IEEE encodings and finite values
throughout; their local half-ULP terms cover subnormals as well as normal values.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- All values encountered by one unfused mixed-precision multiply-accumulate are finite. -/
def MulAccFinite (p : SitePolicy) (a b : Model p.storage)
    (acc : Model p.accumulator) : Prop :=
  let aP := cast p.storage p.product a
  let bP := cast p.storage p.product b
  let product := mul aP bP
  let productA := cast p.product p.accumulator product
  isFinite a = true ∧ isFinite b = true ∧
    isFinite aP = true ∧ isFinite bP = true ∧
    isFinite product = true ∧ isFinite productA = true ∧
    isFinite acc = true ∧ isFinite (add productA acc) = true

/--
Sum of the local half-ULP budgets in one mixed-precision multiply-accumulate.

The input-cast terms include the factors introduced when the rounded operands are multiplied.
-/
noncomputable def mulAccErrorBudget (p : SitePolicy) (a b : Model p.storage)
    (acc : Model p.accumulator) : ℝ :=
  let aP := cast p.storage p.product a
  let bP := cast p.storage p.product b
  let product := mul aP bP
  let productA := cast p.product p.accumulator product
  epsilonAt p.product (toReal a) * |toReal b| +
    |toReal aP| * epsilonAt p.product (toReal b) +
    epsilonAt p.product (toReal aP * toReal bP) +
    epsilonAt p.accumulator (toReal product) +
    epsilonAt p.accumulator (toReal productA + toReal acc)

/-- Real error introduced by one mixed-precision multiply-accumulate step. -/
noncomputable def mulAccError (p : SitePolicy) (a b : Model p.storage)
    (acc : Model p.accumulator) : ℝ :=
  toReal (mulAcc p a b acc) - (toReal a * toReal b + toReal acc)

/--
The error of one mixed-precision multiply-accumulate is exactly the sum of its five site
residuals.

This algebraic identity needs no finiteness hypotheses. To interpret the residuals as rounding
errors, use the finiteness premises of `mulAcc_abs_error_le_budget`: `toReal` maps exceptional
values to zero and does not describe their NaN or infinity behavior.
-/
theorem mulAccError_eq_site_residuals (p : SitePolicy) (a b : Model p.storage)
    (acc : Model p.accumulator) :
    let aP := cast p.storage p.product a
    let bP := cast p.storage p.product b
    let product := mul aP bP
    let productA := cast p.product p.accumulator product
    mulAccError p a b acc =
      (toReal aP - toReal a) * toReal b +
      toReal aP * (toReal bP - toReal b) +
      (toReal product - toReal aP * toReal bP) +
      (toReal productA - toReal product) +
      (toReal (add productA acc) - (toReal productA + toReal acc)) := by
  simp only [mulAccError, mulAcc]
  ring

/--
One finite mixed-precision multiply-accumulate differs from the exact source-value operation by
at most the sum of the local cast, multiply, cast, and add budgets.
-/
theorem mulAcc_abs_error_le_budget (p : SitePolicy) (a b : Model p.storage)
    (acc : Model p.accumulator)
    (hstorage : p.storage.isIEEE = true)
    (hproduct : p.product.isIEEE = true)
    (haccumulator : p.accumulator.isIEEE = true)
    (hfinite : MulAccFinite p a b acc) :
    |mulAccError p a b acc| ≤ mulAccErrorBudget p a b acc := by
  let aP := cast p.storage p.product a
  let bP := cast p.storage p.product b
  let product := mul aP bP
  let productA := cast p.product p.accumulator product
  rcases hfinite with ⟨ha, hb, haP, hbP, hproductFinite, hproductA, hacc, hresult⟩
  have haError := abs_toReal_cast_sub_le a hstorage hproduct ha haP
  have hbError := abs_toReal_cast_sub_le b hstorage hproduct hb hbP
  have hmulError := abs_toReal_mul_sub_le aP bP hproduct haP hbP hproductFinite
  have hproductCastError :=
    abs_toReal_cast_sub_le product hproduct haccumulator hproductFinite hproductA
  have haddError := abs_toReal_add_sub_le productA acc haccumulator hproductA hacc hresult
  have habs : ∀ u v w x y : ℝ, |u + v + w + x + y| ≤ |u| + |v| + |w| + |x| + |y| := by
    intro u v w x y
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact abs_add_le _ _
  rw [mulAccError_eq_site_residuals]
  dsimp only [mulAccErrorBudget]
  refine (habs _ _ _ _ _).trans ?_
  rw [abs_mul, abs_mul]
  gcongr

/-- Accumulator state after the first `count` sequential product-add sites. -/
def sequentialAccumulator (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (count : Nat) : Model p.accumulator :=
  (List.range count).foldl
    (fun acc i ↦ mulAcc p xs[i]! ys[i]! acc)
    (posZero p.accumulator)

/-- Exact real dot product of the first `count` source-value pairs. -/
noncomputable def sequentialDotReal (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (count : Nat) : ℝ :=
  ∑ i ∈ Finset.range count, toReal xs[i]! * toReal ys[i]!

/-- Sum of the local error budgets along the actual sequential accumulator path. -/
noncomputable def sequentialErrorBudget (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (count : Nat) : ℝ :=
  ∑ i ∈ Finset.range count,
    mulAccErrorBudget p xs[i]! ys[i]! (sequentialAccumulator p xs ys i)

/--
The executable accumulator's error is the sum of its local errors, evaluated at the successive
accumulator states.
-/
theorem sequentialAccumulator_error_eq_sum (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (count : Nat)
    (haccumulator : p.accumulator.isIEEE = true) :
    toReal (sequentialAccumulator p xs ys count) - sequentialDotReal p xs ys count =
      ∑ i ∈ Finset.range count,
        mulAccError p xs[i]! ys[i]! (sequentialAccumulator p xs ys i) := by
  induction count with
  | zero => simp [sequentialAccumulator, sequentialDotReal, haccumulator]
  | succ count ih =>
      rw [sequentialAccumulator, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [sequentialDotReal, Finset.sum_range_succ, Finset.sum_range_succ]
      change toReal
          (mulAcc p xs[count]! ys[count]! (sequentialAccumulator p xs ys count)) -
          (sequentialDotReal p xs ys count +
            toReal xs[count]! * toReal ys[count]!) =
        (∑ i ∈ Finset.range count,
          mulAccError p xs[i]! ys[i]! (sequentialAccumulator p xs ys i)) +
          mulAccError p xs[count]! ys[count]! (sequentialAccumulator p xs ys count)
      rw [← ih]
      simp only [mulAccError]
      ring

/--
The absolute error of a finite sequential accumulator is bounded by the sum of its local
budgets. Finiteness is required along the executed prefix states; storage, product, and
accumulator may use different IEEE formats.
-/
theorem sequentialAccumulator_abs_error_le_budget (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (count : Nat)
    (hstorage : p.storage.isIEEE = true)
    (hproduct : p.product.isIEEE = true)
    (haccumulator : p.accumulator.isIEEE = true)
    (hfinite : ∀ i < count,
      MulAccFinite p xs[i]! ys[i]! (sequentialAccumulator p xs ys i)) :
    |toReal (sequentialAccumulator p xs ys count) - sequentialDotReal p xs ys count| ≤
      sequentialErrorBudget p xs ys count := by
  rw [sequentialAccumulator_error_eq_sum p xs ys count haccumulator]
  calc
    |∑ i ∈ Finset.range count,
        mulAccError p xs[i]! ys[i]! (sequentialAccumulator p xs ys i)| ≤
        ∑ i ∈ Finset.range count,
          |mulAccError p xs[i]! ys[i]! (sequentialAccumulator p xs ys i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ sequentialErrorBudget p xs ys count := by
      apply Finset.sum_le_sum
      intro i hi
      exact mulAcc_abs_error_le_budget p xs[i]! ys[i]!
        (sequentialAccumulator p xs ys i) hstorage hproduct haccumulator
        (hfinite i (Finset.mem_range.mp hi))

/-- The executable dot loop is the prefix accumulator followed by its one output cast. -/
theorem dotSequential_eq_cast_sequentialAccumulator (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (hsize : xs.size = ys.size) :
    dotSequential p xs ys =
      .ok (cast p.accumulator p.output (sequentialAccumulator p xs ys xs.size)) := by
  simp [dotSequential, hsize, sequentialAccumulator,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    ← List.range_eq_range']

/--
A successful finite mixed-precision dot product is bounded by all per-step budgets plus the final
accumulator-to-output cast budget, following the reduction order of `dotSequential`.
-/
theorem dotSequential_abs_error_le_budget (p : SitePolicy)
    (xs ys : Array (Model p.storage)) (result : Model p.output)
    (hsize : xs.size = ys.size)
    (hstorage : p.storage.isIEEE = true)
    (hproduct : p.product.isIEEE = true)
    (haccumulator : p.accumulator.isIEEE = true)
    (houtput : p.output.isIEEE = true)
    (hfinite : ∀ i < xs.size,
      MulAccFinite p xs[i]! ys[i]! (sequentialAccumulator p xs ys i))
    (haccFinite : isFinite (sequentialAccumulator p xs ys xs.size) = true)
    (hresultFinite : isFinite result = true)
    (hresult : dotSequential p xs ys = .ok result) :
    |toReal result - sequentialDotReal p xs ys xs.size| ≤
      epsilonAt p.output (toReal (sequentialAccumulator p xs ys xs.size)) +
        sequentialErrorBudget p xs ys xs.size := by
  have hresultEq :
      result = cast p.accumulator p.output (sequentialAccumulator p xs ys xs.size) := by
    rw [dotSequential_eq_cast_sequentialAccumulator p xs ys hsize] at hresult
    exact Except.ok.inj hresult.symm
  subst result
  have hcast := abs_toReal_cast_sub_le (sequentialAccumulator p xs ys xs.size)
    haccumulator houtput haccFinite hresultFinite
  have haccError := sequentialAccumulator_abs_error_le_budget p xs ys xs.size
    hstorage hproduct haccumulator hfinite
  calc
    |toReal (cast p.accumulator p.output (sequentialAccumulator p xs ys xs.size)) -
        sequentialDotReal p xs ys xs.size| =
        |(toReal (cast p.accumulator p.output (sequentialAccumulator p xs ys xs.size)) -
            toReal (sequentialAccumulator p xs ys xs.size)) +
          (toReal (sequentialAccumulator p xs ys xs.size) -
            sequentialDotReal p xs ys xs.size)| := by ring_nf
    _ ≤
        |toReal (cast p.accumulator p.output (sequentialAccumulator p xs ys xs.size)) -
          toReal (sequentialAccumulator p xs ys xs.size)| +
        |toReal (sequentialAccumulator p xs ys xs.size) -
          sequentialDotReal p xs ys xs.size| := abs_add_le _ _
    _ ≤ epsilonAt p.output (toReal (sequentialAccumulator p xs ys xs.size)) +
        sequentialErrorBudget p xs ys xs.size := add_le_add hcast haccError

end Model
end FloatLib.Floats.Formats.BinaryInterchange
