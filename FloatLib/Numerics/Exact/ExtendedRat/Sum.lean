/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.ExtendedRat.Algebra
public import FloatLib.Numerics.Quantization.Block.Reduction
public import Mathlib.Data.List.Induction

/-!
# Exact reduction of extended rational values

The reduction starts at positive zero and follows the list order. Associativity allows block
totals to be flattened without changing any finite, infinite, or exceptional result. Completed
sums use canonical NaN; no identity law for arbitrary exceptional tags is assumed.

The public `Block.Extended` namespace is retained for existing clients.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Block.Extended

/-- Ordered exact reduction with a positive-zero identity, in the closed extended-rational
arithmetic `P3109.Arithmetic`: NaN is absorbing and opposite infinities give NaN. -/
def sum (values : List (NumericalValue Rat)) : NumericalValue Rat :=
  Reduction.exact.run values

private theorem foldl_finite (values : List Rat) (initial : Rat) :
    (values.map NumericalValue.finite).foldl P3109.Arithmetic.Add (.finite initial) =
      .finite (initial + values.sum) := by
  induction values generalizing initial with
  | nil => simp
  | cons value values ih =>
    simp only [List.map_cons, List.foldl_cons, P3109.Arithmetic.Add, ih, List.sum_cons]
    rw [add_assoc]

/-- Exact finite reduction agrees with the algebraic sum, independently of cancellation. -/
theorem sum_finite (values : List Rat) :
    sum (values.map NumericalValue.finite) = .finite values.sum := by
  simpa [sum, Reduction.run, Reduction.fold, Reduction.exact] using foldl_finite values 0

/-- A left fold that starts at or meets an absorbing value ends there, when every term and the
start lie in a class that the step keeps and that the absorbing value absorbs from either side. -/
private theorem foldl_eq_of_absorbing {α : Type} (step : α → α → α) (absorbing : α)
    (P : α → Prop) (hleft : ∀ x, P x → step absorbing x = absorbing)
    (hright : ∀ x, P x → step x absorbing = absorbing)
    (hclosed : ∀ x y, P x → P y → P (step x y)) :
    ∀ (values : List α) (initial : α), P initial → (∀ x ∈ values, P x) →
      absorbing ∈ values ∨ initial = absorbing → values.foldl step initial = absorbing := by
  intro values
  induction values with
  | nil => rintro initial - - (h | rfl) <;> simp_all
  | cons value values ih =>
    intro initial hinitial hvalues hmem
    have hvalue := hvalues value List.mem_cons_self
    refine ih (step initial value) (hclosed _ _ hinitial hvalue)
      (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)) ?_
    rcases hmem with hmem | rfl
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inr (hright _ hinitial)
      · exact Or.inl hmem
    · exact Or.inr (hleft _ hvalue)

/-- An infinity survives a reduction whose other terms are finite or infinities of the same sign. -/
theorem sum_eq_infinity (values : List (NumericalValue Rat)) (sign : Bool)
    (h : ∀ value ∈ values, (∃ q, value = .finite q) ∨ value = .infinity sign)
    (hmem : .infinity sign ∈ values) :
    sum values = .infinity sign := by
  refine foldl_eq_of_absorbing P3109.Arithmetic.Add (.infinity sign)
    (fun value => (∃ q, value = .finite q) ∨ value = .infinity sign) ?_ ?_ ?_ values _
    (Or.inl ⟨0, rfl⟩) h (Or.inl hmem)
  · rintro x (⟨q, rfl⟩ | rfl) <;> simp [P3109.Arithmetic.Add]
  · rintro x (⟨q, rfl⟩ | rfl) <;> simp [P3109.Arithmetic.Add]
  · rintro x y (⟨a, rfl⟩ | rfl) (⟨b, rfl⟩ | rfl) <;> simp [P3109.Arithmetic.Add]

/-- One NaN term makes an exact reduction NaN, wherever it stands. -/
theorem sum_eq_nan_of_mem (values : List (NumericalValue Rat))
    (h : .exceptional .nan ∈ values) : sum values = .exceptional .nan :=
  foldl_eq_of_absorbing P3109.Arithmetic.Add (.exceptional .nan) (fun _ => True)
    (fun _ _ => rfl) (fun x _ => by cases x <;> rfl) (fun _ _ _ _ => trivial) values _ trivial
    (fun _ _ => trivial) (Or.inl h)

/-- Extended rational addition associates, including infinite and exceptional cases. -/
local instance : Std.Associative P3109.Arithmetic.Add := ⟨P3109.Arithmetic.add_assoc⟩

/-- A completed exact sum is unchanged by adding zero. -/
theorem sum_add_zero (values : List (NumericalValue Rat)) :
    P3109.Arithmetic.Add (sum values) (.finite 0) = sum values := by
  rw [P3109.Arithmetic.add_comm]
  have hz : P3109.Arithmetic.Add (.finite 0) (.finite 0) = .finite 0 := by
    simp [P3109.Arithmetic.Add]
  simpa only [sum, Reduction.run, Reduction.fold, Reduction.exact, id_eq, hz] using
    (List.foldl_assoc (op := P3109.Arithmetic.Add) (l := values)
    (a₁ := .finite 0) (a₂ := .finite 0)).symm

/-- Concatenating lists adds their exact sums, including exceptional cases. -/
theorem sum_append (left right : List (NumericalValue Rat)) :
    sum (left ++ right) = P3109.Arithmetic.Add (sum left) (sum right) := by
  change (left ++ right).foldl P3109.Arithmetic.Add (.finite 0) = _
  rw [List.foldl_append]
  change right.foldl P3109.Arithmetic.Add (sum left) = P3109.Arithmetic.Add (sum left)
    (right.foldl P3109.Arithmetic.Add (.finite 0))
  rw [← List.foldl_assoc (op := P3109.Arithmetic.Add) (l := right) (a₁ := sum left) (a₂ :=
    .finite 0),
    sum_add_zero]

/-- Summing blocks separately agrees with their flattened exact reduction. -/
theorem sum_flatten (blocks : List (List (NumericalValue Rat))) :
    sum blocks.flatten = sum (blocks.map sum) := by
  induction blocks using List.reverseRecOn with
  | nil => rfl
  | append_singleton blocks block ih =>
    rw [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      sum_append, ih, List.map_append, List.map_singleton, sum_append]
    congr 1
    change sum block = P3109.Arithmetic.Add (.finite 0) (sum block)
    rw [P3109.Arithmetic.add_comm, sum_add_zero]


end FloatLib.Floats.Formats.Block.Extended
