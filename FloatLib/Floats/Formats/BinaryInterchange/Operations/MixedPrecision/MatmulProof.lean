/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Matmul
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Proof

/-!
# Shape and entry refinement for mixed-precision matrix multiplication

When `matmul` succeeds, it produces one row per left input row and one entry per right input
column, and each entry is the corresponding executable `dotSequential`. For IEEE encodings with
finite inputs, intermediate values and results, `dotSequential_abs_error_le_budget` then bounds
the numerical error of every entry.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Shape and entry contract for a successful mixed-precision matrix product.

The entry equation preserves the implementation's left-to-right dot-product order.
-/
def MatmulRefines (p : SitePolicy) (A B : Matrix p.storage)
    (C : Matrix p.output) : Prop :=
  C.size = A.size ∧
    ∀ i, (hi : i < A.size) →
      C[i]!.size = ncols B ∧
        ∀ j, (hj : j < ncols B) →
          dotSequential p A[i] (column B j) = .ok (C[i]!)[j]!

/--
A `forIn` loop in `Except` whose step pushes the result of `compute` for each element, and fails
with its error, extends the initial array by values that `compute` produced for the elements, in
order.
-/
private theorem forIn_push_eq_ok {α β ε : Type} (compute : α → Except ε β)
    (step : α → Array β → Except ε (ForInStep (Array β)))
    (hstep : ∀ element accumulator, step element accumulator = do
      let value ← compute element
      pure (ForInStep.yield (accumulator.push value))) :
    ∀ (elements : List α) (initial output : Array β),
      forIn elements initial step = Except.ok output →
        ∃ produced, output.toList = initial.toList ++ produced ∧
          List.Forall₂ (fun element value => compute element = Except.ok value)
            elements produced := by
  intro elements
  induction elements with
  | nil =>
      intro initial output hloop
      have hEq : initial = output := Except.ok.inj hloop
      subst output
      exact ⟨[], by simp, .nil⟩
  | cons element rest ih =>
      intro initial output hloop
      rw [List.forIn_cons, hstep] at hloop
      cases hcompute : compute element with
      | error error =>
          rw [hcompute] at hloop
          contradiction
      | ok value =>
          rw [hcompute] at hloop
          obtain ⟨produced, houtput, hproduced⟩ := ih (initial.push value) output hloop
          exact ⟨value :: produced, by rw [houtput, Array.toList_push]; simp,
            .cons hcompute hproduced⟩

private theorem rowLoop_refines
    (p : SitePolicy) (row : Array (Model p.storage))
    (columns : List (Array (Model p.storage)))
    (initial output : Array (Model p.output))
    (hloop :
      forIn columns initial (fun column outputRow =>
        match dotSequential p row column with
        | .ok value =>
            (pure (ForInStep.yield (outputRow.push value)) :
              Except MatrixShapeError (ForInStep (Array (Model p.output))))
        | .error (.lengthMismatch rowLength columnLength) => do
            throw (MatrixShapeError.dotLengthMismatch rowLength columnLength)
            pure (ForInStep.yield outputRow)) = Except.ok output) :
    ∃ produced,
      output.toList = initial.toList ++ produced ∧
      List.Forall₂
        (fun column value => dotSequential p row column = .ok value)
        columns produced := by
  let compute (column : Array (Model p.storage)) : Except MatrixShapeError (Model p.output) :=
    (dotSequential p row column).mapError fun
      | .lengthMismatch rowLength columnLength => .dotLengthMismatch rowLength columnLength
  obtain ⟨produced, houtput, hproduced⟩ := forIn_push_eq_ok compute _ (by
    intro column outputRow
    simp only [compute]
    cases dotSequential p row column with
    | ok value => rfl
    | error error => cases error; rfl) columns initial output hloop
  refine ⟨produced, houtput, hproduced.imp fun column value hvalue => ?_⟩
  cases hdot : dotSequential p row column with
  | ok result =>
      simp only [compute, hdot, Except.mapError] at hvalue
      rw [Except.ok.inj hvalue]
  | error error =>
      cases error
      simp [compute, hdot, Except.mapError] at hvalue

private theorem matrixLoop_refines
    (p : SitePolicy) (A : Matrix p.storage)
    (columns : Array (Array (Model p.storage)))
    (indices : List Nat)
    (initial output : Matrix p.output)
    (hloop :
      forIn indices initial (fun i result => do
        let outputRow ←
          forIn columns #[] (fun column outputRow =>
            match dotSequential p A[i]! column with
            | .ok value =>
                (pure (ForInStep.yield (outputRow.push value)) :
                  Except MatrixShapeError (ForInStep (Array (Model p.output))))
            | .error (.lengthMismatch rowLength columnLength) => do
                throw (MatrixShapeError.dotLengthMismatch rowLength columnLength)
                pure (ForInStep.yield outputRow))
        pure (ForInStep.yield (result.push outputRow))) = Except.ok output) :
    ∃ produced,
      output.toList = initial.toList ++ produced ∧
      List.Forall₂
        (fun i row =>
          List.Forall₂
            (fun column value => dotSequential p A[i]! column = .ok value)
            columns.toList row.toList)
        indices produced := by
  obtain ⟨produced, houtput, hproduced⟩ :=
    forIn_push_eq_ok _ _ (fun _ _ => rfl) indices initial output hloop
  refine ⟨produced, houtput, hproduced.imp fun i row hrow => ?_⟩
  rw [← Array.forIn_toList] at hrow
  obtain ⟨cells, hcellsEq, hcells⟩ := rowLoop_refines p A[i]! columns.toList #[] row hrow
  have hrowEq : row.toList = cells := by
    simpa using hcellsEq
  rw [hrowEq]
  exact hcells

/--
Every successful mixed-precision matrix multiplication satisfies its shape and entry contract.
-/
theorem matmul_refines (p : SitePolicy) (A B : Matrix p.storage)
    (C : Matrix p.output) (hresult : matmul p A B = .ok C) :
    MatmulRefines p A B C := by
  simp only [matmul] at hresult
  split at hresult <;> try contradiction
  split at hresult <;> try contradiction
  split at hresult <;> try contradiction
  have hloop :
      forIn (List.range A.size) #[] (fun i result => do
        let outputRow ←
          forIn (Array.ofFn (n := ncols B) fun j => column B j.val) #[]
              (fun column outputRow =>
            match dotSequential p A[i]! column with
            | .ok value =>
                (pure (ForInStep.yield (outputRow.push value)) :
                  Except MatrixShapeError (ForInStep (Array (Model p.output))))
            | .error (.lengthMismatch rowLength columnLength) => do
                throw (MatrixShapeError.dotLengthMismatch rowLength columnLength)
                pure (ForInStep.yield outputRow))
        pure (ForInStep.yield (result.push outputRow))) = Except.ok C := by
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size] at hresult
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure] at hresult
    convert hresult using 1
    rw [List.range_eq_range']
    rfl
  obtain ⟨rows, hrowsEq, hrows⟩ :=
    matrixLoop_refines p A
      (Array.ofFn (n := ncols B) fun j => column B j.val)
      (List.range A.size) #[] C hloop
  have hCList : C.toList = rows := by simpa using hrowsEq
  subst rows
  have hsize : C.size = A.size := by simpa using hrows.length_eq.symm
  refine ⟨hsize, ?_⟩
  · intro i hi
    have hiC : i < C.size := by simpa [hsize] using hi
    have hrow :
        List.Forall₂
          (fun column value => dotSequential p A[i]! column = .ok value)
          (Array.ofFn (n := ncols B) fun j => column B j.val).toList
          C[i].toList := by
      have hrow := hrows.get (by simpa using hi) (by simpa using hiC)
      simp only [List.get_eq_getElem, List.getElem_range] at hrow
      exact hrow
    constructor
    · rw [getElem!_pos C i hiC]
      simpa using hrow.length_eq.symm
    · intro j hj
      have hjColumns :
          j < (Array.ofFn (n := ncols B) fun j => column B j.val).size := by
        simpa using hj
      have hrowSize :
          C[i].size = (Array.ofFn (n := ncols B) fun j => column B j.val).size := by
        simpa using hrow.length_eq.symm
      have hjRow : j < C[i].size := by simpa [hrowSize] using hjColumns
      have hentry := hrow.get (by simpa using hjColumns) (by simpa using hjRow)
      simp only [List.get_eq_getElem] at hentry
      rw [Array.getElem_toList, Array.getElem_toList] at hentry
      rw [getElem!_pos C i hiC, getElem!_pos C[i] j hjRow]
      simpa [getElem!_pos A i hi] using hentry

/--
The sequential-dot budget bounds a selected entry of a successful matrix product, under the
dot theorem's encoding and local finiteness hypotheses.
-/
theorem matmul_entry_abs_error_le_budget (p : SitePolicy)
    (A B : Matrix p.storage) (C : Matrix p.output)
    (hmatmul : matmul p A B = .ok C)
    (i : Nat) (hi : i < A.size) (j : Nat) (hj : j < ncols B)
    (hproduct : p.product.isIEEE = true)
    (haccumulator : p.accumulator.isIEEE = true)
    (houtput : p.output.isIEEE = true)
    (hfinite : ∀ k < (A[i]!).size,
      MulAccFinite p (A[i]!)[k]! (column B j)[k]!
        (sequentialAccumulator p A[i]! (column B j) k))
    (hresultFinite : isFinite (C[i]!)[j]! = true) :
    |toReal (C[i]!)[j]! -
        sequentialDotReal p A[i]! (column B j) (A[i]!).size| ≤
      halfUlpAt p.output
          (toReal (sequentialAccumulator p A[i]! (column B j) (A[i]!).size)) +
        sequentialErrorBudget p A[i]! (column B j) (A[i]!).size := by
  have hdot := (matmul_refines p A B C hmatmul).2 i hi |>.2 j hj
  have hdot' : dotSequential p A[i]! (column B j) = .ok (C[i]!)[j]! := by
    simpa [getElem!_pos A i hi] using hdot
  exact dotSequential_abs_error_le_budget p A[i]! (column B j) (C[i]!)[j]!
    hproduct haccumulator houtput hfinite hresultFinite hdot'

end Model
end FloatLib.Floats.Formats.BinaryInterchange
