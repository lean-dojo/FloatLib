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

Successful `matmul` execution produces exactly one row per left input row and one entry per right
input column. Every output entry is the corresponding executable `dotSequential`. For IEEE
encodings with finite inputs, intermediate values, and results,
`dotSequential_abs_error_le_budget` supplies its numerical error bound.
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
  induction columns generalizing initial with
  | nil =>
      change Except.ok initial = Except.ok output at hloop
      have hEq : initial = output := Except.ok.inj hloop
      subst output
      exact ⟨[], by simp⟩
  | cons column columns ih =>
      rw [List.forIn_cons] at hloop
      cases hdot : dotSequential p row column with
      | error error =>
          cases error with
          | lengthMismatch rowLength columnLength =>
              rw [hdot] at hloop
              change Except.error
                (MatrixShapeError.dotLengthMismatch rowLength columnLength) =
                  Except.ok output at hloop
              contradiction
      | ok value =>
          rw [hdot] at hloop
          have htail :
              forIn columns (initial.push value) (fun column outputRow =>
                match dotSequential p row column with
                | .ok value =>
                    (pure (ForInStep.yield (outputRow.push value)) :
                      Except MatrixShapeError (ForInStep (Array (Model p.output))))
                | .error (.lengthMismatch rowLength columnLength) => do
                    throw (MatrixShapeError.dotLengthMismatch rowLength columnLength)
                    pure (ForInStep.yield outputRow)) = Except.ok output := by
            exact hloop
          obtain ⟨produced, houtput, hproduced⟩ :=
            ih (initial := initial.push value) htail
          refine ⟨value :: produced, ?_, .cons hdot hproduced⟩
          rw [houtput, Array.toList_push]
          simp

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
  induction indices generalizing initial with
  | nil =>
      change Except.ok initial = Except.ok output at hloop
      have hEq : initial = output := Except.ok.inj hloop
      subst output
      exact ⟨[], by simp⟩
  | cons i indices ih =>
      rw [List.forIn_cons] at hloop
      cases hrow :
          forIn columns #[] (fun column outputRow =>
            match dotSequential p A[i]! column with
            | .ok value =>
                (pure (ForInStep.yield (outputRow.push value)) :
                  Except MatrixShapeError (ForInStep (Array (Model p.output))))
            | .error (.lengthMismatch rowLength columnLength) => do
                throw (MatrixShapeError.dotLengthMismatch rowLength columnLength)
                pure (ForInStep.yield outputRow)) with
      | error error =>
          rw [hrow] at hloop
          change Except.error error = Except.ok output at hloop
          contradiction
      | ok row =>
          rw [hrow] at hloop
          have htail :
              forIn indices (initial.push row) (fun i result => do
                let outputRow ←
                  forIn columns #[] (fun column outputRow =>
                    match dotSequential p A[i]! column with
                    | .ok value =>
                        (pure (ForInStep.yield (outputRow.push value)) :
                          Except MatrixShapeError
                            (ForInStep (Array (Model p.output))))
                    | .error (.lengthMismatch rowLength columnLength) => do
                        throw (MatrixShapeError.dotLengthMismatch
                          rowLength columnLength)
                        pure (ForInStep.yield outputRow))
                pure (ForInStep.yield (result.push outputRow))) = Except.ok output := by
            exact hloop
          obtain ⟨rows, houtput, hrows⟩ :=
            ih (initial := initial.push row) htail
          have hrowList :
              forIn columns.toList #[] (fun column outputRow =>
                match dotSequential p A[i]! column with
                | .ok value =>
                    (pure (ForInStep.yield (outputRow.push value)) :
                      Except MatrixShapeError (ForInStep (Array (Model p.output))))
                | .error (.lengthMismatch rowLength columnLength) => do
                    throw (MatrixShapeError.dotLengthMismatch rowLength columnLength)
                    pure (ForInStep.yield outputRow)) = Except.ok row := by
            rw [Array.forIn_toList]
            exact hrow
          obtain ⟨produced, hproducedEq, hproduced⟩ :=
            rowLoop_refines p A[i]! columns.toList #[] row hrowList
          have hrowEq : row.toList = produced := by
            simpa using hproducedEq
          subst produced
          refine ⟨row :: rows, ?_, .cons hproduced hrows⟩
          rw [houtput, Array.toList_push]
          simp

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
dot theorem's IEEE-encoding and local finiteness hypotheses.
-/
theorem matmul_entry_abs_error_le_budget (p : SitePolicy)
    (A B : Matrix p.storage) (C : Matrix p.output)
    (hmatmul : matmul p A B = .ok C)
    (i : Nat) (hi : i < A.size) (j : Nat) (hj : j < ncols B)
    (hstorage : p.storage.isIEEE = true)
    (hproduct : p.product.isIEEE = true)
    (haccumulator : p.accumulator.isIEEE = true)
    (houtput : p.output.isIEEE = true)
    (hfinite : ∀ k < (A[i]!).size,
      MulAccFinite p (A[i]!)[k]! (column B j)[k]!
        (sequentialAccumulator p A[i]! (column B j) k))
    (haccFinite :
      isFinite (sequentialAccumulator p A[i]! (column B j) (A[i]!).size) = true)
    (hresultFinite : isFinite (C[i]!)[j]! = true) :
    |toReal (C[i]!)[j]! -
        sequentialDotReal p A[i]! (column B j) (A[i]!).size| ≤
      epsilonAt p.output
          (toReal (sequentialAccumulator p A[i]! (column B j) (A[i]!).size)) +
        sequentialErrorBudget p A[i]! (column B j) (A[i]!).size := by
  have hdot := (matmul_refines p A B C hmatmul).2 i hi |>.2 j hj
  have hdot' : dotSequential p A[i]! (column B j) = .ok (C[i]!)[j]! := by
    simpa [getElem!_pos A i hi] using hdot
  have hsize : (A[i]!).size = (column B j).size := by
    by_contra hne
    simp [dotSequential, hne] at hdot'
  apply dotSequential_abs_error_le_budget p A[i]! (column B j) (C[i]!)[j]!
    hsize hstorage hproduct haccumulator houtput hfinite haccFinite hresultFinite
  exact hdot'

end Model
end FloatLib.Floats.Formats.BinaryInterchange
