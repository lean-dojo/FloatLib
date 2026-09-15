/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import FloatLib.Floats.Formats.Codebook.Core.Runtime
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Nearest-codeword quantization for finite codebooks

A codebook is a finite table, so the natural quantizer is exhaustive: scan every word, keep the
finite entries, and select one whose denotation is closest to the target. This module provides
that quantizer, `nearestCode`, together with the theorem that its result minimizes the distance
`|x - c|` over all finite codewords `c`.

The tie policy is fixed and simple: the scan runs in ascending order of the unsigned word value,
and a candidate replaces the current best only when it is strictly closer. A tie therefore
resolves to the lower word. Applications that need a different tie rule, or a rule for reserved
words, can still define their own quantizer against the same table.

The scalar type only needs subtraction, negation, and a linear order so that `|x - c|` is
defined and comparable. No ordered-group axioms are used by the minimality proof.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Codebook

universe u

variable {width : Nat} {α : Type u}

/--
All codewords with a finite denotation, paired with that denotation, in ascending order of the
unsigned word value. Exceptional words are omitted.
-/
def finiteEntries (book : Codebook width α) : List (Code book × α) :=
  (List.range (2 ^ width)).filterMap fun bits =>
    match book.denote (BitVec.ofNat width bits) with
    | .finite value => some (BitVec.ofNat width bits, value)
    | _ => none

/-- A word appears in `finiteEntries` with a value exactly when the table decodes it to that
value. -/
theorem mem_finiteEntries_iff (book : Codebook width α) (code : Code book) (value : α) :
    (code, value) ∈ finiteEntries book ↔ book.denote code = .finite value := by
  unfold finiteEntries
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨bits, -, hbits⟩
    split at hbits
    · rename_i hvalue
      simp only [Option.some.injEq, Prod.mk.injEq] at hbits
      obtain ⟨rfl, rfl⟩ := hbits
      exact hvalue
    · exact absurd hbits (by simp)
  · intro hdenote
    refine ⟨code.toNat, List.mem_range.2 code.isLt, ?_⟩
    have hcode : BitVec.ofNat width code.toNat = code := by
      apply BitVec.eq_of_toNat_eq
      simp
    simp [hcode, hdenote]

section Nearest

variable [AddGroup α] [LinearOrder α]

/-- Keep the current best entry unless the candidate is strictly closer to `x`. -/
def closerEntry {book : Codebook width α} (x : α)
    (best : Option (Code book × α)) (entry : Code book × α) : Option (Code book × α) :=
  match best with
  | none => some entry
  | some current => if |x - entry.2| < |x - current.2| then some entry else some current

/--
The first finite codeword whose denotation minimizes `|x - c|`, scanning words in ascending
unsigned order and replacing the current best only on a strict improvement. Ties resolve to the
lower word. The result is `none` exactly when the table has no finite entry.
-/
def nearestCode (book : Codebook width α) (x : α) : Option (Code book) :=
  ((finiteEntries book).foldl (closerEntry x) none).map Prod.fst

/-- Folding `closerEntry` from a present accumulator always yields a present result. -/
theorem foldl_closerEntry_isSome {book : Codebook width α} (x : α)
    (entries : List (Code book × α)) (start : Code book × α) :
    ∃ result, entries.foldl (closerEntry x) (some start) = some result := by
  induction entries generalizing start with
  | nil => exact ⟨start, rfl⟩
  | cons entry rest ih =>
      simp only [List.foldl_cons, closerEntry]
      split
      · exact ih entry
      · exact ih start

/--
The fold invariant behind `nearestCode`: a selected entry comes from the scanned list or the
initial accumulator, and it is at least as close to `x` as every scanned entry and as the initial
accumulator.
-/
theorem foldl_closerEntry_spec {book : Codebook width α} (x : α)
    (entries : List (Code book × α)) (acc : Option (Code book × α))
    (selected : Code book × α)
    (hfold : entries.foldl (closerEntry x) acc = some selected) :
    (selected ∈ entries ∨ acc = some selected) ∧
      (∀ entry ∈ entries, |x - selected.2| ≤ |x - entry.2|) ∧
      (∀ current, acc = some current → |x - selected.2| ≤ |x - current.2|) := by
  induction entries generalizing acc with
  | nil => simp_all
  | cons entry rest ih =>
      obtain ⟨hmem, hrest, hacc⟩ := ih (closerEntry x acc entry) hfold
      cases acc <;> simp only [closerEntry] at hmem hacc <;> grind

/--
The selected codeword is finite and its denotation is at least as close to `x` as the denotation
of every finite codeword in the table.
-/
theorem nearestCode_spec (book : Codebook width α) (x : α) (code : Code book)
    (hnearest : nearestCode book x = some code) :
    ∃ value, book.denote code = .finite value ∧
      ∀ other otherValue, book.denote other = .finite otherValue →
        |x - value| ≤ |x - otherValue| := by
  unfold nearestCode at hnearest
  obtain ⟨selected, hfold, hfirst⟩ := Option.map_eq_some_iff.1 hnearest
  obtain ⟨hmem, hmin, -⟩ := foldl_closerEntry_spec x (finiteEntries book) none selected hfold
  rcases hmem with hmem | hnone
  · refine ⟨selected.2, ?_, ?_⟩
    · rw [← hfirst]
      exact (mem_finiteEntries_iff book selected.1 selected.2).1 hmem
    · intro other otherValue hother
      exact hmin (other, otherValue) ((mem_finiteEntries_iff book other otherValue).2 hother)
  · exact absurd hnone (by simp)

/-- A table with at least one finite word always has a nearest codeword. -/
theorem nearestCode_isSome_of_denote_finite (book : Codebook width α) (x : α)
    {code : Code book} {value : α} (hfinite : book.denote code = .finite value) :
    ∃ nearest, nearestCode book x = some nearest := by
  have hmem := (mem_finiteEntries_iff book code value).2 hfinite
  unfold nearestCode
  obtain ⟨first, rest, hentries⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hentries, List.foldl_cons]
  obtain ⟨result, hresult⟩ :=
    foldl_closerEntry_isSome x rest (book := book) first
  simp only [closerEntry]
  exact ⟨result.1, by rw [hresult]; rfl⟩

end Nearest

end FloatLib.Floats.Formats.Codebook
