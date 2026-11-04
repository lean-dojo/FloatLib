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
that quantizer, `nearestCode`, together with the theorems that its result minimizes the distance
`|x - c|` over all finite codewords `c` and that among the minimizers it is the lowest word.

Ties follow one fixed, simple rule. The scan runs in ascending order of the unsigned word value,
and a candidate replaces the current best only when it is strictly closer, so a tie resolves to
the lower word. Applications that need a different tie rule, or a rule for reserved words, can
define their own quantizer against the same table.

For the scalar type, subtraction, negation, and a linear order are enough to define and compare
`|x - c|`, and the minimality proof uses no ordered-group axioms.
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

/-- A word appears in `finiteEntries` with a value if and only if the table decodes it to that
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

/-- `finiteEntries` lists its words in strictly ascending unsigned order. -/
theorem finiteEntries_pairwise (book : Codebook width α) :
    (finiteEntries book).Pairwise (fun left right => left.1.toNat < right.1.toNat) := by
  unfold finiteEntries
  have hrange : (List.range (2 ^ width)).Pairwise (fun a b => a < b ∧ b < 2 ^ width) :=
    List.pairwise_lt_range.imp_of_mem fun _ hb hab => ⟨hab, List.mem_range.1 hb⟩
  refine hrange.filterMap _ ?_
  intro a b hab left hleft right hright
  split at hleft <;> simp only [Option.some.injEq, reduceCtorEq] at hleft
  split at hright <;> simp only [Option.some.injEq, reduceCtorEq] at hright
  subst left right
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (hab.1.trans hab.2), Nat.mod_eq_of_lt hab.2]
  exact hab.1

section Nearest

variable [AddGroup α] [LinearOrder α]

/-- Keep the current best entry unless the candidate is strictly closer to `x`. -/
def closerEntry {book : Codebook width α} (x : α)
    (best : Option (Code book × α)) (entry : Code book × α) : Option (Code book × α) :=
  match best with
  | none => some entry
  | some current => if |x - entry.2| < |x - current.2| then some entry else some current

/-- Cache the distance of a selected word while scanning the remaining entries. -/
private def withDistance {book : Codebook width α} (x : α) (entry : Code book × α) :
    Code book × α :=
  (entry.1, |x - entry.2|)

/-- Compare each candidate with the cached distance of the current best word. -/
private def closerDistance {book : Codebook width α} (x : α)
    (best : Option (Code book × α)) (entry : Code book × α) : Option (Code book × α) :=
  let candidate := withDistance x entry
  match best with
  | none => some candidate
  | some current => if candidate.2 < current.2 then some candidate else some current

/-- The first entry retains its value until a second finite entry requires a comparison. -/
private def cachedDistance (x : α) : α ⊕ α → α
  | .inl value => |x - value|
  | .inr distance => distance

/-- Normalize the first entry and later cached entries to the same distance invariant. -/
private def distanceEntry {book : Codebook width α} (x : α)
    (entry : Code book × (α ⊕ α)) : Code book × α :=
  (entry.1, cachedDistance x entry.2)

/-- Compare distances only after two finite entries have been found. -/
private def closerLazyDistance {book : Codebook width α} (x : α)
    (best : Option (Code book × (α ⊕ α))) (entry : Code book × α) :
    Option (Code book × (α ⊕ α)) :=
  match best with
  | none => some (entry.1, .inl entry.2)
  | some current =>
    let distance := |x - entry.2|
    match current.2 with
    | .inl value =>
      let previous := |x - value|
      if distance < previous then some (entry.1, .inr distance)
      else some (current.1, .inr previous)
    | .inr previous =>
      if distance < previous then some (entry.1, .inr distance) else best

/--
The first finite codeword whose denotation minimizes `|x - c|`. Words are scanned in ascending
unsigned order and the best is replaced only on a strict improvement, so ties resolve to the lower
word. The result is `none` if and only if the table has no finite entry.

The scan builds no intermediate list and computes each distance at most once. A table with a single
finite entry needs no distance calculation at all.
-/
def nearestCode (book : Codebook width α) (x : α) : Option (Code book) :=
  (Fin.foldl (2 ^ width) (fun best bits =>
    let code := BitVec.ofNat width bits.val
    match book.denote code with
    | .finite value =>
      match best with
      | none => some (code, Sum.inl value)
      | some current =>
        let distance := |x - value|
        match current.2 with
        | .inl first =>
          let previous := |x - first|
          if distance < previous then some (code, .inr distance)
          else some (current.1, .inr previous)
        | .inr previous =>
          if distance < previous then some (code, .inr distance) else best
    | _ => best) none).map Prod.fst

private theorem nearestCode_eq_foldl (book : Codebook width α) (x : α) :
    nearestCode book x = ((finiteEntries book).foldl (closerEntry x) none).map Prod.fst := by
  have hindices : List.range (2 ^ width) = (List.finRange (2 ^ width)).map Fin.val := by
    apply List.ext_getElem <;> simp
  have hcached : (finiteEntries book).foldl (closerDistance x) none =
      ((finiteEntries book).foldl (closerEntry x) none).map (withDistance x) := by
    exact List.foldl_hom (Option.map (withDistance x))
      (g₁ := closerEntry x) (g₂ := closerDistance x) (init := none) (by
        intro best entry
        cases best with
        | none => rfl
        | some current =>
          simp only [Option.map_some, closerDistance, closerEntry, withDistance]
          by_cases h : |x - entry.2| < |x - current.2| <;>
            simp only [h, ↓reduceIte, Option.map_some, withDistance])
  have hlazy : (finiteEntries book).foldl (closerDistance x) none =
      ((finiteEntries book).foldl (closerLazyDistance x) none).map (distanceEntry x) := by
    exact List.foldl_hom (Option.map (distanceEntry x))
      (g₁ := closerLazyDistance x) (g₂ := closerDistance x) (init := none) (by
        intro best entry
        cases best with
        | none => rfl
        | some current =>
          rcases current with ⟨code, value | distance⟩ <;>
            simp only [Option.map_some, closerLazyDistance, closerDistance,
              withDistance, distanceEntry, cachedDistance] <;> split <;>
            rename_i h <;> simp only [h, ↓reduceIte, Option.map_some,
              distanceEntry, cachedDistance])
  unfold nearestCode
  rw [Fin.foldl_eq_finRange_foldl]
  change ((List.finRange (2 ^ width)).foldl (fun best bits =>
    let code := BitVec.ofNat width bits.val
    match book.denote code with
    | .finite value => closerLazyDistance x best (code, value)
    | _ => best) none).map Prod.fst = _
  have hscan : (List.finRange (2 ^ width)).foldl (fun best bits =>
      let code := BitVec.ofNat width bits.val
      match book.denote code with
      | .finite value => closerLazyDistance x best (code, value)
      | _ => best) none = (finiteEntries book).foldl (closerLazyDistance x) none := by
    simp only [finiteEntries, hindices, List.foldl_filterMap, List.foldl_map]
    congr 1
    funext best bits
    cases book.denote (BitVec.ofNat width bits.val) <;> rfl
  rw [hscan]
  have hprojection := congrArg (Option.map Prod.fst) (hlazy.symm.trans hcached)
  simpa only [Option.map_map, Function.comp_def, distanceEntry, withDistance] using hprojection

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

/-- One scan step either takes the candidate, which is then strictly closer to `x` than any current
best, or keeps the current best, which is then no farther from `x` than the candidate. -/
private theorem closerEntry_cases {book : Codebook width α} (x : α)
    (acc : Option (Code book × α)) (entry : Code book × α) :
    (closerEntry x acc entry = some entry ∧
        ∀ current, acc = some current → |x - entry.2| < |x - current.2|) ∨
      ∃ current, acc = some current ∧ closerEntry x acc entry = some current ∧
        |x - current.2| ≤ |x - entry.2| := by
  cases acc with
  | none => exact Or.inl ⟨rfl, fun _ h => absurd h (by simp)⟩
  | some current =>
      by_cases h : |x - entry.2| < |x - current.2|
      · exact Or.inl ⟨by simp only [closerEntry, h, ↓reduceIte], fun _ hc => by cases hc; exact h⟩
      · exact Or.inr ⟨current, rfl, by simp only [closerEntry, h, ↓reduceIte], not_lt.1 h⟩

/-- A fold result other than the initial accumulator is strictly closer to `x` than it. -/
private theorem foldl_closerEntry_strict {book : Codebook width α} (x : α)
    (entries : List (Code book × α)) (acc : Option (Code book × α))
    (selected : Code book × α)
    (hfold : entries.foldl (closerEntry x) acc = some selected) :
    acc = some selected ∨ ∀ current, acc = some current → |x - selected.2| < |x - current.2| := by
  induction entries generalizing acc with
  | nil => exact Or.inl hfold
  | cons entry rest ih =>
      have h := ih (closerEntry x acc entry) hfold
      rcases closerEntry_cases x acc entry with ⟨hstep, hcloser⟩ | ⟨current, rfl, hstep, -⟩
      · rw [hstep] at h
        refine Or.inr fun current hcurrent => ?_
        rcases h with h | h
        · cases h
          exact hcloser current hcurrent
        · exact (h entry rfl).trans (hcloser current hcurrent)
      · rwa [hstep] at h

/--
Over entries in ascending unsigned order, every scanned entry below the fold result is strictly
farther from `x`, provided the initial accumulator lies below all entries.
-/
private theorem foldl_closerEntry_first {book : Codebook width α} (x : α)
    (entries : List (Code book × α)) (acc : Option (Code book × α))
    (selected : Code book × α)
    (hsorted : entries.Pairwise (fun left right => left.1.toNat < right.1.toNat))
    (hacc : ∀ current, acc = some current → ∀ entry ∈ entries,
      current.1.toNat < entry.1.toNat)
    (hfold : entries.foldl (closerEntry x) acc = some selected) :
    ∀ entry ∈ entries, entry.1.toNat < selected.1.toNat → |x - selected.2| < |x - entry.2| := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry rest ih =>
      rw [List.pairwise_cons] at hsorted
      have hstrict := foldl_closerEntry_strict x rest (closerEntry x acc entry) selected hfold
      rw [List.forall_mem_cons]
      rcases closerEntry_cases x acc entry with ⟨hstep, -⟩ | ⟨previous, rfl, hstep, hle⟩
      · -- The step takes `entry`, which lies below the rest of the scan.
        rw [hstep] at hstrict
        refine ⟨fun hlt => ?_, ih (closerEntry x acc entry) hsorted.2 ?_ hfold⟩
        · rcases hstrict with h | h
          · cases h
            exact absurd hlt (lt_irrefl _)
          · exact h entry rfl
        · rw [hstep]
          rintro _ ⟨⟩ other hother
          exact hsorted.1 other hother
      · -- The step keeps `previous`, which lies below `entry` and is no farther from `x`.
        rw [hstep] at hstrict
        refine ⟨fun hlt => ?_, ih (closerEntry x (some previous) entry) hsorted.2 ?_ hfold⟩
        · rcases hstrict with h | h
          · cases h
            exact absurd (hacc _ rfl entry List.mem_cons_self) (not_lt.2 hlt.le)
          · exact (h previous rfl).trans_le hle
        · rw [hstep]
          rintro _ ⟨⟩ other hother
          exact hacc _ rfl other (List.mem_cons_of_mem _ hother)

/-- The selected codeword denotes a finite value, it is the entry the full table scan reaches from
no accumulator, and that value is at least as close to `x` as every finite entry. -/
private theorem nearestCode_selected (book : Codebook width α) (x : α) {code : Code book}
    (hnearest : nearestCode book x = some code) :
    ∃ value, book.denote code = .finite value ∧
      (finiteEntries book).foldl (closerEntry x) none = some (code, value) ∧
      ∀ entry ∈ finiteEntries book, |x - value| ≤ |x - entry.2| := by
  rw [nearestCode_eq_foldl] at hnearest
  obtain ⟨selected, hfold, rfl⟩ := Option.map_eq_some_iff.1 hnearest
  obtain ⟨hmem, hmin, -⟩ := foldl_closerEntry_spec x (finiteEntries book) none selected hfold
  rcases hmem with hmem | hnone
  · exact ⟨selected.2, (mem_finiteEntries_iff book selected.1 selected.2).1 hmem, hfold, hmin⟩
  · exact absurd hnone (by simp)

/--
The selected codeword is finite and its denotation is at least as close to `x` as the denotation
of every finite codeword in the table.
-/
theorem nearestCode_spec (book : Codebook width α) (x : α) (code : Code book)
    (hnearest : nearestCode book x = some code) :
    ∃ value, book.denote code = .finite value ∧
      ∀ other otherValue, book.denote other = .finite otherValue →
        |x - value| ≤ |x - otherValue| := by
  obtain ⟨value, hvalue, -, hmin⟩ := nearestCode_selected book x hnearest
  exact ⟨value, hvalue, fun other otherValue hother =>
    hmin (other, otherValue) ((mem_finiteEntries_iff book other otherValue).2 hother)⟩

/--
Ties resolve to the lower word: a finite codeword that is no farther from `x` than the selected
one, and hence equally far by `nearestCode_spec`, has an unsigned value no smaller than the
selected word.
-/
theorem nearestCode_toNat_le (book : Codebook width α) (x : α) {code other : Code book}
    {value otherValue : α} (hnearest : nearestCode book x = some code)
    (hvalue : book.denote code = .finite value) (hother : book.denote other = .finite otherValue)
    (hdistance : |x - otherValue| ≤ |x - value|) : code.toNat ≤ other.toNat := by
  obtain ⟨selected, hselected, hfold, -⟩ := nearestCode_selected book x hnearest
  obtain rfl : value = selected := by rw [hvalue] at hselected; injection hselected
  refine not_lt.1 fun hlt => (not_lt.2 hdistance) ?_
  exact foldl_closerEntry_first x (finiteEntries book) none (code, value)
    (finiteEntries_pairwise book) (by simp) hfold (other, otherValue)
    ((mem_finiteEntries_iff book other otherValue).2 hother) hlt

/-- A table with at least one finite word always has a nearest codeword. -/
theorem nearestCode_isSome_of_denote_finite (book : Codebook width α) (x : α)
    {code : Code book} {value : α} (hfinite : book.denote code = .finite value) :
    ∃ nearest, nearestCode book x = some nearest := by
  have hmem := (mem_finiteEntries_iff book code value).2 hfinite
  rw [nearestCode_eq_foldl]
  obtain ⟨first, rest, hentries⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hentries, List.foldl_cons]
  obtain ⟨result, hresult⟩ :=
    foldl_closerEntry_isSome x rest (book := book) first
  simp only [closerEntry]
  exact ⟨result.1, by rw [hresult]; rfl⟩

end Nearest

end FloatLib.Floats.Formats.Codebook
