/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RadixText.Runtime
public import Mathlib.Data.Nat.Find

/-!
# Longest accepted character prefixes

A complete parser determines a prefix parser without changing its grammar.
The greatest accepted length gives both a sound parse and maximal consumption;
failure means that no prefix is accepted. This reference implementation scans
prefix lengths in descending order. Its parsing cost is quadratic when the
complete parser is linear.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- Greatest length accepted by a complete parser, or zero if none is accepted. -/
def prefixLength {α : Type} (parse : List Char → Option α) (input : List Char) : Nat :=
  Nat.findGreatest (fun length ↦ (parse (input.take length)).isSome) input.length

/-- The longest accepted prefix and its value, or failure when no prefix is accepted. -/
def parsePrefix {α : Type} (parse : List Char → Option α) (input : List Char) :
    Option (Nat × α) :=
  let length := prefixLength parse input
  (parse (input.take length)).map (length, ·)

/-- The selected prefix cannot extend beyond the input. -/
theorem prefixLength_le {α : Type} (parse : List Char → Option α) (input : List Char) :
    prefixLength parse input ≤ input.length :=
  Nat.findGreatest_le _

/-- Every accepted prefix is at most as long as the selected prefix. -/
theorem le_prefixLength {α : Type} (parse : List Char → Option α) (input : List Char)
    (length : Nat) (value : α) (hbound : length ≤ input.length)
    (hparse : parse (input.take length) = some value) :
    length ≤ prefixLength parse input :=
  Nat.le_findGreatest hbound (by simp [hparse])

/-- A successful longest-prefix result is a complete parse at the reported position. -/
theorem parsePrefix_eq_some_iff {α : Type} (parse : List Char → Option α)
    (input : List Char) (length : Nat) (value : α) :
    parsePrefix parse input = some (length, value) ↔
      length = prefixLength parse input ∧ parse (input.take length) = some value := by
  simp only [parsePrefix, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨parsed, hparse, hlength, rfl⟩
    exact ⟨hlength.symm, hlength ▸ hparse⟩
  · rintro ⟨rfl, hparse⟩
    exact ⟨value, hparse, rfl, rfl⟩

/-- Failure is equivalent to failure of the complete parser on every input prefix. -/
theorem parsePrefix_eq_none_iff {α : Type} (parse : List Char → Option α)
    (input : List Char) :
    parsePrefix parse input = none ↔
      ∀ length ≤ input.length, parse (input.take length) = none := by
  simp only [parsePrefix, Option.map_eq_none_iff]
  constructor
  · intro hnone length hbound
    cases hparse : parse (input.take length) with
    | none => rfl
    | some value =>
      have hsome : (parse (input.take (prefixLength parse input))).isSome :=
        Nat.findGreatest_spec (P := fun length ↦ (parse (input.take length)).isSome)
          hbound (by simp [hparse])
      simp [hnone] at hsome
  · intro hnone
    exact hnone _ (prefixLength_le parse input)

end FloatLib.Numerics.RadixText
