/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.DecimalText.Runtime

/-! # Shared ASCII infinity and NaN spellings

The caller supplies the special-value constructors and interprets the diagnostic
suffix. The scanner accepts case-independent Inf/Infinity/NaN/sNaN and decimal
payload digits. An absent suffix denotes zero; the binding chooses its meaning.
-/

@[expose] public section

namespace FloatLib.Numerics.SpecialText

open DecimalText

/-- Match a lowercase ASCII keyword case-insensitively, leaving the remaining characters unchanged. -/
def consumeKeyword : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | expected :: word, actual :: rest =>
      if actual.toLower = expected then consumeKeyword word rest else none
  | _, _ => none

/-- A missing diagnostic suffix denotes payload zero; otherwise every character must be a digit. -/
def parsePayload (characters : List Char) : Option Nat :=
  if characters = [] then some 0
  else
    let (payload, count, tail) := RadixText.scanDigits characters 0 10 digitValue?
    if count = 0 ∨ tail ≠ [] then none else some payload

/--
Parse the unsigned part of a special value, consuming the entire input.
The `nan` constructor receives the sign, signaling bit, and payload, in that order.
-/
def parseSpecial {α : Type} (infinity : Bool → α) (nan : Bool → Bool → Nat → α)
    (negative : Bool) (characters : List Char) : Option α :=
  if consumeKeyword "inf".toList characters = some [] ∨
      consumeKeyword "infinity".toList characters = some [] then
    some (infinity negative)
  else
    match consumeKeyword "nan".toList characters with
    | some rest => (parsePayload rest).map (nan negative false)
    | none =>
        match consumeKeyword "snan".toList characters with
        | some rest => (parsePayload rest).map (nan negative true)
        | none => none

/-- Exact special output, retaining sign, signaling state, and diagnostic digits. -/
def nanCharacters (negative signaling : Bool) (payload : Nat) : List Char :=
  (if negative then ['-'] else []) ++
    (if signaling then "sNaN".toList else "NaN".toList) ++ RadixText.naturalDigits payload 10

/-- Infinity output preserves the sign and uses the full IEEE name. -/
def infinityCharacters (negative : Bool) : List Char :=
  (if negative then ['-'] else []) ++ "Infinity".toList

end FloatLib.Numerics.SpecialText
