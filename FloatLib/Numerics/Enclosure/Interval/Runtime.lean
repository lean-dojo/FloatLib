/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Bounds

/-!
# Partial interval arithmetic on arbitrary endpoint carriers

Exact endpoint calculations take place in an ordered field. A supplied `OutwardRounding`
encodes the lower and upper results; failure is explicit rather than silently saturating an
invalid enclosure. Binary, decimal, and posit adapters can instantiate the scalar field with
exact rationals. No IEEE-specific exceptional values enter this layer.
-/

@[expose] public section

namespace FloatLib.Numerics

namespace OutwardRounding

variable {α β : Type*} [LinearOrder β]

/-- Check candidate encodings against the exact scalar before accepting an enclosure. -/
def checkedCandidates? (decode : α → Option β) (candidate : β → Interval α) (x : β) :
    Option (Interval α) :=
  let I := candidate x
  match decode I.lo, decode I.hi with
  | some lo, some hi => if lo ≤ x ∧ x ≤ hi then some I else none
  | _, _ => none

/--
Build a sound partial rounder from candidate endpoints and their exact decoder.

The check also rejects overflowed, saturated-on-the-wrong-side, and exceptional results.
Candidate generation may use a fast untrusted search; successful results carry checked bounds.
-/
def ofCandidates (decode : α → Option β) (candidate : β → Interval α) :
    OutwardRounding α β where
  decode := decode
  enclose? := checkedCandidates? decode candidate
  sound := by
    intro x I h
    cases hlo : decode (candidate x).lo with
    | none => simp [checkedCandidates?, hlo] at h
    | some lo =>
      cases hhi : decode (candidate x).hi with
      | none => simp [checkedCandidates?, hlo, hhi] at h
      | some hi =>
        by_cases hbounds : lo ≤ x ∧ x ≤ hi
        · simp [checkedCandidates?, hlo, hhi, hbounds] at h
          subst I
          exact ⟨lo, hi, hlo, hhi, hbounds⟩
        · simp [checkedCandidates?, hlo, hhi, hbounds] at h

end OutwardRounding

namespace Interval

variable {α β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

/-- Round the lower bound downward and the upper bound upward, with explicit failure. -/
def encloseInterval? (R : OutwardRounding α β) (I : Interval β) : Option (Interval α) := do
  let lo ← R.enclose? I.lo
  let hi ← R.enclose? I.hi
  pure ⟨lo.lo, hi.hi⟩

/-- Decode, apply an exact endpoint enclosure, and round outward. -/
def liftUnary? (R : OutwardRounding α β) (f : Interval β → Interval β)
    (I : Interval α) : Option (Interval α) :=
  match I.decode? R.decode with
  | some a => encloseInterval? R (f a)
  | none => none

/-- Decode two intervals, apply an exact endpoint enclosure, and round outward. -/
def liftBinary? (R : OutwardRounding α β) (f : Interval β → Interval β → Interval β)
    (I J : Interval α) : Option (Interval α) :=
  match I.decode? R.decode, J.decode? R.decode with
  | some a, some b => encloseInterval? R (f a b)
  | _, _ => none

/-- Outward-rounded negation, exchanging the endpoints. -/
def neg? (R : OutwardRounding α β) (I : Interval α) : Option (Interval α) :=
  liftUnary? R (fun a => ⟨-a.hi, -a.lo⟩) I

/-- Outward-rounded addition; missing finite interpretations and overflow return `none`. -/
def add? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  liftBinary? R (fun a b => ⟨a.lo + b.lo, a.hi + b.hi⟩) I J

/-- Outward-rounded subtraction. -/
def sub? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  liftBinary? R (fun a b => ⟨a.lo - b.hi, a.hi - b.lo⟩) I J

/-- Outward-rounded four-corner multiplication. -/
def mul? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  liftBinary? R (fun a b =>
    ⟨minOfFour (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi),
      maxOfFour (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi)⟩) I J

/--
Outward-rounded four-corner division, defined only away from a zero-crossing denominator.

The generic endpoint carrier need not represent unbounded intervals, so a denominator that
does not lie strictly on one side of zero returns `none`.
-/
def div? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  match I.decode? R.decode, J.decode? R.decode with
  | some a, some b =>
    if b.hi < 0 ∨ 0 < b.lo then
      encloseInterval? R
        ⟨minOfFour (a.lo / b.lo) (a.lo / b.hi) (a.hi / b.lo) (a.hi / b.hi),
          maxOfFour (a.lo / b.lo) (a.lo / b.hi) (a.hi / b.lo) (a.hi / b.hi)⟩
    else none
  | _, _ => none

end Interval
end FloatLib.Numerics
