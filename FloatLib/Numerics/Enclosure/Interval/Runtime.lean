/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Bounds

/-!
# Partial interval arithmetic on arbitrary endpoint carriers

Endpoint calculations happen exactly, in an ordered field, and a supplied `OutwardRounding` encodes
the lower and upper results. An operation returns `none` if decoding fails, if an outward bound is
unavailable, or if a divisor interval contains zero. The binary, decimal, and posit adapters
instantiate the scalar field with exact rationals.

Watch out for one thing. The arithmetic operations in this file don't check that decoded endpoints
are ordered, so a reversed input, which has no member, can still give a `some` result. The
containment theorems then say nothing, because they quantify over members. `Interval.ofBounds?`
builds only ordered intervals, and `hull?` and `intersect?` in `Interval.Operations` reject reversed
bounds.

This implements the outward enclosure construction in Rump's [Verification
methods](https://doi.org/10.1017/S096249291000005X), §5.3, equations (5.14)-(5.15).
`OutwardRounding` only requires containment, so an adapter may return wider bounds than the tight
directed rounding used there.
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

The check also rejects overflowed, saturated-on-the-wrong-side, and exceptional results. Candidate
generation may use a fast untrusted search, because successful results carry checked bounds.
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

/-- Outward-rounded addition. Missing finite interpretations and overflow return `none`. -/
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
Outward-rounded four-corner division of the numerator `I` by the denominator `J`, both decoded by
`R`, defined only away from a zero-crossing denominator.

The generic endpoint carrier need not represent unbounded intervals, so the result is `none`
unless the decoded denominator `b` satisfies `b.hi < 0 ∨ 0 < b.lo`. Every denominator range
containing zero is therefore rejected (`div?_eq_none_of_contains_zero`). The test reads the
endpoints only: a reversed, empty denominator such as `[1, -1]` passes it.
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
