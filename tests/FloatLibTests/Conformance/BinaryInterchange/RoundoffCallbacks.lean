/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions

/-!
# Functions that index data applies

Inside index data, a function over numerical values is applied at index data only, wherever it
travels. These checks hide
one in each place a helper generic in its type can receive it: a list, an array, a vector, an
option, a sum, a pair, a subtype, a thunk, the result of a function, a record or a record of
records, and an indexed family whose index fixes its type. Others hide its type instead, behind a
local abbreviation or as a metavariable still to be filled, also one a record holds, or pass a
callback that takes any type, which a helper can apply at a numerical one, or a record that packs a
value with its type. A getter or a default that reads the function from a container is checked the
same way. A stored function of indices, or a record of one, read at index data stays index data.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffCallbacks

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics
open FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions (countAfter Callback countAt)

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The entry `i` of a list of functions, applied to `x`, for any type of `x`. -/
def callAt {α : Type} (fs : List (α → Nat)) (i : Nat) (x : α) : Nat := fs[i]! x

/--
error: roundoff: ↑(callAt fs i x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_at_error :=
  fun (fs : List (Value → Nat)) (i : Nat) (x : Value) => ((callAt fs i x : Nat) : ℝ)

/-- The same for an array of functions. -/
def callAtArray {α : Type} (fs : Array (α → Nat)) (i : Nat) (x : α) : Nat := fs[i]! x

/--
error: roundoff: ↑(callAtArray fs i x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_at_array_error :=
  fun (fs : Array (Value → Nat)) (i : Nat) (x : Value) => ((callAtArray fs i x : Nat) : ℝ)

/-- `countAfter` of the function of a record, behind a helper generic in the record's type. -/
def countCallback {α : Type} [BEq α] (c : Callback α) (xs : List α) (y : α) : Nat :=
  countAfter c.run xs y

/--
error: roundoff: ↑(countCallback c xs y) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem count_callback_error :=
  fun (c : Callback Value) (xs : List Value) (y : Value) =>
    ((countCallback c xs y : Nat) : ℝ)

-- A function read from a list at an index with its proof, applied to a pair of values.
/--
error: roundoff: ↑(fs[i] p) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem read_pair_error :=
  fun (fs : List ((Value × Value) → Nat)) (i : Nat) (h : i < fs.length)
    (p : Value × Value) => (((fs[i]'h) p : Nat) : ℝ)

/-- The function an option holds, applied to `x`. -/
def callOption {α : Type} (o : Option (α → Nat)) (x : α) : Nat :=
  match o with
  | some f => f x
  | none => 0

/--
error: roundoff: ↑(callOption o x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_option_error :=
  fun (o : Option (Value → Nat)) (x : Value) => ((callOption o x : Nat) : ℝ)

/-- The function a sum holds on its left, applied to `x`. -/
def callSum {α : Type} (s : (α → Nat) ⊕ Nat) (x : α) : Nat :=
  match s with
  | .inl f => f x
  | .inr n => n

/--
error: roundoff: ↑(callSum s x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_sum_error :=
  fun (s : (Value → Nat) ⊕ Nat) (x : Value) => ((callSum s x : Nat) : ℝ)

/-- The function of a pair, applied to `x`. -/
def callProd {α : Type} (p : (α → Nat) × Nat) (x : α) : Nat := p.1 x + p.2

/--
error: roundoff: ↑(callProd p x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_prod_error :=
  fun (p : (Value → Nat) × Nat) (x : Value) => ((callProd p x : Nat) : ℝ)

/-- The function of a dependent pair, applied to `x`. -/
def callSigma {α : Type} (s : (_ : Nat) × (α → Nat)) (x : α) : Nat := s.2 x

/--
error: roundoff: ↑(callSigma s x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_sigma_error :=
  fun (s : (_ : Nat) × (Value → Nat)) (x : Value) => ((callSigma s x : Nat) : ℝ)

/-- A record that holds a function to the naturals. -/
structure Scorer (α : Type) where
  /-- The function. -/
  score : α → Nat

/-- A record of such a record. -/
structure Outer (α : Type) where
  /-- The inner record. -/
  inner : Scorer α

/-- The function of the inner record, applied to `x`. -/
def callOuter {α : Type} (o : Outer α) (x : α) : Nat := o.inner.score x

/--
error: roundoff: ↑(callOuter o x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_outer_error :=
  fun (o : Outer Value) (x : Value) => ((callOuter o x : Nat) : ℝ)

/-- The sum of the functions of a list at `x`, mapped through `Functor.map`. -/
def mapCalls {α : Type} (fs : List (α → Nat)) (x : α) : Nat :=
  ((fun f => f x) <$> fs).foldl (· + ·) 0

/--
error: roundoff: ↑(mapCalls fs x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem map_calls_error :=
  fun (fs : List (Value → Nat)) (x : Value) => ((mapCalls fs x : Nat) : ℝ)

/-- The same sum, folded over the list. -/
def foldCalls {α : Type} (fs : List (α → Nat)) (x : α) : Nat :=
  fs.foldl (fun total f => total + f x) 0

/--
error: roundoff: ↑(foldCalls fs x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem fold_calls_error :=
  fun (fs : List (Value → Nat)) (x : Value) => ((foldCalls fs x : Nat) : ℝ)

/-- A class of functions to the naturals. -/
class Scored (α : Type) where
  /-- The function. -/
  score : α → Nat

/-- A record that holds a dictionary of that class. -/
structure WithScore (α : Type) where
  /-- The dictionary. -/
  scored : Scored α

/-- The method of the record's dictionary, applied to `x`. -/
def scoreWith {α : Type} (w : WithScore α) (x : α) : Nat := @Scored.score α w.scored x

/--
error: roundoff: ↑(scoreWith w x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem score_with_error :=
  fun (w : WithScore Value) (x : Value) => ((scoreWith w x : Nat) : ℝ)

/-- The first function of a list, applied to `x`. -/
def headCall {α : Type} (fs : List (α → Nat)) (x : α) : Nat := (fs.headD fun _ => 0) x

/--
error: roundoff: ↑(headCall fs x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem head_call_error :=
  fun (fs : List (Value → Nat)) (x : Value) => ((headCall fs x : Nat) : ℝ)

/-- The function of a subtype, applied to `x`. -/
def callSubtype {α : Type} (s : {f : α → Nat // f = f}) (x : α) : Nat := s.1 x

/--
error: roundoff: ↑(callSubtype s x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_subtype_error :=
  fun (s : {f : Value → Nat // f = f}) (x : Value) => ((callSubtype s x : Nat) : ℝ)

/-- The function a thunk computes, applied to `x`. -/
def callThunk {α : Type} (t : Thunk (α → Nat)) (x : α) : Nat := t.get x

/--
error: roundoff: ↑(callThunk t x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_thunk_error :=
  fun (t : Thunk (Value → Nat)) (x : Value) => ((callThunk t x : Nat) : ℝ)

/-- The entry `i` of a vector of functions, applied to `x`. -/
def callVector {α : Type} {n : Nat} (fs : Vector (α → Nat) n) (i : Fin n) (x : α) : Nat := fs[i] x

/--
error: roundoff: ↑(callVector fs i x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_vector_error :=
  fun {n : Nat} (fs : Vector (Value → Nat) n) (i : Fin n) (x : Value) =>
    ((callVector fs i x : Nat) : ℝ)

-- A function read from a list with a default, applied to a pair of values.
/--
error: roundoff: ↑(fs.getD i (fun x => 0) p) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem get_default_pair_error :=
  fun (fs : List ((Value × Value) → Nat)) (i : Nat) (p : Value × Value) =>
    (((fs.getD i fun _ => 0) p : Nat) : ℝ)

/-- The first function of the list that `g` gives at zero, applied to `x`. -/
def useFamily {α : Type} (g : Nat → List (α → Nat)) (x : α) : Nat := (g 0)[0]! x

/--
error: roundoff: ↑(useFamily (fun x => fs) x) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem use_family_error :=
  fun (fs : List (Value → Nat)) (x : Value) => ((useFamily (fun _ => fs) x : Nat) : ℝ)

/-- A record of a test of two values. -/
structure Matcher (α : Type) where
  /-- The test. -/
  same : α → α → Bool

/-- The number of entries of `xs` that the record's test matches with `y`. -/
def countMatching {α : Type} (m : Matcher α) (xs : List α) (y : α) : Nat :=
  (xs.filter fun z => m.same z y).length

/--
error: roundoff: ↑(countMatching m xs y) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem count_matching_error :=
  fun (m : Matcher Value) (xs : List Value) (y : Value) =>
    ((countMatching m xs y : Nat) : ℝ)

/-- The function of a successful result, applied to `x`. -/
def callExcept {α : Type} (e : Except String (α → Nat)) (x : α) : Nat :=
  match e with
  | .ok f => f x
  | .error _ => 0

/--
error: roundoff: ↑(callExcept e x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_except_error :=
  fun (e : Except String (Value → Nat)) (x : Value) => ((callExcept e x : Nat) : ℝ)

/-- The sum of the functions of a list at `x`, accumulated in a `for` loop. -/
def runCalls {α : Type} (fs : List (α → Nat)) (x : α) : Nat := Id.run do
  let mut total := 0
  for f in fs do
    total := total + f x
  return total

/--
error: roundoff: ↑(runCalls fs x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem run_calls_error :=
  fun (fs : List (Value → Nat)) (x : Value) => ((runCalls fs x : Nat) : ℝ)

/-- The sum of the functions of a list applied to the values of another, entry by entry. -/
def zipCalls {α : Type} (fs : List (α → Nat)) (xs : List α) : Nat :=
  (List.zipWith (fun f x => f x) fs xs).foldl (· + ·) 0

/--
error: roundoff: ↑(zipCalls fs xs) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem zip_calls_error :=
  fun (fs : List (Value → Nat)) (xs : List Value) => ((zipCalls fs xs : Nat) : ℝ)

-- The function of an option with a default, applied to a pair of values.
/--
error: roundoff: ↑(o.getD (fun x => 0) p) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem option_default_pair_error :=
  fun (o : Option ((Value × Value) → Nat)) (p : Value × Value) =>
    (((o.getD fun _ => 0) p : Nat) : ℝ)

/-- Functions held by an indexed family: one function or a list of them, told apart by the index. -/
inductive Callbacks : Bool → Type → Type 1 where
  /-- One function. -/
  | single {α : Type} : (α → Nat) → Callbacks false α
  /-- A list of functions. -/
  | batch {α : Type} : List (α → Nat) → Callbacks true α

/-- The function of a single entry, applied to `x`. -/
def callSingle {α : Type} (c : Callbacks false α) (x : α) : Nat :=
  match c with
  | .single f => f x

/--
error: roundoff: ↑(callSingle c x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_single_error :=
  fun (c : Callbacks false Value) (x : Value) => ((callSingle c x : Nat) : ℝ)

/--
error: roundoff: ↑(callSingle c x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_single_float_error :=
  fun (c : Callbacks false Float) (x : Float) => ((callSingle c x : Nat) : ℝ)

/-- The functions of either kind of entry, applied to `x`. -/
def callAny {b : Bool} {α : Type} (c : Callbacks b α) (x : α) : Nat :=
  match c with
  | .single f => f x
  | .batch fs => fs.foldl (fun total f => total + f x) 0

/--
error: roundoff: ↑(callAny c x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem call_any_error :=
  fun (b : Bool) (c : Callbacks b Value) (x : Value) => ((callAny c x : Nat) : ℝ)

/-- A family whose type index the constructors choose: a function, or a number of type `Nat`. -/
inductive Lifted : Type → Type 1 where
  /-- A function. -/
  | lift {α : Type} (f : α → Nat) : Lifted α
  /-- A number. -/
  | const (n : Nat) : Lifted Nat

/-- The function of a lifted entry at `x`, or its number. -/
def runLifted {α : Type} (o : Lifted α) (x : α) : Nat :=
  match o with
  | .lift f => f x
  | .const n => n

/--
error: roundoff: ↑(runLifted o x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem run_lifted_error :=
  fun (o : Lifted Value) (x : Value) => ((runLifted o x : Nat) : ℝ)

-- A function whose type is a local abbreviation, applied to a stored value.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example (x : Value) : True := by
  let F := Value → Nat
  have h : ∀ f : F, True := by
    intro f
    have bound := by roundoff (((f x : Nat) : ℝ))
    trivial
  trivial

-- A list of such functions passed to a generic helper.
/--
error: roundoff: ↑(callAt fs i x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example (x : Value) (i : Nat) : True := by
  let F := Value → Nat
  have h : ∀ fs : List F, True := by
    intro fs
    have bound := by roundoff (((callAt fs i x : Nat) : ℝ))
    trivial
  trivial

-- The list type itself abbreviated.
/--
error: roundoff: ↑(callAt fs i x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example (x : Value) (i : Nat) : True := by
  let G := List (Value → Nat)
  have h : ∀ fs : G, True := by
    intro fs
    have bound := by roundoff (((callAt fs i x : Nat) : ℝ))
    trivial
  trivial

-- The value type abbreviated, under the function's domain.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example : True := by
  let W := Value
  have h : ∀ (f : W → Nat) (x : W), True := by
    intro f x
    have bound := by roundoff (((f x : Nat) : ℝ))
    trivial
  trivial

-- A function on a type that is still a metavariable when the analysis runs, as `refine_lift` leaves
-- it for a later goal, may take numerical values.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example : True := by
  let A : Type := ?carrier
  have h : ∀ (f : A → Nat) (x : A), True := by
    intro f x
    have bound := by roundoff (((f x : Nat) : ℝ))
    trivial
  trivial
  case carrier => exact Float

/-- A callback that takes any type, applied at the type of `x`. -/
def applyPoly {α : Type} (f : (β : Type) → β → Nat) (x : α) : Nat := f α x

/--
error: roundoff: ↑(applyPoly f x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_poly_error :=
  fun (f : (β : Type) → β → Nat) (x : Value) => ((applyPoly f x : Nat) : ℝ)

/--
error: roundoff: ↑(applyPoly f x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_poly_float_error :=
  fun (f : (β : Type) → β → Nat) (x : Float) => ((applyPoly f x : Nat) : ℝ)

/-- The sum of a list of such callbacks, their type argument implicit, at `x`. -/
def applyPolys {α : Type} (fs : List ({β : Type} → β → Nat)) (x : α) : Nat :=
  fs.foldl (fun total f => total + f x) 0

/--
error: roundoff: ↑(applyPolys fs x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_polys_error :=
  fun (fs : List ({β : Type} → β → Nat)) (x : Value) => ((applyPolys fs x : Nat) : ℝ)

/-- Such a callback applied at an index, which stays index data. -/
def applyIndex (f : (β : Type) → β → Nat) (n : Nat) : Nat := f Nat n

/-- The reference is the number itself. -/
roundoff theorem apply_index_error :=
  fun (f : (β : Type) → β → Nat) (n : Nat) => ((applyIndex f n : Nat) : ℝ)

/-- The type of such callbacks, under a name. -/
abbrev PolyReader := (β : Type) → β → Nat

/-- A callback of that type, applied at the type of `x`. -/
def applyReader {α : Type} (f : PolyReader) (x : α) : Nat := f α x

/--
error: roundoff: ↑(applyReader f x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_reader_error :=
  fun (f : PolyReader) (x : Value) => ((applyReader f x : Nat) : ℝ)

/-- A record of such a callback. -/
structure PolyBox where
  /-- The callback. -/
  run : (β : Type) → β → Nat

/-- The callback of a record, applied at the type of `x`. -/
def applyBox {α : Type} (p : PolyBox) (x : α) : Nat := p.run α x

/--
error: roundoff: ↑(applyBox p x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_box_error :=
  fun (p : PolyBox) (x : Value) => ((applyBox p x : Nat) : ℝ)

/-- The callback of a record that a function gives, applied at the type of `x`. -/
def applyMade {α : Type} (make : Nat → PolyBox) (x : α) : Nat := (make 0).run α x

/--
error: roundoff: ↑(applyMade make x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_made_error :=
  fun (make : Nat → PolyBox) (x : Value) => ((applyMade make x : Nat) : ℝ)

/-- A record that packs a value with its type, which it proves to be a function type. -/
structure Packed (α : Type) where
  /-- The type of the value. -/
  F : Type
  /-- The type is a function type. -/
  isFunction : F = (α → Nat)
  /-- The value. -/
  run : F

/-- The packed function, applied to `x`. -/
def applyPacked {α : Type} (p : Packed α) (x : α) : Nat := (cast p.isFunction p.run) x

/--
error: roundoff: ↑(applyPacked p x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_packed_error :=
  fun (p : Packed Value) (x : Value) => ((applyPacked p x : Nat) : ℝ)

/-- The same packed in a dependent pair. -/
def applySigma {α : Type} (p : (F : Type) × (F = (α → Nat)) ×' F) (x : α) : Nat :=
  (cast p.2.1 p.2.2) x

/--
error: roundoff: ↑(applySigma p x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_sigma_error :=
  fun (p : (F : Type) × (F = (Value → Nat)) ×' F) (x : Value) => ((applySigma p x : Nat) : ℝ)

/-- `Type` under another name. -/
abbrev TypeArgument := Type

/-- Callbacks that take a type of that name. -/
abbrev Reader := (β : TypeArgument) → β → Nat

/-- Such a callback, applied at the type of `x`. -/
def applyNamed {α : Type} (f : Reader) (x : α) : Nat := f α x

/--
error: roundoff: ↑(applyNamed f x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_named_error :=
  fun (f : Reader) (x : Value) => ((applyNamed f x : Nat) : ℝ)

/-- A record of a function on indices. -/
structure IndexBox where
  /-- The function. -/
  run : Nat → Nat

/-- The function of such a record, read at an index, stays index data. -/
roundoff theorem index_box_error :=
  fun (p : IndexBox) (n : Nat) => ((p.run n : Nat) : ℝ)

/-- A record that holds a type. -/
structure TypeBox where
  /-- The type. -/
  ty : Type

-- A function on the type of a record that is still a metavariable when the analysis runs.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example : True := by
  let b : TypeBox := ?box
  let A : Type := b.ty
  have h : ∀ (f : A → Nat) (x : A), True := by
    intro f x
    have bound := by roundoff (((f x : Nat) : ℝ))
    trivial
  trivial
  case box => exact ⟨Float⟩

-- A type that a function gives in a record, still a metavariable when the analysis runs.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
example : True := by
  let boxes : Unit → TypeBox := ?boxes
  let A : Type := (boxes ()).ty
  have h : ∀ (f : A → Nat) (x : A), True := by
    intro f x
    have bound := by roundoff (((f x : Nat) : ℝ))
    trivial
  trivial
  case boxes => exact fun _ => ⟨Float⟩

-- A stored function read at indices only stays index data under such an abbreviation.
example (n : Nat) (y : Value) : True := by
  let W := Value
  have h : ∀ f : Nat → W, True := by
    intro f
    have bound := by roundoff (((countAt f n y : Nat) : ℝ))
    trivial
  trivial

-- A function on a type parameter of the theorem, applied at a value of it. The theorem can be
-- specialized to a numerical type, so the value counts as numerical.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_error :=
  fun {β : Type} (f : β → Nat) (x : β) => ((f x : Nat) : ℝ)

-- The same function read from a list.
/--
error: roundoff: ↑(callAt fs i x) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_list_error :=
  fun {β : Type} (fs : List (β → Nat)) (i : Nat) (x : β) => ((callAt fs i x : Nat) : ℝ)

-- The same function as a field of a pair.
/--
error: roundoff: ↑(p.1 x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_pair_error :=
  fun {β : Type} (p : (β → Nat) × Nat) (x : β) => ((p.1 x : Nat) : ℝ)

-- A comparison of values of a type parameter through a dictionary of it, which can compute.
/--
error: roundoff: ↑(List.count y xs) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_count_error :=
  fun {β : Type} [BEq β] (xs : List β) (y : β) => ((xs.count y : Nat) : ℝ)

/-- The length of a stored list of a type parameter, also through a map, stays index data. -/
roundoff theorem type_parameter_length_error :=
  fun {β : Type} (f : β → Nat) (xs : List β) => (((xs.map f).length : Nat) : ℝ)

/-- A type under another name. -/
abbrev Alias (α : Type) := α

/-- A function on `X` cast from a value of a type `F`, applied to `x`. -/
def castApply {F X : Type} (h : F = (X → Nat)) (f : Alias F) (x : Alias X) : Nat := (cast h f) x

-- The same through the alias of type parameters, which a helper unfolds to a function.
/--
error: roundoff: ↑(castApply h f x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_alias_error :=
  fun {F X : Type} (h : F = (X → Nat)) (f : Alias F) (x : Alias X) =>
    ((castApply h f x : Nat) : ℝ)

/-- A type under another name, behind a definition that only default transparency unfolds. -/
def Hidden (α : Type) := α

/-- `castApply` on values of hidden types. -/
def castHidden {F X : Type} (h : F = (X → Nat)) (f : Hidden F) (x : Hidden X) : Nat :=
  (cast h f) x

-- The same through that definition.
/--
error: roundoff: ↑(castHidden h f x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_hidden_error :=
  fun {F X : Type} (h : F = (X → Nat)) (f : Hidden F) (x : Hidden X) =>
    ((castHidden h f x : Nat) : ℝ)

/-- A type parameter or `Float`, as a flag chooses. -/
def Pick (b : Bool) (α : Type) : Type := if b then α else Float

-- The same through a definition that names a carrier but gives the type parameter here.
/--
error: roundoff: ↑(castApply h f x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_parameter_pick_error :=
  fun {F X : Type} (h : F = (X → Nat)) (f : Pick true F) (x : Pick true X) =>
    ((@castApply F X h f x : Nat) : ℝ)

/-- A class that holds a type, which no read trusts. -/
class TypeClass where
  /-- The type. -/
  ty : Type

-- A function on the type that an instance argument of such a class holds.
/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem type_class_error :=
  fun [b : TypeClass] (f : b.ty → Nat) (x : b.ty) => ((f x : Nat) : ℝ)

end FloatLibTests.Conformance.BinaryInterchange.RoundoffCallbacks
