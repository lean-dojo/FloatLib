/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public meta import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public meta import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Extension
public meta import Lean.Elab.Command

/-!
# What `roundoff` states, and where it stops

These checks read the generated statements themselves. A configured mixed theorem concludes the
finiteness of its output, a model or wrapped observation the mixed bound alone. A loop over a
computed container is fused into its step, so that its reference squares the stored entries rather
than summing rounded products, also when the entries are decoded inside the container, and a
container that cannot be fused is rejected when its reference would read any of its entries, even
integers that encode a rounded value; the entries of an index computation, such as `List.range` or
`List.finRange`, remain data only when its length, start, step and offset are themselves index data,
not numbers taken from a rounded value, also when a helper over the natural numbers or an instance
on an alias of a float type computes them, and its length must be index data even when the loop
ignores its entries; a helper whose value is index arithmetic is read through that value. An integer
computed from a rounded value is not exact data when it is cast to the reals or indexes a stored
function, also through Lean's own model of `Float32`, while the length of a stored list, or of a map
of one, is, and so is a core definition that the module system exports without a value when Lean's
own library holds its module. The position of the largest of stored values, which comparisons alone
find, is index data, but not when the comparisons read a computed value, the helper computes with
the values, or the stored bits are read. A getter of another dictionary than a list's own is
analyzed as the function it is, and the getter of a mapped option as the map at the option's
getter; the exponential of an option's value with no producer fails for its operand's reason. A
contract whose model the analysis has no rule for keeps its model at the computed argument, while a
contract against `Real.exp` propagates the argument's error. A
test of a loop's rounded state is no agreement test when it is not FloatLib's own under the
observation, as a reversed order, the structural equality of the stored word or a test under a
negated codec, or when the reference of an operand would keep a rounded value, as a stored entry
read at an index chosen by a rounded square, a contract's model at a rounded argument or through a
helper that hides a rounded square, or a stored function read at the rounded state, or when it reads
a component whose reference keeps a rounded value, as a stored entry read at an index chosen by a
rounded square one step before, also through a flag whose test of exact values reads such a
component, as one that holds such an entry or a value that a rounded square chooses; the flag it
sets is then rejected. A loop analyzed inside another loop's step states no new agreement premise
there, since its references could read the enclosing loop's state; an estimate established outside
the step is reused there as it is. An agreement test compares by the reals' own order, and a plain
real expression takes only the reals' own dictionaries, also where a section declares a rounding
addition and order on the reals. Finiteness rules that need their own conclusion, directly or
through another rule or a growing chain, do not loop: the condition left is the finiteness of the
input. A rule's premise read through a registered getter stays a condition as the rule states it
when the analysis cannot prove its normal form, and is the finiteness of an input when that normal
form is one, also through a coordinate read through `id`; a generated proof that depends on a goal
outside its obligations is refused. Extensions follow the environment, rules registered locally end
with their section, a dictionary whose exponential is not correctly rounded gets no half-ulp bound,
a branch keeps its conditions under its guard, and a generated binary32 theorem applies once its
range condition is discharged.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

section Arithmetic

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

/-- The sum of the squares of a list, computed as a container first. -/
def sumSquares (xs : List Value) : Value := (xs.map fun x => x * x).foldl (· + ·) 0

/-- The sum of squares is within its budget of the exact sum of the squares of the stored entries.
-/
roundoff theorem sum_squares_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sumSquares xs)

/-- The sum of squares is finite and has a mixed bound against the exact sum of squares. -/
roundoff mixed theorem sum_squares_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sumSquares xs)

/-- The reference squares the decoded entries of `xs`; it does not sum the rounded products. -/
example (xs : List Value) (hformat : format.isIEEE = true) :=
  show _ → |_ - xs.foldl (fun sum x => sum + ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x)
    0| ≤ _ from sum_squares_error xs hformat

/-- The dot product of two lists through `List.zipWith`. -/
def dotZip (xs ys : List Value) : Value := (List.zipWith (· * ·) xs ys).foldl (· + ·) 0

/-- The dot product is within its budget of the exact dot product of the stored pairs. -/
roundoff theorem dot_zip_error :=
  fun (xs ys : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dotZip xs ys)

/-- The reference multiplies the decoded entries of each pair of `xs.zip ys`. -/
example (xs ys : List Value) (hformat : format.isIEEE = true) :=
  show _ → |_ - (xs.zip ys).foldl (fun sum pair =>
    sum + ExecFloat.Binary.toReal pair.1 * ExecFloat.Binary.toReal pair.2) 0| ≤ _ from
    dot_zip_error xs ys hformat

/-- A sum of squares whose container is reversed, which no fusion law writes into the step. -/
def sumReversed (xs : List Value) : Value := ((xs.map fun x => x * x).reverse).foldl (· + ·) 0

/--
error: roundoff: the loop reads the entries of the computed container (List.map (fun x => x * x)
    xs).reverse as exact data, so its reference would omit their rounding; write the producer into
the step or register a law that does (`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem sum_reversed_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sumReversed xs)

/-- A sum of decoded squares, the decoding done inside the computed container. -/
noncomputable def realSquares (xs : List Value) : ℝ :=
  (xs.map fun x => ExecFloat.Binary.toReal (x * x)).foldl (fun (sum x : ℝ) => sum + x) 0

/-- The real-valued sum is within its budget of the exact sum of squares of the stored entries. -/
roundoff theorem real_squares_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => realSquares xs

/-- The map is fused, so the reference squares the decoded entries of `xs` and the budget carries
each product's rounding. -/
example (xs : List Value) (hformat : format.isIEEE = true) :=
  show _ → |_ - xs.foldl (fun sum x => sum + ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x)
    0| ≤ _ from real_squares_error xs hformat

/-- The same sum over the reversed container, which no fusion law writes into the step. -/
noncomputable def realReversed (xs : List Value) : ℝ :=
  ((xs.map fun x => ExecFloat.Binary.toReal (x * x)).reverse).foldl (fun (sum x : ℝ) => sum + x) 0

/--
error: roundoff: the loop reads the entries of the computed container (List.map (fun x => (x *
x).toReal) xs).reverse as exact data, so its reference would omit their rounding; write the
producer into the step or register a law that does (`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem real_reversed_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => realReversed xs

/-- A sum of the first components of decoded pairs over a reversed computed container. -/
noncomputable def pairReversed (xs : List Value) : ℝ :=
  ((xs.map fun x => (ExecFloat.Binary.toReal (x * x), ExecFloat.Binary.toReal x)).reverse).foldl
    (fun (sum : ℝ) pair => sum + pair.1) 0

/--
error: roundoff: the loop reads the entries of the computed container (List.map (fun x =>
((x * x).toReal, x.toReal)) xs).reverse as exact data, so its reference would omit their rounding;
write the producer into the step or register a law that does (`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem pair_reversed_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => pairReversed xs

/-- The decoded squares, carried as the numerators and denominators of their rational values over a
reversed computed container. -/
noncomputable def encodedReversed (xs : List Value) : ℝ :=
  ((xs.map fun x =>
      let q := (ExecFloat.Binary.toRat? (x * x)).getD 0
      (q.num, q.den)).reverse).foldl
    (fun (sum : ℝ) (pair : Int × Nat) => sum + (pair.1 : ℝ) / (pair.2 : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container (List.map (fun x =>
(((x * x).toRat?.getD 0).num, ((x * x).toRat?.getD 0).den)) xs).reverse as exact data, so its
reference would omit their rounding; write the producer into the step or register a law that does
(`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_reversed_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => encodedReversed xs

/-- Two ranges whose starts are the numerator and denominator of a rounded square and whose step is
zero, so that each repeats its start: their quotients rebuild the rounded square `n` times. -/
noncomputable def encodedStarts (x : Value) (n : Nat) : ℝ :=
  let q := (ExecFloat.Binary.toRat? (x * x)).getD 0
  ((List.range' q.num.natAbs n 0).zip (List.range' q.den n 0)).foldl
    (fun (sum : ℝ) (pair : Nat × Nat) => sum + (pair.1 : ℝ) / (pair.2 : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container (List.range'
((ExecFloat.Binary.toRat? (x * x)).getD 0).num.natAbs n 0).zip (List.range'
((ExecFloat.Binary.toRat? (x * x)).getD 0).den n 0) as exact data, so its
reference would omit their rounding; write the producer into the step or register a law that does
(`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_starts_error :=
  fun (x : Value) (n : Nat) (hformat : format.isIEEE = true) => encodedStarts x n

/-- The indices from zero whose step is the denominator of a rounded square. -/
noncomputable def encodedStep (x : Value) (n : Nat) : ℝ :=
  (List.range' 0 n ((ExecFloat.Binary.toRat? (x * x)).getD 0).den).foldl
    (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container List.range' 0 n
((ExecFloat.Binary.toRat? (x * x)).getD 0).den as exact data, so its
reference would omit their rounding; write the producer into the step or register a law that does
(`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_step_error :=
  fun (x : Value) (n : Nat) (hformat : format.isIEEE = true) => encodedStep x n

/-- The indices below the denominator of a rounded square. -/
noncomputable def encodedLength (x : Value) : ℝ :=
  (List.range ((ExecFloat.Binary.toRat? (x * x)).getD 0).den).foldl
    (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container List.range
((ExecFloat.Binary.toRat? (x * x)).getD 0).den as exact data, so its
reference would omit their rounding; write the producer into the step or register a law that does
(`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_length_error :=
  fun (x : Value) (hformat : format.isIEEE = true) => encodedLength x

/-- One for each index below the numerator of a rounded square: the steps ignore the indices, but
their number is computed from the rounded square. -/
noncomputable def encodedTrips (x : Value) : ℝ :=
  (List.range ((ExecFloat.Binary.toRat? (x * x)).getD 0).num.natAbs).foldl
    (fun (sum : ℝ) _ => sum + 1) 0

/--
error: roundoff: the loop takes a step for each entry of the computed container List.range
((ExecFloat.Binary.toRat? (x * x)).getD 0).num.natAbs, whose length may be computed from numerical
values, so its reference would take as many steps as the rounded computation; traverse index data
or a stored input
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_trips_error :=
  fun (x : Value) (hformat : format.isIEEE = true) => encodedTrips x

/-- The stored entries numbered from the denominator of a rounded square. -/
noncomputable def encodedOffset (xs : List Value) (x : Value) : ℝ :=
  (xs.zipIdx ((ExecFloat.Binary.toRat? (x * x)).getD 0).den).foldl
    (fun (sum : ℝ) (pair : Value × Nat) => sum + (pair.2 : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container xs.zipIdx
((ExecFloat.Binary.toRat? (x * x)).getD 0).den as exact data, so its
reference would omit their rounding; write the producer into the step or register a law that does
(`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_offset_error :=
  fun (xs : List Value) (x : Value) (hformat : format.isIEEE = true) => encodedOffset xs x

/-- The numerator of the binary32 square of `k`, computed by a helper whose signature holds no
number. -/
def hiddenNum (k : Nat) : Nat :=
  let x : ExecFloat.Binary 8 23 := ExecFloat.Binary.ofRat (k : ℚ)
  ((ExecFloat.Binary.toRat? (x * x)).getD 0).num.natAbs

/-- The denominator of the binary32 square of `k`. -/
def hiddenDen (k : Nat) : Nat :=
  let x : ExecFloat.Binary 8 23 := ExecFloat.Binary.ofRat (k : ℚ)
  ((ExecFloat.Binary.toRat? (x * x)).getD 0).den

/-- Two ranges that repeat the numerator and denominator of a rounded square, computed by helpers
over the natural numbers: their quotients rebuild the rounded square `n` times. -/
noncomputable def hiddenStarts (k n : Nat) : ℝ :=
  ((List.range' (hiddenNum k) n 0).zip (List.range' (hiddenDen k) n 0)).foldl
    (fun (sum : ℝ) (pair : Nat × Nat) => sum + (pair.1 : ℝ) / (pair.2 : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container (List.range' (hiddenNum k) n
0).zip (List.range' (hiddenDen k) n 0) as exact data, so its reference would omit their rounding;
write the producer into the step or register a law that does (`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem hidden_starts_error := fun (k n : Nat) => hiddenStarts k n

/-- Lean's floats under a name that does not unfold reducibly, with a hash of their bits. -/
def Wide := Float

instance : Mul Wide := inferInstanceAs (Mul Float)

instance : Hashable Wide := ⟨fun y => Float.toUInt64 y⟩

/-- The indices from the bits of a rounded square of `Wide` values. -/
noncomputable def wideStart (y : Wide) (n : Nat) : ℝ :=
  (List.range' (hash (y * y)).toNat n 0).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/--
error: roundoff: the loop reads the entries of the computed container List.range' (hash (y *
y)).toNat n 0 as exact data, so its reference would omit their rounding; write the producer into
the step or register a law that does (`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff theorem wide_start_error := fun (y : Wide) (n : Nat) => wideStart y n

/-- Twice a natural number, a helper whose value is index arithmetic. -/
def twice (n : Nat) : Nat := 2 * n

/-- The indices from twice a parameter, in steps of two. -/
noncomputable def twiceSum (start n : Nat) : ℝ :=
  (List.range' (twice start) n 2).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/-- The helper is read through its value, so the loop is analyzed as written. -/
roundoff theorem twice_sum_error := fun (start n : Nat) => twiceSum start n

/-- The reference is the sum of those indices itself. -/
example (start n : Nat) :=
  show |_ - (List.range' (twice start) n 2).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0| ≤
    _ from twice_sum_error start n

/-- The numerator over the denominator of a rounded square, each cast to the reals. -/
noncomputable def encodedQuotient (x : Value) : ℝ :=
  (((ExecFloat.Binary.toRat? (x * x)).getD 0).num : ℝ) /
    (((ExecFloat.Binary.toRat? (x * x)).getD 0).den : ℝ)

/--
error: roundoff: ↑((ExecFloat.Binary.toRat? (x * x)).getD 0).num casts an integer computed from real
or floating-point values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem encoded_quotient_error :=
  fun (x : Value) (hformat : format.isIEEE = true) => encodedQuotient x

/-- A stored function read at the numerator of a rounded square. -/
def encodedRead (f : Nat → Value) (x : Value) : Value :=
  f ((ExecFloat.Binary.toRat? (x * x)).getD 0).num.natAbs

/--
error: roundoff: f ((ExecFloat.Binary.toRat? (x * x)).getD 0).num.natAbs reads a stored input at an
index computed from numerical values, so the reference would keep them
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem encoded_read_mixedError :=
  fun (f : Nat → Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (encodedRead f x)

/-- The mean of a list, its sum over the conversion of its length. -/
def mean (xs : List Value) : Value :=
  xs.foldl (· + ·) 0 / ExecFloat.Binary.ofRat ((xs.length : ℤ) : ℚ)

/-- The length of a stored list is index data, so the mean is analyzed as written. -/
roundoff mixed theorem mean_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (mean xs)

/-- The reference divides the exact sum of the decoded entries by the length. -/
example (xs : List Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (xs.foldl (fun sum x => sum + ExecFloat.Binary.toReal x) 0 /
    ((xs.length : ℤ) : ℝ)) _ _ from mean_mixedError xs hformat

/-- A value divided by the length of a map of a stored list, which is the length of the list. -/
def overMapLength (xs : List Value) (y : Value) : Value :=
  y / ExecFloat.Binary.ofRat (((xs.map fun x => x * x).length : ℤ) : ℚ)

/-- A map keeps the length of its container, so the quotient is analyzed as written. -/
roundoff mixed theorem over_map_length_mixedError :=
  fun (xs : List Value) (y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (overMapLength xs y)

/-- The low three bits of a natural number, through the bitwise and of Lean's core library, which
its module system exports without a value. -/
def lowBits (k : Nat) : Nat := k &&& 7

/-- The indices from the low bits of `k`, in steps of one. -/
noncomputable def lowBitsSum (k n : Nat) : ℝ :=
  (List.range' (lowBits k) n).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/-- A core definition whose type mentions no number is index data, so the loop is analyzed as
written. -/
roundoff theorem low_bits_sum_error := fun (k n : Nat) => lowBitsSum k n

/-- The bits of the binary32 square of `k` in Lean's own model of `Float32`, computed by a helper
whose signature holds no number. -/
def hiddenModel (k : Nat) : Nat :=
  let x := Float32.Model.ofNat k
  (Float32.Model.toUInt64 (Float32.Model.mul x x)).toNat

/-- The helper's result as a real number. -/
noncomputable def hiddenModelCast (k : Nat) : ℝ := (hiddenModel k : ℝ)

/--
error: roundoff: ↑(hiddenModel k) casts an integer computed from real or floating-point values, so
the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem hidden_model_error := fun (k : Nat) => hiddenModelCast k

/-- A dictionary of `GetElem` whose getter squares the entry it reads, its value hidden. -/
opaque squaringGetter : GetElem (List (ExecFloat.Binary 8 23)) Nat (ExecFloat.Binary 8 23)
    fun xs i => i < xs.length :=
  ⟨fun xs i h => xs[i] * xs[i]⟩

/-- An entry of a list read through that dictionary. -/
def squaredEntry (xs : List (ExecFloat.Binary 8 23)) (i : Nat) (h : i < xs.length) :
    ExecFloat.Binary 8 23 :=
  @GetElem.getElem _ _ _ _ squaringGetter xs i h

/--
error: roundoff: no numerical rule for squaringGetter.1 xs i h; expose its arithmetic or supply an
explicit bound in the context
-/
#guard_msgs (whitespace := lax) in
roundoff theorem squared_entry_error :=
  fun (xs : List (ExecFloat.Binary 8 23)) (i : Nat) (h : i < xs.length) =>
    ExecFloat.Binary.toReal (squaredEntry xs i h)

/-- The same getter with its value exposed. -/
@[reducible] def squaringRead : GetElem (List (ExecFloat.Binary 8 23)) Nat (ExecFloat.Binary 8 23)
    fun xs i => i < xs.length :=
  ⟨fun xs i h => xs[i] * xs[i]⟩

/-- An entry of a list read through the exposed getter. -/
def squaredRead (xs : List (ExecFloat.Binary 8 23)) (i : Nat) (h : i < xs.length) :
    ExecFloat.Binary 8 23 :=
  @GetElem.getElem _ _ _ _ squaringRead xs i h

/-- The getter is analyzed as the function it is, so the bound carries the product's rounding. -/
roundoff theorem squared_read_error :=
  fun (xs : List (ExecFloat.Binary 8 23)) (i : Nat) (h : i < xs.length) =>
    ExecFloat.Binary.toReal (squaredRead xs i h)

/-- The reference squares the stored entry. -/
example (xs : List (ExecFloat.Binary 8 23)) (i : Nat) (h : i < xs.length) :=
  show _ → |_ - ExecFloat.Binary.toReal xs[i] * ExecFloat.Binary.toReal xs[i]| ≤ _ from
    squared_read_error xs i h

/-- The first position of the largest entry of a function on `Fin n`, for any order. -/
def argmaxOf {α : Type} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] {n : Nat}
    (x : Fin n → α) (h : 0 < n) : Fin n :=
  (List.finRange n).foldl (fun best j => if x best < x j then j else best) ⟨0, h⟩

/-- That position as a real number. -/
noncomputable def argmaxCast {n : Nat} (x : Fin n → Value) (h : 0 < n) : ℝ :=
  ((argmaxOf x h : Nat) : ℝ)

/-- The position compares stored values only, so it is index data and its cast is exact. -/
roundoff theorem argmax_cast_error :=
  fun {n : Nat} (x : Fin n → Value) (h : 0 < n) => argmaxCast x h

/-- The reference is the position itself. -/
example {n : Nat} (x : Fin n → Value) (h : 0 < n) :=
  show |_ - ((argmaxOf x h : Nat) : ℝ)| ≤ 0 from argmax_cast_error x h

/-- The last position of the largest entry, its order decided through `>`, whose dictionary is a
function of the two values. -/
def argmaxLast {α : Type} [LT α] [DecidableRel ((· > ·) : α → α → Prop)] {n : Nat}
    (x : Fin n → α) (h : 0 < n) : Fin n :=
  (List.finRange n).foldl (fun best j => if x best > x j then best else j) ⟨0, h⟩

/-- That position compares stored values only, so its cast is exact too. -/
roundoff theorem argmax_last_error :=
  fun {n : Nat} (x : Fin n → Value) (h : 0 < n) => ((argmaxLast x h : Nat) : ℝ)

/-- The position of the largest square, which the helper computes from the stored values. -/
def argmaxSquare {α : Type} [LT α] [Mul α] [DecidableRel ((· < ·) : α → α → Prop)] {n : Nat}
    (x : Fin n → α) (h : 0 < n) : Fin n :=
  (List.finRange n).foldl (fun best j => if x best * x best < x j * x j then j else best) ⟨0, h⟩

/-- That position as a real number. -/
noncomputable def argmaxSquareCast {n : Nat} (x : Fin n → Value) (h : 0 < n) : ℝ :=
  ((argmaxSquare x h : Nat) : ℝ)

/--
error: roundoff: ↑↑(argmaxSquare x h) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem argmax_square_error :=
  fun {n : Nat} (x : Fin n → Value) (h : 0 < n) => argmaxSquareCast x h

/-- The number of naturals below a thousand whose conversion is below the rounded square of `x`,
which comparisons alone rebuild from the square. -/
noncomputable def countBelow (x : Value) : ℝ :=
  (((List.range 1000).filter fun (i : Nat) =>
    decide (ExecFloat.Binary.ofRat (i : ℚ) < x * x)).length : ℝ)

/--
error: roundoff: ↑(List.filter (fun i => decide (ExecFloat.Binary.ofRat ↑i < x * x)) (List.range
1000)).length casts an integer computed from real or floating-point values, so the reference would
keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem count_below_error := fun (x : Value) => countBelow x

/-- The stored bits of a value, which no comparison reads. -/
noncomputable def storedBits (x : ExecFloat.Binary 8 23) : ℝ := ((x.1.1.toNat : Nat) : ℝ)

/--
error: roundoff: ↑(↑↑x).toNat casts an integer computed from real or floating-point values, so the
reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem stored_bits_error := fun (x : ExecFloat.Binary 8 23) => storedBits x

/-- The number of entries of `xs` whose image under `f` equals `y`, for any type with `==`. -/
def countAfter {α : Type} [BEq α] (f : α → α) (xs : List α) (y : α) : Nat :=
  ((xs.map f).filter fun z => z == y).length

/-- That number for a function `f` the program takes, as a real number. -/
noncomputable def countAfterCast (f : Value → Value) (xs : List Value) (y : Value) : ℝ :=
  (countAfter f xs y : ℝ)

/--
error: roundoff: ↑(countAfter f xs y) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem count_after_error :=
  fun (f : Value → Value) (xs : List Value) (y : Value) => countAfterCast f xs y

/-- The number of indices below `n` at which `f` equals `y`. -/
def countAt {α : Type} [BEq α] (f : Nat → α) (n : Nat) (y : α) : Nat :=
  ((List.range n).filter fun i => f i == y).length

/-- That number for a stored function `f`, as a real number. -/
noncomputable def countAtCast (f : Nat → Value) (n : Nat) (y : Value) : ℝ := (countAt f n y : ℝ)

/-- A stored function read at indices only is index data, so the cast is exact. -/
roundoff theorem count_at_error :=
  fun (f : Nat → Value) (n : Nat) (y : Value) => countAtCast f n y

/-- The reference is the number itself. -/
example (f : Nat → Value) (n : Nat) (y : Value) :=
  show |_ - (countAt f n y : ℝ)| ≤ 0 from count_at_error f n y

/-- A function the program takes, applied to a stored value, as a real number. -/
noncomputable def appliedCast (f : Value → Nat) (x : Value) : ℝ := (f x : ℝ)

/--
error: roundoff: ↑(f x) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem applied_cast_error := fun (f : Value → Nat) (x : Value) => appliedCast f x

/-- A function the program takes, applied to a stored value and then mapped over indices. -/
noncomputable def partialCast (f : Value → Nat → Nat) (x : Value) (n : Nat) : ℝ :=
  ((((List.range n).map (f x)).foldl (· + ·) 0 : Nat) : ℝ)

/--
error: roundoff: ↑(List.foldl (fun x1 x2 => x1 + x2) 0 (List.map (f x) (List.range n))) casts an
integer computed from real or floating-point values, so the reference would keep them; compute it
from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem partial_cast_error :=
  fun (f : Value → Nat → Nat) (x : Value) (n : Nat) => partialCast f x n

/-- `countAfter` of a function held in a pair. -/
noncomputable def pairedCast (p : (Value → Value) × Unit) (xs : List Value) (y : Value) : ℝ :=
  (countAfter p.1 xs y : ℝ)

/--
error: roundoff: ↑(countAfter p.1 xs y) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem paired_cast_error :=
  fun (p : (Value → Value) × Unit) (xs : List Value) (y : Value) => pairedCast p xs y

/-- Functions from a type to itself, under a name that does not unfold reducibly. -/
def Endo (α : Type) := α → α

/-- `countAfter` of a function given through that name. -/
noncomputable def endoCast (f : Endo Value) (xs : List Value) (y : Value) : ℝ :=
  (countAfter f xs y : ℝ)

/--
error: roundoff: ↑(countAfter f xs y) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem endo_cast_error :=
  fun (f : Endo Value) (xs : List Value) (y : Value) => endoCast f xs y

/-- A record that holds a function. -/
structure Callback (α : Type) where
  /-- The function. -/
  run : α → α

/-- `countAfter` of the function of a record. -/
noncomputable def callbackCast (c : Callback Value) (xs : List Value) (y : Value) : ℝ :=
  (countAfter c.run xs y : ℝ)

/--
error: roundoff: ↑(countAfter c.run xs y) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem callback_cast_error :=
  fun (c : Callback Value) (xs : List Value) (y : Value) => callbackCast c xs y

/-- A comparison of configured values that compares their rounded squares. -/
@[instance_reducible] def squareComparison :
    ExecFloat.Comparison (Configured.Family format code plan) :=
  ⟨fun a b => ExecFloat.compare (a * a) (b * b)⟩

/-- Whether two stored values are equal under that comparison, as a real number. -/
noncomputable def squaresEqual (x : Fin 2 → Value) : ℝ :=
  ((if @BEq.beq Value (@execFloatBEq _ _ squareComparison) (x 0) (x 1) then 1 else 0 : Nat) : ℝ)

/--
error: roundoff: ↑(if (x 0 == x 1) = true then 1 else 0) casts an integer computed from real or
floating-point values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem squares_equal_error := fun (x : Fin 2 → Value) => squaresEqual x

/-- An order reversed by a wrapper that holds no number. -/
@[instance_reducible] def reverseOrder (α : Type) (order : LT α) : LT α :=
  ⟨fun a b => order.lt b a⟩

/-- A sum gated by a flag that tests the rounded sum through the reversed order. The test of the
references is the real counterpart of FloatLib's own order only: here it would test the opposite
of what the program tests, so the flag depends on the rounded sum. -/
def reversedGatedSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then
      (state.1 + x, @decide (@LT.lt Value (reverseOrder Value inferInstance) state.1 x)
        (inferInstanceAs (Decidable (x < state.1))))
    else (state.1, true)) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, if shadow = true then decide (accumulator <
value) else true, depends on its rounded state, such as through a test of values that have no
analysis; decide the branch first or keep the tested values exact
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem reversed_gated_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (reversedGatedSum xs)

/-- A sum that stops when an entry leaves it unchanged, tested by the structural equality of the
stored word, under which the two zeros differ while their real values are equal. -/
def wordStallSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then state else
      let next := state.1 + x
      (next, x != 0 && @BEq.beq Value (@instBEqOfDecidableEq Value inferInstance) next state.1))
    (0, false)).1

/--
error: roundoff: a discrete component of the loop state, if shadow = true then shadow else
!decide (ExecFloat.Binary.toReal value = 0) && accumulator + value == accumulator, depends on its
rounded state, such as through a test of values that have no analysis; decide the branch first or
keep the tested values exact
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem word_stall_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (wordStallSum xs)

/-- A sum gated by a flag that compares the rounded sum with a stored entry read at an index chosen
by a rounded square, a choice that the reference of the entry would keep. -/
def tableGatedSum (table : Vector Value 2) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then
      (state.1 + x, decide (state.1 < table[(if x * x < x then 0 else 1 : Fin 2)]))
    else (state.1, true)) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, if shadow = true then decide (accumulator <
table[if value * value < value then 0 else 1]) else true, depends on its rounded state, such as
through a test of values that have no analysis; decide the branch first or keep the tested values
exact
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem table_gated_sum_mixedError :=
  fun (table : Vector Value 2) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (tableGatedSum table xs)

/-- A sum gated by a flag that compares the rounded sum with a function the program takes at a
rounded square. Under a contract against a real function the analysis has no rule for, the
reference of the call would keep the rounded square. -/
def contractGatedSum (f : Value → Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then (state.1 + x, decide (state.1 < f (x * x))) else (state.1, true)) (0, true)).1

/--
error: roundoff: no numerical rule for f (value * value); expose its arithmetic or supply an
explicit bound in the context
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem contract_gated_sum_mixedError :=
  fun (f : Value → Value) (g : ℝ → ℝ) (hformat : format.isIEEE = true)
      (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
        ExecFloat.Binary.isFinite (f a) = true ∧
        MixedError (ExecFloat.Binary.toReal (f a)) (g (ExecFloat.Binary.toReal a))
          (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
      (xs : List Value) =>
    ExecFloat.Binary.toReal (contractGatedSum f xs)

/-- A sum gated by a flag that compares a stored function of the rounded sum with an entry. The
function read at the rounded sum has no analysis, so the test has no references to agree with. -/
def appliedGatedSum (f : Value → Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then (state.1 + x, decide (f state.1 < x)) else (state.1, true)) (0, true)).1

/--
error: roundoff: no numerical rule for f accumulator; expose its arithmetic or supply an explicit
bound in the context
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem applied_gated_sum_mixedError :=
  fun (f : Value → Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (appliedGatedSum f xs)

/-- A real model that hides a rounded square in a definition. -/
noncomputable def hiddenSquare (a : Value) : ℝ := ExecFloat.Binary.toReal (a * a)

/-- A sum gated by a flag that compares the rounded sum with a function the program takes at an
entry. Under a contract against `g (hiddenSquare a)`, the reference of the call would keep the
rounded square inside `hiddenSquare`, which a plain real expression never calls. -/
def callGatedSum (f : Value → Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then (state.1 + x, decide (state.1 < f x)) else (state.1, true)) (0, true)).1

/--
error: roundoff: no numerical rule for f value; expose its arithmetic or supply an explicit bound
in the context
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem hidden_gated_sum_mixedError :=
  fun (f : Value → Value) (g : ℝ → ℝ) (hformat : format.isIEEE = true)
      (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
        ExecFloat.Binary.isFinite (f a) = true ∧
        MixedError (ExecFloat.Binary.toReal (f a)) (g (hiddenSquare a))
          (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
      (xs : List Value) =>
    ExecFloat.Binary.toReal (callGatedSum f xs)

/-- The codec composed with negation, another valid codec of the same stored words. -/
@[instance_reducible] def negatedCodec (c : ExecFloat.ModelCodec plan (Model format) code) :
    ExecFloat.ModelCodec plan (Model format) code where
  toModel raw := Model.neg (c.toModel raw)
  ofModel value := c.ofModel (Model.neg value)
  toModel_ofModel value := by simp [c.toModel_ofModel]
  ofModel_toModel raw := by simp [c.ofModel_toModel]

/-- A sum gated by a flag that tests the rounded sum under the negated codec, while the sum and the
observation keep the codec of the type. Under that codec `<` orders the negated values, so the test
of the references under the observation is not its real counterpart. -/
def negatedGatedSum (c : ExecFloat.ModelCodec plan (Model format) code) (xs : List Value) :
    Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then
      (state.1 + x, letI : ExecFloat.ModelCodec plan (Model format) code := negatedCodec c
        decide (state.1 < x))
    else (state.1, true)) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, if shadow = true then decide (accumulator <
value) else true, depends on its rounded state, such as through a test of values that have no
analysis; decide the branch first or keep the tested values exact
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem negated_gated_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (negatedGatedSum inferInstance xs)

/-- A float component that holds a stored entry read at an index chosen by a rounded square, which
the flag compares with the sum at the next step. The component's reference keeps that choice, so the
test of the references would carry it into the copy. -/
def delayedTableGate (table : Vector Value 2) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value × Bool) x =>
    (if state.2.2 then state.1 + x else state.1, table[(if x * x < x then 0 else 1 : Fin 2)],
      decide (state.1 < state.2.1))) (0, 0, true)).1

/--
error: roundoff: a test of the rounded state reads a component whose reference
ExecFloat.Binary.toReal table[if value * value < value then 0 else 1] is not a plain real
expression, so the test of the references could keep a rounded value
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem delayed_table_gate_mixedError :=
  fun (table : Vector Value 2) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (delayedTableGate table xs)

/-- A sum gated by a flag that compares the rounded sum with an entry and tests a component that
holds a stored entry read at an index chosen by a rounded square. The test of that component is a
test of exact values, so the flag's copy reads the component's reference, which keeps the choice. -/
def carriedTableGate (table : Vector Value 2) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value × Bool) x =>
    (if state.2.2 then state.1 + x else state.1, table[(if x * x < x then 0 else 1 : Fin 2)],
      decide (state.1 + x < x) && decide (state.2.1 < x))) (0, 0, true)).1

/--
error: roundoff: a test of the rounded state reads a component whose reference
ExecFloat.Binary.toReal table[if value * value < value then 0 else 1] is not a plain real
expression, so the test of the references could keep a rounded value
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem carried_table_gate_mixedError :=
  fun (table : Vector Value 2) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (carriedTableGate table xs)

/-- The same flag over a component that holds one of two stored values that a rounded square
chooses. -/
def carriedBranchGate (a b c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value × Bool) x =>
    (if state.2.2 then state.1 + x else state.1, if x * x < c then a else b,
      decide (state.1 + x < x) && decide (state.2.1 < x))) (0, 0, true)).1

/--
error: roundoff: a test of the rounded state reads a component whose reference if h : value * value
< c then ExecFloat.Binary.toReal a else ExecFloat.Binary.toReal b is not a plain real expression, so
the test of the references could keep a rounded value
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem carried_branch_gate_mixedError :=
  fun (a b c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (carriedBranchGate a b c xs)

/-- The same flag over a component that holds the entry itself, a plain reference. -/
def carriedEntryGate (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value × Bool) x =>
    (if state.2.2 then state.1 + x else state.1, x,
      decide (state.1 + x < x) && decide (state.2.1 < x))) (0, 0, true)).1

/-- The bound holds for the executions whose tests of the rounded sum agree with the tests of the
exact sum. -/
roundoff mixed theorem carried_entry_gate_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (carriedEntryGate xs)

/-- A sum of sums whose inner flag compares the inner sum with a component of the outer loop that
holds a stored entry read at an index chosen by a rounded square. An agreement there would read the
outer component's reference, which only the outer loop could check. -/
def nestedTableGate (table : Vector Value 2) (xs ys : List Value) : Value :=
  (xs.foldl (fun (outer : Value × Value) x =>
    ((ys.foldl (fun (inner : Value × Bool) y =>
        if inner.2 then (inner.1 + y, decide (inner.1 < outer.2)) else (inner.1, true))
      (0, true)).1, table[(if x * x < x then 0 else 1 : Fin 2)])) (0, 0)).1

/--
error: roundoff: a test of the rounded state, accumulator < accumulator✝, is in a loop inside
another loop's step, whose state the test of the references could read, so it gets no agreement
premise
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem nested_table_gate_mixedError :=
  fun (table : Vector Value 2) (xs ys : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (nestedTableGate table xs ys)

/-- The same when the outer component holds the entry itself: a loop inside another loop's step
states no agreement premise at all, so this flag is rejected too. -/
def nestedEntryGate (xs ys : List Value) : Value :=
  (xs.foldl (fun (outer : Value × Value) x =>
    ((ys.foldl (fun (inner : Value × Bool) y =>
        if inner.2 then (inner.1 + y, decide (inner.1 < outer.2)) else (inner.1, true))
      (0, true)).1, x)) (0, 0)).1

/--
error: roundoff: a test of the rounded state, accumulator < accumulator✝, is in a loop inside
another loop's step, whose state the test of the references could read, so it gets no agreement
premise
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem nested_entry_gate_mixedError :=
  fun (xs ys : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (nestedEntryGate xs ys)

/-- A sum of sums whose inner flag tests the inner sum through a branch on an outer flag, which
tests an outer component that holds a stored entry read at an index chosen by a rounded square. -/
def nestedFlagGate (table : Vector Value 2) (xs ys : List Value) : Value :=
  (xs.foldl (fun (outer : Value × Value × Bool) x =>
    ((ys.foldl (fun (inner : Value × Bool) y =>
        (if inner.2 then inner.1 + y else inner.1,
          decide ((if outer.2.2 then inner.1 else inner.1 + y) < y))) (0, true)).1,
      table[(if x * x < x then 0 else 1 : Fin 2)], decide (outer.2.1 < 0))) (0, 0, true)).1

/--
error: roundoff: a test of the rounded state, (if discrete✝ = true then accumulator else accumulator
+ value) < value, is in a loop inside another loop's step, whose state the test of the references
could read, so it gets no agreement premise
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem nested_flag_gate_mixedError :=
  fun (table : Vector Value 2) (xs ys : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (nestedFlagGate table xs ys)

/-- The same outer loop whose inner flag starts at the outer flag. -/
def nestedStartGate (table : Vector Value 2) (xs ys : List Value) : Value :=
  (xs.foldl (fun (outer : Value × Value × Bool) x =>
    ((ys.foldl (fun (inner : Value × Bool) y =>
        if inner.2 then (inner.1 + y, decide (inner.1 < y)) else (inner.1, true))
      (0, outer.2.2)).1,
      table[(if x * x < x then 0 else 1 : Fin 2)], decide (outer.2.1 < 0))) (0, 0, true)).1

/--
error: roundoff: a test of the rounded state, accumulator < value, is in a loop inside another
loop's step, whose state the test of the references could read, so it gets no agreement premise
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem nested_start_gate_mixedError :=
  fun (table : Vector Value 2) (xs ys : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (nestedStartGate table xs ys)

/-- A binary32 model that hides a rounded square in a definition. -/
noncomputable def hiddenSquare32 (a : Binary32) : ℝ := ExecFloat.Binary.toReal (a * a)

-- A plain real expression computes on decoded stored values alone: the square of a decoded value
-- is one, and a real function of the rounded square that a definition hides is not, whichever
-- check the tactic meets first.
run_cmd Lean.Elab.Command.liftTermElabM do
  let observe ← Lean.instantiateMVars
    (← Lean.Elab.Term.elabTerm (← `(fun (v : Binary32) => ExecFloat.Binary.toReal v)) none)
  Lean.Meta.withLocalDeclD `x (Lean.mkConst ``Binary32) fun x => do
  let realFunction := Lean.mkForall `r .default (Lean.mkConst ``Real) (Lean.mkConst ``Real)
  Lean.Meta.withLocalDeclD `g realFunction fun g => do
  let decoded := (Lean.mkApp observe x).headBeta
  let square ← Lean.Meta.mkAppM ``HMul.hMul #[decoded, decoded]
  unless ← Roundoff.Tuple.plainReference observe none square do
    throwError "the square of a decoded value is not plain"
  let hidden := Lean.mkApp g (← Lean.Meta.mkAppM ``hiddenSquare32 #[x])
  if ← Roundoff.Tuple.plainReference observe none hidden then
    throwError "a hidden rounded square is plain"

section Reals

/-- An addition on the reals, declared by this section, that rounds the sum to an integer. -/
noncomputable local instance (priority := high) roundingAdd : Add ℝ :=
  ⟨fun a b => (round (a + b) : ℤ)⟩

/-- An order on the reals, declared by this section, that compares the rounded values. -/
noncomputable local instance (priority := high) roundingOrder : LT ℝ :=
  ⟨fun a b => round a < round b⟩

-- Instance search finds both, but a plain real expression takes the reals' own dictionaries only:
-- a sum and a test through them are not plain, the same sum and test through `Real.instAdd` and
-- `Real.instLT` are, as are numerals, `max` and a quotient, and the test of real numbers that an
-- agreement premise states compares by `Real.instLT`.
run_cmd Lean.Elab.Command.liftTermElabM do
  let observe ← Lean.instantiateMVars
    (← Lean.Elab.Term.elabTerm (← `(fun (v : Binary32) => ExecFloat.Binary.toReal v)) none)
  Lean.Meta.withLocalDeclD `x (Lean.mkConst ``Binary32) fun x => do
  let real := Lean.mkConst ``Real
  let decoded := (Lean.mkApp observe x).headBeta
  let sum ← Lean.Meta.mkAppM ``HAdd.hAdd #[decoded, decoded]
  let test ← Lean.Meta.mkAppM ``LT.lt #[decoded, decoded]
  unless (sum.getArg! 3).containsConst (· == ``roundingAdd) &&
      (test.getArg! 1).isConstOf ``roundingOrder do
    throwError "instance search does not find the instances of this section: {sum}, {test}"
  for term in #[sum, test] do
    if ← Roundoff.Tuple.plainReference observe none term then
      throwError "{term}, through an instance of this section, is plain"
  let add := Lean.mkAppN (Lean.mkConst ``instHAdd [0]) #[real, Lean.mkConst ``Real.instAdd]
  let ownSum := Lean.mkAppN (Lean.mkConst ``HAdd.hAdd [0, 0, 0])
    #[real, real, real, add, decoded, decoded]
  let ownTest := Lean.mkAppN (Lean.mkConst ``LT.lt [0])
    #[real, Lean.mkConst ``Real.instLT, decoded, decoded]
  let numerals ← [0, 1, 2, 7].mapM (Lean.Meta.mkNumeral real ·)
  let maximum ← Lean.Meta.mkAppM ``Max.max #[decoded, decoded]
  let quotient ← Lean.Meta.mkAppM ``HDiv.hDiv #[decoded, decoded]
  for term in #[ownSum, ownTest, maximum, quotient] ++ numerals.toArray do
    unless ← Roundoff.Tuple.plainReference observe none term do
      throwError "{term}, through the reals' own dictionary, is not plain"
  let realized ← Roundoff.Tuple.realTest ``LT.lt decoded decoded
  unless (realized.getArg! 1).isConstOf ``Real.instLT do
    throwError "the real test {realized} does not compare by Real.instLT"

/-- A sum gated by a flag that tests the rounded sum, with the instances of this section in scope.
-/
def roundingGatedSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then (state.1 + x, decide (state.1 < x)) else (state.1, true)) (0, true)).1

/-- The bound holds for the executions whose tests of the rounded sum agree with the tests of the
exact sum by the reals' own order. -/
roundoff mixed theorem rounding_gated_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (roundingGatedSum xs)

open Lean in
-- The statement compares real numbers by `Real.instLT` and uses no instance of this section.
run_meta do
  let type := (← getConstInfo ``rounding_gated_sum_mixedError).type
  if type.containsConst (fun name => name == ``roundingAdd || name == ``roundingOrder) then
    throwError "the statement uses an instance of this section: {type}"
  unless (type.find? fun term => term.isAppOfArity ``LT.lt 4 &&
      (term.getArg! 0).isConstOf ``Real && (term.getArg! 1).isConstOf ``Real.instLT).isSome do
    throwError "the statement states no agreement by Real.instLT: {type}"

end Reals

/-- A getter that also takes a multiplication, which it does not use. -/
def mulGet {α : Type} [Inhabited α] [Mul α] (xs : List α) (i : Nat) : α := xs.getD i default

open Lean in
-- A core module is trusted for its origin: Lean's own library holds `Lean.Elab.Command`, while a
-- module of this package, whatever its name, lies in the package's build directory.
run_meta do
  unless ← FloatLib.Floats.Formats.BinaryInterchange.Roundoff.leanLibraryModule
      `Lean.Elab.Command do
    throwError "Lean.Elab.Command is not found in Lean's library"
  if ← FloatLib.Floats.Formats.BinaryInterchange.Roundoff.leanLibraryModule
      `FloatLibTests.Conformance.BinaryInterchange.Roundoff then
    throwError "a test module is taken for one of Lean's library"

/-- The indices from a parameter `start`, `n` of them, in steps of two. -/
noncomputable def stepSum (start n : Nat) : ℝ :=
  (List.range' start n 2).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/-- A range over parameters is index data, so the loop is analyzed as written. -/
roundoff theorem step_sum_error := fun (start n : Nat) => stepSum start n

/-- The reference is the sum of those indices itself. -/
example (start n : Nat) :=
  show |_ - (List.range' start n 2).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0| ≤ _ from
    step_sum_error start n

/-- A sum of the squares of a function on `Fin n`, read over the list of its indices. -/
def finRangeSquares {n : Nat} (x : Fin n → Value) : Value :=
  (List.finRange n).foldl (fun sum i => sum + x i * x i) 0

/-- The indices of `List.finRange` are data, so the loop is analyzed as written. -/
roundoff theorem fin_range_squares_error :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (finRangeSquares x)

/-- The reference squares the decoded entries of `x` at the indices of `List.finRange n`. -/
example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) :=
  show _ → |_ - (List.finRange n).foldl (fun sum i =>
    sum + ExecFloat.Binary.toReal (x i) * ExecFloat.Binary.toReal (x i)) 0| ≤ _ from
    fin_range_squares_error x hformat

/-- The sum of the indices below `n`, as reals. -/
noncomputable def rangeSum (n : Nat) : ℝ :=
  (List.range n).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0

/-- The entries of `List.range` enter the reference as the exact indices. -/
roundoff theorem range_sum_error := fun (n : Nat) => rangeSum n

/-- The reference is the sum of the indices itself. -/
example (n : Nat) :=
  show |_ - (List.range n).foldl (fun (sum : ℝ) (i : Nat) => sum + (i : ℝ)) 0| ≤ _ from
    range_sum_error n

/-- A product passed to a function the program takes. -/
def scaled (f : Value → Value) (x y : Value) : Value := f (x * y)

/-- Under a contract against a real function `g` the analysis has no rule for, the reference is
`g` at the decoded computed product: the product's rounding is not propagated. -/
roundoff mixed theorem scaled_opaque_mixedError :=
  fun (f : Value → Value) (g : ℝ → ℝ) (hformat : format.isIEEE = true)
      (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
        ExecFloat.Binary.isFinite (f a) = true ∧
        MixedError (ExecFloat.Binary.toReal (f a)) (g (ExecFloat.Binary.toReal a))
          (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
      (x y : Value) =>
    ExecFloat.Binary.toReal (scaled f x y)

/-- The reference of the opaque contract is `g` at the computed product. -/
example (f : Value → Value) (g : ℝ → ℝ) (hformat : format.isIEEE = true)
    (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
      ExecFloat.Binary.isFinite (f a) = true ∧
      MixedError (ExecFloat.Binary.toReal (f a)) (g (ExecFloat.Binary.toReal a))
        (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
    (x y : Value) :=
  show _ → _ ∧ MixedError _ (g (ExecFloat.Binary.toReal (x * y))) _ _ from
    scaled_opaque_mixedError f g hformat hf x y

/-- Under the same contract against `Real.exp`, the product's error is propagated through it. -/
roundoff mixed theorem scaled_exp_mixedError :=
  fun (f : Value → Value) (hformat : format.isIEEE = true)
      (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
        ExecFloat.Binary.isFinite (f a) = true ∧
        MixedError (ExecFloat.Binary.toReal (f a)) (Real.exp (ExecFloat.Binary.toReal a))
          (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
      (x y : Value) =>
    ExecFloat.Binary.toReal (scaled f x y)

/-- The reference of the exponential contract is `Real.exp` at the exact product. -/
example (f : Value → Value) (hformat : format.isIEEE = true)
    (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
      ExecFloat.Binary.isFinite (f a) = true ∧
      MixedError (ExecFloat.Binary.toReal (f a)) (Real.exp (ExecFloat.Binary.toReal a))
        (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
    (x y : Value) :=
  show _ → _ ∧ MixedError _ (Real.exp (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal y)) _ _
    from scaled_exp_mixedError f hformat hf x y

/-- The square of a configured value. -/
def square (x : Value) : Value := x * x

/-- An observation under another function states the mixed bound alone. -/
roundoff mixed theorem square_wrapped_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => id (ExecFloat.Binary.toReal (square x))

/-- The configured observation states the finiteness of the square as well. -/
roundoff mixed theorem square_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (square x)

/-- A choice between a product and a sum by a comparison of the operands. -/
def choose (x y : Value) : Value := if x < y then x * y else x + y

/-- Each case is within its budget under its own guard. -/
roundoff theorem choose_error :=
  fun (x y : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (choose x y)

/-- The conditions of the two cases stay under their guards. -/
example (x y : Value) (hformat : format.isIEEE = true)
    (hproduct : x < y → ExecFloat.Binary.isFinite (x * y) = true)
    (hsum : ¬x < y → ExecFloat.Binary.isFinite (x + y) = true) :=
  choose_error x y hformat ⟨hproduct, hsum⟩

/-- The exponential of the correctly rounded dictionary. -/
def expRounded (x : Value) : Value :=
  MathFunctions.exp (self := ExecFloat.Binary.CorrectlyRounded.mathFunctions) x

/-- The exponential of this library's default dictionary, an approximation kernel. -/
def expApprox (x : Value) : Value := MathFunctions.exp x

/-- On an IEEE descriptor the correctly rounded dictionary selects `CorrectlyRounded.exp`, whose
call has the mixed error of one rounding at `Real.exp`. -/
roundoff mixed theorem exp_rounded_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (expRounded x)

/--
error: roundoff: no numerical rule for (ExecFloat.Binary.toModel x).exp; expose its arithmetic or
supply an explicit bound in the context
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem exp_approx_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (expApprox x)

/-- The value an optional choice selects, read through the map that selects it, and a stored
value. -/
roundoff mixed theorem mapped_get_mixedError :=
  fun (choice : Option Bool) (x y : Value)
      (h : (choice.map fun first => if first then x else y).isSome) =>
    ExecFloat.Binary.toReal ((choice.map fun first => if first then x else y).get h + x)

/-- The reference selects between the decoded values by the getter of the original option. -/
example (choice : Option Bool) (x y : Value)
    (h : (choice.map fun first => if first then x else y).isSome) :=
  show _ → _ ∧ MixedError _ ((if choice.get _ = true then ExecFloat.Binary.toReal x
    else ExecFloat.Binary.toReal y) + ExecFloat.Binary.toReal x) _ _ from
    mapped_get_mixedError choice x y h

-- The exponential of the value of an option with no producer fails for the reason its operand
-- does, not through the definition of `Real.exp`.
/--
error: roundoff: no numerical rule for optional producer choice; expose its computation or supply
an explicit bound
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem exp_get_mixedError :=
  fun (choice : Option Value) (h : choice.isSome) (hformat : format.isIEEE = true) =>
    Real.exp (ExecFloat.Binary.toReal (choice.get h))

end Arithmetic

/-- Horner's rule for `a x² + b x + c` on descriptor-model values. -/
def hornerModel (a b c x : Model format) : Model format :=
  Model.add (Model.mul (Model.add (Model.mul a x) b) x) c

/-- A model observation states the mixed bound alone. -/
roundoff mixed theorem horner_model_mixedError :=
  fun (a b c x : Model format) (hformat : format.isIEEE = true) =>
    Model.toReal (hornerModel a b c x)

/-! ## Cyclic finiteness rules -/

/-- A value under a name the rules below mention. -/
def ping (x : Value) : Value := x

/-- The same value under another name. -/
def pong (x : Value) : Value := x

/-- A rule whose premise is its conclusion. -/
theorem isFinite_ping_of_ping (x : Value) (h : ExecFloat.Binary.isFinite (ping x) = true) :
    ExecFloat.Binary.isFinite (ping x) = true := h

/-- One of two rules that need each other. -/
theorem isFinite_ping (x : Value) (h : ExecFloat.Binary.isFinite (pong x) = true) :
    ExecFloat.Binary.isFinite (ping x) = true := h

/-- The other of the two rules. -/
theorem isFinite_pong (x : Value) (h : ExecFloat.Binary.isFinite (ping x) = true) :
    ExecFloat.Binary.isFinite (pong x) = true := h

/-- A rule that applies to every value and needs a new finiteness each time. -/
theorem isFinite_of_neg [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    (x : Value) (h : ExecFloat.Binary.isFinite (-x) = true) :
    ExecFloat.Binary.isFinite x = true := by
  rwa [ExecFloat.Binary.isFinite_neg] at h

section Self

attribute [local roundoff_rule] isFinite_ping_of_ping

/-- The self-cyclic rule is not applied; the finiteness of `ping x` is that of `x`. -/
roundoff mixed theorem ping_self_mixedError := fun (x : Value) => ExecFloat.Binary.toReal (ping x)

end Self

section Mutual

attribute [local roundoff_rule] isFinite_ping isFinite_pong

/-- The finiteness of `ping x` goes through `pong x`, whose own rule would need `ping x` again. -/
roundoff mixed theorem ping_mutual_mixedError :=
  fun (x : Value) => ExecFloat.Binary.toReal (ping x)

end Mutual

section Chain

attribute [local roundoff_rule] isFinite_of_neg

/-- The rule for `-x` would ask for `- -x`, and so on; the search stops and keeps `x`. -/
roundoff mixed theorem ping_chain_mixedError := fun (x : Value) => ExecFloat.Binary.toReal (ping x)

end Chain

/-- Outside their sections the local rules are not registered. -/
roundoff mixed theorem ping_mixedError := fun (x : Value) => ExecFloat.Binary.toReal (ping x)

/-- Each theorem needs only the finiteness of its input. -/
example (x : Value) (h : ExecFloat.Binary.isFinite x = true) :
    ExecFloat.Binary.isFinite (ping x) = true :=
  (ping_self_mixedError x h).1

example (x : Value) (h : ExecFloat.Binary.isFinite x = true) :
    ExecFloat.Binary.isFinite (ping x) = true :=
  (ping_mutual_mixedError x h).1

example [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] (x : Value)
    (h : ExecFloat.Binary.isFinite x = true) : ExecFloat.Binary.isFinite (ping x) = true :=
  (ping_chain_mixedError x h).1

/-! ## Premises read through a getter -/

/-- The entry of a pair at an index, the getter the rules below state their premises with. -/
def entry (xs : Fin 2 → Value) (i : Fin 2) : Value := xs i

omit [ExecFloat.ModelCodec plan (Model format) code] in
/-- An entry is the coordinate it names. -/
theorem entry_eq (xs : Fin 2 → Value) (i : Fin 2) : entry xs i = xs i := rfl

/-- The pair in the other order, a computed container without a finiteness rule. -/
def swap (xs : Fin 2 → Value) : Fin 2 → Value := fun i => xs i.rev

/-- The first entry of a pair. -/
def first (xs : Fin 2 → Value) : Value := xs 0

/-- The second entry of a pair. -/
def second (xs : Fin 2 → Value) : Value := xs 1

/-- The first entry is exact, given that every entry is finite. -/
theorem first_mixedError (xs : Fin 2 → Value) :
    (∀ i, ExecFloat.Binary.isFinite (entry xs i) = true) →
      MixedError (ExecFloat.Binary.toReal (first xs)) (ExecFloat.Binary.toReal (xs 0)) 0 0 :=
  fun _ => MixedError.of_eq rfl

/-- The second entry is exact, given that it is finite. -/
theorem second_mixedError (xs : Fin 2 → Value) :
    ExecFloat.Binary.isFinite (entry xs 1) = true →
      MixedError (ExecFloat.Binary.toReal (second xs)) (ExecFloat.Binary.toReal (xs 1)) 0 0 :=
  fun _ => MixedError.of_eq rfl

public meta section

/-- The getter `entry`, read through its coordinate law. -/
def entries : Roundoff.Extension where
  surfaces := #[``entry]
  coordinateRewrites := #[``entry_eq]

end

section Surface

attribute [local roundoff_extension] entries
attribute [local roundoff_rule] first_mixedError second_mixedError

/-- The premise of `first_mixedError`, about every entry of the swapped pair, normalizes to the
entries of `swap x`, which nothing proves finite; it stays a condition. -/
roundoff mixed theorem first_swap_mixedError :=
  fun (x : Fin 2 → Value) => id (ExecFloat.Binary.toReal (first (swap x)))

/-- The finiteness premise of `second_mixedError` stays a condition the same way. -/
roundoff mixed theorem second_swap_mixedError :=
  fun (x : Fin 2 → Value) => id (ExecFloat.Binary.toReal (second (swap x)))

/-- On a pair of one stored value the premise normalizes to the finiteness of that input. -/
roundoff mixed theorem second_const_mixedError :=
  fun (x : Value) => id (ExecFloat.Binary.toReal (second fun _ => x))

/-- A coordinate read through `id`, as a permutation of tensor axes writes it, normalizes to the
coordinate, so the premise is again the finiteness of the input. -/
roundoff mixed theorem second_id_mixedError :=
  fun (x : Value) => id (ExecFloat.Binary.toReal (second fun i => (id (x, i)).1))

end Surface

/-- Each theorem takes its rule's premise as stated. -/
example (x : Fin 2 → Value) (h : ∀ i, ExecFloat.Binary.isFinite (entry (swap x) i) = true) :
    MixedError (id (ExecFloat.Binary.toReal (first (swap x))))
      (ExecFloat.Binary.toReal (x 1)) 0 0 :=
  first_swap_mixedError x h

example (x : Fin 2 → Value) (h : ExecFloat.Binary.isFinite (entry (swap x) 1) = true) :
    MixedError (id (ExecFloat.Binary.toReal (second (swap x))))
      (ExecFloat.Binary.toReal (x 0)) 0 0 :=
  second_swap_mixedError x h

/-! ## A generated theorem at binary32 -/

/-- A quarter of a binary32 value, by the literal `4`. -/
def quarter (x : Binary32) : Binary32 := x / 4

/-- The quotient by `4` rounds once, under a range condition on the input. -/
roundoff mixed theorem quarter_mixedError :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (quarter x)

/-- For a finite binary32 value of magnitude at most one, the range condition of
`quarter_mixedError` holds, so a quarter of it is finite and rounds once. -/
theorem quarter_of_abs_le_one (x : Binary32) (hfinite : ExecFloat.Binary.isFinite x = true)
    (hx : |ExecFloat.Binary.toReal x| ≤ 1) :
    ExecFloat.Binary.isFinite (quarter x) = true ∧
      MixedError (ExecFloat.Binary.toReal (quarter x)) (ExecFloat.Binary.toReal x / 4)
        (Model.unitRoundoffAt FloatFormat.binary32)
        (Model.underflowErrorAt FloatFormat.binary32) := by
  refine quarter_mixedError x ⟨hfinite, le_trans ?_ (Model.one_le_toReal_posMaxFinite _)⟩
  show |ExecFloat.Binary.toReal x / 4| ≤ 1
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

end FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions

/-! ## Registered extensions -/

public meta section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions

open Lean FloatLib.Floats.Formats.BinaryInterchange

/-- An extension that adds nothing. -/
def nothing : Roundoff.Extension := {}

/-- A read whose container lies past the arguments of `List.length`. -/
def misplaced : Roundoff.Extension where
  reads := #[{ head := ``List.length, arity := 2, fromEnd := 3 }]

/-- A read of a function that is not declared. -/
def undeclared : Roundoff.Extension where
  reads := #[{ head := `List.undeclaredRead, arity := 2 }]

/-- A read through `mulGet`, which trusts no class of the dictionaries it takes. -/
def multiplyingReads : Roundoff.Extension where
  reads := #[{ head := ``mulGet, arity := 5, types := #[``List] }]

/-- Whether `name` is a registered extension in the current environment. -/
def registered (name : Name) : CoreM Bool :=
  return (Roundoff.extensions.getState (← getEnv)).names.contains name

end FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions

open Lean Elab Command FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

section Trust

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

attribute [local roundoff_extension] multiplyingReads

/--
error: roundoff: ↑↑(argmaxSquare x h) casts an integer computed from real or floating-point values,
so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem argmax_square_read_error :=
  fun {n : Nat} (x : Fin n → Value) (h : 0 < n) => argmaxSquareCast x h

end Trust

section Local

attribute [local roundoff_extension] nothing Roundoff.containers

-- A local registration is in the environment, and registering an extension twice keeps one.
run_cmd liftCoreM do
  unless ← registered ``nothing do throwError "the local extension is not registered"
  let names := (Roundoff.extensions.getState (← getEnv)).names
  unless names.size == 3 do throwError "a repeated registration was added: {names}"

end Local

-- The registration ended with its section.
run_cmd liftCoreM do
  if ← registered ``nothing then throwError "the local extension outlived its section"

/--
error: roundoff_extension: `reads` of `misplaced`: the container of `List.length` is argument 3 from
the end of 2
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] misplaced

/--
error: roundoff_extension: `reads` of `undeclared`: `List.undeclaredRead` is not declared
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] undeclared

-- A premise on `entry` that the analysis does not prove is stated through `entry`; one whose normal
-- form it proves is the finiteness of the input.
run_cmd liftTermElabM do
  for (name, stated) in #[(``first_swap_mixedError, true), (``second_swap_mixedError, true),
      (``second_const_mixedError, false), (``second_id_mixedError, false)] do
    let type ← Meta.zetaReduce (← getConstInfo name).type
    let mentions ← Meta.forallTelescope type fun binders _ => binders.anyM fun binder => do
      return ((← Meta.inferType binder).find? (·.isAppOf ``entry)).isSome
    unless mentions == stated do
      throwError "{name} {if stated then "does not state" else "states"} a premise on `entry`"

-- A configured mixed theorem concludes finiteness and a mixed bound; a model or wrapped
-- observation the mixed bound alone; an absolute theorem an absolute bound.
run_cmd liftTermElabM do
  for (name, shape) in #[(``square_mixedError, ``And), (``exp_rounded_mixedError, ``And),
      (``square_wrapped_mixedError, ``MixedError), (``horner_model_mixedError, ``MixedError),
      (``sum_squares_error, ``LE.le)] do
    let type ← Meta.zetaReduce (← getConstInfo name).type
    Meta.forallTelescope type fun _ conclusion => do
      unless conclusion.getAppFn.isConstOf shape do
        throwError "{name} concludes {conclusion}, not a {shape}"
      if shape == ``And then
        let bound := conclusion.appArg!
        unless bound.isAppOfArity ``MixedError 4 do throwError "{name}: no mixed bound"

-- A generated proof depends only on its obligations. A premise goal assigned by a normalization
-- whose residual goal is not an obligation is refused; the residual stated as one is accepted.
/--
error: roundoff: the generated proof depends on a goal that is not an obligation: 2 = 2
-/
#guard_msgs in
run_cmd liftTermElabM do
  let premise ← Meta.mkFreshExprMVar (← Meta.mkEq (mkNatLit 2) (mkNatLit 2))
  let residual ← Meta.mkFreshExprMVar (← Meta.mkEq (mkNatLit 2) (mkNatLit 2))
  premise.mvarId!.assign (← Meta.mkAppM ``id #[residual])
  Roundoff.checkObligations residual #[residual.mvarId!]
  Roundoff.checkObligations premise #[premise.mvarId!]

end FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions
