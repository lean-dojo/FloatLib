/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754
public import FloatLib.Tactic.Roundoff

/-!
# Programs on Lean's native floats, read through their imports

A program on `Float32` or `Float` is observed through `ExecFloat.Binary.ofFloat32` or
`ExecFloat.Binary.ofFloat`, which read the same value as a `Binary32` or `Binary64`. The analysis
moves the import inward by the proved laws of the native operations (addition, subtraction,
multiplication, division, square root, negation, natural-number literals and the two round
trips), so the statements are those of the same program on `Binary32` or `Binary64`, about the
imports of the inputs. These checks read the generated statements in the four modes, for a loop
and for control flow, and the refusal for a host library function with its statement of trust.
-/

@[expose] public section

namespace FloatLibTests.Conformance.IEEE754.RoundoffNative

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

local notation "single " x => (ExecFloat.Binary.ofFloat32 x : Binary32)

local notation "double " x => (ExecFloat.Binary.ofFloat x : Binary64)

local notation "u32" => Model.unitRoundoffAt FloatFormat.binary32

local notation "η32" => Model.underflowErrorAt FloatFormat.binary32

local notation "Ω32" => Model.toReal (Model.posMaxFinite FloatFormat.binary32)

local notation "u64" => Model.unitRoundoffAt FloatFormat.binary64

local notation "η64" => Model.underflowErrorAt FloatFormat.binary64

/-! ## Straight-line arithmetic -/

/-- `a x + y` on native binary32 values. -/
def axpy (a x y : Float32) : Float32 := a * x + y

/-- Forward, mixed. -/
roundoff mixed theorem axpy_mixedError :=
  fun (a x y : Float32) => (single (axpy a x y)).toReal

/-- The statement is that of `a x + y` on `Binary32`: the premises are on the imports of the
inputs and on the real values, and the finiteness of the native result is a conclusion. -/
example (a x y : Float32) (ha : (single a).isFinite = true) (hx : (single x).isFinite = true)
    (hy : (single y).isFinite = true)
    (hproduct : |(single a).toReal * (single x).toReal| ≤ Ω32)
    (hsum : |(single a).toReal * (single x).toReal + (single y).toReal| +
      (u32 * |(single a).toReal * (single x).toReal| + η32) ≤ Ω32) :
    (single (axpy a x y)).isFinite = true ∧
      MixedError (single (axpy a x y)).toReal
        ((single a).toReal * (single x).toReal + (single y).toReal) u32
        ((1 + u32) * (u32 * |(single a).toReal * (single x).toReal| + η32)) :=
  axpy_mixedError a x y ⟨ha, hx, hproduct, hy, hsum⟩

/-- The finiteness of the import is the finiteness test of the native value. -/
example (x : Float32) (hx : x.isFinite = true) : (single x).isFinite = true := by
  rw [ExecFloat.Binary.isFinite_ofFloat32]; exact hx

/-- Forward, absolute. -/
roundoff theorem axpy_error :=
  fun (a x y : Float32) => (single (axpy a x y)).toReal

example (a x y : Float32) :=
  show _ → |(single (axpy a x y)).toReal -
    ((single a).toReal * (single x).toReal + (single y).toReal)| ≤ _ from axpy_error a x y

/-- Closed forward. -/
roundoff closed theorem axpy_closed :=
  fun (a x y : Float32) => (single (axpy a x y)).toReal

example (a x y : Float32)
    (hsum : ((single (a * x)) + (single y)).isFinite = true)
    (hproduct : ((single a) * (single x)).isFinite = true) :
    |(single (axpy a x y)).toReal -
        ((single a).toReal * (single x).toReal + (single y).toReal)| ≤
      |(single a).toReal| * ((1 + u32) ^ 2 - 1) * |(single x).toReal| +
        |(single y).toReal| * u32 + η32 * (1 + u32) :=
  axpy_closed a x y ⟨hsum, hproduct⟩

/-- Backward. -/
roundoff (backward := true) theorem axpy_backward :=
  fun (a x y : Float32) => (single (axpy a x y)).toReal

example (a x y : Float32)
    (hsum : ((single (a * x)) + (single y)).isFinite = true)
    (hproduct : ((single a) * (single x)).isFinite = true) :
    ∃ δa δy, |δa| ≤ (1 + u32) ^ 2 - 1 ∧ |δy| ≤ u32 ∧
      |(single (axpy a x y)).toReal -
        ((single a).toReal * (1 + δa) * (single x).toReal + (single y).toReal * (1 + δy))| ≤
        η32 * (1 + u32) :=
  axpy_backward a x y ⟨hsum, hproduct⟩

/-- A norm on native binary64 values: square root, and the unit roundoff of binary64. -/
def norm (x y : Float) : Float := (x * x + y * y).sqrt

/-- Forward, mixed, for binary64. -/
roundoff mixed theorem norm_mixedError :=
  fun (x y : Float) => (double (norm x y)).toReal

example (x y : Float) :=
  show _ → _ ∧ MixedError _
    (√((double x).toReal * (double x).toReal + (double y).toReal * (double y).toReal)) _ _ from
    norm_mixedError x y

/-- Negation is exact, and a literal is the value it names. -/
def negated (x : Float32) : Float32 := -x * 3

/-- One rounding, of the product. -/
roundoff mixed theorem negated_mixedError :=
  fun (x : Float32) => (single (negated x)).toReal

example (x : Float32) :=
  show _ → _ ∧ MixedError _ (-(single x).toReal * 3) u32 η32 from negated_mixedError x

/-! ## Loops and control flow -/

/-- A native dot product. -/
def dot {n : Nat} (x y : Fin n → Float32) : Float32 :=
  Fin.foldl n (fun s j => s + x j * y j) 0

/-- Forward, mixed: the fold statement of the same loop on `Binary32`, started at exact zero. -/
roundoff mixed theorem dot_mixedError :=
  fun {n : Nat} (x y : Fin n → Float32) => (single (dot x y)).toReal

example {n : Nat} (x y : Fin n → Float32) :=
  show _ → _ ∧ MixedError _ (List.foldl
    (fun reference j => reference + (single (x j)).toReal * (single (y j)).toReal) 0
    (List.finRange n)) _ _ from dot_mixedError x y

/-- Closed forward for the native loop. -/
roundoff closed theorem dot_closed :=
  fun {n : Nat} (x y : Fin n → Float32) => (single (dot x y)).toReal

/-- A branch on a native comparison, kept as the program's choice. -/
def relu (x : Float32) : Float32 := if x > 0 then x * x else 0

/-- The reference and the budgets branch on the native test. -/
roundoff mixed theorem relu_mixedError :=
  fun (x : Float32) => (single (relu x)).toReal

example (x : Float32) :=
  show _ → _ ∧ MixedError _ (if x > 0 then (single x).toReal * (single x).toReal else 0)
    (if x > 0 then u32 else 0) (if x > 0 then η32 else 0) from relu_mixedError x

/-- A match on a size around native arithmetic. -/
def head : (n : Nat) → (Fin n → Float32) → Float32 → Float32
  | 0, _, d => d
  | _ + 1, x, d => x 0 * d

/-- The alternatives of the match, each through the import. -/
roundoff mixed theorem head_mixedError :=
  fun (n : Nat) (x : Fin n → Float32) (d : Float32) => (single (head n x d)).toReal

example (n : Nat) (x : Fin (n + 1) → Float32) (d : Float32)
    (hx : (single (x 0)).isFinite = true) (hd : (single d).isFinite = true)
    (hrange : |(single (x 0)).toReal * (single d).toReal| ≤ Ω32) :
    (single (head (n + 1) x d)).isFinite = true ∧
      MixedError (single (head (n + 1) x d)).toReal ((single (x 0)).toReal * (single d).toReal)
        u32 η32 :=
  head_mixedError (n + 1) x d ⟨hd, hx, hrange⟩

/-- A value exported to the native carrier and imported again is the value. -/
def roundTrip (x y : Binary32) : Float32 :=
  ExecFloat.Binary.toFloat32 x * ExecFloat.Binary.toFloat32 y

/-- The round trip is exact: one rounding, of the product. -/
roundoff mixed theorem roundTrip_mixedError :=
  fun (x y : Binary32) => (single (roundTrip x y)).toReal

example (x y : Binary32) :=
  show _ → _ ∧ MixedError _ (x.toReal * y.toReal) u32 η32 from roundTrip_mixedError x y

/-! ## Refusals -/

/-- A host library function. -/
def hostExp (x : Float32) : Float32 := Float32.exp x * x

-- The elementary functions of the native carriers are host library calls with no rounding
-- guarantee, so no law reads them through the import; the refusal says so.
/--
error: roundoff: no numerical rule for the native operation `Float32.exp` in `x.exp`: no proved law
reads it through its import. The arithmetic of the native carriers follows Lean's logical model,
which the compiled code is trusted to match, and their elementary functions are host library calls
with no rounding guarantee (TRUST.md).
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem hostExp_mixedError :=
  fun (x : Float32) => (single (hostExp x)).toReal

end FloatLibTests.Conformance.IEEE754.RoundoffNative
