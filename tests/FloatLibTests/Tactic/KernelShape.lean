/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Division
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Sqrt
public import FloatLib.Numerics.Kernel.Bits.Proof.Length
public import FloatLib.Numerics.Kernel.RootProof
public import FloatLib.Numerics.Kernel.RootShape
public import FloatLib.Tactic.FloatDecide
public import FloatLib.Tactic.KernelShape

/-!
# Checks of `kernel_shape`, of the kernel shape of a term, and of what is built on them

The first section declares the shapes of small stages and compares each with the term that the
shape is meant to be: recursors for `casesOn`, matches and branches on natural numbers, literals
for numerals, the functions behind the operators of `Nat`, computed constants, the shapes of the
stages that a stage calls and the kernel arithmetic of `Int`. It also checks `inlining`, a
private stage, and the error for a constant without a value. The second section checks a
formula tagged `@[kernel_inline]` and a constant with a copy by `kernel_constant`, in a shape
and in a flat form.

The next sections check each branch rule of `Backends.Kernel.Plumbing` by rewriting with it, the
loop over all pairs for a Boolean test, the bit length at the boundaries of its lanes, and the
integer square root on both sides of the 384 bits that its written-out steps cover.

The last section evaluates the scaled decimal projections next to the projections of the same
ratio with its power of ten multiplied out, and decimal quotients and roots by `float_decide`.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.KernelShape

open FloatLib.Numerics.Kernel FloatLib.Floats.ExecFloat.KernelPath

/-! ### The kernel shape of a term -/

/-- A stage as it is written for the compiler: `casesOn`, numerals, operators. -/
def clamp (n : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble n 255) 255 (n + 2 * 3)

kernel_shape clamp

/-- The shape has the recursor, literals, the functions behind the operators and `2 * 3`
computed. -/
example : @clamp.kernel = fun n =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 255) (Nat.add n (nat_lit 6))
      (Nat.ble n (nat_lit 255)) := rfl

example : @clamp = @clamp.kernel := clamp.kernel_eq

/-- A stage that calls a shaped stage and core's integer arithmetic. -/
def clampSum (a b : Int) : Nat :=
  clamp (Int.toNat (Int.add a b))

kernel_shape clampSum

/-- The caller's shape calls the callee's shape and the kernel arithmetic of `Int`. -/
example : @clampSum.kernel = fun a b => clamp.kernel (Z.toNat (Z.add a b)) := rfl

/-- The rule of a shape is in the rewrite set of `float_decide`. -/
example : clampSum 200 (-7) = 199 ∧ clampSum 200 100 = 255 := by
  float_decide

/-- `inlining` unfolds the named stages into the shape. -/
def clampTwice (n : Nat) : Nat := clamp (clamp n)

kernel_shape clampTwice inlining [clamp]

example : @clampTwice.kernel = fun n =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 255)
      (Nat.add
        (Bool.rec (motive := fun _ => Nat) (nat_lit 255) (Nat.add n (nat_lit 6))
          (Nat.ble n (nat_lit 255)))
        (nat_lit 6))
      (Nat.ble
        (Bool.rec (motive := fun _ => Nat) (nat_lit 255) (Nat.add n (nat_lit 6))
          (Nat.ble n (nat_lit 255)))
        (nat_lit 255)) := rfl

/-- A match becomes the recursor, and `Nat.pred` a subtraction. -/
def sign : Int → Nat
  | .ofNat n => Nat.pred n
  | .negSucc _ => 7

kernel_shape sign

example : @sign.kernel = fun x =>
    Int.rec (motive := fun _ => Nat) (fun n => Nat.sub n (nat_lit 1)) (fun _ => nat_lit 7) x := rfl

/-- A branch on an equation of natural numbers becomes the recursor on `Nat.beq`. -/
def pick (a b : Nat) : Nat := if a = b then a <<< 3 else if a < b then b % 7 else 0

kernel_shape pick

example : @pick.kernel = fun a b =>
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.mod b (nat_lit 7))
        (Nat.ble (Nat.succ a) b))
      (Nat.shiftLeft a (nat_lit 3)) (Nat.beq a b) := rfl

section Private

/-- A private stage. -/
private def hidden (n : Nat) : Nat := Bool.casesOn (motive := fun _ => Nat) (Nat.beq n 0) n 1

kernel_shape hidden

example : @hidden.kernel = fun n => Bool.rec (motive := fun _ => Nat) n (nat_lit 1)
    (Nat.beq n (nat_lit 0)) := rfl

example : hidden 0 = 1 ∧ hidden 5 = 5 := by
  simp only [kernel_optimize]
  decide +kernel

end Private

/-- error: `kernel_shape` is for a definition, and `Nat.rec` has no value -/
#guard_msgs in
kernel_shape Nat.rec

/-! ### Tagged formulas and constants with a copy -/

/-- A short formula of a width, unfolded wherever a shape uses it. -/
@[kernel_inline] def mask (w : Nat) : Nat := 2 ^ w - 1

/-- A stage that uses the formula. -/
def low (w n : Nat) : Nat := n &&& mask w

kernel_shape low

example : @low.kernel = fun w n =>
    Nat.land n (Nat.sub (Nat.pow (nat_lit 2) w) (nat_lit 1)) := rfl

/-- A constant of a width that every use evaluates: it gets a copy in kernel shape. -/
def top (w : Nat) : Nat := mask w * 2 ^ w + mask (w + 1)

kernel_constant top

example : @top.kernel = fun w =>
    Nat.add (Nat.mul (Nat.sub (Nat.pow (nat_lit 2) w) (nat_lit 1)) (Nat.pow (nat_lit 2) w))
      (Nat.sub (Nat.pow (nat_lit 2) (Nat.add w (nat_lit 1))) (nat_lit 1)) := rfl

example : @top = @top.kernel := top.kernel_eq

/-- A flat form calls the copy of the constant and unfolds the tagged formula. -/
noncomputable def clipped (w n : Nat) : Nat := kernel_inline% [low] (low w (n + top w))

example : @clipped = fun w n =>
    Nat.land (Nat.add n (top.kernel w)) (Nat.sub (Nat.pow (nat_lit 2) w) (nat_lit 1)) := rfl

example (w n : Nat) : clipped w n = low w (n + top w) := kernel_refl%

/-- A shape calls the copy as well. -/
def above (w n : Nat) : Nat := n - top w

kernel_shape above

example : @above.kernel = fun w n => Nat.sub n (top.kernel w) := rfl

example : clipped 4 20 = 3 ∧ above 4 300 = 29 := by
  simp only [kernel_optimize]
  decide +kernel

/-- error: `kernel_constant` is for a definition, and `Nat.rec` has no value -/
#guard_msgs in
kernel_constant Nat.rec

/-- A constant of a case, defined by a match. -/
def digits : Bool → Nat
  | true => 8
  | false => 6

/-- In a flat form a match on a constructor selects its branch, and one on a variable stays. -/
noncomputable def padded (wide : Bool) (n : Nat) : Nat :=
  kernel_inline% [digits] (n + digits true * digits wide)

/--
info: @[expose] def FloatLibTests.Conformance.Numerics.KernelShape.padded : Bool → ℕ → ℕ :=
fun wide n =>
  n.add
    (Nat.mul 8
      (match wide with
      | true => 8
      | false => 6))
-/
#guard_msgs in
#print padded

/-! ### Branches on natural numbers -/

example (a b x y : Nat) : (if a = b then x else y) =
    Bool.rec (motive := fun _ => Nat) y x (Nat.beq a b) := by
  simp only [kernel_optimize]

example (a b x y : Nat) : (if a ≤ b then x else y) =
    Bool.rec (motive := fun _ => Nat) y x (Nat.ble a b) := by
  simp only [kernel_optimize]

example (a b x y : Nat) : (if a < b then x else y) =
    Bool.rec (motive := fun _ => Nat) y x (Nat.ble (Nat.succ a) b) := by
  simp only [kernel_optimize]

example (a b x y : Nat) : (if a ≠ b then x else y) =
    Bool.rec (motive := fun _ => Nat) x y (Nat.beq a b) := by
  simp only [kernel_optimize]

example (c : Bool) (x y : Nat) : (if c then x else y) =
    Bool.rec (motive := fun _ => Nat) y x c := by
  simp only [kernel_optimize]

example (a b : Nat) : (decide (a = b), decide (a ≤ b), decide (a < b)) =
    (Nat.beq a b, Nat.ble a b, Nat.ble (Nat.succ a) b) := by
  simp only [kernel_optimize]

/-- An `if` between two decidable propositions is stated through their decisions. -/
example (a b : Nat) (c : Bool) (p q : Prop) [Decidable p] [Decidable q] :
    ((if a = b then p else q) =
        (Bool.rec (motive := fun _ => Bool) (decide q) (decide p) (Nat.beq a b) = true)) ∧
      ((if c then p else q) =
        (Bool.rec (motive := fun _ => Bool) (decide q) (decide p) c = true)) := by
  simp only [kernel_optimize, and_self]

/-- An `if` on a Boolean literal is its branch, and the word of a natural number is read back
as a remainder. -/
example (b : Bool) (x y width n : Nat) :
    ((if (false && b) = true then x else y) = y) ∧
      ((if (true && true) = true then x else y) = x) ∧
      ((BitVec.ofNat width n).toNat = Nat.mod n (Nat.pow 2 width)) := by
  simp only [kernel_optimize, and_self]

/-- Two Booleans are compared by recursors. -/
example (a b : Bool) :
    ((a != b) = Bool.rec (motive := fun _ => Bool) b
        (Bool.rec (motive := fun _ => Bool) true false b) a) ∧
      ((a == b) = Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true false b) b a) := by
  simp only [kernel_optimize, and_self]

/-- The signed rational of a rational reads its sign bit from the numerator. -/
example (q : ℚ) : FloatLib.Numerics.SignedRat.ofRat q = FloatLib.Numerics.SignedRat.ofNum q := by
  simp only [kernel_optimize]

example : (FloatLib.Numerics.SignedRat.ofNum (-7 / 3)).negative = true ∧
    (FloatLib.Numerics.SignedRat.ofNum 0).negative = false ∧
    (FloatLib.Numerics.SignedRat.ofNum (7 / 3)).negative = false := by
  decide +kernel

/-- It is still decided, with literals in the condition and with a computed one. -/
example : (if (3 : Nat) = 4 then (1 : Nat) = 2 else (5 : Nat) < 6) ∧
    (if Nat.sqrt 17 ≤ 4 then (5 : Nat) < 6 else (1 : Nat) = 2) := by
  float_decide

example : (if (3 : Nat) = 4 then 10 else if (3 : Nat) < 4 then 20 else 30) = 20 := by
  float_decide

/-! ### The loop over all pairs for a Boolean test -/

example : ∀ a b : Fin 16, Nat.ble (Nat.mul a.val b.val) 225 = true :=
  forall_fin_pairs_test (fun x y => Nat.ble (Nat.mul x y) 225) 256 rfl (by decide +kernel)

/-- The decidable form is the same loop. -/
example : ∀ a b : Fin 16, a.val * b.val ≤ 225 :=
  forall_fin_pairs (relation := fun x y => x * y ≤ 225) 256 rfl (by decide +kernel)

/-! ### Bit lengths at the boundaries of the lanes -/

example : size 0 = 0 ∧ size 1 = 1 ∧ size (2 ^ 64 - 1) = 64 ∧ size (2 ^ 64) = 65 ∧
    size (2 ^ 128 - 1) = 128 ∧ size (2 ^ 128) = 129 ∧ size (2 ^ 192 + 5) = 193 ∧
    size (2 ^ 256 - 1) = 256 ∧ size (2 ^ 256) = 257 ∧ size (2 ^ 1000) = 1001 := by
  decide +kernel

example : size.kernel 0 = 0 ∧ size.kernel 1 = 1 ∧ size.kernel (2 ^ 64 - 1) = 64 ∧
    size.kernel (2 ^ 64) = 65 ∧ size.kernel (2 ^ 128 - 1) = 128 ∧ size.kernel (2 ^ 128) = 129 ∧
    size.kernel (2 ^ 192 + 5) = 193 ∧ size.kernel (2 ^ 256 - 1) = 256 ∧
    size.kernel (2 ^ 256) = 257 ∧ size.kernel (2 ^ 1000) = 1001 := by
  decide +kernel

/-- Above 256 bits: the halvings below `2 ^ 1024` and the windows beyond, at their boundaries. -/
example : size (2 ^ 384 + 1) = 385 ∧ size (2 ^ 512 - 1) = 512 ∧ size (2 ^ 512) = 513 ∧
    size (2 ^ 768 + 3) = 769 ∧ size (2 ^ 1024 - 1) = 1024 ∧ size (2 ^ 1024) = 1025 ∧
    size (2 ^ 4096 - 1) = 4096 ∧ size (2 ^ 4096) = 4097 ∧ size (2 ^ 16384) = 16385 ∧
    size (2 ^ 100000 + 7) = 100001 := by
  decide +kernel

example : size.kernel (2 ^ 384 + 1) = 385 ∧ size.kernel (2 ^ 512 - 1) = 512 ∧
    size.kernel (2 ^ 512) = 513 ∧ size.kernel (2 ^ 768 + 3) = 769 ∧
    size.kernel (2 ^ 1024 - 1) = 1024 ∧ size.kernel (2 ^ 1024) = 1025 ∧
    size.kernel (2 ^ 4096 - 1) = 4096 ∧ size.kernel (2 ^ 4096) = 4097 ∧
    size.kernel (2 ^ 16384) = 16385 ∧ size.kernel (2 ^ 100000 + 7) = 100001 := by
  decide +kernel

example : size256 0 = 0 ∧ size256 (2 ^ 127) = 128 ∧ size256 (2 ^ 255 + 1) = 256 ∧
    size512 (2 ^ 63) = 64 ∧ size512 (2 ^ 300) = 301 ∧ size512 (2 ^ 512 - 1) = 512 ∧
    size256.kernel (2 ^ 200) = 201 ∧ size512.kernel (2 ^ 511) = 512 ∧
    sizeAbove.kernel (2 ^ 256) = 257 := by
  decide +kernel

/-- The rules of the shapes rewrite a bit length under `float_decide`. -/
example : size (2 ^ 700 + 2 ^ 3) = 701 := by
  float_decide

/-! ### Integer square roots: written-out steps, and the full iteration above 384 bits -/

example : isqrt 0 = 0 ∧ isqrt 1 = 1 ∧ isqrt 15 = 3 ∧ isqrt 16 = 4 ∧
    isqrt (10 ^ 40 - 1) = 10 ^ 20 - 1 ∧ isqrt (2 ^ 384 - 1) = 2 ^ 192 - 1 ∧
    isqrt (10 ^ 120) = 10 ^ 60 ∧ isqrt (10 ^ 400 + 1) = 10 ^ 200 := by
  decide +kernel

example : isqrt.kernel 0 = 0 ∧ isqrt.kernel 1 = 1 ∧ isqrt.kernel 15 = 3 ∧ isqrt.kernel 16 = 4 ∧
    isqrt.kernel (10 ^ 40 - 1) = 10 ^ 20 - 1 ∧ isqrt.kernel (2 ^ 384 - 1) = 2 ^ 192 - 1 ∧
    isqrt.kernel (10 ^ 120) = 10 ^ 60 ∧ isqrt.kernel (10 ^ 400 + 1) = 10 ^ 200 := by
  decide +kernel

/-- The eight written-out steps reach the root at the top of their range. -/
example : isRoot 2 (sqrtGuess (2 ^ 384 - 1) 384) (2 ^ 384 - 1) = true := by decide +kernel

end FloatLibTests.Conformance.Numerics.KernelShape

namespace FloatLibTests.Conformance.Formats.DecimalScaled

open FloatLib.Floats.Formats.DecimalInterchange

/-! ### Decimal division and square root on scaled ratios -/

/-- The scaled projection is the projection of the ratio with its power, evaluated: a power
that is cancelled, a small one, a zero numerator, a tie, and decimal128. -/
example :
    KernelPath.projectScaled .decimal64 .nearest false 1 3 398 0 =
        KernelPath.projectRatio .decimal64 .nearest false (1 * 10 ^ 398) 3 0 ∧
      KernelPath.projectScaled .decimal64 .nearest true 12345 67 5 (-3) =
        KernelPath.projectRatio .decimal64 .nearest true (12345 * 10 ^ 5) 67 (-3) ∧
      KernelPath.projectScaled .decimal64 .up false 0 7 400 2 =
        KernelPath.projectRatio .decimal64 .up false (0 * 10 ^ 400) 7 2 ∧
      KernelPath.projectScaled .decimal32 .nearest false 12345675 10 101 0 =
        KernelPath.projectRatio .decimal32 .nearest false (12345675 * 10 ^ 101) 10 0 ∧
      KernelPath.projectScaled .decimal128 .down true 7 9 6176 0 =
        KernelPath.projectRatio .decimal128 .down true (7 * 10 ^ 6176) 9 0 := by
  decide +kernel

example :
    KernelPath.sqrtScaled .decimal64 .nearest 2 1 796 0 =
        KernelPath.sqrtRatio .decimal64 .nearest (2 * 10 ^ 796) 1 0 ∧
      KernelPath.sqrtScaled .decimal64 .up 2 1 797 0 =
        KernelPath.sqrtRatio .decimal64 .up (2 * 10 ^ 797) 1 0 ∧
      KernelPath.sqrtScaled .decimal64 .nearest 0 1 800 0 =
        KernelPath.sqrtRatio .decimal64 .nearest (0 * 10 ^ 800) 1 0 ∧
      KernelPath.sqrtScaled .decimal32 .nearest 144 1 3 1 =
        KernelPath.sqrtRatio .decimal32 .nearest (144 * 10 ^ 3) 1 1 ∧
      KernelPath.sqrtScaled .decimal128 .down 3 7 12352 0 =
        KernelPath.sqrtRatio .decimal128 .down (3 * 10 ^ 12352) 7 0 := by
  decide +kernel

/-- One third in decimal64, with its flag, and an exact quotient at its preferred exponent. -/
example : Arithmetic.div .decimal64 .nearest (.finite false 1 0) (.finite false 3 0) =
      { value := .finite false 3333333333333333 (-16), status := { inexact := true } } ∧
    (Arithmetic.div .decimal64 .nearest (.finite false 1000 0) (.finite true 8 2)).1 =
      .finite true 125 (-2) ∧
    (Arithmetic.div .decimal128 .nearest (.finite false 2 0) (.finite false 3 0)).1 =
      .finite false 6666666666666666666666666666666667 (-34) := by
  float_decide

/-- The square root of two, of an exact square, and a reciprocal square root. -/
example : (Arithmetic.sqrt .decimal64 .nearest (.finite false 2 0)).1 =
      .finite false 1414213562373095 (-15) ∧
    (Arithmetic.sqrt .decimal64 .nearest (.finite false 144 0)).1 = .finite false 12 0 ∧
    (Arithmetic.rSqrt .decimal64 .nearest (.finite false 4 0)).1 = .finite false 5 (-1) ∧
    (Arithmetic.hypot .decimal64 .nearest (.finite false 3 0) (.finite false 4 0)).1 =
      .finite false 5 0 := by
  float_decide

end FloatLibTests.Conformance.Formats.DecimalScaled
