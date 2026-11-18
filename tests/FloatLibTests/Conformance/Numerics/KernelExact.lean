/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
public import FloatLib.Numerics.Exact.IntegerRoot.Runtime
public import FloatLib.Numerics.Kernel.BallProof
public import FloatLib.Numerics.Kernel.Bisection
public import FloatLib.Numerics.Kernel.FracProof
public import FloatLib.Numerics.Kernel.ModProof
public import FloatLib.Numerics.Kernel.QProof
public import FloatLib.Numerics.Kernel.RootProof
public import FloatLib.Numerics.Packed.F2Proof
public import FloatLib.Numerics.Packed.MatrixProof
public import FloatLib.Numerics.Packed.OrderProof
public import FloatLib.Tactic.FloatDecide
public import Mathlib.Basic.Real.Basic

meta import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime

/-!
# Checks of the kernel arithmetic layer

Concrete arithmetic checks use `decide +kernel`. The transfer examples apply the specification
theorems and compose the normal-form, rounding and enclosure guarantees. The examples cover
each sign case of the `Int` functions against core's operations, the bit
operations, the `Rat` functions against core's, fractions with their reading in the rationals,
dyadic numbers and balls with a bound
on real numbers, modular powers and inverses, the
packed matrix inverse over `𝔽₂`, the rewrite rules tagged `@[kernel_optimize]` both directly
and through `float_decide`, and the
`BinaryGrid` operations on values worked out by hand. The last section checks that a false
statement is refused and that the definitions still have compiled code.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.KernelExact

open FloatLib.Numerics FloatLib.Numerics.Kernel FloatLib.Numerics.Interval

/-! ### Bits -/

example : size 0 = 0 ∧ size 1 = 1 ∧ size 255 = 8 ∧ size 256 = 9 := by decide +kernel
example : size (2 ^ 63) = 64 ∧ size (2 ^ 64) = 65 ∧ size (2 ^ 127 + 1) = 128 := by decide +kernel
example : size (2 ^ 300 + 5) = 301 ∧ size (2 ^ 511) = 512 ∧ size (2 ^ 512) = 513 := by
  decide +kernel
example : size (2 ^ 5000 - 1) = 5000 ∧ size (2 ^ 70000) = 70001 := by decide +kernel
example : testBit (2 ^ 300 + 5) 2 = true ∧ testBit (2 ^ 300 + 5) 1 = false ∧ bit 6 1 = 1 := by
  decide +kernel
example : lowBits 1000 4 = 8 ∧ ceilShift 1000 4 = 63 ∧ ceilShift 1024 4 = 64 ∧
    ceilDiv 10 3 = 4 := by
  decide +kernel
example : popCount 0 = 0 ∧ popCount 255 = 8 ∧ popCount (2 ^ 300 + 5) = 3 ∧
    popCount (2 ^ 1000 - 1) = 1000 ∧ factorial 20 = 2432902008176640000 := by decide +kernel
example : popCount (2 ^ 64 - 1) = 64 ∧ popCount (2 ^ 64) = 1 ∧ popCount (2 ^ 64 + 2 ^ 63 + 5) = 4 ∧
    popCount (2 ^ 100000 - 1 - 2 ^ 777) = 99999 := by decide +kernel

/-- Transfer a packed bit and a low-bit window to core's bit and remainder operations. -/
example : (Nat.testBit 0xdeadbeef 5).toNat = 1 ∧ (2 ^ 70000 + 5) % 2 ^ 512 = 5 := by
  rw [← bit_eq, ← lowBits_eq]
  decide +kernel

/-! ### `Int` functions: all sign cases on a small grid, against core's operations -/

/-- Whether `f` and `g` agree on all pairs of integers in `[-4, 4]`. -/
def agree (f g : Int → Int → Int) : Bool :=
  (List.range 9).all fun i => (List.range 9).all fun j =>
    f (Int.ofNat i - 4) (Int.ofNat j - 4) == g (Int.ofNat i - 4) (Int.ofNat j - 4)

example : agree Z.add (· + ·) = true := by decide +kernel
example : agree Z.sub (· - ·) = true := by decide +kernel
example : agree Z.mul (· * ·) = true := by decide +kernel
example : agree Z.ediv (· / ·) = true := by decide +kernel
example : agree Z.emod (· % ·) = true := by decide +kernel
example : agree Z.fdiv Int.fdiv = true := by decide +kernel
example : agree Z.min min = true := by decide +kernel
example : agree Z.max max = true := by decide +kernel
example : agree (fun a b => Z.pow a b.toNat) (fun a b => a ^ b.toNat) = true := by decide +kernel
example : agree (fun a b => Z.shiftRight a b.toNat) (fun a b => a >>> b.toNat) = true := by
  decide +kernel
example : agree (fun a b => Z.ceilShift a b.toNat) (fun a b => -((-a) >>> b.toNat)) = true := by
  decide +kernel
example : Z.neg 5 = -5 ∧ Z.neg (-5) = 5 ∧ Z.neg 0 = 0 ∧ Z.natAbs (-7) = 7 ∧ Z.toNat (-7) = 0 := by
  decide +kernel
example : Z.floorDiv (-37) 5 = -8 ∧ Z.ceilDiv (-37) 5 = -7 ∧ Z.mod (-37) 5 = 3 := by decide +kernel
example : Z.mul (-(2 ^ 200 + 7)) (2 ^ 190 + 3) = -((2 ^ 200 + 7) * (2 ^ 190 + 3)) := by
  decide +kernel

/-! ### Pairs and fractions -/

example : (Signed.mul ⟨3, 10⟩ ⟨2, 0⟩).toInt = -14 ∧ (Signed.add ⟨3, 10⟩ ⟨9, 0⟩).toInt = 2 := by
  decide +kernel
example : Signed.le ⟨3, 10⟩ ⟨0, 6⟩ = true ∧ (Signed.floorShift ⟨0, 37⟩ 2).toInt = -10 := by
  decide +kernel

/-- Addition is already normalized, so conversion to an integer and back preserves the pair. -/
example (x y : Signed) : Signed.ofInt (x.add y).toInt = x.add y := by
  apply Signed.eq_of_toInt_eq (Signed.normal_ofInt _) (Signed.normal_add x y)
  simp

/-- Normalization and multiplication compose with the canonical integer representation. -/
example (x : Signed) (n : Nat) :
    x.norm.mul (Signed.ofNat n) = Signed.ofInt (x.toInt * n) := by
  apply Signed.eq_of_toInt_eq
    (Signed.normal_mul (Signed.normal_norm x) (Signed.normal_ofNat n)) (Signed.normal_ofInt _)
  simp

/-- Negating a difference also keeps the canonical representation. -/
example (x y : Signed) :
    (x.sub y).neg = Signed.ofInt (-(x.toInt - y.toInt)) := by
  apply Signed.eq_of_toInt_eq
    (Signed.normal_neg (Signed.normal_sub x y)) (Signed.normal_ofInt _)
  simp

/-- `1/3 + 1/6 ≤ 1/2`, checked on fractions by cross-multiplication. -/
theorem third_add_sixth :
    Frac.le (Frac.add ⟨1, 0, 3, by decide⟩ ⟨1, 0, 6, by decide⟩) ⟨1, 0, 2, by decide⟩ = true := by
  decide +kernel

/-- The same statement in the rationals, from the kernel check. -/
example : (1 : ℚ) / 3 + 1 / 6 ≤ 1 / 2 := by
  have h := (Frac.le_iff _ _).1 third_add_sixth
  simpa using h

/-- And in the reals. -/
example : ((1 / 3 + 1 / 6 : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
  have h := Frac.le_cast (K := ℝ) third_add_sixth
  simpa using h

example : Frac.lt (Frac.mul ⟨0, 2, 3, by decide⟩ ⟨5, 0, 7, by decide⟩) (Frac.ofNat 0) = true ∧
    Frac.beq (Frac.div ⟨1, 0, 2, by decide⟩ ⟨0, 3, 4, by decide⟩) ⟨0, 2, 3, by decide⟩ = true ∧
    (Frac.floor ⟨0, 7, 2, by decide⟩).toInt = -4 ∧ (Frac.ceil ⟨0, 7, 2, by decide⟩).toInt = -3 := by
  decide +kernel
example : (Frac.normalize ⟨0, 12, 18, by decide⟩).den = 3 ∧
    (Frac.normalize ⟨0, 12, 18, by decide⟩).minus = 2 := by decide +kernel

/-- The floor and ceiling specifications transfer negative rounding to ordinary rationals. -/
example : ⌊(Frac.mk 0 7 2 (by decide)).toRat⌋ = -4 ∧
    ⌈(Frac.mk 0 7 2 (by decide)).toRat⌉ = -3 := by
  rw [← Frac.toInt_floor, ← Frac.toInt_ceil]
  decide +kernel

/-! ### `Rat` functions: against core's operations on a grid of small fractions -/

/-- The fractions `i / j - 2` for `i < 9` and `1 ≤ j ≤ 3`, in lowest terms. -/
def fractions : List Rat :=
  (List.range 9).flatMap fun i => (List.range 3).map fun j => mkRat (Int.ofNat i) (j + 1) - 2

/-- Whether `f` and `g` agree on all pairs of `fractions`. -/
def agreeRat {α : Type} [DecidableEq α] (f g : Rat → Rat → α) : Bool :=
  fractions.all fun a => fractions.all fun b => decide (f a b = g a b)

example : agreeRat Q.add (· + ·) = true := by decide +kernel
example : agreeRat Q.sub (· - ·) = true := by decide +kernel
example : agreeRat Q.mul (· * ·) = true := by decide +kernel
example : agreeRat Q.div (· / ·) = true := by decide +kernel
example : agreeRat Q.le (fun a b => decide (a ≤ b)) = true := by decide +kernel
example : agreeRat Q.lt (fun a b => decide (a < b)) = true := by decide +kernel
example : agreeRat Q.beq (fun a b => decide (a = b)) = true := by decide +kernel
example : agreeRat (fun a _ => Q.neg a) (fun a _ => -a) = true := by decide +kernel
example : agreeRat (fun a _ => Q.inv a) (fun a _ => a⁻¹) = true := by decide +kernel
example : agreeRat (fun a _ => Q.pow a 5) (fun a _ => a ^ 5) = true := by decide +kernel
example : agreeRat (fun a _ => Q.floor a) (fun a _ => Rat.floor a) = true := by decide +kernel
example : agreeRat (fun a _ => Q.ceil a) (fun a _ => Rat.ceil a) = true := by decide +kernel
example : agreeRat (fun a _ => Q.mulPow2 a 3) (fun a _ => a * 8) = true := by decide +kernel
example : agreeRat (fun a _ => Q.divPow2 a 3) (fun a _ => a / 8) = true := by decide +kernel
example : Q.mk 6 (-4 : Int).natAbs = mkRat 3 2 ∧ Q.mk 5 0 = 0 ∧
    Q.abs (mkRat (-3) 4) = mkRat 3 4 := by
  decide +kernel

/-! ### Dyadic numbers and balls -/

example : Dyad.ofScaled 5 (-3) = ⟨5, 0, 3⟩ ∧ Dyad.ofScaled (-3) 2 = ⟨0, 12, 0⟩ := by
  constructor <;> rfl
example : (Dyad.mk 5 0 3).add ⟨3, 0, 2⟩ = ⟨11, 0, 3⟩ ∧ (Dyad.mk 5 0 3).sub ⟨3, 0, 2⟩ = ⟨0, 1, 3⟩ ∧
    (Dyad.mk 5 0 3).mul ⟨0, 3, 2⟩ = ⟨0, 15, 5⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl
example : Dyad.le ⟨5, 0, 3⟩ ⟨3, 0, 2⟩ = true ∧ Dyad.lt ⟨3, 0, 2⟩ ⟨5, 0, 3⟩ = false ∧
    Dyad.beq ⟨6, 0, 3⟩ ⟨3, 0, 2⟩ = true ∧ Dyad.isNeg ⟨2, 7, 9⟩ = true := by decide +kernel
/-- `11/8` and `-11/8` rounded to halves, down and up, and `11/8` cut to two bits. -/
example : (Dyad.mk 11 0 3).roundDown 1 = ⟨2, 0, 1⟩ ∧ (Dyad.mk 11 0 3).roundUp 1 = ⟨3, 0, 1⟩ ∧
    (Dyad.mk 0 11 3).roundDown 1 = ⟨0, 3, 1⟩ ∧ (Dyad.mk 0 11 3).roundUp 1 = ⟨0, 2, 1⟩ ∧
    (Dyad.mk 11 0 3).trimDown 2 = ⟨2, 0, 1⟩ ∧ (Dyad.mk 11 0 1).dropDown 3 = ⟨4, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
example : (Dyad.mk 5 0 3).mulPow2 5 = ⟨20, 0, 0⟩ ∧ (Dyad.mk 5 0 3).divPow2 2 = ⟨5, 0, 5⟩ := by
  constructor <;> rfl

/-- Directed rounding brackets a value within two grid units. -/
example (x : Dyad) (p : Nat) :
    (x.roundUp p).toRat - (x.roundDown p).toRat < 2 / 2 ^ p := by
  have hsum : (2 : ℚ) / 2 ^ p = 1 / 2 ^ p + 1 / 2 ^ p := by ring
  rw [hsum]
  linarith [Dyad.lt_roundDown_add x p, Dyad.roundUp_lt_add x p]

/-- Trimming preserves the order of the two enclosing endpoints. -/
example (x : Dyad) (count : Nat) :
    (x.trimDown count).toRat ≤ (x.trimUp count).toRat :=
  (Dyad.trimDown_le x count).trans (Dyad.le_trimUp x count)

/-- The radius invariant makes every ball's endpoints ordered. -/
example (b : Ball) : b.lower.toRat ≤ b.upper.toRat := by
  rw [Ball.toRat_lower, Ball.toRat_upper]
  linarith [Ball.radius_nonneg b]

/-- The ball `5/8 ± 1/8` squared is `25/64 ± 11/64`, whose upper end is `9/16`. -/
example : (Ball.mk 5 0 1 3).mul ⟨5, 0, 1, 3⟩ = ⟨25, 0, 11, 6⟩ ∧
    ((Ball.mk 5 0 1 3).mul ⟨5, 0, 1, 3⟩).upper = ⟨36, 0, 6⟩ := by
  constructor <;> rfl
/-- Rounding `25/64 ± 11/64` to quarters gives `1/4 ± 1/2`, and to eighths `3/8 ± 3/8`. -/
example : (Ball.mk 25 0 11 6).round 2 = ⟨1, 0, 2, 2⟩ ∧ (Ball.mk 25 0 11 6).round 3 = ⟨3, 0, 3, 3⟩ ∧
    (Ball.mk 25 0 11 6).round 9 = ⟨25, 0, 11, 6⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
example : Ball.ofFrac ⟨1, 0, 3, by decide⟩ 4 = ⟨5, 0, 1, 4⟩ ∧
    Ball.ofFrac ⟨0, 1, 3, by decide⟩ 4 = ⟨0, 6, 1, 4⟩ ∧
    Ball.ofBounds ⟨1, 0, 2⟩ ⟨3, 0, 1⟩ = ⟨7, 0, 5, 3⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Fraction enclosures and a strict ball comparison prove a real inequality. -/
example : (1 : ℝ) / 3 + 1 / 6 < 1 := by
  have h₁ := Ball.contains_ofFrac (K := ℝ) ⟨1, 0, 3, by decide⟩ 8
  have h₂ := Ball.contains_ofFrac (K := ℝ) ⟨1, 0, 6, by decide⟩ 8
  have h := Ball.lt_sound (by decide +kernel) (Ball.contains_add h₁ h₂)
    (Ball.contains_ofNat (K := ℝ) 1)
  convert h using 1 <;> norm_num

/-- Constructing, rounding and trimming a ball keeps every real in the original interval. -/
example (x : ℝ) (hlo : 1 / 4 ≤ x) (hhi : x ≤ 3 / 2) : x < 2 := by
  have hb : (Ball.ofBounds ⟨1, 0, 2⟩ ⟨3, 0, 1⟩).Contains x :=
    Ball.contains_ofBounds (by norm_num at hlo ⊢; exact hlo)
      (by norm_num at hhi ⊢; exact hhi)
  exact Ball.lt_sound (by decide +kernel)
    (Ball.contains_trim (Ball.contains_round hb 8) 16) (Ball.contains_ofNat 2)

/-- A passing nonzero check excludes zero from the ball's real interpretation. -/
example : ¬ (Ball.mk 5 7 1 2).Contains (0 : ℝ) :=
  (Ball.apart_iff _).1 (by decide +kernel)

/-- A bound on real numbers from a kernel check: `x * x ≤ 9/16` for `|x - 5/8| ≤ 1/8`. -/
example (x : ℝ) (hx : |x - 5 / 8| ≤ 1 / 8) : x * x ≤ 9 / 16 := by
  have hb : (Ball.mk 5 0 1 3).Contains x := by
    rw [Ball.contains_mk]
    norm_num at hx ⊢
    exact hx
  have hc : (Ball.mk 9 0 0 4).Contains ((9 : ℝ) / 16) := by
    rw [Ball.contains_mk]
    norm_num
  exact Ball.le_sound (by decide +kernel) (Ball.contains_mul hb hb) hc

/-- The reciprocals of `3` and `-3` to ten binary digits, and the test for zero. -/
example : Ball.inv ⟨3, 0, 0, 0⟩ 10 = ⟨683, 0, 1, 11⟩ ∧ Ball.inv ⟨0, 3, 0, 0⟩ 10 = ⟨0, 683, 1, 11⟩ ∧
    Ball.apart ⟨5, 0, 5, 2⟩ = false ∧ Ball.apart ⟨5, 7, 1, 2⟩ = true ∧
    Ball.div ⟨1, 0, 0, 0⟩ ⟨3, 0, 0, 0⟩ 10 = ⟨683, 0, 1, 11⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- A bound on a reciprocal from a kernel check: `x⁻¹ ≤ 2` for `|x - 5/8| ≤ 1/8`. -/
example (x : ℝ) (hx : |x - 5 / 8| ≤ 1 / 8) : x⁻¹ ≤ 2 := by
  have hb : (Ball.mk 5 0 1 3).Contains x := by
    rw [Ball.contains_mk]
    norm_num at hx ⊢
    exact hx
  have hc : (Ball.mk 2 0 0 0).Contains (2 : ℝ) := by
    rw [Ball.contains_mk]
    norm_num
  exact Ball.le_sound (by decide +kernel) (Ball.contains_inv (by decide +kernel) 10 hb) hc

/-- A bound on a quotient from a kernel check: `x / y ≤ 2` for `x` and `y` within `1/8` of
`5/8`. -/
example (x y : ℝ) (hx : |x - 5 / 8| ≤ 1 / 8) (hy : |y - 5 / 8| ≤ 1 / 8) : x / y ≤ 2 := by
  have hb : ∀ t : ℝ, |t - 5 / 8| ≤ 1 / 8 → (Ball.mk 5 0 1 3).Contains t := fun t ht => by
    rw [Ball.contains_mk]
    norm_num at ht ⊢
    exact ht
  have hc : (Ball.mk 2 0 0 0).Contains (2 : ℝ) := by
    rw [Ball.contains_mk]
    norm_num
  exact Ball.le_sound (by decide +kernel)
    (Ball.contains_div (by decide +kernel) 10 (hb x hx) (hb y hy)) hc

/-! ### Modular arithmetic -/

example : powMod 3 (2 ^ 127 - 2) (2 ^ 127 - 1) = 1 := by decide +kernel
example : powModWindow 0 3 1000 1000003 = powModWindow 5 3 1000 1000003 := by decide +kernel
example : invMod 7 1000003 = 714288 ∧ isInvMod 7 714288 1000003 = true := by decide +kernel

/-- Coprimality supplies the premise that makes the computed modular inverse valid. -/
example : isInvMod 7 (invMod 7 1000003) 1000003 = true :=
  (isInvMod_iff _ _ _).2 (invMod_spec (by decide +kernel))

/-- A statement about a power, from the kernel check of `powMod`. -/
example : 3 ^ (2 ^ 127 - 2) % (2 ^ 127 - 1) = 1 := by
  rw [← powMod_eq]
  decide +kernel

/-! ### A matrix inverse over the field of two elements -/

/-- The rows of a matrix of size twelve, its inverse, and the matrix in lanes of twelve bits. -/
def rowsB : List Nat := [2856, 2872, 3192, 3276, 1852, 2575, 787, 3762, 3885, 3035, 4064, 388]
def rowsM : List Nat := [841, 3380, 1619, 2046, 3, 2971, 2595, 3527, 916, 3498, 1051, 602]
def packedB : Nat := 2117875901641740415363549333427729839917864

example : Packed.F2.isInverse 12 12 packedB rowsM = true := by decide +kernel
/-- The single packed check proves every row of the matrix product is a unit row. -/
example : ∀ i < 12, Packed.F2.rowMul (Packed.lane 12 i packedB) rowsM = 2 ^ i :=
  Packed.F2.isInverse_sound (by decide +kernel)

example : Packed.lane 12 3 packedB = 3276 ∧ Packed.F2.rowMul 3276 rowsM = 2 ^ 3 := by
  decide +kernel
/-- A wrong inverse is refused. -/
example : Packed.F2.isInverse 12 12 packedB (rowsM.set 0 840) = false := by decide +kernel
/-- A matrix that is not square is refused: `[0, 1]` has two rows where `n = 1`, although row
`10₂` times it is the unit row. -/
example : Packed.F2.isInverse 2 1 2 [0, 1] = false := by decide +kernel
/-- A passing check gives the shape: twelve rows, each below `2 ^ 12`. -/
example : rowsM.length = 12 ∧ ∀ m ∈ rowsM, m < 2 ^ 12 :=
  (Packed.F2.isInverse_square (w := 12) (B := packedB) (by decide +kernel)).2

/-! ### A matrix product and a lanewise comparison on packed rows -/

/-- `[[1, 2], [3, 4]] * [[5, 6], [7, -8]] = [[19, -10], [43, -14]]`: the columns of the first
matrix in lanes of 16 bits, the rows of the second in lanes of 32 bits, the product column after
column in lanes of 16 bits. -/
theorem product_check :
    Packed.matMulCheck 16 3 4 2 2 [Packed.pack 16 [1, 3], Packed.pack 16 [2, 4]]
      [Packed.pack 32 [5, 6], Packed.pack 32 [7, -8]] (Packed.pack 16 [19, 43, -10, -14]) =
          true := by
  decide +kernel

/-- A wrong entry is refused. -/
example :
    Packed.matMulCheck 16 3 4 2 2 [Packed.pack 16 [1, 3], Packed.pack 16 [2, 4]]
      [Packed.pack 32 [5, 6], Packed.pack 32 [7, -8]] (Packed.pack 16 [19, 43, -10, -13]) =
          false := by
  decide +kernel

/-- Two columns against one row is refused, although the first pair alone has the product. -/
example : Packed.matMulCheck 8 1 1 1 1 [129, 129] [129] 129 = false := by decide +kernel

/-- A passing check has as many columns as rows. -/
example : [Packed.pack 16 [1, 3], Packed.pack 16 [2, 4]].length =
    [Packed.pack 32 [5, 6], Packed.pack 32 [7, -8]].length :=
  Packed.length_eq_of_matMulCheck product_check

/-- Transfer the passing check to the ordinary integer matrix product, in column order. -/
example :
    Packed.colRowProduct [[1, 3], [2, 4]] [[5, 6], [7, -8]] = [19, 43, -10, -14] := by
  exact (Packed.entries_matMul product_check (by decide) (by decide)).symm

example : Packed.lanesLe 16 3 (Packed.pack 16 [1, 20, 300] (signed := false))
    (Packed.pack 16 [1, 21, 30000] (signed := false)) = true := by decide +kernel
example : Packed.lanesLe 16 3 (Packed.pack 16 [1, 22, 300] (signed := false))
    (Packed.pack 16 [1, 21, 30000] (signed := false)) = false := by decide +kernel

/-- The packed comparison transfers to each of the three unsigned lanes. -/
example : ∀ k < 3,
    Packed.lane 16 k (Packed.pack 16 [1, 20, 300] (signed := false)) ≤
      Packed.lane 16 k (Packed.pack 16 [1, 21, 30000] (signed := false)) :=
  Packed.lanesLe_sound (by decide +kernel) (by decide)

/-! ### Bisection -/

/-- Whether `r * r ≤ 1000`, on the kernel's own product and comparison. -/
def squareBelow (r : Nat) : Bool := Nat.ble (Nat.mul r r) 1000

/-- The largest `r` with `r * r ≤ 1000` among the numbers below `2 ^ 6`: six steps. -/
example : Kernel.bisect squareBelow 6 0 = 31 := by decide +kernel

/-- The search stays in its interval: a predicate that always holds gives the last number, and
one that fails right after the start gives the start. -/
example : Kernel.bisect (fun _ => true) 6 10 = 73 ∧
    Kernel.bisect (fun r => Nat.ble r 10) 6 10 = 10 := by
  decide +kernel

/-- The result is the largest number at which a downward-closed predicate holds. -/
example : squareBelow (Kernel.bisect squareBelow 6 0) = true ∧
    ∀ j, Kernel.bisect squareBelow 6 0 < j → squareBelow j = false := by
  refine Kernel.bisect_spec _ (fun i j hij hj => ?_) 6 0 (by decide) (fun j hj => ?_)
  · have hj' : j * j ≤ 1000 := Nat.le_of_ble_eq_true hj
    exact Nat.ble_eq_true_of_le ((Nat.mul_le_mul hij hij).trans hj')
  · have hbig : 64 * 64 ≤ j * j := Nat.mul_le_mul hj hj
    cases h : squareBelow j
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (show ¬ (j * j ≤ 1000) by omega)

/-! ### Roots -/

example : isqrt (10 ^ 40) = 10 ^ 20 ∧ isqrt (10 ^ 40 - 1) = 10 ^ 20 - 1 ∧ isqrt 0 = 0 ∧
    isqrt 1 = 1 := by
  decide +kernel
example : isRoot 3 (10 ^ 10) (10 ^ 30 + 5) = true ∧ isRoot 3 (10 ^ 10) (10 ^ 30 - 1) = false := by
  decide +kernel
example : IntegerRoot.newton 5 (7 ^ 50 + 3) = 7 ^ 10 ∧ IntegerRoot.newton 0 9 = 1 ∧
    IntegerRoot.newton 1 9 = 9 := by decide +kernel

/-! ### Rewrite rules -/

example : (123456789 : Int) * 987654321 - 5 ≤ 121932631112635270 := by
  simp only [kernel_optimize]
  decide +kernel

example : (-7 : Int) ^ 3 + 2 * 171 = -1 ∧ min (-3 : Int) 4 = -3 := by
  simp only [kernel_optimize]
  decide +kernel

example : Nat.log2 (2 ^ 300 + 5) = 300 ∧ Nat.testBit (2 ^ 300 + 5) 2 = true ∧
    (Nat.digits 2 (2 ^ 300 + 5)).sum = 3 := by
  simp only [kernel_optimize]
  decide +kernel

example : (1 : Rat) / 3 + 1 / 6 ≤ 1 / 2 ∧ |(-7 : Rat) / 4| * 2 < 4 ∧ (2 : Rat) / 3 ≠ 3 / 4 := by
  simp only [kernel_optimize]
  decide +kernel

/-- A false statement is not proved: its negation is. -/
example : ¬ ((3 : Int) * 4 = 13) := by
  simp only [kernel_optimize]
  decide +kernel

/-! ### Exact rules through `float_decide` -/

open FloatLib.Floats.ExecFloat.KernelPath

namespace FloatDecide

/-- Integer multiplication, subtraction and comparison use the exact registry. -/
theorem integer :
    (123456789 : Int) * 987654321 - 5 ≤ 121932631112635270 := by float_decide

/-- Rational division and addition compose with the comparison rule. -/
theorem rational : (3 : Rat) / 7 + 2 / 5 < 6 / 7 := by float_decide

/-- Large bit lengths use the shared windowed algorithm. -/
theorem logarithm : (2 ^ 4000 + 12345).log2 = 4000 := by float_decide

/-- The bit-test rule reaches a natural-number shift and mask. -/
theorem bit : Nat.testBit 0xdeadbeef 5 = true := by float_decide

/-- Powers and modular arithmetic compose with the integer projection rule. -/
theorem modular : ((7 : Int) ^ 4 % 11).natAbs = 3 := by float_decide

/-- A binary digit sum is rewritten to the packed population count. -/
theorem population : (Nat.digits 2 (2 ^ 300 + 5)).sum = 3 := by float_decide

/-- Absolute value, floor and comparisons can occur in one compound goal. -/
theorem floor : |(-7 : Rat) / 4| * 2 < 4 ∧ ⌊(22 : Rat) / 7⌋ = 3 := by float_decide

end FloatDecide

/-! ### `BinaryGrid` on values worked out by hand, in the kernel and compiled -/

/-- Binary splitting handles an empty range and composes two affine steps in Horner order. -/
example (term : Nat → Enclosure.Taylor.Block) (start : Nat) (tail : ℚ) :
    (Enclosure.Taylor.split term start 0).eval tail = tail := by
  rw [Enclosure.Taylor.split_zero, Enclosure.Taylor.Block.eval_identity]

example (term : Nat → Enclosure.Taylor.Block) (start : Nat) (tail : ℚ) :
    (Enclosure.Taylor.split term start 2).eval tail =
      (term start).eval ((term (start + 1)).eval tail) := by
  rw [Enclosure.Taylor.split_add_two term start 0, Enclosure.Taylor.split_one,
    Enclosure.Taylor.split_one, Enclosure.Taylor.Block.eval_comp]

/-- The documented range-reduction heuristic agrees with its kernel implementation. -/
example : Enclosure.BinaryGrid.expExtraScale (1 / 8) 4 64 = 9 := by
  rw [Enclosure.BinaryGrid.expExtraScale_def]
  decide +kernel

example : BinaryGrid.mul 4 ⟨-37, 21⟩ ⟨5, 9⟩ = ⟨-21, 12⟩ := by decide +kernel
example : BinaryGrid.square 4 ⟨-37, 21⟩ = ⟨0, 86⟩ := by decide +kernel
example : BinaryGrid.add ⟨-37, 21⟩ ⟨5, 9⟩ = ⟨-32, 30⟩ ∧
    BinaryGrid.sub ⟨-37, 21⟩ ⟨5, 9⟩ = ⟨-46, 16⟩ ∧
    BinaryGrid.neg ⟨-37, 21⟩ = ⟨-21, 37⟩ ∧ BinaryGrid.abs ⟨-37, 21⟩ = ⟨0, 37⟩ := by decide +kernel
example : BinaryGrid.divBounds (-37) 5 = ⟨-8, -7⟩ ∧ BinaryGrid.divBounds 35 (-5) = ⟨-7, -7⟩ ∧
    BinaryGrid.div? 4 ⟨1, 2⟩ ⟨-1, 1⟩ = none := by decide +kernel
example : BinaryGrid.pow 4 ⟨-32, 16⟩ 3 = ⟨-128, 16⟩ ∧ BinaryGrid.pow 4 ⟨-32, 16⟩ 2 = ⟨0, 64⟩ := by
  decide +kernel
example : Enclosure.BinaryGrid.divideNat ⟨-37, 21⟩ 5 = ⟨-8, 5⟩ := by decide +kernel

/-- The operations keep compiled code: this is evaluated by the compiler, not by the kernel. -/
def compiledProduct : Interval Int := BinaryGrid.mul 4 ⟨-37, 21⟩ ⟨5, 9⟩

#guard compiledProduct.lo == -21 && compiledProduct.hi == 12
#guard (BinaryGrid.pow 4 ⟨-32, 16⟩ 3).lo == -128
#guard (Enclosure.BinaryGrid.exp (1 / 3) 20 64).lo ≤ (Enclosure.BinaryGrid.exp (1 / 3) 20 64).hi

end FloatLibTests.Conformance.Numerics.KernelExact
