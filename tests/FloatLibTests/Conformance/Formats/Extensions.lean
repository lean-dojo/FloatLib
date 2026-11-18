/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats

/-!
# Clients of the general posit theory, the working quantizer and the evaluation tables

These tests apply the theorems of `Posit.General` (posits with any number of exponent bits) and of
`Block.Working` (block quantizers in a working arithmetic) as a user would, and read single
entries out of the evaluation tables that the library proves by Lean's kernel
(`FixedPoint.Embedded.Examples`, `P3109.Block.Named`, `P3109.KernelPath.Examples`,
`Posit.KernelPath.Examples`).
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.Extensions

open FloatLib.Numerics FloatLib.Floats FloatLib.Floats.Formats

/-! ## Posits with any number of exponent bits -/

section GeneralPosit

open Posit.General Posit.KernelPath

/-- Codes are ordered as values with three exponent bits, and every value is positive. -/
example : 0 < value 7 3 5 ∧ value 7 3 5 < value 7 3 6 :=
  ⟨value_pos 7 3 5, value_strictMono (by decide) (by decide) (by decide) (by decide)⟩

/-- Rule 2 of the rounding rule, for every `es`: saturation at the least positive code. -/
example {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0)
    (hx : (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) ≤ value p es 1) :
    encode p es bK M E = 1 :=
  encode_of_le_value_one hp hM hx

/-- Rule 2 of the rounding rule, for every `es`: saturation at the greatest code. -/
example {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0)
    (hx : value p es (2 ^ p - 1) ≤ (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) :
    encode p es bK M E = 2 ^ p - 1 :=
  encode_of_value_max_le hp hM hx

/-- Rules 3 to 6, for every `es`: the input is at or above the lower midpoint. -/
example {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0) (hlo : -(p : ℤ) < regime es bK M E)
    (hhi : regime es bK M E < (p : ℤ) - 1) :
    value (p + 1) es (2 * encode p es bK M E - 1) ≤ (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) :=
  (encode_between hp hM hlo hhi).1

/-- An exact product of two positive codes is returned by `mul`, for every `es`. -/
example {p es a b m : ℕ} (hp : 0 < p) (ha0 : 0 < a) (ha : a < 2 ^ p) (hb0 : 0 < b)
    (hb : b < 2 ^ p) (hm0 : 0 < m) (hm : m < 2 ^ p)
    (h : value p es a * value p es b = value p es m) : mul p es a b = m :=
  mul_of_eq_value hp ha0 ha hb0 hb hm0 hm h

/-- At `es = 2` the general value is the standard's value, here for a positive word. -/
example {format : Posit.Format} (x : Posit.Model format) (hnar : x ≠ Posit.Model.nar format)
    (hzero : x ≠ Posit.Model.zero format) (hsign : x.signBit = false) :
    x.toRat? = some (value format.payloadBits 2 x.magnitudeBits) := by
  rw [toRat?_eq_value x hnar hzero, hsign]
  simp

/-- One plus one is two with no exponent bits. -/
example : add 7 0 0x40 0x40 = 0x60 :=
  (List.cons.inj other_exponent_sizes.1).1

end GeneralPosit

/-! ## Quantizers in a working arithmetic -/

section Working

open Block

variable {ι γ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- With the exact scaled input the working quantizer is the exact one. -/
example (F : Block.Format ι γ K) (x : ι → K) (i : ι) :
    F.quantizeWith F.normalized x i = F.quantize x i ∧
      F.reconstructWith F.normalized x i = F.reconstruct x i := by
  rw [Block.Format.quantizeWith_normalized, Block.Format.reconstructWith_normalized]
  exact ⟨rfl, rfl⟩

/-- An exact working arithmetic adds only the error of the reciprocal scale. -/
example (F : Block.Format ι γ K) (r : ι → K) (x : ι → K) (i : ι) {u η M ρ : K}
    (hE : (F.element i).Budget u η M) (hu : 0 ≤ u) (hσ : 0 < F.scale x i)
    (hr : |r i - 1 / F.scale x i| ≤ ρ / F.scale x i) :
    |F.reconstructWith (fun x i => (Rounding.exact : Rounding K).round (x i * r i)) x i - x i| ≤
      (u * (1 + ((1 + 0) * (1 + ρ) - 1)) + ((1 + 0) * (1 + ρ) - 1)) * |x i| +
        F.scale x i * (η + (1 + u) * 0) +
        max 0 ((1 + ((1 + 0) * (1 + ρ) - 1)) * |x i| + F.scale x i * 0 - F.scale x i * M) :=
  F.abs_reconstructWith_mul_sub_le Rounding.exact r x i hE hu Rounding.exact_accurate le_rfl hσ hr

/-- The reciprocal of a product of two scales, computed with one rounded division. -/
example {W : Rounding K} {ε θ ρ o s c : K} (hW : W.Accurate ε θ) (hε : 0 ≤ ε) (ho : 0 < o)
    (hs : 0 < s) (hc : |c - 1 / o| ≤ ρ / o) :
    |W.round (c / s) - 1 / (o * s)| ≤ ((1 + ε) * (1 + ρ) - 1) / (o * s) + θ :=
  hW.abs_round_div_sub_le hε ho hs hc

/-- NVFP4 in binary32 with an exact reciprocal: the bound of the general theorem at `ρ = 0`. -/
example {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ) (x : Fin m × Fin n → ℝ)
    (i : Fin m × Fin n) (hσ : 0 < (nvfp4 outer block).scale x i) :=
  nvfp4_abs_reconstructWith_sub_le outer block x i
    (fun i => 1 / (nvfp4 outer block).scale x i) (ρ := 0) hσ (by simp)

/-- NVFP4: the working quantizer and the exact one store the same element away from a
midpoint. -/
example {m n : ℕ} (outer block : Fin m × Fin n → ℕ × ℕ) (x : Fin m × Fin n → ℝ)
    (i : Fin m × Fin n) (input : (Fin m × Fin n → ℝ) → Fin m × Fin n → ℝ) (a b : ℝ) :=
  nvfp4_quantizeWith_eq_quantize outer block x i input (a := a) (b := b)

end Working

/-! ## Entries of the evaluation tables -/

section Tables

open FixedPoint.Embedded

/-- The first entry of each N1169 table that the library evaluates at the example layout. -/
example : SACCUM_IBIT Layout.example = 8 := (List.cons.inj Examples.ibit).1

example := (List.cons.inj Examples.countls).1
example := (List.cons.inj Examples.strtofx).1
example := (List.cons.inj Examples.strtofx_end).1
example := (List.cons.inj Examples.compare_integerLeft).1
example := (List.cons.inj Examples.compare_integerRight).1
example := (List.cons.inj Examples.integerLeft).1
example := (List.cons.inj Examples.integerRight).1
example := (List.cons.inj Examples.assign_integerLeft).1
example := (List.cons.inj Examples.assign_integerRight).1
example := (List.cons.inj Examples.prefixUpdate).1
example := (List.cons.inj Examples.postfixUpdate).1

/-- The named scaled and block functions of P3109 chapter 5, at the logarithm and at the two
arc tangents.

P3109 interim report v4.1, §§5.6–5.8, specifies these operation families. -/
example (format : P3109.Format) (scale value : Rat) (mode : P3109.RoundingMode)
    (saturation : P3109.SaturationMode) :=
  P3109.Block.Named.scaled_functions format scale value mode saturation _ List.mem_cons_self

example (format : P3109.Format) (policy : P3109.BlockPolicy P3109.Block.Named.Two)
    (block : P3109.Block Rat Rat P3109.Block.Named.Two) (scale : Rat) (lane : Fin 2) :=
  P3109.Block.Named.block_functions format policy block scale lane _ List.mem_cons_self

example (format : P3109.Format) (yScale y xScale x : Rat) (mode : P3109.RoundingMode)
    (saturation : P3109.SaturationMode) :=
  P3109.Block.Named.scaled_angles format yScale y xScale x mode saturation _ List.mem_cons_self

example (format : P3109.Format) (policy : P3109.BlockPolicy P3109.Block.Named.Two)
    (y x : P3109.Block Rat Rat P3109.Block.Named.Two) (scale : Rat) (lane : Fin 2) :=
  P3109.Block.Named.block_angles format policy y x scale lane _ List.mem_cons_self

example := (List.cons.inj P3109.Block.Named.scaled_roots).1
example := (List.cons.inj P3109.KernelPath.Examples.external_queries.1).1
example := Posit.KernelPath.Examples.quire_sum.1
example := Posit.KernelPath.Examples.root_fma.1

end Tables

end FloatLibTests.Conformance.Formats.Extensions
