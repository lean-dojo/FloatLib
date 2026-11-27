/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Expression.Real
public import FloatLib.Numerics.Enclosure.Interval.FusedProof
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.InverseTrigProof

import FloatLib.Numerics.Enclosure.Expression.ElementaryTableProof

/-!
# Real-containment contracts for expression backends

The elementary enclosures contain the function value at every real member of the input
interval, and outward rounding keeps those bounds when they're stored in another endpoint format.
`containsReal_elementaryBounds?` is the containment theorem of `Backend.elementaryWith` at its
legacy settings. `ofRoundings_sound` asks for that contract from the table it is given and for
three rounders that read endpoints alike, and `ofRounding_sound` and `rational_sound` are its
instances. For its algebraic operations, the integer backend uses the binary-grid arithmetic
theorems themselves.
-/

public section

namespace FloatLib.Numerics.Interval.Backend

variable {α : Type*}

/--
Successful elementary enclosures contain the function value at every real input member: the table
`elementaryWith` at its legacy settings (`containsReal_elementaryWith`, `elementaryWith_legacy`).
-/
theorem containsReal_elementaryBounds? (config : Config) {op : UnaryOp}
    {I J : Interval ℚ} (h : elementaryBounds? config op I = some J)
    {x : ℝ} (hx : I.ContainsReal some x) : J.ContainsReal some (op.eval x) :=
  containsReal_elementaryWith (.legacy config)
    ((congrFun (congrFun (elementaryWith_legacy config) op) I).trans h) hx

/-- The elementary step of `ofRoundings`: decode with `R`, enclose with `table` and round outward
with `R`. When every enclosure of `table` contains the function value, so does the result. -/
private theorem containsReal_roundTable? (R : OutwardRounding α ℚ)
    {table : UnaryOp → Interval ℚ → Option (Interval ℚ)}
    (htable : ∀ {op : UnaryOp} {I J : Interval ℚ}, table op I = some J →
      ∀ {x : ℝ}, I.ContainsReal some x → J.ContainsReal some (op.eval x))
    (op : UnaryOp) {I J : Interval α}
    (h : (match I.decode? R.decode with
      | none => none
      | some a =>
        match table op a with
        | none => none
        | some b => encloseInterval? R b) = some J)
    {x : ℝ} (hx : I.ContainsReal R.decode x) : J.ContainsReal R.decode (op.eval x) := by
  cases ha : I.decode? R.decode with
  | none => simp [ha] at h
  | some a =>
    cases hb : table op a with
    | none => simp [ha, hb] at h
    | some b =>
      have hxa : a.ContainsReal some x := by
        simpa [ContainsReal, Contains] using (containsReal_iff_of_decode? ha x).mp hx
      exact containsReal_encloseInterval? R (by simpa [ha, hb] using h)
        (by simpa [ContainsReal, Contains] using htable hb hxa)

/--
Three rational outward rounders that decode endpoints alike, and a table whose successful
enclosures contain the function value at every real member of the input, give a sound expression
backend. `containsReal_elementaryBounds?` is this contract for `elementaryBounds?`.
-/
theorem ofRoundings_sound (algebra quotient elementary : OutwardRounding α ℚ)
    (table : UnaryOp → Interval ℚ → Option (Interval ℚ))
    (hquotient : quotient.decode = algebra.decode)
    (helementary : elementary.decode = algebra.decode)
    (htable : ∀ {op : UnaryOp} {I J : Interval ℚ}, table op I = some J →
      ∀ {x : ℝ}, I.ContainsReal some x → J.ContainsReal some (op.eval x)) :
    (ofRoundings algebra quotient elementary table).Sound := by
  obtain ⟨_, quotientEnclose, quotientSound⟩ := quotient
  obtain ⟨_, elementaryEnclose, elementarySound⟩ := elementary
  dsimp only at hquotient helementary
  subst hquotient helementary
  set quotient : OutwardRounding α ℚ := ⟨algebra.decode, quotientEnclose, quotientSound⟩
  set elementary : OutwardRounding α ℚ := ⟨algebra.decode, elementaryEnclose, elementarySound⟩
  constructor
  · intro q I h
    obtain ⟨lo, hi, hlo, hhi, hl, hh⟩ := algebra.sound h
    exact ⟨(lo : ℝ), (hi : ℝ), by simp [ofRoundings, hlo], by simp [ofRoundings, hhi],
      by exact_mod_cast hl, by exact_mod_cast hh⟩
  · intro op I J x h hx
    cases op with
    | neg => exact containsReal_neg? algebra h hx
    | abs => exact containsReal_abs? algebra h hx
    | inv => exact containsReal_inv? quotient h hx
    | pow n => exact containsReal_pow? algebra n h hx
    | _ => exact containsReal_roundTable? elementary htable _ h hx
  · intro op I J K x y h hx hy
    cases op with
    | add => exact containsReal_add? algebra h hx hy
    | sub => exact containsReal_sub? algebra h hx hy
    | mul => exact containsReal_mul? algebra h hx hy
    | div => exact containsReal_div? quotient h hx hy
    | min => exact containsReal_min? algebra h hx hy
    | max => exact containsReal_max? algebra h hx hy
  · intro op I J K L x y z h hx hy hz
    cases op with
    | fma => exact containsReal_fma? algebra h hx hy hz
  · intros
    contradiction

/-- Any sound rational outward rounder supplies a sound expression backend. -/
theorem ofRounding_sound (R : OutwardRounding α ℚ) (config : Config := {}) :
    (ofRounding R config).Sound :=
  ofRoundings_sound R R R _ rfl rfl (containsReal_elementaryBounds? config)

/-- Exact rational endpoints satisfy the common real-containment contract. -/
theorem rational_sound (config : Config := {}) : (rational config).Sound :=
  ofRounding_sound _ config

/-- Direct integer arithmetic and rounded elementary bounds give a sound binary-grid backend. -/
theorem binaryGrid_sound (config : Config := {}) : (binaryGrid config).Sound where
  const := by
    intro q I h
    cases Option.some.inj h
    exact BinaryGrid.containsReal_enclose config.precision q
  unary := by
    intro op I J x h hx
    simp only [binaryGrid] at hx ⊢
    cases op with
    | neg =>
      cases Option.some.inj h
      exact BinaryGrid.containsReal_neg config.precision hx
    | abs =>
      cases Option.some.inj h
      exact BinaryGrid.containsReal_abs config.precision hx
    | inv =>
      have hone : (point (BinaryGrid.scale config.precision)).ContainsReal
          (BinaryGrid.decode config.precision) (1 : ℝ) := by
        simp [BinaryGrid.containsReal_iff, point]
      simpa only [UnaryOp.eval, one_div] using
        BinaryGrid.containsReal_div? config.precision h hone hx
    | pow n =>
      by_cases hn : n = 2
      · subst n
        simp only [binaryGrid, ↓reduceIte, Option.some.injEq] at h
        subst J
        exact BinaryGrid.containsReal_square config.precision hx
      · simp only [binaryGrid, hn, ↓reduceIte, Option.some.injEq] at h
        subst J
        exact BinaryGrid.containsReal_pow config.precision hx n
    | exp | log | sin | cos | tan | asin | acos | atan | sinh | cosh | tanh | sqrt =>
      apply (ofRounding_sound (BinaryGrid.rounding config.precision) config).unary _ hx
      simpa [ofRounding, ofRoundings, binaryGrid, decode?, BinaryGrid.decode,
        BinaryGrid.rounding, encloseInterval?, map] using h
  binary := by
    intro op I J K x y h hx hy
    simp only [binaryGrid] at hx hy ⊢
    cases op with
    | add =>
      cases Option.some.inj h
      exact BinaryGrid.containsReal_add config.precision hx hy
    | sub =>
      cases Option.some.inj h
      exact BinaryGrid.containsReal_sub config.precision hx hy
    | mul =>
      cases Option.some.inj h
      exact BinaryGrid.containsReal_mul config.precision hx hy
    | div => exact BinaryGrid.containsReal_div? config.precision h hx hy
    | min =>
      cases Option.some.inj h
      rw [BinaryGrid.containsReal_iff] at hx hy ⊢
      simpa [BinaryGrid.value_min, BinaryOp.eval] using
        And.intro (min_le_min hx.1 hy.1) (min_le_min hx.2 hy.2)
    | max =>
      cases Option.some.inj h
      rw [BinaryGrid.containsReal_iff] at hx hy ⊢
      simpa [BinaryGrid.value_max, BinaryOp.eval] using
        And.intro (max_le_max hx.1 hy.1) (max_le_max hx.2 hy.2)
  ternary := by
    intro op I J K L x y z h hx hy hz
    cases op with
    | fma =>
      cases Option.some.inj h
      exact BinaryGrid.containsReal_fma config.precision hx hy hz

  call := by intros; contradiction

end FloatLib.Numerics.Interval.Backend
