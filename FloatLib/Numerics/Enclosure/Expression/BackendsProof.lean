/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Expression.Real
public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof
public import FloatLib.Numerics.Enclosure.Interval.FusedProof
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.InverseTrigProof
public import FloatLib.Numerics.Enclosure.Interval.OperationsProof

/-!
# Real-containment contracts for expression backends

The elementary-function proofs hold for every real member of the input interval.
Outward rounding preserves those bounds when they are stored in another endpoint format.
The integer backend uses the direct binary-grid arithmetic theorems for its algebraic operations.
-/

public section

namespace FloatLib.Numerics.Interval.Backend

variable {α : Type*}

/-- Successful elementary enclosures contain the function value at every real input member. -/
theorem containsReal_elementaryBounds? (config : Config) {op : UnaryOp}
    {I J : Interval ℚ} (h : elementaryBounds? config op I = some J)
    {x : ℝ} (hx : I.ContainsReal some x) : J.ContainsReal some (op.eval x) := by
  cases op with
  | neg | abs | inv | pow => simp [elementaryBounds?] at h
  | exp =>
    cases Option.some.inj h
    exact containsReal_expBounds I config.degree hx
  | log => exact containsReal_logBounds? h hx
  | sin =>
    cases Option.some.inj h
    exact containsReal_sinBounds I config.degree hx
  | cos =>
    cases Option.some.inj h
    exact containsReal_cosBounds I config.degree hx
  | tan => exact containsReal_tanBounds? h hx
  | asin => exact containsReal_asinBounds? h hx
  | acos => exact containsReal_acosBounds? h hx
  | atan =>
    cases Option.some.inj h
    exact containsReal_atanBounds I config.degree hx
  | sinh =>
    cases Option.some.inj h
    exact containsReal_sinhBounds I config.degree hx
  | cosh =>
    cases Option.some.inj h
    exact containsReal_coshBounds I config.degree hx
  | tanh =>
    cases Option.some.inj h
    exact containsReal_tanhBounds I config.degree hx
  | sqrt => exact containsReal_sqrtBounds? h hx

private theorem containsReal_roundElementary? (R : OutwardRounding α ℚ)
    (config : Config) (op : UnaryOp) {I J : Interval α}
    (h : (match I.decode? R.decode with
      | none => none
      | some a =>
        match elementaryBounds? config op a with
        | none => none
        | some b => encloseInterval? R b) = some J)
    {x : ℝ} (hx : I.ContainsReal R.decode x) : J.ContainsReal R.decode (op.eval x) := by
  cases ha : I.decode? R.decode with
  | none => simp [ha] at h
  | some a =>
    cases hb : elementaryBounds? config op a with
    | none => simp [ha, hb] at h
    | some b =>
      have hxa : a.ContainsReal some x := by
        simpa [ContainsReal, Contains] using (containsReal_iff_of_decode? ha x).mp hx
      have hxb := containsReal_elementaryBounds? config hb hxa
      exact containsReal_encloseInterval? R (by simpa [ha, hb] using h)
        (by simpa [ContainsReal, Contains] using hxb)

/-- Any sound rational outward rounder supplies a sound expression backend. -/
theorem ofRounding_sound (R : OutwardRounding α ℚ) (config : Config := {}) :
    (ofRounding R config).Sound where
  const := by
    intro q I h
    obtain ⟨lo, hi, hlo, hhi, hl, hh⟩ := R.sound h
    exact ⟨(lo : ℝ), (hi : ℝ), by simp [ofRounding, hlo], by simp [ofRounding, hhi],
      by exact_mod_cast hl, by exact_mod_cast hh⟩
  unary := by
    intro op I J x h hx
    cases op with
    | neg => exact containsReal_neg? R h hx
    | abs => exact containsReal_abs? R h hx
    | inv => exact containsReal_inv? R h hx
    | pow n => exact containsReal_pow? R n h hx
    | exp => exact containsReal_roundElementary? R config .exp h hx
    | log => exact containsReal_roundElementary? R config .log h hx
    | sin => exact containsReal_roundElementary? R config .sin h hx
    | cos => exact containsReal_roundElementary? R config .cos h hx
    | tan => exact containsReal_roundElementary? R config .tan h hx
    | asin => exact containsReal_roundElementary? R config .asin h hx
    | acos => exact containsReal_roundElementary? R config .acos h hx
    | atan => exact containsReal_roundElementary? R config .atan h hx
    | sinh => exact containsReal_roundElementary? R config .sinh h hx
    | cosh => exact containsReal_roundElementary? R config .cosh h hx
    | tanh => exact containsReal_roundElementary? R config .tanh h hx
    | sqrt => exact containsReal_roundElementary? R config .sqrt h hx
  binary := by
    intro op I J K x y h hx hy
    cases op with
    | add => exact containsReal_add? R h hx hy
    | sub => exact containsReal_sub? R h hx hy
    | mul => exact containsReal_mul? R h hx hy
    | div => exact containsReal_div? R h hx hy
    | min => exact containsReal_min? R h hx hy
    | max => exact containsReal_max? R h hx hy
  ternary := by
    intro op I J K L x y z h hx hy hz
    cases op with
    | fma => exact containsReal_fma? R h hx hy hz

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
      simpa [ofRounding, binaryGrid, decode?, BinaryGrid.decode, BinaryGrid.rounding,
        encloseInterval?, map] using h
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

end FloatLib.Numerics.Interval.Backend
