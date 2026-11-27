/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Expression.ElementaryTable
public import FloatLib.Numerics.Enclosure.Expression.Real
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.InverseTrigProof
public import FloatLib.Numerics.Enclosure.Interval.SharpTrigProof
public import FloatLib.Numerics.Enclosure.Interval.TotalProof

/-!
# The elementary table: the legacy settings and real containment

At the legacy settings, `Backend.elementaryWith` is `Backend.elementaryBounds?`
(`Backend.elementaryWith_legacy`) by definition. Every enclosure of
`Backend.elementaryWith s` contains the value of its operation at every real member of the input
interval, whatever the settings `s` (`Backend.containsReal_elementaryWith`). Each case is the
containment theorem of the enclosure that the settings select. For the binary-grid exponential and
logarithm, FloatLib's point kernels enclose the values at the two ends of the interval, and
`Real.exp` and `Real.log` are monotone.
-/

public section

namespace FloatLib.Numerics.Interval

/-- The binary-grid exponential bounds contain `exp x` for every real member `x` of the
interval. -/
theorem containsReal_gridExpBounds (I : Interval ℚ) (degree bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (gridExpBounds I degree bits).ContainsReal some (Real.exp x) := by
  apply containsReal_monotoneBounds _ Real.exp I (fun _ _ _ _ h => Real.exp_le_exp.mpr h) ?_ hx
  intro q _
  exact (containsReal_some_iff _ _).2 (Enclosure.BinaryGrid.contains_exp q degree bits)

/-- A binary-grid logarithm enclosure contains `log x` for every real member `x` of the
interval. -/
theorem containsReal_gridLogBounds? {I K : Interval ℚ} {degree bits : Nat}
    (h : gridLogBounds? I degree bits = some K) {x : ℝ} (hx : I.ContainsReal some x) :
    K.ContainsReal some (Real.log x) := by
  unfold gridLogBounds? at h
  split at h
  · rename_i hpos
    cases h
    have hreal : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    apply containsReal_monotoneBounds _ Real.log I ?_ ?_ hx
    · intro a ha b hb hab
      exact Real.strictMonoOn_log.monotoneOn (hreal.trans_le ha.1) (hreal.trans_le hb.1) hab
    · intro q hq
      exact (containsReal_some_iff _ _).2
        (Enclosure.BinaryGrid.contains_log q degree bits (hpos.trans_le hq.1))
  · simp at h

namespace Backend

/-- At the legacy settings the table is `elementaryBounds? config`, for every operation and every
interval. -/
theorem elementaryWith_legacy (config : Config) :
    elementaryWith (.legacy config) = elementaryBounds? config := rfl

/-- Every enclosure of the table contains the value of its operation at every real member of the
input interval, at every setting. -/
theorem containsReal_elementaryWith (s : ElementarySettings) {op : UnaryOp}
    {I J : Interval ℚ} (h : elementaryWith s op I = some J)
    {x : ℝ} (hx : I.ContainsReal some x) : J.ContainsReal some (op.eval x) := by
  cases op with
  | neg | abs | inv | pow => simp [elementaryWith] at h
  | exp =>
    cases Option.some.inj h
    split
    · exact containsReal_gridExpBounds I _ _ hx
    · exact containsReal_expBounds I _ hx
  | log =>
    simp only [elementaryWith] at h
    split at h
    · exact containsReal_gridLogBounds? h hx
    · split at h
      · exact Total.containsReal_log? h hx
      · exact containsReal_logBounds? h hx
  | sin =>
    cases Option.some.inj h
    split
    · exact containsReal_sharpSinBounds I _ _ hx
    · exact containsReal_sinBounds I _ hx
  | cos =>
    cases Option.some.inj h
    split
    · exact containsReal_sharpCosBounds I _ _ hx
    · exact containsReal_cosBounds I _ hx
  | tan =>
    simp only [elementaryWith] at h
    split at h
    · split at h
      · rename_i hdiv
        cases h
        rw [Internal.divRational?_def] at hdiv
        simpa only [UnaryOp.eval, Real.tan_eq_sin_div_cos, Internal.rationalOutwardRounding] using
          containsReal_div? Internal.rationalOutwardRounding hdiv
            (containsReal_sharpSinBounds I _ _ hx) (containsReal_sharpCosBounds I _ _ hx)
      · exact containsReal_tanBounds? h hx
    · exact containsReal_tanBounds? h hx
  | asin =>
    simp only [elementaryWith] at h
    split at h
    · cases h
      exact Total.containsReal_asin I _ hx
    · exact containsReal_asinBounds? h hx
  | acos =>
    simp only [elementaryWith] at h
    split at h
    · cases h
      exact Total.containsReal_acos I _ hx
    · exact containsReal_acosBounds? h hx
  | atan =>
    cases Option.some.inj h
    exact containsReal_atanBounds I _ hx
  | sinh =>
    cases Option.some.inj h
    exact containsReal_sinhBounds I _ hx
  | cosh =>
    cases Option.some.inj h
    exact containsReal_coshBounds I _ hx
  | tanh =>
    cases Option.some.inj h
    exact containsReal_tanhBounds I _ hx
  | sqrt =>
    simp only [elementaryWith] at h
    split at h
    · cases h
      exact Total.containsReal_sqrt I _ hx
    · exact containsReal_sqrtBounds? h hx

end Backend

end FloatLib.Numerics.Interval
