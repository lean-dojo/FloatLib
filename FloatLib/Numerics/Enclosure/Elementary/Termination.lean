/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.Irrational

/-!
# Termination of adaptive elementary comparison

The Taylor degree doubles at each refinement. Positive rational arguments other than `1`
have irrational logarithms, so the convergent enclosures eventually exclude any rational
boundary. The exactly representable value `log 1 = 0` is handled before this search.
The exponential argument is analogous, with `exp 0 = 1` handled separately.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- The adaptive logarithm comparison terminates at every rational boundary. -/
theorem exists_log_separating (argument boundary : ℚ)
    (hpositive : 0 < argument) (hone : argument ≠ 1) :
    ∃ n, Comparison.Separates (log argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational
    (irrational_log_ratCast argument hpositive hone) boundary
    ((tendsto_log_lo argument hpositive).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_log_hi argument hpositive).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- The adaptive exponential comparison terminates away from its exact zero-input case. -/
theorem exists_exp_separating (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    ∃ n, Comparison.Separates (exp argument (2 ^ n)) boundary :=
  Comparison.exists_separating_of_irrational
    (irrational_exp_ratCast argument hnonzero) boundary
    ((tendsto_exp_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_exp_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

end FloatLib.Numerics.Enclosure
