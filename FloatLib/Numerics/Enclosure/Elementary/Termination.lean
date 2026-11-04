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

Each refinement doubles the Taylor degree. A positive rational argument other than `1` has an
irrational logarithm, so the convergent enclosures eventually exclude any rational boundary.
`log 1 = 0` is exactly representable and gets handled before this search. The exponential works the
same way, with `exp 0 = 1` handled up front.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- The adaptive logarithm comparison terminates at every rational boundary. -/
theorem exists_log_separating (argument boundary : ℚ)
    (hpositive : 0 < argument) (hone : argument ≠ 1) :
    ∃ n, Comparison.Separates (log argument (2 ^ n)) boundary :=
  Comparison.exists_separating_two_pow_of_irrational
    (irrational_log_ratCast argument hpositive hone) boundary
    (tendsto_log_lo argument hpositive)
    (tendsto_log_hi argument hpositive)

/-- The adaptive exponential comparison terminates away from its exact zero-input case. -/
theorem exists_exp_separating (argument boundary : ℚ) (hnonzero : argument ≠ 0) :
    ∃ n, Comparison.Separates (exp argument (2 ^ n)) boundary :=
  Comparison.exists_separating_two_pow_of_irrational
    (irrational_exp_ratCast argument hnonzero) boundary
    (tendsto_exp_lo argument)
    (tendsto_exp_hi argument)

end FloatLib.Numerics.Enclosure
