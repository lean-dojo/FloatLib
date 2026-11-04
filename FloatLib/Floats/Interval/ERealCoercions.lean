/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Coercion lemmas for `ℝ → EReal`

Several soundness proofs for executable intervals prove their bounds in `ℝ` and then reason about
the endpoints in `EReal`, where overflow is safe. Its lemmas say that the order-preserving embedding
commutes with `min` and `max`. We rewrite with them by name, so importing this module doesn't change
the default simplification of coerced bounds.
-/

@[expose] public section

namespace FloatLib.Floats.Interval

/-- Coercion distributes over `min` for reals embedded into `EReal`. -/
theorem coe_min (a b : ℝ) : ((min a b : ℝ) : EReal) = min (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_min

/-- Coercion distributes over `max` for reals embedded into `EReal`. -/
theorem coe_max (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_max

end FloatLib.Floats.Interval
