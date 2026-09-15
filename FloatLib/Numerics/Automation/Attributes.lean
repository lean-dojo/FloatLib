/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Aesop
public import Mathlib.Tactic.Attr.Register

/-!
# Attributes for representation-independent numerical automation

The attributes are declared separately so numerical families can register semantic and concrete
rules without importing the tactic implementation. Semantic rules must be proved equations or
equivalences. Concrete reduction rules are used only by the explicit closed-term phase.
-/

declare_aesop_rule_sets [Numerics]

public meta section

/-- Representation-independent semantic rewrites used by `numerics`. -/
register_simp_attr numerics_simps

/-- Routine finiteness, range, and operation-precondition rewrites used by `numerics`. -/
register_simp_attr numerics_side

/-- Concrete carrier and decoder reductions used by `numerics_reduce` and `numerics!`. -/
register_simp_attr numerics_reduction
