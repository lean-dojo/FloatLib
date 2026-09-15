/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Arithmetic.Proof
public import FloatLib.Floats.Formats.Codebook.Catalog.Proof
public import FloatLib.Floats.Formats.Codebook.Core.Proof
public import FloatLib.Numerics.Automation.Numerics -- shake: keep
public import Mathlib.Tactic.NormNum

/-!
# Codebook rules for numerical automation

Named tiny codebooks register their exact lookup semantics and proved arithmetic. Closed
bit-pattern evaluation is deliberately separated from symbolic refinement.
-/

public meta section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Codebook

attribute [numerics_simps]
  Catalog.bipolar1_denote_zero
  Catalog.bipolar1_denote_one
  Catalog.ternary2_denote_zero
  Catalog.ternary2_denote_positive
  Catalog.ternary2_denote_negative
  Catalog.ternary2_denote_reserved

attribute [aesop safe apply (rule_sets := [Numerics])]
  Catalog.bipolar1.neg_refines
  Catalog.bipolar1.mul_refines
  Catalog.ternary2.neg_refines
  Catalog.ternary2.mul_refines

attribute [numerics_reduction]
  Codebook.ofNatBits
  Codebook.toNatBits
  Codebook.numericalSystem_denote
  Codebook.numericalSystem
  Catalog.bipolar1
  Catalog.ternary2
  Catalog.bipolar1.neg
  Catalog.bipolar1.mul
  Catalog.ternary2.neg?
  Catalog.ternary2.mul?

end FloatLib.Floats.Formats.Codebook
