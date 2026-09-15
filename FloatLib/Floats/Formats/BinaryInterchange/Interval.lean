/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Activations
public meta import FloatLib.Floats.Formats.BinaryInterchange.Interval.Info
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Format-generic executable intervals

Public entry point for `Model.Interval fmt`, including endpoint construction, outward-rounded
arithmetic, conservative division, elementary activation ranges, and proof-aware
`#float_info` inspection.
-/

@[expose] public section
