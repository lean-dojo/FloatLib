/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.BinaryInterchange.Interval
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Activations
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Core

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Format-generic executable intervals

This is the public entry point for `Model.Interval fmt`. It brings in endpoint construction,
outward-rounded arithmetic, conservative division, elementary activation ranges, and
proof-aware `#float_info` inspection.
-/

@[expose] public section
