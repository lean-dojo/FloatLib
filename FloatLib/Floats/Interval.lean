/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Interval
public import FloatLib.Floats.Interval.Quantized
public import FloatLib.Floats.Interval.RealBounds
public import FloatLib.Floats.Interval.Rounders
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# `FloatLib.Floats.Interval`

This namespace collects interval and enclosure utilities used across FloatLib:

- proof-friendly interval enclosures for rounding-on-`ℝ` formats,
- quantized intervals (endpoints snapped to a chosen Flocq-style rounded-real grid),
- format-generic executable endpoint intervals (`BinaryInterchange.Model.Interval fmt`).

The optional Arb-backed transcendental enclosure adapter is an explicit import:
`FloatLibTests.Arb.ModelTranscendentals`.

The interval API belongs under `FloatLib.Floats` because format semantics and executable numerical
code both depend on it. External validators remain under `FloatLibTests`, keeping their
additional trust assumptions out of the public numerical core.

## References
- IEEE 1788-2015 (interval arithmetic standard).
- Moore, Kearfott, Cloud, *Introduction to Interval Analysis* (2009).
- Rump, "INTLAB, INTerval LABoratory" (1999).
- Boldo & Melquiond, “Flocq” (ARITH 2011) for rounded-arithmetic-on-`ℝ` modeling.
-/

@[expose] public section
