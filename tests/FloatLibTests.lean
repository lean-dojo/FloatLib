/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibTests.Conformance
import FloatLibTests.Numerics.Affine
import FloatLibTests.Numerics.AffineExpr
import FloatLibTests.Numerics.Diagnose
import FloatLibTests.Numerics.ElementaryTable
import FloatLibTests.Numerics.Exact
import FloatLibTests.Numerics.Rounding
import FloatLibTests.Numerics.Roundings
import FloatLibTests.Numerics.SharpTrig
import FloatLibTests.Numerics.Standard
import FloatLibTests.Numerics.Stochastic
import FloatLibTests.Numerics.StochasticBinary
import FloatLibTests.Tactic.Roundoff.Stochastic
import FloatLibTests.Numerics.StochasticSequential
import FloatLibTests.Numerics.Total
import FloatLibTests.Tactic.KernelCheck
import FloatLibTests.Regression.BinaryInterchange.ExecFloatInstances
import FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
import FloatLibTests.Regression.BinaryInterchange.Model
import FloatLibTests.Regression.BinaryInterchange.NativeHalf
import FloatLibTests.Regression.BinaryInterchange.NativeProduct
import FloatLibTests.Regression.BinaryInterchange.PolicyRounding
import FloatLibTests.Regression.BinaryInterchange.SmallWord
import FloatLibTests.Regression.BinaryInterchange.TinyArithmetic
import FloatLibTests.Regression.BinaryInterchange.TwoWordMul
import FloatLibTests.Regression.BinaryInterchange.WideLimb
import FloatLibTests.Regression.RationalPower

/-!
# Conformance and regression modules

Build the test modules with `lake -d tests build FloatLibTests`. The native test driver in
`Check.lean` imports this root so `lake -d tests test` also checks the conformance proofs. The
modules under `Numerics` test code below the tactics: stochastic rounding, and the enclosures,
roundings and backends of the interval evaluator. `Tactic.KernelCheck` tests the kernel check
that `float_decide` and `interval` share.
-/
