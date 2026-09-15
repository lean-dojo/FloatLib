/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibTests.Conformance
import FloatLibTests.Regression.BinaryInterchange.ExecFloatInstances
import FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals
import FloatLibTests.Regression.BinaryInterchange.Model
import FloatLibTests.Regression.BinaryInterchange.NativeProduct
import FloatLibTests.Regression.BinaryInterchange.PolicyRounding
import FloatLibTests.Regression.BinaryInterchange.SmallWord
import FloatLibTests.Regression.BinaryInterchange.TinyArithmetic
import FloatLibTests.Regression.BinaryInterchange.TwoWordMul
import FloatLibTests.Regression.BinaryInterchange.WideLimb

/-!
# Conformance and regression modules

Build the test modules with `lake -d tests build FloatLibTests`. The native test driver in
`Check.lean` imports this root so `lake -d tests test` also checks the conformance proofs.
-/
