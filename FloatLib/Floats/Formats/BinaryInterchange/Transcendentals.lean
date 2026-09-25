/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.FixedPoint
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Config
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Contract
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.ExpLog
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Hyperbolic
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Trig
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Power
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.PowerProof
public import FloatLib.Numerics.Capabilities.Elementary

/-!
# Optional elementary functions for binary models

This module adds `exp`, `log`, `sinh`, `cosh`, `tanh`, `sin`, and `cos` for `Model fmt` and installs
the `Pow` and `MathFunctions` instances. The default kernels use fixed-point range
reduction, polynomial or series evaluation, and nearest-even destination rounding. Their working
precision follows `GenerationPolicy`; they carry no general real-error bound. For an IEEE
descriptor, `Model.pow` with a finite nonzero base and a finite integral exponent is correctly
rounded whenever its result is finite (`Model.Power.toReal_pow_of_eq_intCast`); other finite
exponents use `exp (y * log x)`.

`Model.Transcendentals.Certified.exp`, `log`, `expMinus1`, and `logPlus1` instead refine rational
enclosures and return `Option (Model fmt)`. The last two retain small results near zero by
subtracting or adding one before any rounding. Every accepted result is proved finite and equal
to nearest-even rounding of the real function. The existing `Contract` is instantiated on this
executable success domain. Options bound direct refinement attempts, with `none` for an
inconclusive search.

`sinCosResult` and `sinCosWithResult` report arguments beyond the trigonometric exponent budget.
Value-only sine and cosine map this failure to `invalidResult`. `Config.generatedFullRange`
generates constants covering the format's full exponent range at a larger generation cost.
These APIs return no IEEE status flags. `FloatLibTests.Arb.ModelTranscendentals` is a separate
optional adapter supporting explicit rounding directions through Arb/python-flint.

Import `Transcendentals.Certified.Proof` alone for the certified model kernels, or
`Configured.Transcendentals` for the configured elementary functions. `import FloatLib` keeps
these binary operations opt-in; the `MathFunctions` class and its host `Float` and real instances
remain available by default. `#float_info` loads only `Contract` through `Info.Profile`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-- Deterministic floating-point exponentiation. -/
instance {fmt : FloatFormat} : Pow (Model fmt) (Model fmt) where
  pow := pow

/-- Generic deterministic transcendental and elementary functions. -/
instance {fmt : FloatFormat} : MathFunctions (Model fmt) where
  exp := exp
  tanh := tanh
  cosh := cosh
  sqrt := sqrt
  abs := abs
  log := log
  pi := pi fmt
  cos := cos
  sin := sin
  sinh := sinh

end Model
end FloatLib.Floats.Formats.BinaryInterchange
