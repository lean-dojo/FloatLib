/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.FixedPoint
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Config
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Contract
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.ExpLog
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Hyperbolic
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Trig
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Power
public import FloatLib.Numerics.Capabilities.Elementary

/-!
# Format-generic executable transcendental functions

Importing `BinaryInterchange.Transcendentals` adds deterministic `exp`, `log`, `sinh`, `cosh`,
`tanh`, `sin`, and `cos` operations for `Model fmt`, with reusable fixed-point primitives and
explicit approximation configuration.

## Approximation and certificates

* `exp` and `log` use fixed-point range reduction and series evaluation. `sin` and `cos` evaluate
  exact Taylor polynomials after an approximate argument reduction. The small hyperbolic branches
  use exact polynomials too; `tanh` adds an integer square-root approximation. Each kernel rounds
  its final approximation to the destination format. Working precision and polynomial length
  depend on the format and `GenerationPolicy`. These kernels have no general real-error or
  correct-rounding theorem; their extra working bits do not constitute a proved one-ULP bound.
* `Model.Transcendentals.Contract` supplies kernel-checked real enclosures and certificate types.
  These are proof objects over `ℝ`; an executable kernel gains an accuracy claim only when a proof
  connects that kernel to one of those contracts.
* `FloatLibTests.Arb.ModelTranscendentals` is an optional `IO` adapter supporting explicit IEEE
  rounding directions. It trusts Arb/python-flint to enclose the real function and fails if an
  enclosure does not stabilize to one destination value.

Tangent can be computed as `sin x / cos x`, with rounding after sine, cosine, and division and
increased sensitivity near zeros of cosine. There is no dedicated tangent kernel. These functions
use nearest-even destination rounding and return values without IEEE status flags.

`sinCosResult` and `sinCosWithResult` report arguments beyond the selected configuration's
trigonometric exponent budget. Value-only sine and cosine map this failure to `invalidResult`.
`Config.generatedFullRange` opts into constants large enough for the format's full exponent
range, with correspondingly larger generation costs. Successful reduction is not an accuracy
certificate.

`ExactExpression` can round an exactly represented rational expression once, but real
transcendentals are not rational operations in general. A composition of these kernels therefore
approximates and rounds at each function boundary. Certifying one final rounding for the whole
composition requires a real enclosure or another exact-real procedure covering that composition.

Import this module for the `Model` functions and instances, or
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` for the configured types.
These imports add the binary elementary functions to those available from `import FloatLib`.
The `MathFunctions` class and its host `Float` and real instances are available by default.
Individual kernel submodules can be imported separately; `#float_info` loads only `Contract`
through `BinaryInterchange/Info/Profile.lean`.
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
