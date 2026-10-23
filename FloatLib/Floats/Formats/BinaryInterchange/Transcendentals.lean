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
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Pi.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Trig
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Power
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.PowerProof
public import FloatLib.Numerics.Capabilities.Elementary

/-!
# Optional elementary functions for binary models

This module adds `exp`, `log`, `sinh`, `cosh`, `tanh`, `sin`, and `cos` for `Model fmt` and
installs the `Pow` and `MathFunctions` instances. The default kernels use fixed-point range
reduction, polynomial or series evaluation, and nearest-even destination rounding. Their working
precision follows `GenerationPolicy` and grows with the argument where reduction needs it (sine
and cosine near multiples of `pi / 2`, the exponential of large arguments). They carry no general
real-error bound. For an IEEE descriptor, `Model.pow` with a finite nonzero base and a finite
integral exponent is correctly rounded whenever its result is finite
(`Model.Power.toReal_pow_of_eq_intCast`). A finite positive base with any other finite exponent
goes to `Model.Transcendentals.Certified.pow`, and the result is correctly rounded whenever that
search settles (`Model.Power.pow_spec_of_certified`). Overflow, most exact results on a rounding
boundary, and an exhausted budget fall back to `exp (y * log x)`.

`Model.Transcendentals.Certified.exp`, `log`, `expMinus1`, `logPlus1`, and `pow` instead refine
rational enclosures and return `Except Certified.Failure (Model fmt)`. `expMinus1` and `logPlus1`
retain small results near zero by subtracting or adding one before any rounding. Every accepted
result is proved finite and equal to nearest-even rounding of the real function, and a failure
names its reason. For `exp`, `log`, `expMinus1`, and `logPlus1` the `Contract` is instantiated on
this executable success domain, and `pow` is covered by its own theorems,
`Model.Transcendentals.Certified.toReal_of_pow_eq_ok` and `Model.Power.pow_spec_of_certified`.
Options bound direct refinement attempts, with `inconclusive` for a search that did not settle.

Sine and cosine reduce their arguments by the Payne-Hanek reduction of
`Numerics.Enclosure.ArgumentReduction`, whose remainder error is proved, to the destination
precision plus 32 bits, reading at most `2^21` bits of `2 / pi`. In a format with at most 524,258
fraction bits, every finite argument below `2^(2^20)` stays within that limit, which covers every
exponent field of at most 21 bits with the conventional bias. An argument whose reduction would need
more bits, such as the largest ones of a 31-bit exponent field, or whose permitted windows are all
rejected, gives the format's invalid result. These APIs return no IEEE status flags. `Model.pi` is
correctly rounded in every IEEE descriptor (`Model.toReal_pi`). One lazily evaluated cache of proved
constants in `Numerics.Enclosure.Constants` supplies the `2 / pi` and `pi / 2` of sine and cosine
reduction, the `log 2` of exponential reduction and of generated configurations, the `log 2` of the
certified power, and the enclosure that `Model.pi` rounds. Two paths still compute their own
constants: the exact comparators, among them the fallback of `Model.pi`, build `pi / 4`, and
`Model.Transcendentals.Certified.log` builds `log 2` through `BinaryGrid.log`.
`FloatLibTests.Arb.ModelTranscendentals` is an optional adapter supporting directed rounding
through Arb/python-flint.

Import `Transcendentals.Certified.Proof` alone for the certified model kernels, or
`Configured.Transcendentals` for the configured elementary functions. `import FloatLib` keeps
these binary operations opt-in, while the `MathFunctions` class and its host `Float` and real
instances are available by default. `#float_info` loads only `Contract` through `Info.Profile`.
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
