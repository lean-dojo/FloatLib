/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.Logarithmic.Automation
public import FloatLib.Floats.Formats.Logarithmic.Configured.Instances
public import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof
public meta import FloatLib.Floats.Formats.Logarithmic.Configured.Info
public meta import FloatLib.Floats.Formats.Logarithmic.Exact.Info
public meta import FloatLib.Numerics.Capabilities.Radix

/-!
# Exact logarithmic numbers

The exact value set is zero together with the signed integral powers `±β^e` of the radix `β`,
with `e` an unbounded integer. Multiplication is the only arithmetic operation supplied, and it is
exact because signs combine and exponents add. General addition and conversion into this value set
require rounding: a sum of radix powers need not be a radix power. Division by a nonzero value
could subtract exponents exactly, but division and its zero-divisor policy are not implemented.
The family supplies a
configured `ExecFloat.Logarithmic` carrier, proof automation, and `#float_info` support.

## References

* E. E. Swartzlander Jr. and A. G. Alexopoulos, “The Sign/Logarithm Number System,”
  *IEEE Transactions on Computers* C-24(12), 1975.
-/

@[expose] public section
