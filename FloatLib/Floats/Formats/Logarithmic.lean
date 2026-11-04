/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.Logarithmic.Automation
public import FloatLib.Floats.Formats.Logarithmic.Configured.Display
public import FloatLib.Floats.Formats.Logarithmic.Configured.Instances
public import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Logarithmic.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof
public meta import FloatLib.Floats.Formats.Logarithmic.Configured.Info
public meta import FloatLib.Floats.Formats.Logarithmic.Exact.Info
public meta import FloatLib.Numerics.Capabilities.Radix

/-!
# Exact logarithmic numbers

A logarithmic number keeps a sign and an exponent, so at radix `β = 2` the value `-8` is the sign
`-` with exponent `3`. The exact value set is zero together with the signed integral powers `±β^e`
of the radix, with `e` an unbounded integer. Multiplying two of them never rounds, because the
signs combine and the exponents add: `-2^3 * 2^-2 = -2^1`. That's why multiplication is the one
arithmetic operation supplied. Addition and conversion into this value set would need rounding,
since a sum of radix powers like `8 + 2` need not be a radix power. Division by a nonzero value
could subtract exponents without rounding, but the library supplies no division and no policy for
dividing by zero.

The family comes with a configured `ExecFloat.Logarithmic` carrier, proof automation, and
`#float_info` support.

## References

* E. E. Swartzlander Jr. and A. G. Alexopoulos, “The Sign/Logarithm Number System,”
  *IEEE Transactions on Computers* C-24(12), 1975.
-/

@[expose] public section
