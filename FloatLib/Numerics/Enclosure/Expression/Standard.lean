/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime

/-!
# The standard calls: π, the real power and e

Constants in the expression language are rationals and its powers have natural exponents, so the
constant `π` and the real power `x ^ y` come in as calls. The constant `e` is a call too: as
`exp 1` it would be enclosed at the degree of the exponential, and as a call its accuracy follows
the configured precision, like that of `π`. `Standard.extensions` registers the three, and
`Backend.withExtensions` adds them to any backend: `π` is `.call 0 []`, `x ^ y` is
`.call 1 [x, y]` and `e` is `.call 2 []`.

`piBounds precision` is four times Machin's enclosure of `π / 4` (`Enclosure.piQuarter`) at
degree `precision / 4 + 1`, which is narrower than `2 ^ (-precision)`, and `eBounds precision` is
the enclosure of the exponential at `1` (`Enclosure.exp`) at degree `precision / 2 + 1`. The real
power is `rpowExtension`, which encloses `x ^ y` when the base enclosure has a positive lower
endpoint. `StandardProof` proves that the three enclosures contain the values of their functions,
and it bounds the width of `piBounds`.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Backend

/--
An enclosure of `π` narrower than `2 ^ (-precision)`: four times Machin's enclosure of `π / 4`
(`Enclosure.piQuarter`) at degree `precision / 4 + 1`.
-/
def piBounds (precision : Nat) : Interval ℚ :=
  let pi := (Enclosure.piQuarter (precision / 4 + 1)).scaleNonnegative 4
  ⟨pi.lo, pi.hi⟩

/-- The constant `π` as a registered call, enclosed by `piBounds` at the configured precision. -/
def piExtension : Extension :=
  Extension.constant fun config => some (piBounds config.precision)

/--
An enclosure of `e = exp 1`: FloatLib's enclosure of the exponential at `1` (`Enclosure.exp`), at
degree `precision / 2 + 1`.
-/
def eBounds (precision : Nat) : Interval ℚ :=
  let e := Enclosure.exp 1 (precision / 2 + 1)
  ⟨e.lo, e.hi⟩

/-- The constant `e` as a registered call, enclosed by `eBounds` at the configured precision. -/
def eExtension : Extension :=
  Extension.constant fun config => some (eBounds config.precision)

/--
The standard calls, by index: `π` (`piExtension`) is call `0`, the real power `x ^ y`
(`rpowExtension`) is call `1`, and `e` (`eExtension`) is call `2`.
-/
def Standard.extensions : List Extension :=
  [piExtension, rpowExtension, eExtension]

end FloatLib.Numerics.Interval.Backend
