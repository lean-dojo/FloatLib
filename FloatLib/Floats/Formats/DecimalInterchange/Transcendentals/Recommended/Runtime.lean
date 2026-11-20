/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Runtime
public meta import FloatLib.Tactic.IEEENames

/-!
# The recommended functions of IEEE 754-2019 §9.2 for decimal formats, certified

The 26 functions of one argument that §9.2 recommends (`exp2`, `exp10`, `log2`, `log10` with
their `m1` and `p1` forms, the trigonometric functions in radians and in half-turns with their
inverses, the hyperbolic functions with their inverses), on a decimal `Datum` of any `Format`.
The names are those of ISO/IEC 9899:2024 (C23, N3220) Annex F, Table F.2, and the functions are
the members of the enumeration `Function` that the binary formats use.

A function returns `some result` when an enclosure certifies the nearest-even rounding of the
real result, and `none` otherwise. The expression `Function.expr` of the function at the exact
value of the operand is evaluated on a binary grid finer than the decimal precision
(`Numerics.Interval`), and the result is accepted when both ends of the enclosure round to the
same finite datum (`Enclosure.round?`), on one of two grids. So a returned result is the
correctly rounded value (`Recommended.Proof`), with the coefficient at full precision or, for
an end of the enclosure that is exact, the least representable quantum, as for `expm1` and
`logp1`.

`none` is returned for an operand that is not valid, a NaN or an infinity; outside the domain
of the function, poles included; for an argument beyond `Function.enclosable` (an exponential or
a hyperbolic function of magnitude above `2 ^ 16`, a trigonometric one above `2 ^ 64`); and when
neither enclosure settles the rounding: a result on a rounding boundary, which includes most
results that are exact, an overflow, and a result too small or too large in magnitude for the
two grids. A zero operand of
a function with `f (±0) = ±0` is returned unchanged. There are no flags and no rounding
direction other than nearest-even.

`exp`, `log`, `powr` and `compound` are certified in the same way, by `unary` with their own
expressions. `expm1` and `logp1` are in `Certified.Runtime`. The same functions as total
functions with flags in the five rounding directions, with `atan2`, `atan2Pi` and `pow`, are in
`Transcendentals.CorrectlyRounded`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified

open FloatLib.Numerics
open BinaryInterchange.Model.Transcendentals.CorrectlyRounded (Function)

/--
The nearest-even rounding into `f` of the real number that `expression` denotes, when one
enclosure settles it: the expression is evaluated on the binary grid of `config`, and the datum
is accepted when both ends of the enclosure round to it (`Enclosure.round?`).
-/
def settle (f : Format) (expression : Interval.Expr) (config : Interval.Backend.Config) :
    Option Datum :=
  match expression.eval? (Interval.Backend.binaryGrid config) fun _ => none with
  | none => none
  | some bounds =>
      Enclosure.round? f (Numerics.Enclosure.BinaryGrid.toRationalInterval config.precision bounds)

/--
The two grids on which an enclosure is tried: 40 bits beyond the bits of the decimal precision
(ten bits for three digits), then twice that precision. The degree of the series is a third of
the precision, and two thirds for an expression with a logarithm (`slow`).
-/
def configs (f : Format) (slow : Bool) : List Interval.Backend.Config :=
  let bits := 10 * f.precision / 3 + 40
  let degree (precision : Nat) : Nat := (if slow then 2 * precision else precision) / 3 + 16
  [{ precision := bits, degree := degree bits },
    { precision := 2 * bits, degree := degree (2 * bits) }]

/-- The result of the first grid of `configs` whose enclosure settles the rounding. -/
def nearest? (f : Format) (expression : Interval.Expr) (slow : Bool := false) : Option Datum :=
  (configs f slow).findSome? (settle f expression)

/--
A certified function of one operand, given by the expression of its value at an exact argument
and whether that expression has a logarithm, or `none` where the function is not enclosed: the
nearest-even rounding of the expression at the exact value of a valid finite operand, when an
enclosure settles it.
-/
def unary (f : Format) (expression : ℚ → Option (Interval.Expr × Bool)) (input : Datum) :
    Option Datum :=
  if ¬input.Valid f then none
  else
    match input.toRat? with
    | none => none
    | some argument =>
        match expression argument with
        | none => none
        | some (enclosed, slow) => nearest? f enclosed slow

/--
A recommended function of IEEE 754-2019 §9.2 on a decimal datum: the nearest-even rounding of
the real function at the operand when an enclosure certifies it. A zero operand of a function
that is zero at zero is returned unchanged, with its sign and quantum. The result is `none` for
an operand that is not valid or not finite or not in the domain of the function, and when no
enclosure settles the rounding.
-/
def apply (f : Format) (function : Function) (input : Datum) : Option Datum :=
  if input.Valid f ∧ input.isZero = true ∧ function.vanishesAtZero = true then some input
  else
    unary f (fun argument =>
      if function.Domain argument ∧ function.enclosable (2 ^ 16) argument = true then
        some (function.expr argument, function.hasLogarithm)
      else none) input

ieee_recommended certified apply (f : Format) (input : Datum) : Option Datum :=
  fun function => apply f function input

/--
IEEE 754-2019 §9.2 `exp` (ISO/IEC 9899:2024 7.12.6.1, F.10.3.1), certified: the nearest-even
rounding of `e ^ x` when an enclosure settles it, for an operand of magnitude at most `2 ^ 16`,
and `none` otherwise.
-/
def exp (f : Format) (input : Datum) : Option Datum :=
  unary f (fun argument =>
    if |argument| ≤ 2 ^ 16 then some (.unary .exp (.const argument), false) else none) input

/--
IEEE 754-2019 §9.2 `log` (ISO/IEC 9899:2024 7.12.6.11, F.10.3.11), certified: the nearest-even
rounding of the natural logarithm of a positive operand when an enclosure settles it, and
`none` otherwise.
-/
def log (f : Format) (input : Datum) : Option Datum :=
  unary f (fun argument =>
    if 0 < argument then some (.unary .log (.const argument), true) else none) input

open BinaryInterchange.Model.Transcendentals.CorrectlyRounded (powerExpr powerEnclosable) in
/--
IEEE 754-2019 §9.2 `compound` (ISO/IEC 9899:2024 `compoundn`, 7.12.7.2, F.10.4.2), certified:
the nearest-even rounding of `(1 + x) ^ n` for an operand above -1 when an enclosure settles
it, and `none` otherwise.
-/
def compound (f : Format) (input : Datum) (n : ℤ) : Option Datum :=
  unary f (fun rate =>
    if powerEnclosable (2 ^ 16) (1 + rate) n then some (powerExpr (1 + rate) n, true)
    else none) input

open BinaryInterchange.Model.Transcendentals.CorrectlyRounded (powerExpr powerEnclosable) in
/--
IEEE 754-2019 §9.2 `powr` (ISO/IEC 9899:2024 7.12.7.7, F.10.4.7), certified: the nearest-even
rounding of `x ^ y` for a positive base and valid finite operands when an enclosure settles it,
and `none` otherwise.
-/
def powr (f : Format) (base exponent : Datum) : Option Datum :=
  if ¬exponent.Valid f then none
  else
    match exponent.toRat? with
    | none => none
    | some power =>
        unary f (fun argument =>
          if powerEnclosable (2 ^ 16) argument power then some (powerExpr argument power, true)
          else none) base

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified
