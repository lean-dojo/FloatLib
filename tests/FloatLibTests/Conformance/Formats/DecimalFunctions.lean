/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
public meta import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof

/-!
# The certified decimal functions of IEEE 754-2019 §9.2

Results of `Transcendentals.Certified.sin`, `exp2`, `log10` and the other functions of one
argument, and of `exp`, `log`, `powr` and `compound`, on decimal data. `cases` holds every case
once, checked by compiled evaluation when this module is elaborated: correctly rounded results
at ordinary operands in the three interchange formats (the digits are those of the constants
`sin (1/2)`, `sqrt 2`, `log10 2`, `pi / 4`, `acosh 2`, `atanh (1/2)` and `2 ^ 1000`), the zero
operands that are returned unchanged, and the operands without a result. The results at
pseudo-random operands are compared with `mpmath` by `tests/oracles/ieee2019.sh`.

The last part applies the theorems: a returned result is the nearest-even rounding of the real
function, whatever the format and the operand. Their premise, that a result is returned, holds
at the operands of the first cases.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.DecimalFunctions

open FloatLib.Floats.Formats.DecimalInterchange
open FloatLib.Floats.Formats.DecimalInterchange.Transcendentals

/-- The positive datum `coefficient × 10 ^ exponent`. -/
def pos (coefficient : Nat) (exponent : Int) : Datum := .finite false coefficient exponent

/-- The negative datum `-coefficient × 10 ^ exponent`. -/
def neg (coefficient : Nat) (exponent : Int) : Datum := .finite true coefficient exponent

/-- The cases: a name and whether the case holds. -/
def cases : List (String × Bool) :=
  [ ("sin 0.5 in decimal64",
      Certified.sin .decimal64 (pos 5 (-1)) == some (pos 4794255386042030 (-16))),
    ("sin 0.5 in decimal128",
      Certified.sin .decimal128 (pos 5 (-1)) ==
        some (pos 4794255386042030002732879352155714 (-34))),
    ("exp2 0.5 is the square root of two",
      Certified.exp2 .decimal64 (pos 5 (-1)) == some (pos 1414213562373095 (-15))),
    ("log10 2", Certified.log10 .decimal64 (pos 2 0) == some (pos 3010299956639812 (-16))),
    ("atan 1 is a quarter of pi",
      Certified.atan .decimal64 (pos 1 0) == some (pos 7853981633974483 (-16))),
    ("acosh 2", Certified.acosh .decimal64 (pos 2 0) == some (pos 1316957896924817 (-15))),
    ("atanh 0.5",
      Certified.atanh .decimal64 (pos 5 (-1)) == some (pos 5493061443340548 (-16))),
    ("exp2 1000", Certified.exp2 .decimal64 (pos 1000 0) == some (pos 1071508607186267 286)),
    ("tanh of 1.23E-7 in decimal32",
      Certified.tanh .decimal32 (pos 123 (-9)) == some (pos 1230000 (-13))),
    ("exp10 2 has the value 100",
      ((Certified.exp10 .decimal64 (pos 2 0)).bind Datum.toRat?) == some 100),
    ("sinPi 0.5 has the value 1",
      ((Certified.sinPi .decimal64 (pos 5 (-1))).bind Datum.toRat?) == some 1),
    ("cos -0 has the value 1",
      ((Certified.cos .decimal64 (neg 0 (-3))).bind Datum.toRat?) == some 1),
    ("sin -0E-3 is that zero", Certified.sin .decimal64 (neg 0 (-3)) == some (neg 0 (-3))),
    ("log2p1 +0E+5 is that zero", Certified.log2p1 .decimal64 (pos 0 5) == some (pos 0 5)),
    ("log2 of a negative number has no result",
      Certified.log2 .decimal64 (neg 3 0) == none),
    ("asin 2 has no result", Certified.asin .decimal64 (pos 2 0) == none),
    ("atanh 1 has no result", Certified.atanh .decimal64 (pos 1 0) == none),
    ("exp2 of a million is not enclosed", Certified.exp2 .decimal64 (pos 1 6) == none),
    ("sin of an infinity has no result", Certified.sin .decimal64 (.infinity false) == none),
    ("sin of a NaN has no result", Certified.sin .decimal64 (.nan false false 0) == none),
    ("sin of a datum with 17 digits in decimal64 has no result",
      Certified.sin .decimal64 (pos 12345678901234567 (-17)) == none),
    ("exp 1 is e", Certified.exp .decimal64 (pos 1 0) == some (pos 2718281828459045 (-15))),
    ("log 10", Certified.log .decimal64 (pos 10 0) == some (pos 2302585092994046 (-15))),
    ("log of zero has no result", Certified.log .decimal64 (pos 0 0) == none),
    ("powr 2 0.5 is the square root of two",
      Certified.powr .decimal64 (pos 2 0) (pos 5 (-1)) == some (pos 1414213562373095 (-15))),
    ("powr of a negative base has no result",
      Certified.powr .decimal64 (neg 2 0) (pos 5 (-1)) == none),
    ("compound 0.05 10 is 1.05 ^ 10",
      Certified.compound .decimal64 (pos 5 (-2)) 10 == some (pos 1628894626777441 (-15))),
    ("compound -2 3 has no result", Certified.compound .decimal64 (neg 2 0) 3 == none) ]

#eval show IO Unit from do
  let failures := cases.filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"certified decimal function cases that fail: {failures.map (·.1)}"
  IO.println s!"{cases.length} cases of the certified decimal functions hold"

/-! ## The theorems -/

/-- A named function is `Certified.apply` at its member, so the theorems apply to it. -/
example (f : Format) {input result : Datum} (h : Certified.sin f input = some result) :
    toReal result = roundAt f (Real.sin (toReal input)) :=
  Certified.toReal_of_apply_eq_some (function := .sin) h

example (f : Format) {input result : Datum} (h : Certified.log10 f input = some result) :
    toReal result = roundAt f (Real.logb 10 (toReal input)) :=
  Certified.toReal_of_apply_eq_some (function := .log10) h

example (f : Format) {input result : Datum} (h : Certified.atanh f input = some result) :
    result.Valid f ∧ result.isFinite = true :=
  ⟨Certified.valid_of_apply_eq_some (function := .atanh) h,
    Certified.isFinite_of_apply_eq_some (function := .atanh) h⟩

/-- `exp`, `log`, `compound` and `powr` are certified in the same way. -/
example (f : Format) {input result : Datum} (h : Certified.exp f input = some result) :
    toReal result = roundAt f (Real.exp (toReal input)) :=
  Certified.toReal_of_exp_eq_some h

example (f : Format) {base exponent result : Datum}
    (h : Certified.powr f base exponent = some result) :
    toReal result = roundAt f (toReal base ^ toReal exponent) :=
  Certified.toReal_of_powr_eq_some h

example (f : Format) {input result : Datum} (h : Certified.log f input = some result) :
    toReal result = roundAt f (Real.log (toReal input)) :=
  Certified.toReal_of_log_eq_some h

example (f : Format) {input result : Datum} (n : ℤ)
    (h : Certified.compound f input n = some result) :
    toReal result = roundAt f ((1 + toReal input) ^ (n : ℝ)) :=
  Certified.toReal_of_compound_eq_some h

/-- A returned result is within half a unit in the last place of the real function. -/
example (f : Format) {input result : Datum} (h : Certified.tan f input = some result) :
    |toReal result - Real.tan (toReal input)| ≤
      FloatLib.Floats.Formats.Flocq.ulp FloatLib.Numerics.decimalRadix (fexpOf f)
        (Real.tan (toReal input)) / 2 :=
  Certified.error_le_half_ulp_of_apply_eq_some (function := .tan) h

end FloatLibTests.Conformance.Formats.DecimalFunctions
