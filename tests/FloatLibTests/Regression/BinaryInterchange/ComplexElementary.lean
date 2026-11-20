/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Algebraic
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Inverse
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Power
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Tangent
public import FloatLibTests.Accounting

/-!
# The special values of the complex functions in C23 Annex G

The tables of C23 (working draft N3220) G.6.2.1 `cacos`, G.6.3.1 `cacosh`, G.6.3.2 `casinh`,
G.6.3.3 `catanh`, G.6.3.4 `ccosh`, G.6.3.5 `csinh`, G.6.3.6 `ctanh`, G.6.4.1 `cexp`, G.6.4.2
`clog` and G.6.5.2 `csqrt` are transcribed here row by row and checked on the compiled functions,
in binary16, bfloat16, binary32 and binary64 and in all six rounding directions.

Each table states the function where the imaginary sign bit is clear, or in the first quadrant
for an odd or even function. As G.6.1, paragraph 9, says, `f (conj z) = conj (f z)` and the
parity give the other half-planes and quadrants, and the checks apply both to every row. `casin`,
`catan`, `ccos`, `csin` and `ctan` are checked through the formulas of G.6.1, paragraph 8:
`casin z = -i casinh (i z)`, `catan z = -i catanh (i z)`, `ccos z = ccosh (i z)`,
`csin z = -i csinh (i z)` and `ctan z = -i ctanh (i z)`.

A row with a "finite" argument is checked at several finite values. A result `π`, `π / 2`,
`π / 4` or `3 π / 4` must be the rounding, in the direction of the call, of that multiple of two
rationals that enclose `π` to fifty decimal digits, which round alike in these formats. A sign
that C leaves unspecified is not checked.

The second group checks the two sides of each branch cut at finite arguments (C23 7.3.3 and
G.6, paragraph 3), and the third the special values of `pow` and `rsqrt`, which are FloatLib's
own: C23 gives `cpow` no table (G.6.5.1) and has no `rsqrt`.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only. Elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.BinaryInterchange.ComplexElementary

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding (roundRat)
open FloatLibTests.Accounting

/-- One part of an argument or of an expected result. -/
inductive Part where
  /-- A zero with its sign bit. -/
  | zero (negative : Bool)
  /-- An infinity with its sign bit. -/
  | inf (negative : Bool)
  /-- A NaN. -/
  | nan
  /-- A rational, exactly representable where it is an argument. -/
  | rat (value : Rat)
  /-- A rational multiple of `π`, rounded in the direction of the call. -/
  | pi (multiple : Rat)
  /-- A zero of unspecified sign. -/
  | anyZero
  /-- An infinity of unspecified sign. -/
  | anyInf
  /-- A rational multiple of `π` of unspecified sign. -/
  | piAnySign (multiple : Rat)
  deriving Inhabited

/-- The part of the conjugate or of the negation. -/
def Part.neg : Part → Part
  | .zero negative => .zero !negative
  | .inf negative => .inf !negative
  | .rat value => .rat (-value)
  | .pi multiple => .pi (-multiple)
  | other => other

/-- The encoding of an argument part. -/
def Part.encode (fmt : FloatFormat) : Part → Model fmt
  | .zero negative => Model.zero fmt negative
  | .inf negative => if negative then Model.negInf fmt else Model.posInf fmt
  | .rat value => roundRat fmt .nearest value
  | _ => Model.invalidResult fmt

/-- A lower bound of `π`, to fifty decimal digits. -/
def piLower : Rat := 314159265358979323846264338327950288419716939937510 / 10 ^ 50

/-- An upper bound of `π`: the lower bound plus one unit of its last digit. -/
def piUpper : Rat := piLower + 1 / 10 ^ 50

/-- Whether a result part is the expected one. -/
def Part.agrees (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (expected : Part)
    (actual : Model fmt) : Bool :=
  match expected with
  | .zero negative => Model.isZero actual && Model.signBit actual == negative
  | .inf negative => Model.isInfinite actual && Model.signBit actual == negative
  | .nan => Model.isNaN actual
  | .rat value => decide (actual = roundRat fmt mode value)
  | .pi multiple =>
      decide (actual = roundRat fmt mode (multiple * piLower)) &&
        decide (actual = roundRat fmt mode (multiple * piUpper))
  | .anyZero => Model.isZero actual
  | .anyInf => Model.isInfinite actual
  | .piAnySign multiple =>
      (decide (actual = roundRat fmt mode (multiple * piLower)) &&
          decide (actual = roundRat fmt mode (multiple * piUpper))) ||
        (decide (actual = roundRat fmt mode (-multiple * piLower)) &&
          decide (actual = roundRat fmt mode (-multiple * piUpper)))

/-- A row of a table: the two parts of the argument and of the result. -/
structure Row where
  /-- Real and imaginary part of the argument. -/
  argument : Part × Part
  /-- Real and imaginary part of the result. -/
  result : Part × Part

/-- The row at the conjugate argument. -/
def Row.conj (row : Row) : Row :=
  ⟨(row.argument.1, row.argument.2.neg), (row.result.1, row.result.2.neg)⟩

/-- The row at the negated argument of an odd (`true`) or even function. -/
def Row.negated (odd : Bool) (row : Row) : Row :=
  ⟨(row.argument.1.neg, row.argument.2.neg),
    if odd then (row.result.1.neg, row.result.2.neg) else row.result⟩

/--
The row of the circular function that G.6.1, paragraph 8, derives from a row of the hyperbolic
one at `w = i z`: the argument `z = -i w`, and the result times `-i`, or unchanged for `ccos`.
-/
def Row.circular (rotateResult : Bool) (row : Row) : Row :=
  ⟨(row.argument.2, row.argument.1.neg),
    if rotateResult then (row.result.2, row.result.1.neg) else row.result⟩

/-- A table with its symmetries: `none` for conjugation alone, or the parity. -/
def closure (parity : Option Bool) (rows : List Row) : List Row :=
  let withParity := match parity with
    | some odd => rows ++ rows.map (Row.negated odd)
    | none => rows
  withParity ++ withParity.map Row.conj

/-- The number of rows that a compiled function fails, over four formats and six directions. -/
def failures (function : (fmt : FloatFormat) → ExecComplex fmt → Model.IEEERoundingMode →
    ExecComplex fmt) (rows : List Row) : Nat := Id.run do
  let mut count := 0
  for fmt in [FloatFormat.binary16, FloatFormat.bfloat16, FloatFormat.binary32,
      FloatFormat.binary64] do
    for mode in Model.IEEERoundingMode.all do
      for row in rows do
        let value := function fmt ⟨row.argument.1.encode fmt, row.argument.2.encode fmt⟩ mode
        count := count + failureCount
          (row.result.1.agrees fmt mode value.re && row.result.2.agrees fmt mode value.im)
  return count

/-! ## Notation of the tables -/

/-- `+0`. -/
abbrev p0 : Part := .zero false
/-- `-0`. -/
abbrev n0 : Part := .zero true
/-- `+∞`. -/
abbrev pInf : Part := .inf false
/-- `-∞`. -/
abbrev nInf : Part := .inf true
/-- A NaN. -/
abbrev nan : Part := .nan
/-- A finite rational. -/
abbrev q (value : Rat) : Part := .rat value
/-- A multiple of `π`. -/
abbrev pi (multiple : Rat) : Part := .pi multiple

/-- One row for each of several arguments with the same result. -/
def each (arguments : List (Part × Part)) (result : Part × Part) : List Row :=
  arguments.map fun argument => ⟨argument, result⟩

/-- The finite real parts at which a row "for finite x" is checked. -/
def finiteParts : List Part := [p0, n0, q 1, q (-2)]

/-- The finite nonzero real parts at which a row "for finite nonzero x" is checked. -/
def nonzeroParts : List Part := [q 1, q (-2)]

/-! ## The tables of Annex G -/

/-- G.6.4.1, `cexp`. `cis y` has the signs of `cos y` and `sin y` at `y = 1, 2, 4, 5`. -/
def expRows : List Row :=
  each [(p0, p0), (n0, p0)] (q 1, p0) ++
  each (finiteParts.map (·, pInf)) (nan, nan) ++
  each (finiteParts.map (·, nan)) (nan, nan) ++
  [⟨(pInf, p0), (pInf, p0)⟩,
    ⟨(nInf, p0), (p0, p0)⟩, ⟨(nInf, q 1), (p0, p0)⟩, ⟨(nInf, q 2), (n0, p0)⟩,
    ⟨(nInf, q 4), (n0, n0)⟩, ⟨(nInf, q 5), (p0, n0)⟩,
    ⟨(pInf, q 1), (pInf, pInf)⟩, ⟨(pInf, q 2), (nInf, pInf)⟩,
    ⟨(pInf, q 4), (nInf, nInf)⟩, ⟨(pInf, q 5), (pInf, nInf)⟩,
    ⟨(nInf, pInf), (.anyZero, .anyZero)⟩,
    ⟨(pInf, pInf), (.anyInf, nan)⟩,
    ⟨(nInf, nan), (.anyZero, .anyZero)⟩,
    ⟨(pInf, nan), (.anyInf, nan)⟩,
    ⟨(nan, p0), (nan, p0)⟩,
    ⟨(nan, q 1), (nan, nan)⟩, ⟨(nan, pInf), (nan, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.4.2, `clog`. -/
def logRows : List Row :=
  [⟨(n0, p0), (nInf, pi 1)⟩, ⟨(p0, p0), (nInf, p0)⟩] ++
  each (finiteParts.map (·, pInf)) (pInf, pi (1 / 2)) ++
  each (finiteParts.map (·, nan)) (nan, nan) ++
  [⟨(nInf, p0), (pInf, pi 1)⟩, ⟨(nInf, q 1), (pInf, pi 1)⟩,
    ⟨(pInf, p0), (pInf, p0)⟩, ⟨(pInf, q 1), (pInf, p0)⟩,
    ⟨(nInf, pInf), (pInf, pi (3 / 4))⟩,
    ⟨(pInf, pInf), (pInf, pi (1 / 4))⟩,
    ⟨(pInf, nan), (pInf, nan)⟩, ⟨(nInf, nan), (pInf, nan)⟩,
    ⟨(nan, p0), (nan, nan)⟩, ⟨(nan, q 1), (nan, nan)⟩,
    ⟨(nan, pInf), (pInf, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.5.2, `csqrt`. -/
def sqrtRows : List Row :=
  each [(p0, p0), (n0, p0)] (p0, p0) ++
  each ((finiteParts ++ [pInf, nInf, nan]).map (·, pInf)) (pInf, pInf) ++
  each (finiteParts.map (·, nan)) (nan, nan) ++
  [⟨(nInf, p0), (p0, pInf)⟩, ⟨(nInf, q 1), (p0, pInf)⟩,
    ⟨(pInf, p0), (pInf, p0)⟩, ⟨(pInf, q 1), (pInf, p0)⟩,
    ⟨(nInf, nan), (nan, .anyInf)⟩,
    ⟨(pInf, nan), (pInf, nan)⟩,
    ⟨(nan, p0), (nan, nan)⟩, ⟨(nan, q 1), (nan, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.2.1, `cacos`. -/
def acosRows : List Row :=
  each [(p0, p0), (n0, p0)] (pi (1 / 2), n0) ++
  each [(p0, nan), (n0, nan)] (pi (1 / 2), nan) ++
  each (finiteParts.map (·, pInf)) (pi (1 / 2), nInf) ++
  each (nonzeroParts.map (·, nan)) (nan, nan) ++
  [⟨(nInf, p0), (pi 1, nInf)⟩, ⟨(nInf, q 1), (pi 1, nInf)⟩,
    ⟨(pInf, p0), (p0, nInf)⟩, ⟨(pInf, q 1), (p0, nInf)⟩,
    ⟨(nInf, pInf), (pi (3 / 4), nInf)⟩,
    ⟨(pInf, pInf), (pi (1 / 4), nInf)⟩,
    ⟨(pInf, nan), (nan, .anyInf)⟩, ⟨(nInf, nan), (nan, .anyInf)⟩,
    ⟨(nan, p0), (nan, nan)⟩, ⟨(nan, q 1), (nan, nan)⟩,
    ⟨(nan, pInf), (nan, nInf)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.3.1, `cacosh`. -/
def acoshRows : List Row :=
  each [(p0, p0), (n0, p0)] (p0, pi (1 / 2)) ++
  each (finiteParts.map (·, pInf)) (pInf, pi (1 / 2)) ++
  each [(p0, nan), (n0, nan)] (nan, .piAnySign (1 / 2)) ++
  each (nonzeroParts.map (·, nan)) (nan, nan) ++
  [⟨(nInf, p0), (pInf, pi 1)⟩, ⟨(nInf, q 1), (pInf, pi 1)⟩,
    ⟨(pInf, p0), (pInf, p0)⟩, ⟨(pInf, q 1), (pInf, p0)⟩,
    ⟨(nInf, pInf), (pInf, pi (3 / 4))⟩,
    ⟨(pInf, pInf), (pInf, pi (1 / 4))⟩,
    ⟨(pInf, nan), (pInf, nan)⟩, ⟨(nInf, nan), (pInf, nan)⟩,
    ⟨(nan, p0), (nan, nan)⟩, ⟨(nan, q 1), (nan, nan)⟩,
    ⟨(nan, pInf), (pInf, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.3.2, `casinh`, in the first quadrant. -/
def asinhRows : List Row :=
  [⟨(p0, p0), (p0, p0)⟩,
    ⟨(p0, pInf), (pInf, pi (1 / 2))⟩, ⟨(q 1, pInf), (pInf, pi (1 / 2))⟩,
    ⟨(p0, nan), (nan, nan)⟩, ⟨(q 1, nan), (nan, nan)⟩,
    ⟨(pInf, p0), (pInf, p0)⟩, ⟨(pInf, q 1), (pInf, p0)⟩,
    ⟨(pInf, pInf), (pInf, pi (1 / 4))⟩,
    ⟨(pInf, nan), (pInf, nan)⟩,
    ⟨(nan, p0), (nan, p0)⟩,
    ⟨(nan, q 1), (nan, nan)⟩,
    ⟨(nan, pInf), (.anyInf, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.3.3, `catanh`, in the first quadrant. -/
def atanhRows : List Row :=
  [⟨(p0, p0), (p0, p0)⟩,
    ⟨(p0, nan), (p0, nan)⟩,
    ⟨(q 1, p0), (pInf, p0)⟩,
    ⟨(p0, pInf), (p0, pi (1 / 2))⟩, ⟨(q 1, pInf), (p0, pi (1 / 2))⟩,
    ⟨(q 2, pInf), (p0, pi (1 / 2))⟩,
    ⟨(q 1, nan), (nan, nan)⟩, ⟨(q 2, nan), (nan, nan)⟩,
    ⟨(pInf, p0), (p0, pi (1 / 2))⟩, ⟨(pInf, q 1), (p0, pi (1 / 2))⟩,
    ⟨(pInf, pInf), (p0, pi (1 / 2))⟩,
    ⟨(pInf, nan), (p0, nan)⟩,
    ⟨(nan, p0), (nan, nan)⟩, ⟨(nan, q 1), (nan, nan)⟩,
    ⟨(nan, pInf), (.anyZero, pi (1 / 2))⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.3.4, `ccosh`, in the first quadrant. -/
def coshRows : List Row :=
  [⟨(p0, p0), (q 1, p0)⟩,
    ⟨(p0, pInf), (nan, .anyZero)⟩,
    ⟨(p0, nan), (nan, .anyZero)⟩,
    ⟨(q 1, pInf), (nan, nan)⟩,
    ⟨(q 1, nan), (nan, nan)⟩,
    ⟨(pInf, p0), (pInf, p0)⟩,
    ⟨(pInf, q 1), (pInf, pInf)⟩, ⟨(pInf, q 2), (nInf, pInf)⟩,
    ⟨(pInf, q 4), (nInf, nInf)⟩, ⟨(pInf, q 5), (pInf, nInf)⟩,
    ⟨(pInf, pInf), (.anyInf, nan)⟩,
    ⟨(pInf, nan), (pInf, nan)⟩,
    ⟨(nan, p0), (nan, .anyZero)⟩,
    ⟨(nan, q 1), (nan, nan)⟩, ⟨(nan, pInf), (nan, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.3.5, `csinh`, in the first quadrant. -/
def sinhRows : List Row :=
  [⟨(p0, p0), (p0, p0)⟩,
    ⟨(p0, pInf), (.anyZero, nan)⟩,
    ⟨(p0, nan), (.anyZero, nan)⟩,
    ⟨(q 1, pInf), (nan, nan)⟩,
    ⟨(q 1, nan), (nan, nan)⟩,
    ⟨(pInf, p0), (pInf, p0)⟩,
    ⟨(pInf, q 1), (pInf, pInf)⟩, ⟨(pInf, q 2), (nInf, pInf)⟩,
    ⟨(pInf, q 4), (nInf, nInf)⟩, ⟨(pInf, q 5), (pInf, nInf)⟩,
    ⟨(pInf, pInf), (.anyInf, nan)⟩,
    ⟨(pInf, nan), (.anyInf, nan)⟩,
    ⟨(nan, p0), (nan, p0)⟩,
    ⟨(nan, q 1), (nan, nan)⟩, ⟨(nan, pInf), (nan, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/-- G.6.3.6, `ctanh`, in the first quadrant. `0 sin 2y` is `+0` at `y = 0, 1` and `-0` at
`y = 2`. -/
def tanhRows : List Row :=
  [⟨(p0, p0), (p0, p0)⟩,
    ⟨(p0, pInf), (p0, nan)⟩,
    ⟨(q 1, pInf), (nan, nan)⟩,
    ⟨(p0, nan), (p0, nan)⟩,
    ⟨(q 1, nan), (nan, nan)⟩,
    ⟨(pInf, p0), (q 1, p0)⟩, ⟨(pInf, q 1), (q 1, p0)⟩, ⟨(pInf, q 2), (q 1, n0)⟩,
    ⟨(pInf, pInf), (q 1, .anyZero)⟩,
    ⟨(pInf, nan), (q 1, .anyZero)⟩,
    ⟨(nan, p0), (nan, p0)⟩,
    ⟨(nan, q 1), (nan, nan)⟩, ⟨(nan, pInf), (nan, nan)⟩,
    ⟨(nan, nan), (nan, nan)⟩]

/--
The harness itself: a row with a wrong result, `cexp (+0 + 0 i) = 2 + 0 i`, must fail in each of
the four formats and six directions. The count is the number of those 24 checks that pass.
-/
def undetected : Nat :=
  24 - failures (fun _ z mode => ExecComplex.exp z mode) [⟨(p0, p0), (q 2, p0)⟩]

/-- The failures of every table, by function. Every row should be zero. -/
def annexGRows : List (String × Nat) :=
  let asinhAll := closure (some true) asinhRows
  let atanhAll := closure (some true) atanhRows
  let coshAll := closure (some false) coshRows
  let sinhAll := closure (some true) sinhRows
  let tanhAll := closure (some true) tanhRows
  [("a wrong row is detected", undetected),
    ("cexp, G.6.4.1", failures (fun _ z mode => ExecComplex.exp z mode) (closure none expRows)),
    ("clog, G.6.4.2", failures (fun _ z mode => ExecComplex.log z mode) (closure none logRows)),
    ("csqrt, G.6.5.2",
      failures (fun _ z mode => ExecComplex.sqrt z mode) (closure none sqrtRows)),
    ("cacos, G.6.2.1",
      failures (fun _ z mode => ExecComplex.acos z mode) (closure none acosRows)),
    ("cacosh, G.6.3.1",
      failures (fun _ z mode => ExecComplex.acosh z mode) (closure none acoshRows)),
    ("casinh, G.6.3.2", failures (fun _ z mode => ExecComplex.asinh z mode) asinhAll),
    ("catanh, G.6.3.3", failures (fun _ z mode => ExecComplex.atanh z mode) atanhAll),
    ("ccosh, G.6.3.4", failures (fun _ z mode => ExecComplex.cosh z mode) coshAll),
    ("csinh, G.6.3.5", failures (fun _ z mode => ExecComplex.sinh z mode) sinhAll),
    ("ctanh, G.6.3.6", failures (fun _ z mode => ExecComplex.tanh z mode) tanhAll),
    ("casin, G.6.1", failures (fun _ z mode => ExecComplex.asin z mode)
      (asinhAll.map (Row.circular true))),
    ("catan, G.6.1", failures (fun _ z mode => ExecComplex.atan z mode)
      (atanhAll.map (Row.circular true))),
    ("ccos, G.6.1", failures (fun _ z mode => ExecComplex.cos z mode)
      (coshAll.map (Row.circular false))),
    ("csin, G.6.1", failures (fun _ z mode => ExecComplex.sin z mode)
      (sinhAll.map (Row.circular true))),
    ("ctan, G.6.1", failures (fun _ z mode => ExecComplex.tan z mode)
      (tanhAll.map (Row.circular true)))]

/-! ## Branch cuts at finite arguments -/

/-- A part that is not a NaN and has a clear sign bit. -/
def positive {fmt : FloatFormat} (value : Model fmt) : Bool :=
  !Model.signBit value && !Model.isNaN value

/--
The two sides of each branch cut (C23 7.3.3), at arguments whose results have an exactly known
part: `csqrt (-4 ± 0 i) = +0 ± 2 i`, `clog (-1 ± 0 i) = +0 ± π i`,
`casinh (±0 + 2 i) = ±arcosh 2 + (π / 2) i`, `catanh (2 ± 0 i) = artanh (1 / 2) ± (π / 2) i`,
`cacosh (-2 ± 0 i) = arcosh 2 ± π i`, `cacos (2 ± 0 i) = +0 ∓ arcosh 2 i`, and the same
functions on their cuts through `casin z = -i casinh (i z)` and `catan z = -i catanh (i z)`.
The parts that are not exactly known are compared with GNU MPC elsewhere.
-/
def cutFailures : List (String × Nat) :=
  let check (function : (fmt : FloatFormat) → ExecComplex fmt → Model.IEEERoundingMode →
      ExecComplex fmt) (argument : Part × Part) (re im : Option Part) : Nat := Id.run do
    let mut count := 0
    for fmt in [FloatFormat.binary16, FloatFormat.bfloat16, FloatFormat.binary32,
        FloatFormat.binary64] do
      for mode in Model.IEEERoundingMode.all do
        let value := function fmt ⟨argument.1.encode fmt, argument.2.encode fmt⟩ mode
        let reOk := match re with | some part => part.agrees fmt mode value.re | none => true
        let imOk := match im with | some part => part.agrees fmt mode value.im | none => true
        count := count + failureCount (reOk && imOk)
    return count
  let signs (function : (fmt : FloatFormat) → ExecComplex fmt → Model.IEEERoundingMode →
      ExecComplex fmt) (argument : Part × Part) (reNegative imNegative : Bool) : Nat := Id.run do
    let mut count := 0
    for fmt in [FloatFormat.binary16, FloatFormat.bfloat16, FloatFormat.binary32,
        FloatFormat.binary64] do
      for mode in Model.IEEERoundingMode.all do
        let value := function fmt ⟨argument.1.encode fmt, argument.2.encode fmt⟩ mode
        count := count + failureCount
          (positive value.re != reNegative && positive value.im != imNegative)
    return count
  [("csqrt on the negative real axis",
      check (fun _ z mode => ExecComplex.sqrt z mode) (q (-4), p0) (some p0) (some (q 2)) +
      check (fun _ z mode => ExecComplex.sqrt z mode) (q (-4), n0) (some p0) (some (q (-2)))),
    ("clog on the negative real axis",
      check (fun _ z mode => ExecComplex.log z mode) (q (-1), p0) (some p0) (some (pi 1)) +
      check (fun _ z mode => ExecComplex.log z mode) (q (-1), n0) (some p0) (some (pi (-1)))),
    ("casinh on the imaginary axis beyond i",
      check (fun _ z mode => ExecComplex.asinh z mode) (p0, q 2) none (some (pi (1 / 2))) +
      check (fun _ z mode => ExecComplex.asinh z mode) (n0, q 2) none (some (pi (1 / 2))) +
      signs (fun _ z mode => ExecComplex.asinh z mode) (p0, q 2) false false +
      signs (fun _ z mode => ExecComplex.asinh z mode) (n0, q 2) true false +
      signs (fun _ z mode => ExecComplex.asinh z mode) (p0, q (-2)) false true +
      signs (fun _ z mode => ExecComplex.asinh z mode) (n0, q (-2)) true true),
    ("casin on the real axis beyond 1",
      check (fun _ z mode => ExecComplex.asin z mode) (q 2, p0) (some (pi (1 / 2))) none +
      check (fun _ z mode => ExecComplex.asin z mode) (q 2, n0) (some (pi (1 / 2))) none +
      signs (fun _ z mode => ExecComplex.asin z mode) (q 2, p0) false false +
      signs (fun _ z mode => ExecComplex.asin z mode) (q 2, n0) false true +
      signs (fun _ z mode => ExecComplex.asin z mode) (q (-2), p0) true false +
      signs (fun _ z mode => ExecComplex.asin z mode) (q (-2), n0) true true),
    ("catanh on the real axis beyond 1",
      check (fun _ z mode => ExecComplex.atanh z mode) (q 2, p0) none (some (pi (1 / 2))) +
      check (fun _ z mode => ExecComplex.atanh z mode) (q 2, n0) none (some (pi (-1 / 2))) +
      check (fun _ z mode => ExecComplex.atanh z mode) (q (-2), p0) none (some (pi (1 / 2))) +
      check (fun _ z mode => ExecComplex.atanh z mode) (q (-2), n0) none (some (pi (-1 / 2))) +
      signs (fun _ z mode => ExecComplex.atanh z mode) (q 2, p0) false false +
      signs (fun _ z mode => ExecComplex.atanh z mode) (q (-2), n0) true true),
    ("catan on the imaginary axis beyond i",
      check (fun _ z mode => ExecComplex.atan z mode) (p0, q 2) (some (pi (1 / 2))) none +
      check (fun _ z mode => ExecComplex.atan z mode) (n0, q 2) (some (pi (-1 / 2))) none +
      signs (fun _ z mode => ExecComplex.atan z mode) (p0, q 2) false false +
      signs (fun _ z mode => ExecComplex.atan z mode) (n0, q (-2)) true true),
    ("cacosh on the real axis below 1",
      check (fun _ z mode => ExecComplex.acosh z mode) (q (-2), p0) none (some (pi 1)) +
      check (fun _ z mode => ExecComplex.acosh z mode) (q (-2), n0) none (some (pi (-1))) +
      check (fun _ z mode => ExecComplex.acosh z mode) (q 2, p0) none (some p0) +
      check (fun _ z mode => ExecComplex.acosh z mode) (q 2, n0) none (some n0) +
      signs (fun _ z mode => ExecComplex.acosh z mode) (q (-2), n0) false true),
    ("cacos on the real axis beyond 1",
      check (fun _ z mode => ExecComplex.acos z mode) (q 2, p0) (some p0) none +
      check (fun _ z mode => ExecComplex.acos z mode) (q 2, n0) (some p0) none +
      check (fun _ z mode => ExecComplex.acos z mode) (q (-2), p0) (some (pi 1)) none +
      check (fun _ z mode => ExecComplex.acos z mode) (q (-2), n0) (some (pi 1)) none +
      signs (fun _ z mode => ExecComplex.acos z mode) (q 2, p0) false true +
      signs (fun _ z mode => ExecComplex.acos z mode) (q 2, n0) false false +
      signs (fun _ z mode => ExecComplex.acos z mode) (q (-2), p0) false true +
      signs (fun _ z mode => ExecComplex.acos z mode) (q (-2), n0) false false)]

/-! ## Special values that C leaves open -/

/--
The special values of `rsqrt`, which is `1 / csqrt z` rounded once, and of `pow`, to which C23
G.6.5.1 gives no table: `rsqrt (±0 + 0 i) = ∞ + NaN i`, `rsqrt (∞ + 0 i) = +0 - 0 i`,
`rsqrt (4 + 0 i) = 1 / 2 - 0 i`, `rsqrt (-4 + 0 i) = +0 - i / 2`; `pow z 0 = 1 + 0 i` also at a
NaN, `pow 0 w` by the sign of the real part of `w`, exact integer and half-integer powers, exact
powers `n / 2 ^ k` of a base with a complex rational root such as `(-4) ^ (1 / 4) = 1 + i`,
certified in every direction, the two sides of the cut of the base, powers that overflow or
lie below the least positive number in each part, with their signs, and even powers of a base on
a diagonal that are too long to form.
-/
def openFailures : List (String × Nat) :=
  let unary (function : (fmt : FloatFormat) → ExecComplex fmt → Model.IEEERoundingMode →
      ExecComplex fmt) (rows : List Row) : Nat := failures function rows
  let power (base exponent result : Part × Part) (certified : Bool) : Nat := Id.run do
    let mut count := 0
    for fmt in [FloatFormat.binary16, FloatFormat.bfloat16, FloatFormat.binary32,
        FloatFormat.binary64] do
      for mode in Model.IEEERoundingMode.all do
        let value := ExecComplex.powChecked (fmt := fmt) ⟨base.1.encode fmt, base.2.encode fmt⟩
          ⟨exponent.1.encode fmt, exponent.2.encode fmt⟩ mode
        count := count + failureCount (result.1.agrees fmt mode value.1.re &&
          result.2.agrees fmt mode value.1.im && value.2 == certified)
    return count
  [("rsqrt", unary (fun _ z mode => ExecComplex.rsqrt z mode)
      [⟨(p0, p0), (pInf, nan)⟩, ⟨(n0, p0), (pInf, nan)⟩, ⟨(pInf, p0), (p0, n0)⟩,
        ⟨(pInf, n0), (p0, p0)⟩, ⟨(q 4, p0), (q (1 / 2), n0)⟩, ⟨(q 4, n0), (q (1 / 2), p0)⟩,
        ⟨(q (-4), p0), (p0, q (-1 / 2))⟩, ⟨(q (-4), n0), (p0, q (1 / 2))⟩,
        ⟨(nan, p0), (nan, nan)⟩]),
    ("pow with a zero exponent",
      power (q 3, q 4) (p0, p0) (q 1, p0) true + power (nan, pInf) (n0, p0) (q 1, p0) true +
      power (p0, p0) (p0, n0) (q 1, p0) true + power (q 3, n0) (p0, p0) (q 1, n0) true),
    ("pow of a zero base",
      power (p0, p0) (q 2, q 1) (p0, p0) true + power (n0, p0) (q 1, p0) (p0, p0) true +
      power (p0, p0) (q (-2), q 1) (pInf, nan) true + power (p0, p0) (p0, q 1) (nan, nan) true),
    ("pow at a NaN or an infinity",
      power (nan, p0) (q 2, p0) (nan, nan) true + power (q 2, p0) (pInf, p0) (nan, nan) true +
      power (pInf, p0) (q 2, p0) (nan, nan) true),
    ("exact powers",
      power (q 3, q 4) (q 2, p0) (q (-7), q 24) true +
      power (q 3, q 4) (q (-1), p0) (q (3 / 25), q (-4 / 25)) true +
      power (q 2, p0) (q 10, p0) (q 1024, p0) true +
      power (q (-2), p0) (q 3, p0) (q (-8), p0) true +
      power (q 4, p0) (q (1 / 2), p0) (q 2, p0) true +
      power (q 4, p0) (q (-1 / 2), p0) (q (1 / 2), p0) true +
      power (p0, q 2) (q 2, p0) (q (-4), p0) true +
      power (q (-3), q 4) (q (1 / 2), p0) (q 1, q 2) true +
      power (q 1, p0) (q 5, q 7) (q 1, p0) true),
    ("exact powers of a complex rational root",
      power (q (-4), p0) (q (1 / 4), p0) (q 1, q 1) true +
      power (q (-4), n0) (q (1 / 4), p0) (q 1, q (-1)) true +
      power (q (-1 / 4), p0) (q (1 / 4), p0) (q (1 / 2), q (1 / 2)) true +
      power (p0, q 2) (q (-1 / 2), p0) (q (1 / 2), q (-1 / 2)) true +
      power (p0, q (1 / 2)) (q (-1 / 2), p0) (q 1, q (-1)) true +
      power (q 16, p0) (q (3 / 4), p0) (q 8, p0) true +
      power (q (-7), q 24) (q (3 / 2), p0) (q (-117), q 44) true +
      power (q (-7), q (-24)) (q (3 / 2), p0) (q (-117), q (-44)) true +
      power (q (-7), q 24) (q (-1 / 2), p0) (q (3 / 25), q (-4 / 25)) true),
    ("pow on the cut of the base",
      power (q (-1), p0) (q (1 / 2), p0) (p0, q 1) true +
      power (q (-1), n0) (q (1 / 2), p0) (p0, q (-1)) true +
      power (q (-4), p0) (q (3 / 2), p0) (p0, q (-8)) true +
      power (q (-4), n0) (q (3 / 2), p0) (p0, q 8) true +
      power (q (-1), p0) (q 3, p0) (q (-1), p0) true +
      power (q (-1), n0) (q 3, p0) (q (-1), n0) true),
    ("pow beyond the range",
      power (q 3, q 4) (q 32768, p0) (q (2 ^ 2000), q (2 ^ 2000)) true +
      power (q 3, q (-4)) (q 32768, p0) (q (2 ^ 2000), q (-(2 ^ 2000))) true +
      power (q 3, q 4) (q (-32768), p0) (q (1 / 2 ^ 3000), q (-1 / 2 ^ 3000)) true +
      power (q 3, q 4) (q (-32768), q 12288) (q (-1 / 2 ^ 3000), q (-1 / 2 ^ 3000)) true +
      power (q 3, q 4) (q 32768, q (-12288)) (q (-(2 ^ 2000)), q (2 ^ 2000)) true +
      power (q (-2), q 1) (q 32768, p0) (q (2 ^ 2000), q (-(2 ^ 2000))) true +
      power (q (-2), q 1) (q (-32768), p0) (q (1 / 2 ^ 3000), q (1 / 2 ^ 3000)) true),
    ("pow of a base on a diagonal",
      power (q 3, q 3) (q 6, p0) (p0, q (-5832)) true +
      power (q 3, q 3) (q 32768, p0) (q (2 ^ 2000), p0) true +
      power (q 3, q (-3)) (q 32768, p0) (q (2 ^ 2000), n0) true +
      power (q (-3), q 3) (q 32768, p0) (q (2 ^ 2000), p0) true +
      power (q 3, q 3) (q (-32768), p0) (q (1 / 2 ^ 3000), p0) true +
      power (q (-3), q 3) (q 6, p0) (p0, q 5832) true +
      power (q 3, q (-3)) (q 6, p0) (p0, q 5832) true)]

/-- The special values of Annex G. -/
def annexG : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "complex functions: C23 Annex G special values" annexGRows⟩

/-- The branch cuts at finite arguments. -/
def cuts : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "complex functions: branch cuts" cutFailures⟩

/-- The special values of `rsqrt` and `pow`. -/
def unspecified : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "complex functions: rsqrt and pow special values" openFailures⟩

end FloatLibTests.Regression.BinaryInterchange.ComplexElementary
