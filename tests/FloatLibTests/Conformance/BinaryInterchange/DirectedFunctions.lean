/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Directed.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Directed.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public meta import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Directed.Runtime
public meta import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Directed.Runtime
public meta import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public meta import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# `exp`, `expm1`, `log`, `logp1`, `rSqrt`, `hypot`, `rootn` and `pown` with flags

Special cases of the functions of `Model.Transcendentals.Directed` and
`Model.Algebraic.Directed` on binary16, as IEEE 754-2019 §9.2.1 and ISO/IEC 9899:2024 F.10.3
state them: the results at zeros, infinities and NaNs, the domain errors with `invalid`, the
poles with `divideByZero`, the exact results that raise no flag, and results in several
rounding directions. `cases` holds every case once, and compiled evaluation checks it when this
module is elaborated. `agreementCases` compare the values to nearest-even with `Model.rSqrt`,
`hypot`, `rootn` and `pown` on every 97th encoding of binary16. `smallCases` are results on the
two formats of the OCP 8-bit specification, E4M3 and E5M2, and on the ONNX format E4M3FNUZ. The
results at ordinary operands are compared with `mpmath` by `tests/oracles/ieee2019.sh`, on
every encoding of the eight-bit formats.

The second half applies the theorems to binary32, E5M2, E4M3, E2M1 and the ONNX formats
E4M3FNUZ and E5M2FNUZ in every rounding direction: the theorems have no premise on the format.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.DirectedFunctions

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model

/-- The value of the format with the encoding `bits`. -/
def value (fmt : FloatFormat) (bits : Nat) : Model fmt := Model.ofNatBits bits

/-- The binary16 value with the encoding `bits`. -/
def b16 (bits : Nat) : Model FloatFormat.binary16 := value _ bits

/--
The encoding of a result and its flags as the sum of invalid 1, divideByZero 2, overflow 4,
underflow 8 and inexact 16.
-/
def result {fmt : FloatFormat} (outcome : IEEEOutcome fmt) : Nat × Nat :=
  (outcome.value.toNatBits,
    (if outcome.status.invalid then 1 else 0) + (if outcome.status.divideByZero then 2 else 0) +
      (if outcome.status.overflow then 4 else 0) + (if outcome.status.underflow then 8 else 0) +
      (if outcome.status.inexact then 16 else 0))

open Transcendentals Algebraic in
/-- The special cases: a name and whether the case holds, on binary16. -/
def cases : List (String × Bool) :=
  [ ("exp (+0) is 1", result (Directed.exp (b16 0x0000)) == (0x3C00, 0)),
    ("exp (-inf) is +0", result (Directed.exp (b16 0xFC00)) == (0x0000, 0)),
    ("exp (+inf) is +inf", result (Directed.exp (b16 0x7C00)) == (0x7C00, 0)),
    ("exp 1 toward negative and toward positive are neighbours",
      (result (Directed.exp (b16 0x3C00) .down), result (Directed.exp (b16 0x3C00) .up)) ==
        ((0x416F, 16), (0x4170, 16))),
    ("exp 12 overflows to +inf to nearest and to the largest value toward zero",
      (result (Directed.exp (b16 0x4A00)), result (Directed.exp (b16 0x4A00) .towardZero)) ==
        ((0x7C00, 20), (0x7BFF, 20))),
    ("expm1 (-0) is -0", result (Directed.expm1 (b16 0x8000)) == (0x8000, 0)),
    ("expm1 (-inf) is -1", result (Directed.expm1 (b16 0xFC00)) == (0xBC00, 0)),
    ("log (+0) is -inf with divideByZero", result (Directed.log (b16 0x0000)) == (0xFC00, 2)),
    ("log 1 is +0", result (Directed.log (b16 0x3C00)) == (0x0000, 0)),
    ("log (-1) is invalid", result (Directed.log (b16 0xBC00)) == (0x7E00, 1)),
    ("logp1 (-1) is -inf with divideByZero", result (Directed.logp1 (b16 0xBC00)) == (0xFC00, 2)),
    ("logp1 (-0) is -0", result (Directed.logp1 (b16 0x8000)) == (0x8000, 0)),
    ("rSqrt (+0) is +inf with divideByZero", result (Directed.rSqrt (b16 0x0000)) == (0x7C00, 2)),
    ("rSqrt (-0) is -inf with divideByZero", result (Directed.rSqrt (b16 0x8000)) == (0xFC00, 2)),
    ("rSqrt (-1) is invalid", result (Directed.rSqrt (b16 0xBC00)) == (0x7E00, 1)),
    ("rSqrt (+inf) is +0", result (Directed.rSqrt (b16 0x7C00)) == (0x0000, 0)),
    ("rSqrt (-inf) is invalid", result (Directed.rSqrt (b16 0xFC00)) == (0x7E00, 1)),
    ("rSqrt 4 is 0.5, exactly", result (Directed.rSqrt (b16 0x4400)) == (0x3800, 0)),
    ("rSqrt 2 toward negative and toward positive are neighbours",
      (result (Directed.rSqrt (b16 0x4000) .down), result (Directed.rSqrt (b16 0x4000) .up)) ==
        ((0x39A8, 16), (0x39A9, 16))),
    ("hypot 3 4 is 5, exactly", result (Directed.hypot (b16 0x4200) (b16 0x4400)) == (0x4500, 0)),
    ("hypot (-0) (+0) is +0", result (Directed.hypot (b16 0x8000) (b16 0x0000)) == (0x0000, 0)),
    ("hypot (-inf) NaN is +inf", result (Directed.hypot (b16 0xFC00) (b16 0x7E00)) == (0x7C00, 0)),
    ("hypot of a signaling NaN and an infinity is invalid",
      result (Directed.hypot (b16 0x7D00) (b16 0x7C00)) == (0x7F00, 1)),
    ("hypot of the largest value with itself overflows",
      result (Directed.hypot (b16 0x7BFF) (b16 0x7BFF)) == (0x7C00, 20)),
    ("hypot of two values whose squares overflow is finite",
      result (Directed.hypot (b16 0x7800) (b16 0x7800)) == (0x79A8, 16)),
    ("rootn (-8) 3 is -2", result (Directed.rootn (b16 0xC800) 3) == (0xC000, 0)),
    ("cbrt 27 is 3", result (Directed.cbrt (b16 0x4EC0)) == (0x4200, 0)),
    ("rootn (-0) (-3) is -inf with divideByZero",
      result (Directed.rootn (b16 0x8000) (-3)) == (0xFC00, 2)),
    ("rootn (-0) (-2) is +inf with divideByZero",
      result (Directed.rootn (b16 0x8000) (-2)) == (0x7C00, 2)),
    ("rootn (-0) 3 is -0", result (Directed.rootn (b16 0x8000) 3) == (0x8000, 0)),
    ("rootn (-4) 2 is invalid", result (Directed.rootn (b16 0xC400) 2) == (0x7E00, 1)),
    ("rootn 4 0 is invalid", result (Directed.rootn (b16 0x4400) 0) == (0x7E00, 1)),
    ("rootn 4 (-2) is 0.5", result (Directed.rootn (b16 0x4400) (-2)) == (0x3800, 0)),
    ("rootn (-inf) 3 is -inf", result (Directed.rootn (b16 0xFC00) 3) == (0xFC00, 0)),
    ("rootn (-inf) (-3) is -0", result (Directed.rootn (b16 0xFC00) (-3)) == (0x8000, 0)),
    ("pown 2 10 is 1024", result (Directed.pown (b16 0x4000) 10) == (0x6400, 0)),
    ("pown of a quiet NaN and 0 is 1", result (Directed.pown (b16 0x7E00) 0) == (0x3C00, 0)),
    ("pown of a signaling NaN and 0 is invalid",
      result (Directed.pown (b16 0x7D00) 0) == (0x7F00, 1)),
    ("pown (-0) (-3) is -inf with divideByZero",
      result (Directed.pown (b16 0x8000) (-3)) == (0xFC00, 2)),
    ("pown (-0) 2 is +0", result (Directed.pown (b16 0x8000) 2) == (0x0000, 0)),
    ("pown (-inf) 3 is -inf", result (Directed.pown (b16 0xFC00) 3) == (0xFC00, 0)),
    ("pown (-inf) (-2) is +0", result (Directed.pown (b16 0xFC00) (-2)) == (0x0000, 0)),
    ("pown (-2) 3 is -8", result (Directed.pown (b16 0xC000) 3) == (0xC800, 0)),
    ("pown 3 (-1) toward negative and toward positive are neighbours",
      (result (Directed.pown (b16 0x4200) (-1) .down),
        result (Directed.pown (b16 0x4200) (-1) .up)) == ((0x3555, 16), (0x3556, 16))) ]

open Algebraic in
/--
To nearest-even the values are those of `Model.rSqrt`, `hypot`, `rootn` and `pown`, on every
97th encoding of binary16 (a NaN is compared as a NaN).
-/
def agreementCases : List (String × Bool) :=
  let same (left right : Model FloatFormat.binary16) : Bool :=
    left.toNatBits == right.toNatBits || (isNaN left && isNaN right)
  (List.range 676).flatMap fun index =>
    let x := b16 (97 * index)
    let y := b16 ((97 * index * 31 + 5) % 65536)
    [(s!"rSqrt of the encoding {97 * index}", same (Directed.rSqrt x).value (Model.rSqrt x)),
      (s!"hypot of the encodings {x.toNatBits} and {y.toNatBits}",
        same (Directed.hypot x y).value (Model.hypot x y)),
      (s!"rootn 3 of the encoding {97 * index}", same (Directed.rootn x 3).value (Model.rootn x 3)),
      (s!"rootn -2 of the encoding {97 * index}",
        same (Directed.rootn x (-2)).value (Model.rootn x (-2))),
      (s!"pown 3 of the encoding {97 * index}", same (Directed.pown x 3).value (Model.pown x 3)),
      (s!"pown -2 of the encoding {97 * index}",
        same (Directed.pown x (-2)).value (Model.pown x (-2)))]

open Transcendentals Algebraic in
/--
Results on E4M3 (largest finite value 448, no infinity, the NaN `S.1111.111`), E5M2 (an IEEE
format) and E4M3FNUZ (largest finite value 240, one zero, the NaN `0x80`).
-/
def smallCases : List (String × Bool) :=
  let e4m3 := value FloatFormat.e4m3
  let e5m2 := value FloatFormat.e5m2
  let fnuz := value FloatFormat.e4m3fnuz
  [ ("E4M3 exp 0 is 1", result (Directed.exp (e4m3 0x00)) == (0x38, 0)),
    ("E4M3 exp 1 is 2.75 to nearest", result (Directed.exp (e4m3 0x38)) == (0x43, 16)),
    ("E4M3 exp 1 is 2.5 toward negative", result (Directed.exp (e4m3 0x38) .down) == (0x42, 16)),
    ("E4M3 exp 448 overflows to the NaN", result (Directed.exp (e4m3 0x7E)) == (0x7F, 20)),
    ("E4M3 exp 448 toward zero is 448",
      result (Directed.exp (e4m3 0x7E) .towardZero) == (0x7E, 20)),
    ("E4M3 log 0 is the NaN with divideByZero", result (Directed.log (e4m3 0x00)) == (0xFF, 2)),
    ("E4M3 rSqrt 4 is 0.5", result (Directed.rSqrt (e4m3 0x48)) == (0x30, 0)),
    ("E4M3 cbrt (-8) is -2", result (Directed.cbrt (e4m3 0xD0)) == (0xC0, 0)),
    ("E4M3 pown 2 8 is 256", result (Directed.pown (e4m3 0x40) 8) == (0x78, 0)),
    ("E4M3 pown 2 9 overflows to the NaN", result (Directed.pown (e4m3 0x40) 9) == (0x7F, 20)),
    ("E4M3 hypot 3 4 is 5", result (Directed.hypot (e4m3 0x44) (e4m3 0x48)) == (0x4A, 0)),
    ("E5M2 exp 0 is 1", result (Directed.exp (e5m2 0x00)) == (0x3C, 0)),
    ("E5M2 log 0 is -inf with divideByZero", result (Directed.log (e5m2 0x00)) == (0xFC, 2)),
    ("E5M2 rSqrt 4 is 0.5", result (Directed.rSqrt (e5m2 0x44)) == (0x38, 0)),
    ("E5M2 cbrt 8 is 2", result (Directed.cbrt (e5m2 0x48)) == (0x40, 0)),
    ("E4M3FNUZ exp 0 is 1", result (Directed.exp (fnuz 0x00)) == (0x40, 0)),
    ("E4M3FNUZ log 0 is the NaN with divideByZero",
      result (Directed.log (fnuz 0x00)) == (0x80, 2)),
    ("E4M3FNUZ pown 2 8 overflows to the NaN",
      result (Directed.pown (fnuz 0x48) 8) == (0x80, 20)) ]

#eval show IO Unit from do
  let failures := (cases ++ agreementCases ++ smallCases).filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"cases that fail: {failures.map (·.1)}"
  IO.println <| s!"{cases.length} special cases hold, {agreementCases.length} values agree with " ++
    s!"the nearest-even functions, and {smallCases.length} results on eight-bit formats hold"

/-! ## The theorems on binary32 and on the eight-bit formats -/

section Contracts

open Algebraic

variable {x y : Model FloatFormat.binary32} {p q : ℚ}

example (mode : IEEERoundingMode) (hq : toRat? x = some q) (hpos : 0 < q) :
    RoundsTo FloatFormat.binary32 mode (Real.sqrt q)⁻¹ false (Directed.rSqrt x mode).value :=
  Directed.rSqrt_roundsTo hq hpos

example (mode : IEEERoundingMode) (hx : toRat? x = some p) (hy : toRat? y = some q)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    RoundsTo FloatFormat.binary32 mode (Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) false
      (Directed.hypot x y mode).value :=
  Directed.hypot_roundsTo hx hy hne

example (mode : IEEERoundingMode) (hq : toRat? x = some q) (hneg : q < 0) :
    RoundsTo FloatFormat.binary32 mode (-((-q : ℝ) ^ ((3 : ℝ)⁻¹))) true
      (Directed.cbrt x mode).value :=
  Directed.cbrt_roundsTo_of_neg hq hneg

example (mode : IEEERoundingMode) (hq : toRat? x = some q) (hpos : 0 < q) (degree : ℤ)
    (hdegree : degree ≠ 0) :
    RoundsTo FloatFormat.binary32 mode ((q : ℝ) ^ ((degree : ℝ)⁻¹)) false
      (Directed.rootn x degree mode).value :=
  Directed.rootn_roundsTo_of_pos hq hpos hdegree

example (mode : IEEERoundingMode) (hq : toRat? x = some q) (hne : q ≠ 0) (exponent : ℤ) :
    RoundsTo FloatFormat.binary32 mode ((q : ℝ) ^ exponent) (decide ((q : ℝ) ^ exponent < 0))
      (Directed.pown x exponent mode).value :=
  Directed.pown_roundsTo hq hne exponent

example (mode : IEEERoundingMode) (hq : toRat? x = some q) (hne : q ≠ 0) (exponent : ℤ)
    (hfinite : isFinite (Directed.pown x exponent mode).value = true) :
    (Directed.pown x exponent mode).status.inexact = true ↔
      toReal (Directed.pown x exponent mode).value ≠ (q : ℝ) ^ exponent :=
  Directed.pown_inexact_iff hq hne exponent mode hfinite

/-- `inexact` is raised exactly when the finite result is not the real value. -/
example (mode : IEEERoundingMode) (hq : toRat? x = some q) (hpos : 0 < q)
    (hexp : isFinite (Transcendentals.Directed.exp x mode).value = true)
    (hexpm1 : isFinite (Transcendentals.Directed.expm1 x mode).value = true)
    (hlog : isFinite (Transcendentals.Directed.log x mode).value = true)
    (hlogp1 : isFinite (Transcendentals.Directed.logp1 x mode).value = true) :
    ((Transcendentals.Directed.exp x mode).status.inexact = true ↔
        toReal (Transcendentals.Directed.exp x mode).value ≠ Real.exp q) ∧
      ((Transcendentals.Directed.expm1 x mode).status.inexact = true ↔
        toReal (Transcendentals.Directed.expm1 x mode).value ≠ Real.exp q - 1) ∧
      ((Transcendentals.Directed.log x mode).status.inexact = true ↔
        toReal (Transcendentals.Directed.log x mode).value ≠ Real.log q) ∧
      ((Transcendentals.Directed.logp1 x mode).status.inexact = true ↔
        toReal (Transcendentals.Directed.logp1 x mode).value ≠ Real.log ((q : ℝ) + 1)) :=
  ⟨Transcendentals.Directed.exp_inexact_iff hq mode hexp,
    Transcendentals.Directed.expm1_inexact_iff hq mode hexpm1,
    Transcendentals.Directed.log_inexact_iff hq hpos mode hlog,
    Transcendentals.Directed.logp1_inexact_iff hq (by linarith) mode hlogp1⟩

/--
`overflow` is raised exactly when the rounding of the real value with an unbounded exponent
range exceeds the largest finite value in magnitude (IEEE 754-2019 §7.4), on every format: here
on E4M3FNUZ, which delivers its NaN or its largest finite value there.
-/
example (mode : IEEERoundingMode) {z w : Model FloatFormat.e4m3fnuz} {r : ℚ}
    (hz : toRat? z = some q) (hw : toRat? w = some r) (hpos : 0 < q) (hone : q ≠ 1)
    (hnegative : r < 0) (exponent : ℤ) :
    ((Transcendentals.Directed.exp z mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (Real.exp q) mode|) ∧
      ((Transcendentals.Directed.expm1 z mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (Real.exp q - 1) mode|) ∧
      ((Transcendentals.Directed.log z mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (Real.log q) mode|) ∧
      ((Transcendentals.Directed.logp1 z mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (Real.log ((q : ℝ) + 1)) mode|) ∧
      ((Directed.rSqrt z mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (Real.sqrt q)⁻¹ mode|) ∧
      ((Directed.hypot z w mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (Real.sqrt ((q : ℝ) ^ 2 + (r : ℝ) ^ 2)) mode|) ∧
      ((Directed.rootn z 5 mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz ((q : ℝ) ^ (((5 : ℤ) : ℝ)⁻¹)) mode|) ∧
      ((Directed.rootn w 5 mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz (-((-r : ℝ) ^ (((5 : ℤ) : ℝ)⁻¹))) mode|) ∧
      ((Directed.pown z exponent mode).status.overflow = true ↔
        toReal (posMaxFinite FloatFormat.e4m3fnuz) <
          |roundAt FloatFormat.e4m3fnuz ((q : ℝ) ^ exponent) mode|) :=
  ⟨Transcendentals.Directed.exp_overflow_iff hz mode,
    Transcendentals.Directed.expm1_overflow_iff hz hpos.ne' mode,
    Transcendentals.Directed.log_overflow_iff hz hpos hone mode,
    Transcendentals.Directed.logp1_overflow_iff hz (by linarith) hpos.ne' mode,
    Directed.rSqrt_overflow_iff hz hpos mode,
    Directed.hypot_overflow_iff hz hw (.inl hpos.ne') mode,
    Directed.rootn_overflow_iff_of_pos hz hpos (by decide) mode,
    Directed.rootn_overflow_iff_of_neg hw hnegative (by decide) mode,
    Directed.pown_overflow_iff hz hpos.ne' exponent mode⟩

/--
Neither `invalid` nor `divideByZero` is raised at finite operands in the domain, and `rootn`
raises `inexact` exactly when its finite result is not the root, on every format: here on
E4M3FNUZ.
-/
example (mode : IEEERoundingMode) {z w : Model FloatFormat.e4m3fnuz} {r : ℚ}
    (hz : toRat? z = some q) (hw : toRat? w = some r) (hpos : 0 < q) (hnegative : r < 0)
    (exponent : ℤ) (hfinite : isFinite (Directed.rootn z 5 mode).value = true)
    (hfinite' : isFinite (Directed.rootn w 5 mode).value = true) :
    (Transcendentals.Directed.exp z mode).status.invalid = false ∧
      (Transcendentals.Directed.expm1 z mode).status.invalid = false ∧
      (Transcendentals.Directed.log z mode).status.divideByZero = false ∧
      (Transcendentals.Directed.logp1 z mode).status.divideByZero = false ∧
      (Directed.rSqrt z mode).status.invalid = false ∧
      (Directed.hypot z w mode).status.invalid = false ∧
      (Directed.rootn z 5 mode).status.invalid = false ∧
      (Directed.rootn w 5 mode).status.divideByZero = false ∧
      (Directed.pown z exponent mode).status.invalid = false ∧
      ((Directed.rootn z 5 mode).status.inexact = true ↔
        toReal (Directed.rootn z 5 mode).value ≠ (q : ℝ) ^ (((5 : ℤ) : ℝ)⁻¹)) ∧
      ((Directed.rootn w 5 mode).status.inexact = true ↔
        toReal (Directed.rootn w 5 mode).value ≠ -((-r : ℝ) ^ (((5 : ℤ) : ℝ)⁻¹))) :=
  ⟨(Transcendentals.Directed.exp_invalid_divideByZero hz mode).1,
    (Transcendentals.Directed.expm1_invalid_divideByZero hz mode).1,
    (Transcendentals.Directed.log_invalid_divideByZero hz hpos mode).2,
    (Transcendentals.Directed.logp1_invalid_divideByZero hz (by linarith) mode).2,
    (Directed.rSqrt_invalid_divideByZero hz hpos mode).1,
    (Directed.hypot_invalid_divideByZero hz hw (.inl hpos.ne') mode).1,
    (Directed.rootn_invalid_divideByZero_of_pos hz hpos (by decide) mode).1,
    (Directed.rootn_invalid_divideByZero_of_neg hw hnegative (by decide) mode).2,
    (Directed.pown_invalid_divideByZero hz hpos.ne' exponent mode).1,
    Directed.rootn_inexact_iff_of_pos hz hpos (by decide) mode hfinite,
    Directed.rootn_inexact_iff_of_neg hw hnegative (by decide) mode hfinite'⟩

/--
`underflow` is raised exactly when the result is inexact and the magnitude of the real value is
tiny after rounding in the direction (IEEE 754-2019 §7.5), on every format: here on E4M3FNUZ,
whose one zero is also what a tiny negative value rounds to.
-/
example (mode : IEEERoundingMode) {z : Model FloatFormat.e4m3fnuz} (hz : toRat? z = some q) :
    (Transcendentals.Directed.exp z mode).status.underflow = true ↔
      (Transcendentals.Directed.exp z mode).status.inexact = true ∧
        AlgebraicRounding.TinyAfterRounding FloatFormat.e4m3fnuz
          (mode.magnitudeRounding (decide (Real.exp q < 0))) |Real.exp q| :=
  Transcendentals.Directed.exp_underflow_iff hz mode

/-- An `exp` that raises `underflow` has a real value below the least normal magnitude. -/
example (mode : IEEERoundingMode) {z : Model FloatFormat.e4m3fnuz} (hz : toRat? z = some q)
    (h : (Transcendentals.Directed.exp z mode).status.underflow = true) :
    Real.exp q < (minNormalDyadic FloatFormat.e4m3fnuz).toReal := by
  have htiny := ((Transcendentals.Directed.exp_underflow_iff hz mode).mp h).2
  rw [abs_of_pos (Real.exp_pos _)] at htiny
  exact htiny.lt_minNormal

/-- The same statement for the other functions with flags: `underflow` comes with `inexact`. -/
example (mode : IEEERoundingMode) {z w : Model FloatFormat.e4m3fnuz} {r : ℚ}
    (hz : toRat? z = some q) (hw : toRat? w = some r) (hpos : 0 < q) (hone : q ≠ 1)
    (hnegative : r < 0) (exponent : ℤ) :
    ((Transcendentals.Directed.expm1 z mode).status.underflow = true →
        (Transcendentals.Directed.expm1 z mode).status.inexact = true) ∧
      ((Transcendentals.Directed.log z mode).status.underflow = true →
        (Transcendentals.Directed.log z mode).status.inexact = true) ∧
      ((Transcendentals.Directed.logp1 z mode).status.underflow = true →
        (Transcendentals.Directed.logp1 z mode).status.inexact = true) ∧
      ((Directed.rSqrt z mode).status.underflow = true →
        (Directed.rSqrt z mode).status.inexact = true) ∧
      ((Directed.hypot z w mode).status.underflow = true →
        (Directed.hypot z w mode).status.inexact = true) ∧
      ((Directed.rootn z 5 mode).status.underflow = true →
        (Directed.rootn z 5 mode).status.inexact = true) ∧
      ((Directed.rootn w 5 mode).status.underflow = true →
        (Directed.rootn w 5 mode).status.inexact = true) ∧
      ((Directed.pown z exponent mode).status.underflow = true →
        (Directed.pown z exponent mode).status.inexact = true) :=
  ⟨fun h => ((Transcendentals.Directed.expm1_underflow_iff hz hpos.ne' mode).mp h).1,
    fun h => ((Transcendentals.Directed.log_underflow_iff hz hpos hone mode).mp h).1,
    fun h => ((Transcendentals.Directed.logp1_underflow_iff hz (by linarith) hpos.ne' mode).mp h).1,
    fun h => ((Directed.rSqrt_underflow_iff hz hpos mode).mp h).1,
    fun h => ((Directed.hypot_underflow_iff hz hw (.inl hpos.ne') mode).mp h).1,
    fun h => ((Directed.rootn_underflow_iff_of_pos hz hpos (by decide) mode).mp h).1,
    fun h => ((Directed.rootn_underflow_iff_of_neg hw hnegative (by decide) mode).mp h).1,
    fun h => ((Directed.pown_underflow_iff hz hpos.ne' exponent mode).mp h).1⟩

/-- E5M2 is an IEEE format, so every contract holds on it. -/
example (mode : IEEERoundingMode) {z : Model FloatFormat.e5m2} (hq : toRat? z = some q) :
    RoundsTo FloatFormat.e5m2 mode (Real.exp q) false (Transcendentals.Directed.exp z mode).value :=
  Transcendentals.Directed.exp_roundsTo hq

example (mode : IEEERoundingMode) {z : Model FloatFormat.e5m2} (hq : toRat? z = some q)
    (hpos : 0 < q) :
    RoundsTo FloatFormat.e5m2 mode ((q : ℝ) ^ ((3 : ℝ)⁻¹)) false (Directed.cbrt z mode).value :=
  Directed.cbrt_roundsTo_of_pos hq hpos

/--
E4M3 has no infinity and E2M1 has neither an infinity nor a NaN, so they are not IEEE formats.
Every contract holds on them in every rounding direction: the result is the correctly rounded
value of the format, or the overflow result of the format, its NaN or its largest finite value.
-/
example (mode : IEEERoundingMode) {z : Model FloatFormat.e4m3} (hq : toRat? z = some q) :
    RoundsTo FloatFormat.e4m3 mode (Real.exp q) false
      (Transcendentals.Directed.exp z mode).value :=
  Transcendentals.Directed.exp_roundsTo hq

/-- To nearest-even on E4M3: a result in range is the nearest value of the format. -/
example {z : Model FloatFormat.e4m3} (hq : toRat? z = some q)
    (hrange : |roundAt FloatFormat.e4m3 (Real.exp q)| ≤ toReal (posMaxFinite FloatFormat.e4m3)) :
    isFinite (Transcendentals.Directed.exp z).value = true ∧
      toReal (Transcendentals.Directed.exp z).value = roundAt FloatFormat.e4m3 (Real.exp q) :=
  (Transcendentals.Directed.exp_roundsTo (mode := .nearest) hq).finite hrange

example (mode : IEEERoundingMode) {z : Model FloatFormat.e4m3} (hq : toRat? z = some q)
    (hpos : 0 < q) (hone : q ≠ 1) :
    RoundsTo FloatFormat.e4m3 mode (Real.sqrt q)⁻¹ false (Directed.rSqrt z mode).value ∧
      RoundsTo FloatFormat.e4m3 mode ((q : ℝ) ^ ((3 : ℝ)⁻¹)) false (Directed.cbrt z mode).value ∧
      RoundsTo FloatFormat.e4m3 mode (Real.log q)
        (decide (Real.log q < 0)) (Transcendentals.Directed.log z mode).value :=
  ⟨Directed.rSqrt_roundsTo hq hpos, Directed.cbrt_roundsTo_of_pos hq hpos,
    Transcendentals.Directed.log_roundsTo hq hpos hone⟩

open Transcendentals.CorrectlyRounded in
example (mode : IEEERoundingMode) {w z : Model FloatFormat.e4m3} (hw : toRat? w = some p)
    (hz : toRat? z = some q) (hp : 0 < p) (hne : Real.sin q ≠ 0) :
    RoundsTo FloatFormat.e4m3 mode ((p : ℝ) ^ (q : ℝ)) false (pow w z mode).value ∧
      RoundsTo FloatFormat.e4m3 mode (Real.sin q) (decide (Real.sin q < 0))
        (Function.sin.apply z mode).value :=
  ⟨pow_roundsTo_of_pos hw hz hp,
    Function.apply_roundsTo .sin hz trivial hne⟩

example (mode : IEEERoundingMode) {z : Model FloatFormat.e2m1} (hq : toRat? z = some q)
    (hne : q ≠ 0) :
    RoundsTo FloatFormat.e2m1 mode ((q : ℝ) ^ (3 : ℤ)) (decide ((q : ℝ) ^ (3 : ℤ) < 0))
      (Directed.pown z 3 mode).value :=
  Directed.pown_roundsTo hq hne 3

/--
The ONNX formats E4M3FNUZ and E5M2FNUZ have one zero and one NaN, the encoding `0x80`. The
contracts hold on them too: in range the result is finite and denotes the correctly rounded
value, and beyond the largest finite value it is the overflow result of the direction, the NaN
or the largest finite value. The sign bit is not part of the contract there: a negative value
that rounds to zero gives the one zero.
-/
example (mode : IEEERoundingMode) {z : Model FloatFormat.e4m3fnuz} (hq : toRat? z = some q)
    (hpos : 0 < q)
    (hrange : |roundAt FloatFormat.e4m3fnuz (Real.exp q) mode| ≤
      toReal (posMaxFinite FloatFormat.e4m3fnuz)) :
    (isFinite (Transcendentals.Directed.exp z mode).value = true ∧
        toReal (Transcendentals.Directed.exp z mode).value =
          roundAt FloatFormat.e4m3fnuz (Real.exp q) mode) ∧
      RoundsTo FloatFormat.e4m3fnuz mode (Real.sqrt q)⁻¹ false (Directed.rSqrt z mode).value ∧
      RoundsTo FloatFormat.e4m3fnuz mode ((q : ℝ) ^ ((3 : ℝ)⁻¹)) false
        (Directed.cbrt z mode).value :=
  ⟨(Transcendentals.Directed.exp_roundsTo hq).finite hrange, Directed.rSqrt_roundsTo hq hpos,
    Directed.cbrt_roundsTo_of_pos hq hpos⟩

open Transcendentals.CorrectlyRounded in
example (mode : IEEERoundingMode) {w z : Model FloatFormat.e5m2fnuz} (hw : toRat? w = some p)
    (hz : toRat? z = some q) (hp : 0 < p) (hne : Real.tanh q ≠ 0) :
    RoundsTo FloatFormat.e5m2fnuz mode ((p : ℝ) ^ (q : ℝ)) false (pow w z mode).value ∧
      RoundsTo FloatFormat.e5m2fnuz mode (Real.tanh q) (decide (Real.tanh q < 0))
        (Function.tanh.apply z mode).value :=
  ⟨pow_roundsTo_of_pos hw hz hp, Function.apply_roundsTo .tanh hz trivial hne⟩

end Contracts

end FloatLibTests.Conformance.BinaryInterchange.DirectedFunctions
