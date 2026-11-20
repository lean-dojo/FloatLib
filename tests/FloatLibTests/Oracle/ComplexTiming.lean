/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Exponential
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Inverse
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Power
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Tangent
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Runtime
import FloatLib.Numerics.Enclosure.Expression.Backends

/-!
# Timing of the enclosures behind the complex functions

`oracle complex-timing` prints the time of the rational and binary-grid enclosures that the
complex elementary functions can draw on, at the precisions binary64 needs.
`oracle complex-timing functions` prints the time of a call of each function in binary64 at
arguments of six kinds: subnormal, near `2 ^ -600`, near `2 ^ -30`, moderate, and with one
subnormal and one moderate part. `oracle complex-timing pow` prints the time of a call of `pow`
in binary64 for a moderate base, a base next to the negative real axis, powers far outside the
range and an even power of a base on a diagonal.
-/

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace FloatLibTests.Oracle.ComplexTiming

def timeIt (label : String) (count : Nat) (work : Nat → Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let mut acc := 0
  for i in [0:count] do
    acc := acc + work i
  let stop ← IO.monoNanosNow
  IO.println s!"{label}: {(stop - start) / count / 1000} us per call (checksum {acc % 1000})"

def sample (i : Nat) : Rat := (1 + (i : Rat) / 97) * ((3 : Rat) / 7) + 1 / (2 ^ 40)

def bits (I : RationalInterval) : Nat := (I.hi - I.lo).den.log2 % 7

/-- Run the timing table. -/
public def run : IO Unit := do
  for degree in [16, 32, 64, 128] do
    timeIt s!"atan2Interval degree {degree}" 50 fun i =>
      bits (TrigonometricComparison.atan2Interval (sample i) (sample (i + 3)) degree)
    timeIt s!"Enclosure.log degree {degree}" 50 fun i =>
      bits (Enclosure.log (sample i * sample i + 1) degree)
    timeIt s!"cosReduced degree {degree}" 50 fun i => bits (Enclosure.cosReduced (sample i) degree)
    timeIt s!"Enclosure.exp degree {degree}" 50 fun i => bits (Enclosure.exp (sample i) degree)
  for precision in [70, 140] do
    timeIt s!"logEnclosure precision {precision}" 200 fun i =>
      let split := Model.Transcendentals.Certified.splitTwoPow (sample i * sample i + 1)
      bits (Model.Transcendentals.CorrectlyRounded.logEnclosure split.1 split.2 precision)
    timeIt s!"expReducedEnclosure precision {precision}" 200 fun i =>
      bits (Model.Transcendentals.CorrectlyRounded.expReducedEnclosure (sample i * 50) 30 8 20
        precision)
    timeIt s!"BinaryGrid.exp precision {precision}" 200 fun i =>
      bits (Enclosure.BinaryGrid.exp (sample i) 20 precision)
  for (precision, degree) in [(70, 12), (70, 20), (70, 32), (140, 40)] do
    let backend := Interval.Backend.binaryGrid { precision := precision, degree := degree }
    let run (op : Interval.UnaryOp) (i : Nat) : Nat :=
      match (Interval.Expr.unary op (.const (sample i))).eval? backend (fun _ => none) with
      | some I => (I.hi - I.lo).toNat % 1000
      | none => 999
    timeIt s!"grid cos p{precision} d{degree}" 100 (run .cos)
    timeIt s!"grid sin p{precision} d{degree}" 100 (run .sin)
    timeIt s!"grid atan p{precision} d{degree}" 100 (run .atan)
    timeIt s!"grid exp p{precision} d{degree}" 100 (run .exp)
    timeIt s!"grid log p{precision} d{degree}" 100 (run .log)
    timeIt s!"grid sinh p{precision} d{degree}" 100 (run .sinh)
    timeIt s!"grid asin p{precision} d{degree}" 100 fun i =>
      match (Interval.Expr.unary .asin (.const (sample i / 3))).eval? backend (fun _ => none) with
      | some I => (I.hi - I.lo).toNat % 1000
      | none => 999
  let fmt := FloatFormat.ieee 8 23 (by decide) (by decide)
  let points : List (String × Rat × Rat) := [("moderate", 7 / 10, 3 / 10),
    ("large", 10000000000, 30000000), ("tiny", 1 / 10 ^ 20, 1 / 10 ^ 25),
    ("near cut", 1 / 10 ^ 10, 2), ("near focus", 1 / 10 ^ 6, 1)]
  for (label, p, q) in points do
    let report (name : String) (enclose : Unit → Option RationalInterval)
        (exact : Rat → Ordering) : IO Unit := do
      match enclose () with
      | some I =>
          IO.println s!"{name} {label}: tight {ExecComplex.isTight fmt I}, width 2^{
            ((I.hi - I.lo).num.natAbs.log2 : Int) - (I.hi - I.lo).den.log2}"
          let middle := (I.lo + I.hi) / 2
          timeIt s!"{name} {label} exact comparison inside" 5 fun i =>
            if exact (middle + (i : Rat) * (I.hi - I.lo) / 16) == .lt then 1 else 0
      | none => IO.println s!"{name} {label}: no enclosure"
      timeIt s!"{name} {label} enclosure" 20 fun i =>
        match enclose () with | some I => bits I + i | none => 999
    report "arcosh"
      (fun _ => ExecComplex.refineTwice fmt fun precision =>
        some (ExecComplex.arcoshEnclosure p q (precision + bitsBelowOne
          ((|q + 1| + |q - 1| - 2) / 2 + p ^ 2 / (4 * (|p| + |q| + 1))))))
      (ConfocalComparison.compareArcosh p q (ExecComplex.cacheLevels fmt))
    report "arcsin"
      (fun _ => ExecComplex.exprEnclosure? fmt (ExecComplex.arcsinExpr p q)
        (max (bitsBelowOne (|q| / (|p| + |q| + 1)))
          (bitsBelowOne (ExecComplex.minorGap p q) / 2 + 1)))
      (ConfocalComparison.compareArcsin p q (ExecComplex.cacheLevels fmt))
    report "arccos"
      (fun _ => ExecComplex.exprEnclosure? fmt (ExecComplex.arccosExpr p q)
        (bitsBelowOne (ExecComplex.minorGap p q)))
      (ConfocalComparison.compareArccos p q (ExecComplex.cacheLevels fmt))
  for (label, b) in [("2^1000", (2 : Rat) ^ 1000 * (4 / 3)), ("2^120", (2 : Rat) ^ 120 * (4 / 3)),
      ("1", (4 : Rat) / 3), ("2^-30", (4 : Rat) / 3 / 2 ^ 30),
      ("2^-1070", (4 : Rat) / 3 / 2 ^ 1070)] do
    for precision in [80, 384] do
      match ProductComparison.trigBounds? .sin ⟨b, b⟩ precision with
      | some I => IO.println s!"trigBounds sin {label} precision {precision}: tight {
          ExecComplex.isTight (FloatFormat.ieee 11 52 (by decide) (by decide)) I}"
      | none => IO.println s!"trigBounds sin {label} precision {precision}: none"
      timeIt s!"trigBounds sin {label} precision {precision}" 20 fun i =>
        match ProductComparison.trigBounds? .sin ⟨b + i, b + i⟩ precision with
        | some I => bits I | none => 999
  let hugeA : Rat := 2 ^ 1023
  let tinyA : Rat := 1 / 2 ^ 1074
  for (label, a, b) in [("huge", hugeA, hugeA), ("tiny", tinyA, 2 * tinyA)] do
    for n in [0, 2, 4, 5, 6, 7] do
      timeIt s!"expLadder {label} level {n}" 2 fun i =>
        bits (TanhComparison.expLadder (-(2 * a) + i) n)
      timeIt s!"sin intervals {label} level {n}" 2 fun i =>
        bits (ProductComparison.Trig.sin.intervals (2 * b + i) n)
    if ha : a ≠ 0 then
      for (name, t) in [("1", (1 : Rat)), ("1 - 2^-53", 1 - 1 / 2 ^ 53), ("a", a),
          ("a - a/2^53", a - a / 2 ^ 53)] do
        timeIt s!"compareRe {label} boundary {name}" 2 fun i =>
          if TanhComparison.compareRe a b (8 + i) ha t == .lt then 1 else 0
      for (name, t) in [("0", (0 : Rat)), ("2^-1075", 1 / 2 ^ 1075), ("2b", 2 * b),
          ("2b - b/2^52", 2 * b - b / 2 ^ 52)] do
        timeIt s!"compareIm {label} boundary {name}" 2 fun i =>
          if TanhComparison.compareIm a b (8 + i) ha t == .lt then 1 else 0
    let fmt64 := FloatFormat.ieee 11 52 (by decide) (by decide)
    timeIt s!"tanhEnclosure re {label}" 2 fun i =>
      match ExecComplex.tanhEnclosure? fmt64 false (a + i) b with | some I => bits I | none => 999
    timeIt s!"tanhEnclosure im {label}" 2 fun i =>
      match ExecComplex.tanhEnclosure? fmt64 true (a + i) b with | some I => bits I | none => 999
  timeIt "compareExp near" 50 fun i =>
    if ElementaryComparison.compareExp (sample i) (3 / 2 + (i : Rat) / 1000) == .lt then 1 else 0
  timeIt "compareLog near" 50 fun i =>
    if ElementaryComparison.compareLog (sample i + 1) ((i : Rat) / 1000 + 1 / 3) (by
      unfold sample; positivity) == .lt then 1 else 0

/-- The time of each complex function at arguments of four sizes, in two rounding directions. -/
public def runFunctions : IO Unit := do
  let fmt := FloatFormat.ieee 11 52 (by decide) (by decide)
  let functions :
      List (String × (ExecComplex fmt → Model.IEEERoundingMode → ExecComplex fmt)) :=
    [("sin", fun z mode => ExecComplex.sin z mode),
      ("sinh", fun z mode => ExecComplex.sinh z mode),
      ("tan", fun z mode => ExecComplex.tan z mode),
      ("tanh", fun z mode => ExecComplex.tanh z mode),
      ("asin", fun z mode => ExecComplex.asin z mode),
      ("asinh", fun z mode => ExecComplex.asinh z mode),
      ("atan", fun z mode => ExecComplex.atan z mode),
      ("atanh", fun z mode => ExecComplex.atanh z mode),
      ("expm1", fun z mode => ExecComplex.expm1 z mode),
      ("log1p", fun z mode => ExecComplex.log1p z mode),
      ("exp", fun z mode => ExecComplex.exp z mode),
      ("cos", fun z mode => ExecComplex.cos z mode)]
  let arguments : List (String × Nat × Nat) :=
    [("subnormal", 0x000123456789abcd, 0x0000fedcba987654),
      ("2^-600", 0x1a7123456789abcd, 0x1a6fedcba9876543),
      ("2^-30", 0x3e1123456789abcd, 0x3e0fedcba9876543),
      ("moderate", 0x3fe6666666666666, 0x3fd3333333333333),
      ("subnormal + moderate i", 0x000123456789abcd, 0x3fd3333333333333),
      ("moderate + subnormal i", 0x3fe6666666666666, 0x0000fedcba987654)]
  for (name, function) in functions do
    for (label, re, im) in arguments do
      for mode in [Model.IEEERoundingMode.nearest, Model.IEEERoundingMode.towardZero] do
        timeIt s!"{name} {label} {mode}" 4 fun i =>
          let w := function ⟨Model.ofNatBits (re + 2 * i), Model.ofNatBits (im + 6 * i)⟩ mode
          (Model.toNatBits w.re + Model.toNatBits w.im) % 1000

/-- The time of `pow` in binary64 at bases and exponents of six kinds, in two rounding
directions. A call differs from the one before in the last bits of the real part of the base,
and for the base on the diagonal in the exponent, which stays an even integer. -/
public def runPow : IO Unit := do
  let fmt := FloatFormat.ieee 11 52 (by decide) (by decide)
  let arguments : List (String × (Nat × Nat) × (Nat × Nat) × (Nat × Nat)) :=
    [("moderate base, complex exponent", (0x3fe6666666666666, 0x3fd3333333333333),
        (0x3ff4cccccccccccd, 0x3fc999999999999a), (2, 0)),
      ("moderate base, exponent 5", (0x3fe6666666666666, 0x3fd3333333333333),
        (0x4014000000000000, 0), (2, 0)),
      ("base next to the negative real axis, exponent 5/2",
        (0xbff8000000000000, 0x0010000000000000), (0x4004000000000000, 0), (2, 0)),
      ("3 - 2 i, exponent 10^7 + 1/2", (0x4008000000000000, 0xc000000000000000),
        (0x416312d010000000, 0), (2, 0)),
      ("3 - 2 i, exponent -2^40 + i/2", (0x4008000000000000, 0xc000000000000000),
        (0xc270000000000000, 0x3fe0000000000000), (2, 0)),
      ("1 + i, exponent 2^40", (0x3ff0000000000000, 0x3ff0000000000000),
        (0x4270000000000000, 0), (0, 8192))]
  for (label, base, exponent, step) in arguments do
    for mode in [Model.IEEERoundingMode.nearest, Model.IEEERoundingMode.towardZero] do
      timeIt s!"pow {label} {mode}" 4 fun i =>
        let w := ExecComplex.powChecked (fmt := fmt)
          ⟨Model.ofNatBits (base.1 + step.1 * i), Model.ofNatBits base.2⟩
          ⟨Model.ofNatBits (exponent.1 + step.2 * i), Model.ofNatBits exponent.2⟩ mode
        (Model.toNatBits w.1.re + Model.toNatBits w.1.im + (if w.2 then 1 else 0)) % 1000

end FloatLibTests.Oracle.ComplexTiming
