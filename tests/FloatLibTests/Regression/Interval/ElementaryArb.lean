/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Backends
public import FloatLib.Numerics.Enclosure.Expression.Extensions
public import FloatLibTests.Regression.Interval.ArbTranscendentals

/-!
# Independent checks for certified elementary enclosures

Compare binary-grid endpoint bounds against higher-precision Arb balls at representative positive,
negative, and near-boundary inputs. Arb is external test evidence; production containment proofs
are checked by Lean and do not depend on this oracle. Approximation degree grows with precision.
Containment is already proved, so the width check is what detects a loss of accuracy.
-/

@[expose] public section

namespace FloatLibTests.Regression.Interval.ElementaryArb

open Lean FloatLib.Numerics FloatLib.Numerics.Interval

/-- Encode an exact rational as an oracle expression leaf. -/
def constant (x : ℚ) : Json :=
  Json.mkObj [("const", Json.str x.toArbString)]

/-- Encode a whitelisted oracle operation with rational operands. -/
def application (name : String) (args : List ℚ) : Json :=
  Json.mkObj [("op", Json.str name), ("args", Json.arr (args.map constant).toArray)]

/-- Bits of accuracy an enclosure may lose relative to its endpoint precision. The current
enclosures lose at most one bit on these inputs. -/
def widthSlack : Nat := 4

/-- Check that the Lean enclosure contains the independent higher-precision Arb ball and that its
width is at most `2 ^ (widthSlack - precision)` relative to the larger of one and the result. -/
def checkEnclosure (precision : Nat) (enclosure : Option (Interval Int))
    (reference : Json) : IO Bool := do
  let some I := enclosure | return false
  let result ← Arb.runExpr [] reference (precBits := precision + 128) (digits := precision + 128)
  let bounds ← match result.outputBall.toRatBoundsChecked with
    | .ok bounds => pure bounds
    | .error message => throw (IO.userError message)
  let lo := BinaryGrid.toRat precision I.lo
  let hi := BinaryGrid.toRat precision I.hi
  let scale := max 1 (max |bounds.1| |bounds.2|)
  return decide (lo ≤ bounds.1 ∧ bounds.2 ≤ hi ∧
    hi - lo ≤ scale * 2 ^ widthSlack / 2 ^ precision)

/-- Exercise all seventeen supported elementary functions at three endpoint precisions. -/
def run : IO Nat := do
  let mut failures := 0
  let unaryCases : List (String × Extension × List ℚ) :=
    [("exp", Backend.elementaryExtension .exp, [-2, 1 / 2, 2]),
     ("log", Backend.elementaryExtension .log, [3 / 4, 3 / 2, 10]),
     ("sin", Backend.elementaryExtension .sin, [-1 / 2, 1 / 2, 10]),
     ("cos", Backend.elementaryExtension .cos, [-1 / 2, 1 / 2, 10]),
     ("tan", Backend.elementaryExtension .tan, [-1 / 2, 1 / 4, 1]),
     ("asin", Backend.elementaryExtension .asin, [-3 / 4, 1 / 4, 3 / 4]),
     ("acos", Backend.elementaryExtension .acos, [-3 / 4, 1 / 4, 3 / 4]),
     ("atan", Backend.elementaryExtension .atan, [-2, 1 / 2, 2]),
     ("sinh", Backend.elementaryExtension .sinh, [-2, 1 / 2, 2]),
     ("cosh", Backend.elementaryExtension .cosh, [-2, 1 / 2, 2]),
     ("tanh", Backend.elementaryExtension .tanh, [-2, 1 / 2, 2]),
     ("sqrt", Backend.elementaryExtension .sqrt, [1 / 8, 2, 10]),
     ("asinh", Backend.asinhExtension, [-2, 1 / 2, 2]),
     ("acosh", Backend.acoshExtension, [3 / 2, 2, 10]),
     ("atanh", Backend.atanhExtension, [-3 / 4, 1 / 4, 3 / 4])]
  let binaryCases : List (String × Extension × List (ℚ × ℚ)) :=
    [("rpow", Backend.rpowExtension, [(1 / 4, -3 / 2), (3 / 2, 3 / 2), (2, -1 / 2)]),
     ("logb", Backend.logbExtension, [(2, 3 / 2), (10, 3 / 2), (1 / 2, 3 / 2)])]
  for precision in [32, 128, 256] do
    let config : Backend.Config := { precision, degree := precision + 24 }
    let base := Backend.binaryGrid config
    for (name, enclosure, inputs) in unaryCases do
      let B := base.withExtensions config [enclosure]
      for x in inputs do
        failures := failures + (← ArbTranscendentals.runCheck
          s!"elementary.{name}.{precision}.{x}" do
            let some I := B.const? x | return false
            checkEnclosure precision (B.call? 0 [I]) (application name [x]))
    for (name, enclosure, inputs) in binaryCases do
      let B := base.withExtensions config [enclosure]
      for (x, y) in inputs do
        failures := failures + (← ArbTranscendentals.runCheck
          s!"elementary.{name}.{precision}.{x}.{y}" do
            let some I := B.const? x | return false
            let some J := B.const? y | return false
            checkEnclosure precision (B.call? 0 [I, J]) (application name [x, y]))
  return failures

end FloatLibTests.Regression.Interval.ElementaryArb
