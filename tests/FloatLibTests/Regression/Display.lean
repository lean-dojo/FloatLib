/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib
public import FloatLibTests.Accounting

/-!
# Value displays of every family

`toString` and `#eval` show values, never stored codes. Configured binary values and descriptor
models print a round-trip decimal, decimal fixed point keeps its scale, codebook values print
their table entry, logarithmic values print their exact value or a power, decimal datums keep their
quantum, and intervals, complex values and status outcomes show their components the same way.
-/

@[expose] public section

-- Keep regression computations in their requested suite rather than module initialization.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.Display

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLibTests.Accounting

/-- The pretty-printed `repr` of a value, as `#eval` shows it. -/
def shown {α : Type} [Repr α] (value : α) : String := Std.Format.pretty (repr value)

/-- Configured binary values, descriptor models, and the structures that contain them. -/
def binaryDisplays : Nat :=
  let tenth : Model FloatFormat.binary64 := Model.ofNatBits 0x3fb999999999999a
  let fifth : Model FloatFormat.binary64 := Model.ofNatBits 0x3fc999999999999a
  countFailures
    [ toString (0.1 : Binary64) == "0.1"
    , toString ((0.1 : Binary64) + 0.2) == "0.30000000000000004"
    , toString (0.1 : Binary32) == "0.1"
    , toString (65504 : Binary16) == "65504"
    , shown (some (-1.5 : Binary32)) == "some (-1.5)"
    , shown (-1.5 : Binary32) == "-1.5"
    , ExecFloat.Binary.format (12.5 : Binary32) (style := .fixed 3) == "12.500"
    , (ExecFloat.Binary.format (0.1 : Binary32) (status := true)).status.inexact
    , shown tenth == "0.1"
    , shown (some (Model.neg tenth)) == "some (-0.1)"
    , (shown (Model.Interval.mk tenth fifth)).drop 2 == "lo := 0.1, hi := 0.2 }"
    , (shown (ExecComplex.mk tenth (Model.neg fifth))).drop 2 == "re := 0.1, im := -0.2 }"
    , ((shown (Model.add tenth fifth (status := true))).drop 2).startsWith
        "value := 0.30000000000000004," ]

/-- Exact and bounded decimal fixed point keep their scale, and other radices print exact values. -/
def fixedPointDisplays : Nat :=
  let ternary : Radix := ⟨3, by decide⟩
  countFailures
    [ toString (3.5 : ExecFloat.FixedPoint decimalRadix 3) == "3.500"
    , toString (-0.125 : ExecFloat.FixedPoint decimalRadix 3) == "-0.125"
    , toString (12 : ExecFloat.FixedPoint decimalRadix 2) == "12.00"
    , toString (0.375 : ExecFloat.FixedPoint binaryRadix 3) == "0.375"
    , toString (ExecFloat.ofRaw ⟨1⟩ : ExecFloat.FixedPoint ternary 1) == "1/3"
    , toString (ExecFloat.ofRaw (Formats.FixedPoint.Bounded.ofInt 8 125) :
        ExecFloat.BoundedFixedPoint decimalRadix 2 8) == "1.25"
    , toString (ExecFloat.ofRaw (Formats.FixedPoint.Bounded.ofInt 8 (-3)) :
        ExecFloat.BoundedFixedPoint binaryRadix 2 8) == "-0.75"
    , shown (some (-0.125 : ExecFloat.FixedPoint decimalRadix 3)) == "some (-0.125)" ]

/-- A dyadic codebook with every kind of entry. -/
def book : Formats.Codebook 3 FloatLib.Numerics.Dyadic where
  denote code :=
    match code.toNat with
    | 0 => .finite ⟨false, 0, 0⟩
    | 1 => .finite ⟨false, 3, -1⟩
    | 2 => .finite ⟨true, 5, 2⟩
    | 3 => .infinity true
    | 4 => .exceptional (.nan)
    | 5 => .exceptional .notAReal
    | _ => .finite ⟨true, 0, 0⟩

/-- Codebook values print their table entries, logarithmic values their exact value or a power. -/
def tableDisplays : Nat :=
  let entry := fun (bits : Nat) =>
    toString (ExecFloat.ofRaw (Formats.Codebook.ofNatBits book bits) : ExecFloat.Codebook book)
  let ternary : Radix := ⟨3, by decide⟩
  countFailures
    [ entry 0 == "0", entry 1 == "1.5", entry 2 == "-20", entry 3 == "-inf", entry 4 == "nan"
    , entry 5 == "NaR", entry 7 == "-0"
    , toString (ExecFloat.ofRaw (.value false 3) : ExecFloat.Logarithmic binaryRadix) == "8"
    , toString (ExecFloat.ofRaw (.value true (-1)) : ExecFloat.Logarithmic binaryRadix) == "-0.5"
    , toString (ExecFloat.ofRaw .zero : ExecFloat.Logarithmic binaryRadix) == "0"
    , toString (ExecFloat.ofRaw (.value false 30) : ExecFloat.Logarithmic binaryRadix) ==
        "1073741824"
    , toString (ExecFloat.ofRaw (.value false 33) : ExecFloat.Logarithmic binaryRadix) == "2^33"
    , toString (ExecFloat.ofRaw (.value false (-1)) : ExecFloat.Logarithmic ternary) == "3^-1"
    , toString (ExecFloat.ofRaw (.value true 2) : ExecFloat.Logarithmic ternary) == "-9" ]

/-- Decimal datums keep their quantum. -/
def decimalDisplays : Nat :=
  let datum := fun (value : Formats.DecimalInterchange.Datum) => toString value
  countFailures
    [ datum (.finite false 150 (-2)) == "1.50"
    , datum (.finite false 120 0) == "120"
    , datum (.finite true 12 3) == "-1.2e4"
    , datum (.finite false 5 (-9)) == "5e-9"
    , datum (.finite false 12 (-7)) == "0.0000012"
    , datum (.finite true 0 (-2)) == "-0.00"
    , datum (.infinity true) == "-inf"
    , datum (.nan false true 7) == "nan"
    , shown (some (Formats.DecimalInterchange.Datum.finite true 5 0)) == "some (-5)" ]

/-- Failure counts for the value displays of each family. -/
def report : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "value displays"
    #[ ("binary values and models", binaryDisplays)
     , ("fixed point", fixedPointDisplays)
     , ("codebook and logarithmic", tableDisplays)
     , ("decimal datums", decimalDisplays) ]⟩

end FloatLibTests.Regression.Display
