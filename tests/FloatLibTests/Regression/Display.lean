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
Status records list exactly their raised flags, and conversion outcomes and failure reasons print
their constructors with a leading dot.
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
    , shown (Model.add tenth fifth (status := true)) ==
        "{ value := 0.30000000000000004, status := { inexact := true }, ternary := Ordering.gt }"
    , (shown (Model.format tenth (status := true))).drop 2 ==
        "text := \"0.1\", status := { inexact := true } }" ]

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
    , datum 1.50 == "1.50"
    , datum (-1.2e4) == "-1.2e4"
    , datum 5e-9 == "5e-9"
    , datum (-0.00) == "-0.00"
    , datum (.infinity true) == "-inf"
    , datum (.nan false true 7) == "nan"
    , shown (some (Formats.DecimalInterchange.Datum.finite true 5 0)) == "some (-5)" ]

/-- Whether `text` contains `part`. -/
def mentions (text part : String) : Bool := (text.splitOn part).length > 1

/-- The text names exactly the raised flags, and is `{}` exactly when none is raised. -/
def listsRaised {α : Type} [Repr α] (flags : α) (fields : List (String × Bool)) : Bool :=
  let text := shown flags
  !mentions text ":= false" && (text == "{}") == fields.all (!·.2) &&
    fields.all fun (name, raised) => mentions text (name ++ " := true") == raised

/-- All 32 IEEE flag records and all 128 conversion flag records list their raised flags. -/
def flagRecords : Nat :=
  let ieee := (List.range 32).map fun bits =>
    let status : IEEEStatus :=
      { invalid := bits.testBit 0, divideByZero := bits.testBit 1, overflow := bits.testBit 2,
        underflow := bits.testBit 3, inexact := bits.testBit 4 }
    listsRaised status
      [("invalid", status.invalid), ("divideByZero", status.divideByZero),
        ("overflow", status.overflow), ("underflow", status.underflow),
        ("inexact", status.inexact)]
  let conversion := (List.range 128).map fun bits =>
    let status : ExecFloat.ConversionStatus :=
      { inexact := bits.testBit 0, overflow := bits.testBit 1, underflow := bits.testBit 2,
        saturated := bits.testBit 3, wrapped := bits.testBit 4, mappedSpecial := bits.testBit 5,
        invalid := bits.testBit 6 }
    listsRaised status
      [("inexact", status.inexact), ("overflow", status.overflow),
        ("underflow", status.underflow), ("saturated", status.saturated),
        ("wrapped", status.wrapped), ("mappedSpecial", status.mappedSpecial),
        ("invalid", status.invalid)]
  countFailures (ieee ++ conversion)

/-- Sixteen-bit integers as a fixed-point grid with no fraction digits. -/
abbrev Int16Grid := ExecFloat.BoundedFixedPoint binaryRadix 0 16

/-- Outcomes, statuses and failure reasons print compactly, and a printed status is its value. -/
def outcomeDisplays : Nat :=
  let rounded := (16777216 : Binary32).add 1 (status := true)
  countFailures
    [ shown ({} : IEEEStatus) == "{}"
    , shown rounded ==
        "{ value := 16777216, status := { inexact := true }, ternary := Ordering.lt }"
    , rounded.status == { inexact := true }
    , shown ({ value := false, status := { invalid := true } } : IEEEComparison.Result) ==
        "{ value := false, status := { invalid := true } }"
    , shown ({ value := .finite false 150 (-2), status := { inexact := true } } :
        Formats.DecimalInterchange.Outcome) == "{ value := 1.50, status := { inexact := true } }"
    , shown ((1.5 : Binary32).cast (target := Binary64)) == ".success 1.5"
    , shown ((70000 : Binary32).cast (target := Binary16)) ==
        ".success inf { inexact := true, overflow := true }"
    , ((70000 : Binary32).cast (target := Binary16)).status? ==
        some { inexact := true, overflow := true }
    , shown (some ((-(0 : Binary32)).cast (target := Binary64))) == "some (.success (-0))"
    , shown (ExecFloat.cast (target := Int16Grid) (40000 : Binary64)) == ".failure .outOfRange"
    , shown ((40000 : Binary64).cast (target := Int16Grid)
        (context := ExecFloat.BoundedFixedPoint.OverflowPolicy.wrap)) ==
        ".success (-25536) { inexact := true, overflow := true, wrapped := true }"
    , shown (ExecFloat.ConversionOutcome.failure (α := Posit32) (.infinity .source false)) ==
        ".failure (.infinity .source (negative := false))"
    , shown (ExecFloat.ConversionOutcome.failure (α := Posit32)
        (.exceptional (.operand 2) (.nan (payload := some 0)))) ==
        ".failure (.exceptional (.operand 2) (.nan (payload := some 0)))"
    , shown [ExecFloat.ConversionOutcome.failure (α := Binary32) .divisionByZero,
        .failure .unsupportedPolicy] == "[.failure .divisionByZero, .failure .unsupportedPolicy]"
    , shown ExecFloat.InputPosition.left == ".left"
    , shown ExecFloat.InputPosition.right == ".right"
    , shown ExecFloat.InputPosition.addend == ".addend"
    , shown (ExecFloat.ConversionFailure.infinity .right true) ==
        ".infinity .right (negative := true)"
    , shown (ExecFloat.ConversionFailure.exceptional .addend .undefined) ==
        ".exceptional .addend .undefined"
    , shown ExceptionalValue.nan == ".nan"
    , shown (ExceptionalValue.nan (negative := true) (signaling := true)) ==
        ".nan (negative := true) (signaling := true)"
    , shown (some ExceptionalValue.notAReal) == "some .notAReal"
    , shown (some (ExceptionalValue.reserved (some 3))) == "some (.reserved (payload := some 3))"
    , shown ExceptionalValue.reserved == ".reserved"
    , shown ExceptionalValue.undefined == ".undefined" ]

/-- Failure counts for the value displays of each family. -/
def report : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "value displays"
    #[ ("binary values and models", binaryDisplays)
     , ("fixed point", fixedPointDisplays)
     , ("codebook and logarithmic", tableDisplays)
     , ("decimal datums", decimalDisplays)
     , ("flag records", flagRecords)
     , ("outcomes and failures", outcomeDisplays) ]⟩

end FloatLibTests.Regression.Display
