/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.DecimalInterchange
public import FloatLib.Floats.Formats.IEEE754.Environment
public meta import FloatLib.Tactic.IEEENames
public meta import Lean.Elab.Command

/-!
# The operation names of IEEE 754-2019

The commands `ieee_by_direction`, `ieee_by_predicate` and `ieee_extrema` declare the members of
an operation family under the names of the standard. The first check computes the names that
the three commands owe, from the direction table, the comparison predicates and the eight
extrema, and fails when one is not declared. Their docstrings are checked with those of the
whole public interface by `tests/checks/public-api-docs.sh`. The examples then check that a
member is its family at the argument its name says, and that a command whose body does not
elaborate is rejected.

The last part checks the conformance predicates of §5.7.1 and the dynamic modes of §9.3.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.IEEENames

open FloatLib.Floats
open FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

open Lean Elab Command in
/-- The names among `names` that are not declared. -/
meta def undeclared (names : List Name) : CommandElabM (List Name) := do
  let env ← getEnv
  return names.filter fun name => !env.contains name

open Lean Elab Command FloatLib.Numerics.IEEENames in
run_cmd do
  let model := `FloatLib.Floats.Formats.BinaryInterchange.Model
  let binary := `FloatLib.Floats.ExecFloat.Binary
  let dtype := `FloatLib.Floats.Formats.BinaryInterchange.ExecDType
  let decimal := `FloatLib.Floats.Formats.DecimalInterchange
  let directions := directionSuffixes.map fun (_, suffix, _) => suffix
  let predicates := (← getConstInfoInduct
      ``FloatLib.Numerics.IEEEComparison.Predicate).ctors.filterMap
    fun constructor => match constructor with
      | .str _ short => some short.capitalize
      | _ => none
  let signaling := predicates.filter fun predicate => predicate != "Unordered" &&
      predicate != "Ordered"
  let byDirection (namespaces : List Name) (family : String) : List Name :=
    namespaces.flatMap fun ns => directions.map fun suffix => ns ++ Name.mkSimple (family ++ suffix)
  let byPredicate (ns : Name) : List Name :=
    predicates.map (fun predicate => ns ++ Name.mkSimple ("compareQuiet" ++ predicate)) ++
      signaling.map (fun predicate => ns ++ Name.mkSimple ("compareSignaling" ++ predicate))
  let extrema : List Name :=
    ["minimum", "maximum"].flatMap fun base => ["", "Magnitude"].flatMap fun magnitude =>
      ["", "Number"].map fun number =>
        decimal ++ `Arithmetic ++ Name.mkSimple (base ++ magnitude ++ number)
  let owed :=
    byDirection [model, binary] "roundToIntegral" ++
      byDirection [dtype, binary] "convertToInteger" ++
      byDirection [dtype] "convertToIntegerExact" ++
      byPredicate model ++ byPredicate binary ++ byPredicate (decimal ++ `Datum) ++ extrema
  unless owed.length = 5 * 5 + 3 * 22 + 8 do
    throwError "the list of owed names has {owed.length} entries"
  let missing ← undeclared owed
  unless missing.isEmpty do
    throwError "operations of IEEE 754-2019 that are not declared: {missing}"

/-! ## A member is its family at one argument -/

example (x y : Model FloatFormat.binary32) :
    Model.compareQuietLessEqual x y = Model.compareQuiet .lessEqual x y ∧
      Model.compareSignalingNotGreater x y = Model.compareSignaling .notGreater x y :=
  ⟨rfl, rfl⟩

example (value : Model FloatFormat.binary32) :
    Model.roundToIntegralTiesToEven value = Model.roundToIntegral value (mode := .nearest) ∧
      Model.roundToIntegralTiesToAway value = Model.roundToIntegral value (mode := .nearestAway) ∧
      Model.roundToIntegralTowardZero value = Model.roundToIntegral value (mode := .towardZero) ∧
      Model.roundToIntegralTowardPositive value = Model.roundToIntegral value (mode := .up) ∧
      Model.roundToIntegralTowardNegative value = Model.roundToIntegral value (mode := .down) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example (value : Model FloatFormat.binary32) (mode : Model.IEEERoundingMode) :
    Model.roundToIntegralExact value mode = Model.roundToIntegral value mode (status := true) :=
  rfl

example (x y : Binary64) :
    ExecFloat.Binary.compareQuietGreater x y = ExecFloat.Binary.compareQuiet .greater x y ∧
      ExecFloat.Binary.roundToIntegralTowardZero x =
        ExecFloat.Binary.roundToIntegral x (mode := .towardZero) ∧
      ExecFloat.Binary.convertToIntegerTiesToAway x = x.toInt? (mode := .nearestAway) ∧
      ExecFloat.Binary.copy x = x ∧ ExecFloat.Binary.radix x = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example (x : Model FloatFormat.binary64) :
    (ExecDType.convertToIntegerTowardNegative x :
        FloatLib.Floats.ExecFloat.ConversionOutcome
            (FloatLib.Numerics.Representations.FixedInt 32)) =
      ExecDType.convertToInteger x .down ∧
    (ExecDType.convertToIntegerExactTiesToEven x :
        FloatLib.Floats.ExecFloat.ConversionOutcome
            (FloatLib.Numerics.Representations.FixedInt 32)) =
      ExecDType.convertToIntegerExact x .nearest ∧
    Model.copy x = x ∧ Model.radix x = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

example (f : DecimalInterchange.Format) (x y : DecimalInterchange.Datum) :
    DecimalInterchange.Datum.compareQuietNotEqual x y =
        DecimalInterchange.Datum.compareQuiet .notEqual x y ∧
      DecimalInterchange.Arithmetic.minimumMagnitudeNumber f x y =
        DecimalInterchange.Arithmetic.extremum f false true true x y ∧
      DecimalInterchange.Arithmetic.maximum f x y =
        DecimalInterchange.Arithmetic.extremum f true false false x y :=
  ⟨rfl, rfl, rfl⟩

/-! ## What the commands reject -/

/-- error: Unknown identifier `noSuchOperation` -/
#guard_msgs (error, substring := true) in
ieee_by_direction "IEEE 754-2019 §5.3.1" roundToIntegral (value : Nat) : Nat :=
  fun mode => noSuchOperation value mode

/-! ## Conformance predicates and dynamic modes -/

example : IEEE754.is754version1985 = false ∧ IEEE754.is754version2008 = false ∧
    IEEE754.is754version2019 = false :=
  ⟨rfl, rfl, rfl⟩

example :
    ((IEEE754.Modes.defaultModes.setBinaryRoundingDirection .up).setDecimalRoundingDirection
        .down).getBinaryRoundingDirection = .up ∧
      (IEEE754.Modes.defaultModes.setBinaryRoundingDirection .up).getDecimalRoundingDirection =
        .nearest ∧
      ((IEEE754.Modes.defaultModes.setDecimalRoundingDirection .down).restoreModes
        IEEE754.Modes.defaultModes.saveModes) = IEEE754.Modes.defaultModes :=
  ⟨rfl, rfl, rfl⟩

end FloatLibTests.Conformance.Formats.IEEENames
