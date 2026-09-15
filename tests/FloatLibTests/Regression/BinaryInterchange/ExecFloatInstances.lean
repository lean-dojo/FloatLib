/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Instances
public import FloatLibTests.Accounting

/-!
# Regression checks for generic executable-float instances

These are compile-time and executable API regressions, not a second implementation of binary
arithmetic. A deliberately nonstandard format exercises literals, algebraic instances,
comparisons, special values, printing, and policy-aware `ExecFloat` capabilities on the default
surface, plus elementary functions after the explicit `Configured.Transcendentals` import.

Additional wide-exponent cases guard against accidentally constructing integers whose size grows
with the exponent range. Keeping the checks together makes instance regressions visible without
scattering test-only modules through the format implementation.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.ExecFloatInstances

open FloatLib.Numerics
open FloatLibTests.Accounting

/-! ## Arbitrary-format interfaces -/

abbrev customFormat : FloatFormat :=
  FloatFormat.ieee 4 5

def sameCustom (left right : Model customFormat) : Bool :=
  left.toNatBits == right.toNatBits

def customChecks : Thunk (List (String × Bool)) := ⟨fun _ =>
  let zero : Model customFormat := 0
  let one : Model customFormat := 1
  let two : Model customFormat := 2
  let three : Model customFormat := 3
  let four : Model customFormat := 4
  let six : Model customFormat := 6
  let eight : Model customFormat := 8
  let half := Model.roundDyadic customFormat { negative := false, significand := 1, exponent := -1 }
  let negativeThree := Model.neg three
  let negativeZero := Model.negZero customFormat
  let positiveInfinity := Model.posInf customFormat
  let negativeInfinity := Model.negInf customFormat
  let quietNaN := Model.canonicalNaN customFormat
  let signalingNaN :=
    Model.ofFields customFormat false (FloatFormat.expAllOnesNat customFormat) 1
  let pointOne := Model.roundRat customFormat false 1 10
  let tolerance := Model.roundRat customFormat false 1 1000000
  let piValue : Model customFormat := MathFunctions.pi
  [ ("natCoe",
      sameCustom (((42 : Nat) : Model customFormat))
        (Model.roundDyadic customFormat { negative := false, significand := 42, exponent := 0 }))
  , ("zero", sameCustom zero (Model.posZero customFormat))
  , ("one", sameCustom one (Model.posOne customFormat))
  , ("neg", sameCustom (-three) (Model.neg three))
  , ("add", sameCustom (two + three) (Model.add two three))
  , ("sub", sameCustom (three - two) (Model.sub three two))
  , ("mul", sameCustom (two * three) six)
  , ("div", sameCustom (six / three) two)
  , ("powNat", sameCustom (two ^ three) eight)
  , ("powNegative", sameCustom ((-two) ^ three) (-eight))
  , ("powNonintegralNegative", Model.isNaN ((-two) ^ half))
  , ("powSignedZero", sameCustom (negativeZero ^ negativeThree) negativeInfinity)
  , ("powQuietNaN", sameCustom (one ^ quietNaN) one)
  , ("powSignalingNaN", Model.isNaN (one ^ signalingNaN))
  , ("beqSignedZero", zero == negativeZero)
  , ("beqNaN", !(quietNaN == quietNaN))
  , ("lt", decide (one < two))
  , ("le", decide (one ≤ one))
  , ("ltNaN", !decide (quietNaN < one))
  , ("leNaN", !decide (quietNaN ≤ one))
  , ("minimumSignedZero", sameCustom (min zero negativeZero) negativeZero)
  , ("maximumSignedZero", sameCustom (max zero negativeZero) zero)
  , ("sqrt", sameCustom (MathFunctions.sqrt four) two)
  , ("abs", sameCustom (MathFunctions.abs (-three)) three)
  , ("exp", sameCustom (MathFunctions.exp negativeInfinity) zero)
  , ("log", sameCustom (MathFunctions.log one) zero)
  , ("sin", sameCustom (MathFunctions.sin negativeZero) negativeZero)
  , ("cos", sameCustom (MathFunctions.cos zero) one)
  , ("piFinite", Model.isFinite piValue)
  , ("piAboveThree", Model.compare piValue three == some .gt)
  , ("pointOne", sameCustom pointOne (Model.roundRat customFormat false 1 10))
  , ("tolerance", sameCustom tolerance (Model.roundRat customFormat false 1 1000000))
  , ("formatZero", toString zero == "0")
  , ("formatNegativeZero", toString negativeZero == "-0")
  , ("formatInfinity", toString positiveInfinity == "inf")
  , ("formatNegativeInfinity", toString negativeInfinity == "-inf")
  , ("formatNaN", toString quietNaN == "nan")
  , ("formatIntegerOne", toString one == "1")
  , ("formatIntegerSix", toString six == "6")
    ]⟩

def failedCustomChecks : Thunk (List String) := ⟨fun _ =>
  (customChecks.get.filter fun check => !check.2).map (·.1)⟩

def failCustomInstances : Thunk Nat := ⟨fun _ =>
  countWhereFailures customChecks.get fun check => check.2⟩

/-! ## Wide-exponent classification -/

abbrev wideExponentFormat : FloatFormat :=
  FloatFormat.ieee 20 37

/-- Ensure integer metadata is obtained without materializing the encoded integer magnitude. -/
def failWideExponentClassification : Thunk Nat := ⟨fun _ =>
  let maximumFiniteExponent := FloatFormat.expAllOnesNat wideExponentFormat - 1
  let hugePositive :=
    Model.ofFields wideExponentFormat false maximumFiniteExponent 0
  let hugeNegative :=
    Model.ofFields wideExponentFormat true maximumFiniteExponent 0
  let tinyFraction := Model.posMinSubnormal wideExponentFormat
  let positiveCheck :=
    match Model.Power.classifyInteger? hugePositive with
    | some metadata =>
        !metadata.negative && !metadata.odd && metadata.smallMagnitude?.isNone
    | none => false
  let negativeCheck :=
    match Model.Power.classifyInteger? hugeNegative with
    | some metadata =>
        metadata.negative && !metadata.odd && metadata.smallMagnitude?.isNone
    | none => false
  countFailures [positiveCheck, negativeCheck,
    (Model.Power.classifyInteger? tinyFraction).isNone]⟩

/-! ## Configured correctly rounded reductions -/

/-- IEEE binary32 through the public configured carrier. -/
abbrev Binary32 :=
  FloatLib.Floats.ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/--
Exercise List and Array reducers through the configured API, including every rounding direction
and explicit dot-product length errors.
-/
def failConfiguredReductions : Thunk Nat := ⟨fun _ =>
  let one : Binary32 := FloatLib.Floats.ExecFloat.Binary.ofNatBits 0x3f800000
  let tiny : Binary32 := FloatLib.Floats.ExecFloat.Binary.ofNatBits 0x00000001
  let large : Binary32 := FloatLib.Floats.ExecFloat.Binary.ofNatBits 0x4b800000
  let negativeLarge : Binary32 :=
    FloatLib.Floats.ExecFloat.Binary.ofNatBits 0xcb800000
  let exactCancellation :=
    FloatLib.Floats.ExecFloat.Binary.sumList
      [large, one, negativeLarge] .nearestEven
  let nearest :=
    FloatLib.Floats.ExecFloat.Binary.sum #[one, tiny] .nearestEven
  let towardZero :=
    FloatLib.Floats.ExecFloat.Binary.sum #[one, tiny] .towardZero
  let downward :=
    FloatLib.Floats.ExecFloat.Binary.sum
      #[one, tiny] .towardNegativeInfinity
  let upward :=
    FloatLib.Floats.ExecFloat.Binary.sum
      #[one, tiny] .towardPositiveInfinity
  let dot :=
    FloatLib.Floats.ExecFloat.Binary.dot
      #[large, one, large] #[one, one, -one] .nearestEven
  let mismatch :=
    FloatLib.Floats.ExecFloat.Binary.dot #[one, one] #[one] .nearestEven
  countFailures
    [ FloatLib.Floats.ExecFloat.Binary.toNatBits exactCancellation == 0x3f800000
    , FloatLib.Floats.ExecFloat.Binary.toNatBits nearest == 0x3f800000
    , FloatLib.Floats.ExecFloat.Binary.toNatBits towardZero == 0x3f800000
    , FloatLib.Floats.ExecFloat.Binary.toNatBits downward == 0x3f800000
    , FloatLib.Floats.ExecFloat.Binary.toNatBits upward == 0x3f800001
    , match dot with
      | .ok value =>
          FloatLib.Floats.ExecFloat.Binary.toNatBits value == 0x3f800000
      | .error _ => false
    , match mismatch with
      | .error (.lengthMismatch 2 1) => true
      | _ => false
    ]⟩

def totalFailures : Thunk Nat := ⟨fun _ =>
  failCustomInstances.get + failWideExponentClassification.get + failConfiguredReductions.get⟩

def report : Thunk String := ⟨fun _ =>
  let failedNames :=
    if failedCustomChecks.get.isEmpty then "none" else String.intercalate ", " failedCustomChecks.get
  String.intercalate "\n"
    [ s!"customInstances: {failCustomInstances.get}"
    , s!"failedCustomChecks: {failedNames}"
    , s!"wideExponentClassification: {failWideExponentClassification.get}"
    , s!"configuredReductions: {failConfiguredReductions.get}"
    , s!"TOTAL: {totalFailures.get}"
    ]⟩

end FloatLibTests.Regression.BinaryInterchange.ExecFloatInstances
