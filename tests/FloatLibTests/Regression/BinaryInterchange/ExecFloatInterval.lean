/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Interval
public import FloatLibTests.Accounting

/-!
# Regression checks for format-generic executable intervals

The smallest tiny-format pair sweep is exhaustive; a second format and binary32 use representative
extrema, units, subnormals, and signed zeros. Arithmetic results must contain every directed corner
result, and activation checks enumerate representable members.

The executable descriptor-model regression suite imports this module and includes `totalFailures`
in its aggregate zero-failure check.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.ExecFloatInterval

open FloatLibTests.Accounting

abbrev f32 := FloatFormat.binary32
/-! ## Exhaustive tiny-format enclosure checks -/

def finiteValues (fmt : FloatFormat) : List (Model fmt) :=
  ((List.range (2 ^ fmt.bitWidth)).map (Model.ofNatBits (fmt := fmt))).filter
    Model.isFinite

def intervalsFromValues {fmt : FloatFormat}
    (values : List (Model fmt)) : List (Model.Interval fmt) :=
  values.flatMap fun lo =>
    values.filterMap fun hi =>
      if Model.Interval.leB lo hi then some ⟨lo, hi⟩ else none

def validIntervals (fmt : FloatFormat) : List (Model.Interval fmt) :=
  intervalsFromValues (finiteValues fmt)

def representativeValues (fmt : FloatFormat) : List (Model fmt) :=
  [ Model.negMaxFinite fmt
  , Model.negOne fmt
  , Model.negMinSubnormal fmt
  , Model.negZero fmt
  , Model.posZero fmt
  , Model.posMinSubnormal fmt
  , Model.posOne fmt
  , Model.posMaxFinite fmt
  ]

def representativeIntervals (fmt : FloatFormat) : List (Model.Interval fmt) :=
  intervalsFromValues (representativeValues fmt)

@[inline] def sameGenericInterval {fmt : FloatFormat}
    (A B : Model.Interval fmt) : Bool :=
  A.lo.toNatBits == B.lo.toNatBits && A.hi.toNatBits == B.hi.toNatBits

@[inline] def containsB {fmt : FloatFormat} (I : Model.Interval fmt)
    (x : Model fmt) : Bool :=
  Model.Interval.leB I.lo x && Model.Interval.leB x I.hi

def corners {fmt : FloatFormat} (A B : Model.Interval fmt) :
    List (Model fmt × Model fmt) :=
  [(A.lo, B.lo), (A.lo, B.hi), (A.hi, B.lo), (A.hi, B.hi)]

def directedCornersEnclosed {fmt : FloatFormat} (result : Model.Interval fmt)
    (down up : Model fmt → Model fmt → Model fmt)
    (A B : Model.Interval fmt) : Bool :=
  (corners A B).all fun (x, y) =>
    containsB result (down x y) && containsB result (up x y)

def hullEncloses {fmt : FloatFormat} (A B : Model.Interval fmt) : Bool :=
  let result := Model.Interval.hull A B
  containsB result A.lo && containsB result A.hi &&
    containsB result B.lo && containsB result B.hi

def pairArithmeticEnclosed {fmt : FloatFormat}
    (A B : Model.Interval fmt) : Bool :=
  let addResult := Model.Interval.add A B
  let subResult := Model.Interval.sub A B
  let mulResult := Model.Interval.mul A B
  let divResult := Model.Interval.div A B
  hullEncloses A B &&
    directedCornersEnclosed addResult Model.addDown Model.addUp A B &&
    directedCornersEnclosed subResult Model.subDown Model.subUp A B &&
    directedCornersEnclosed mulResult Model.mulDown Model.mulUp A B &&
    if Model.Interval.containsZero B then
      sameGenericInterval divResult (Model.Interval.whole fmt)
    else
      directedCornersEnclosed divResult Model.divDown Model.divUp A B

def imageEnclosed {fmt : FloatFormat} (values : List (Model fmt))
    (input output : Model.Interval fmt) (f : Model fmt → Model fmt) : Bool :=
  values.all fun x => !containsB input x || containsB output (f x)

def unaryImagesEnclosed {fmt : FloatFormat} (values : List (Model fmt))
    (A : Model.Interval fmt) : Bool :=
  let reluResult := Model.Interval.relu A
  let absResult := Model.Interval.abs A
  let sqrtResult := Model.Interval.sqrt A
  imageEnclosed values A reluResult
      (fun x => Model.maximum x (Model.posZero fmt)) &&
    imageEnclosed values A absResult Model.abs &&
    if Model.Interval.leB (Model.posZero fmt) A.lo then
      imageEnclosed values A sqrtResult Model.sqrt
    else
      true

def tinyPairFailures (fmt : FloatFormat) : Nat :=
  let intervals := validIntervals fmt
  countPairFailures intervals intervals pairArithmeticEnclosed

def representativePairFailures (fmt : FloatFormat) : Nat :=
  let intervals := representativeIntervals fmt
  countPairFailures intervals intervals pairArithmeticEnclosed

def representativeUnaryFailures (fmt : FloatFormat) : Nat :=
  let values := representativeValues fmt
  countWhereFailures (representativeIntervals fmt) (unaryImagesEnclosed values)

def tinyUnaryFailures (fmt : FloatFormat) : Nat :=
  let values := finiteValues fmt
  countWhereFailures (validIntervals fmt) (unaryImagesEnclosed values)

def tinyFormat1 : FloatFormat :=
  FloatFormat.ieee 2 1

def tinyFormat2 : FloatFormat :=
  FloatFormat.ieee 2 2

def failTinyPairEnclosures : Thunk Nat := ⟨fun _ =>
  tinyPairFailures tinyFormat1 + representativePairFailures tinyFormat2⟩

def failTinyUnaryEnclosures : Thunk Nat := ⟨fun _ =>
  tinyUnaryFailures tinyFormat1 + tinyUnaryFailures tinyFormat2⟩

def failBinary32RepresentativeEnclosures : Thunk Nat := ⟨fun _ =>
  representativePairFailures f32 + representativeUnaryFailures f32⟩

end FloatLibTests.Regression.BinaryInterchange.ExecFloatInterval
