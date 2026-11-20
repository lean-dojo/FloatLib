/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.InlineStages
public import FloatLib.Tactic.InlineStatus
public meta import FloatLib.Tactic.KernelRefl
public import FloatLib.Tactic.SpecializeDirections
public import FloatLib.Tactic.SpecializeSums

/-!
# Fully expanded binary operations on natural words

`Flat.add`, `Flat.sub`, `Flat.mul`, `Flat.fma`, `Flat.div` and `Flat.sqrt` are the
operations of `BinaryInterchange.KernelPath` on natural-number encodings with every stage
unfolded at elaboration time. Their equations with the staged operations hold by reflexivity,
which Lean's kernel checks (`kernel_refl%`).
Addition, subtraction and multiplication use the short paths of `KernelPath.Fast`.

The module also expands status, comparison, conversion and literal computations, then
specializes arithmetic to each rounding direction. Stored-carrier transport is in
`KernelPath.Value`; no encoded-format carrier is needed here.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

namespace Flat

/-- `KernelPath.add` with its stages unfolded: the general addition, for every operand. -/
noncomputable def addGeneral (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    Nat :=
  inline_stages% (KernelPath.add fmt mode a b)

/-- `KernelPath.mul` with its stages unfolded: the general multiplication, for every operand. -/
noncomputable def mulGeneral (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    Nat :=
  inline_stages% (KernelPath.mul fmt mode a b)

/--
The short path of addition for operands ordered by magnitude, with its stages unfolded, falling
back to `addGeneral`.
-/
noncomputable def addOrdered (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    Nat :=
  inline_short% (addFastWith fmt mode a b (addGeneral fmt mode a b))

/--
The carry path of addition with its stages unfolded, falling back to `addOrdered`: two operands
of one sign whose sum carries into the next exponent.
-/
noncomputable def addCarry (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  kernel_inline% [KernelPath.addCarryWith, KernelPath.roundUp]
    (addCarryWith fmt mode a b (addOrdered fmt mode a b))

/--
The shortest path of addition for operands of one sign with its stages unfolded, falling back
to `addCarry` for a sum that carries.
-/
noncomputable def addSame (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  kernel_inline% [KernelPath.addSameWith, KernelPath.roundUpShift]
    (addSameWith fmt mode a b (addCarry fmt mode a b))

/--
Addition on encodings: `addSame` for operands of one sign and `addOrdered` for operands of
different signs. It is the encoding of the sum of the values encoded by `a` and `b`, rounded in
the direction `mode` (`add_eq_spec`).
-/
noncomputable def add (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  kernel_inline% [KernelPath.bySign]
    (bySign fmt a b (addSame fmt mode a b) (addOrdered fmt mode a b))

/-- Subtraction on encodings: `add` on the negated second operand (`sub_eq_spec`). -/
noncomputable def sub (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  (fun negated =>
    kernel_inline% [KernelPath.bySign]
      (bySign fmt a negated (addSame fmt mode a negated) (addOrdered fmt mode a negated)))
    (inline_short% (KernelPath.neg fmt b))

/--
The short path of multiplication with its stages unfolded, falling back to `mulGeneral`
(`mul_eq_spec`).
-/
noncomputable def mul (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  inline_short% (mulFastWith fmt mode a b (mulGeneral fmt mode a b))

/-- `KernelPath.fma` with its stages unfolded. -/
noncomputable def fma (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b c : Nat) : Nat :=
  inline_stages% (KernelPath.fma fmt mode a b c)

/-- `KernelPath.div` with its stages unfolded. -/
noncomputable def div (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  inline_stages% (KernelPath.div fmt mode a b)

/--
`KernelPath.ofRatio` with its stages unfolded: the encoding of `± num / den` rounded in the
direction `mode`.
-/
noncomputable def ofRatio (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign num den : Nat) :
    Nat :=
  kernel_inline% [KernelPath.ofRatio, KernelPath.natLength, KernelPath.divCore,
    KernelPath.roundQuotient, KernelPath.roundUp, KernelPath.pack]
    (KernelPath.ofRatio fmt mode sign num den)

/-- `KernelPath.sqrt` with its stages unfolded (`sqrt_eq_spec`). -/
noncomputable def sqrt (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  inline_stages% (KernelPath.sqrt fmt mode a)

/-- `KernelPath.neg`: the encoding of the negation. -/
noncomputable def neg (fmt : FloatFormat) (a : Nat) : Nat :=
  inline_stages% (KernelPath.neg fmt a)

/-- `KernelPath.ofScientific` with its stages unfolded: the encoding of a scientific literal. -/
noncomputable def ofScientific (fmt : FloatFormat) (mantissa : Nat) (exponentSign : Bool)
    (exponent : Nat) : Nat :=
  kernel_inline% [KernelPath.ofScientific, KernelPath.ofRatio, KernelPath.natLength,
    KernelPath.divCore, KernelPath.roundQuotient, KernelPath.roundUp, KernelPath.pack]
    (KernelPath.ofScientific fmt mantissa exponentSign exponent)

/-- `KernelPath.ofNatural` with its stages unfolded: the encoding of a natural-number literal. -/
noncomputable def ofNatural (fmt : FloatFormat) (value : Nat) : Nat :=
  kernel_inline% [KernelPath.ofNatural, KernelPath.ofRatio, KernelPath.natLength,
    KernelPath.divCore, KernelPath.roundQuotient, KernelPath.roundUp, KernelPath.pack]
    (KernelPath.ofNatural fmt value)

/-- `KernelPath.compareCode` with its stages unfolded: the comparison code of two words. -/
noncomputable def compare (fmt : FloatFormat) (a b : Nat) : Nat :=
  kernel_inline% [KernelPath.compareCode, KernelPath.compareKey, KernelPath.nanFlag,
    KernelPath.infFlag, KernelPath.nonFinite] (KernelPath.compareCode fmt a b)

/--
`KernelPath.totalOrderCode` with its stages unfolded: one when the first word precedes or equals
the second in the IEEE total order.
-/
noncomputable def totalOrder (fmt : FloatFormat) (a b : Nat) : Nat :=
  kernel_inline% [KernelPath.totalOrderCode, KernelPath.nanKey, KernelPath.compareKey,
    KernelPath.nanFlag, KernelPath.infFlag, KernelPath.nonFinite, KernelPath.geFlag,
    KernelPath.signalingFlag] (KernelPath.totalOrderCode fmt a b)

/-- The flat total-order code is the staged one. -/
theorem totalOrder_eq : @totalOrder = @KernelPath.totalOrderCode := kernel_refl%

/--
`KernelPath.cast` with its stages unfolded: the encoding in `dst` of the value that `a` encodes
in `src`, rounded in the direction `mode`.
-/
noncomputable def cast (src dst : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  inline_stages% (KernelPath.cast src dst mode a)

/-- The flat cast is the staged one. -/
theorem cast_eq : @cast = @KernelPath.cast := kernel_refl%

/--
`KernelPath.castStatus` with its stages unfolded: the status number of the cast into `dst` of
the value that `a` encodes in `src`.
-/
noncomputable def castStatus (src dst : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) :
    Nat :=
  inline_status% (KernelPath.castStatus src dst mode a)

/-- The flat status of a cast is the staged one. -/
theorem castStatus_eq : @castStatus = @KernelPath.castStatus := kernel_refl%

/--
`KernelPath.castStatusWith` with its stages unfolded: the status number of the cast into `dst`
of the value that `a` encodes in `src`, when the cast has the word `w`.
-/
noncomputable def castStatusWith (src dst : FloatFormat) (mode : Model.IEEERoundingMode)
    (a w : Nat) : Nat :=
  inline_status% (KernelPath.castStatusWith src dst mode a w)

/-- The flat status of a cast with a given word is the staged one. -/
theorem castStatusWith_eq : @castStatusWith = @KernelPath.castStatusWith := kernel_refl%

/-- The flat status of a cast with the word of the flat cast is the flat status of the cast. -/
theorem castStatusWith_cast (src dst : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) :
    castStatusWith src dst mode a (cast src dst mode a) = castStatus src dst mode a := by
  rw [castStatusWith_eq, castStatus_eq, cast_eq]
  rfl

/--
`KernelPath.intMagnitude` with its stages unfolded: the magnitude of the integer that rounds a
finite value in the direction `mode`.
-/
noncomputable def intMagnitude (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) :
    Nat :=
  inline_stages% (KernelPath.intMagnitude fmt mode a)

/-- The flat integer magnitude is the staged one. -/
theorem intMagnitude_eq : @intMagnitude = @KernelPath.intMagnitude := kernel_refl%

/--
`KernelPath.roundToIntegral` with its stages unfolded: the encoding of a value rounded to an
integer in the direction `mode`.
-/
noncomputable def roundToIntegral (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) :
    Nat :=
  inline_stages% (KernelPath.roundToIntegral fmt mode a)

/-- `KernelPath.addStatus` with its stages unfolded: the status number of an addition. -/
noncomputable def addStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  inline_status% (KernelPath.addStatus fmt mode a b)

/-- `KernelPath.subStatus` with its stages unfolded: the status number of a subtraction. -/
noncomputable def subStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  inline_status% (KernelPath.subStatus fmt mode a b)

/-- `KernelPath.mulStatus` with its stages unfolded: the status number of a multiplication. -/
noncomputable def mulStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  inline_status% (KernelPath.mulStatus fmt mode a b)

/--
`KernelPath.fmaStatus` with its stages unfolded: the status number of a fused multiply-add.
-/
noncomputable def fmaStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b c : Nat) :
    Nat :=
  inline_status% (KernelPath.fmaStatus fmt mode a b c)

/-- `KernelPath.divStatus` with its stages unfolded: the status number of a division. -/
noncomputable def divStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    Nat :=
  inline_status% (KernelPath.divStatus fmt mode a b)

/--
`KernelPath.roundToIntegralStatus` with its stages unfolded: the status number of a rounding to
an integral value.
-/
noncomputable def roundToIntegralStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a : Nat) : Nat :=
  inline_status% (KernelPath.roundToIntegralStatus fmt mode a)

/--
`KernelPath.sqrtStatus` with its stages unfolded: the status number of a square root. The status
of an operand outside the checked path stays a call.
-/
noncomputable def sqrtStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) :
    Nat :=
  kernel_inline% [KernelPath.sqrtStatus, KernelPath.sqrtStatusCore, KernelPath.rootStatus,
    KernelPath.rootUp, KernelPath.newtonRoot, KernelPath.newton, Kernel.bitLength,
    Kernel.laneLength, KernelPath.significandLength,
    KernelPath.nonFinite] (KernelPath.sqrtStatus fmt mode a)

/-- Unfold every stage of the status of a rounded ratio and of the rounding whose word it reads. -/
local macro "inline_ratio% " body:term : term =>
  `(kernel_inline% [KernelPath.ratioStatus, KernelPath.ratioStatusWith, KernelPath.ofRatio,
      KernelPath.natLength, KernelPath.divCore, KernelPath.roundQuotient, KernelPath.roundUp,
      KernelPath.pack, KernelPath.roundStatus, KernelPath.overflowFlag, KernelPath.tinyFlag,
      KernelPath.signedCompare, KernelPath.gtFlag, KernelPath.geFlag, KernelPath.nonFinite]
      $body)

/--
`KernelPath.ratioStatus` with its stages unfolded: the status number of `± num / den` rounded in
the direction `mode`.
-/
noncomputable def ratioStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign num den : Nat) : Nat :=
  inline_ratio% (KernelPath.ratioStatus fmt mode sign num den)

/--
`KernelPath.ratioStatusWith` with its stages unfolded: the status number of `± num / den`
rounded in the direction `mode`, when the rounded ratio has the word `w`.
-/
noncomputable def ratioStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign num den w : Nat) : Nat :=
  inline_ratio% (KernelPath.ratioStatusWith fmt mode sign num den w)

/--
`KernelPath.addStatusWith` with its stages unfolded: the status number of an addition whose
rounded sum has the word `w`. A statement about the value and the flags of one addition passes
the word of its value, which Lean's kernel then computes once.
-/
noncomputable def addStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b w : Nat) : Nat :=
  inline_status% (KernelPath.addStatusWith fmt mode a b w)

/-- `KernelPath.subStatusWith` with its stages unfolded. -/
noncomputable def subStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b w : Nat) : Nat :=
  inline_status% (KernelPath.subStatusWith fmt mode a b w)

/-- `KernelPath.mulStatusWith` with its stages unfolded. -/
noncomputable def mulStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b w : Nat) : Nat :=
  inline_status% (KernelPath.mulStatusWith fmt mode a b w)

/-- `KernelPath.fmaStatusWith` with its stages unfolded. -/
noncomputable def fmaStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b c w : Nat) : Nat :=
  inline_status% (KernelPath.fmaStatusWith fmt mode a b c w)

/-- `KernelPath.divStatusWith` with its stages unfolded. -/
noncomputable def divStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b w : Nat) : Nat :=
  inline_status% (KernelPath.divStatusWith fmt mode a b w)

/-- `KernelPath.roundToIntegralStatusWith` with its stages unfolded. -/
noncomputable def roundToIntegralStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a w : Nat) : Nat :=
  inline_status% (KernelPath.roundToIntegralStatusWith fmt mode a w)

/-- The flat status of an addition with a given word is the staged one. -/
theorem addStatusWith_eq : @addStatusWith = @KernelPath.addStatusWith := kernel_refl%

/-- The flat status of a subtraction with a given word is the staged one. -/
theorem subStatusWith_eq : @subStatusWith = @KernelPath.subStatusWith := kernel_refl%

/-- The flat status of a multiplication with a given word is the staged one. -/
theorem mulStatusWith_eq : @mulStatusWith = @KernelPath.mulStatusWith := kernel_refl%

/-- The flat status of a fused multiply-add with a given word is the staged one. -/
theorem fmaStatusWith_eq : @fmaStatusWith = @KernelPath.fmaStatusWith := kernel_refl%

/-- The flat status of a division with a given word is the staged one. -/
theorem divStatusWith_eq : @divStatusWith = @KernelPath.divStatusWith := kernel_refl%

/-- The flat status of an integral rounding with a given word is the staged one. -/
theorem roundToIntegralStatusWith_eq :
    @roundToIntegralStatusWith = @KernelPath.roundToIntegralStatusWith := kernel_refl%

/-- The flat integral rounding is the staged one. -/
theorem roundToIntegral_eq : @roundToIntegral = @KernelPath.roundToIntegral := kernel_refl%

/-- The flat status of an addition is the staged one. -/
theorem addStatus_eq : @addStatus = @KernelPath.addStatus := kernel_refl%

/-- The flat status of a subtraction is the staged one. -/
theorem subStatus_eq : @subStatus = @KernelPath.subStatus := kernel_refl%

/-- The flat status of a multiplication is the staged one. -/
theorem mulStatus_eq : @mulStatus = @KernelPath.mulStatus := kernel_refl%

/-- The flat status of a fused multiply-add is the staged one. -/
theorem fmaStatus_eq : @fmaStatus = @KernelPath.fmaStatus := kernel_refl%

/-- The flat status of a division is the staged one. -/
theorem divStatus_eq : @divStatus = @KernelPath.divStatus := kernel_refl%

/-- The flat status of a square root is the staged one. -/
theorem sqrtStatus_eq : @sqrtStatus = @KernelPath.sqrtStatus := kernel_refl%

/-- The flat status of a rounding to an integral value is the staged one. -/
theorem roundToIntegralStatus_eq :
    @roundToIntegralStatus = @KernelPath.roundToIntegralStatus := kernel_refl%

/-- The flat status of a rounded ratio is the staged one. -/
theorem ratioStatus_eq : @ratioStatus = @KernelPath.ratioStatus := kernel_refl%

/-- The flat status of a rounded ratio with a given word is the staged one. -/
theorem ratioStatusWith_eq : @ratioStatusWith = @KernelPath.ratioStatusWith := kernel_refl%

/-- The flat addition is the staged short path. -/
theorem add_eq : @add = @KernelPath.addShort := kernel_refl%

/-- The flat subtraction is the staged short path. -/
theorem sub_eq : @sub = @KernelPath.subShort := kernel_refl%

/-- The flat multiplication is the staged short path. -/
theorem mul_eq : @mul = @KernelPath.mulFast := kernel_refl%

/-- The flat fused multiply-add is the staged one. -/
theorem fma_eq : @fma = @KernelPath.fma := kernel_refl%

/-- The flat division is the staged one. -/
theorem div_eq : @div = @KernelPath.div := kernel_refl%

/-- The flat rounding of a ratio is the staged one. -/
theorem ofRatio_eq : @ofRatio = @KernelPath.ofRatio := kernel_refl%

/-- The flat square root is the staged one. -/
theorem sqrt_eq : @sqrt = @KernelPath.sqrt := kernel_refl%

/--
An equation that holds by unfolding, as a rewrite rule with a proof term: `simp` applies it by
name. A rule stated with `rfl` is applied silently instead, and then the kernel has to compare
the two sides by unfolding both wherever the rule was used.
-/
theorem rewrite_rule {a b : Nat} (h : a = b) : a = b :=
  h

/--
The ordered path of addition on encodings in one rounding direction, with the code of that
direction only.
-/
/-- The flat ordered addition in a literal direction is its specialization to that direction. -/
specialize_directions addOrdered [a b]

specialize_sums

/-- Multiplication on encodings in one rounding direction, with the code of that direction only. -/
/-- The flat multiplication in a literal direction is its specialization to that direction. -/
specialize_directions mul [a b]

/--
Fused multiply-add on encodings in one rounding direction, with the code of that direction only.
-/
/-- The flat fused multiply-add in a literal direction is its specialization to that direction. -/
specialize_directions fma [a b c]

/-- Division on encodings in one rounding direction, with the code of that direction only. -/
/-- The flat division in a literal direction is its specialization to that direction. -/
specialize_directions div [a b]

/-- Square root on encodings in one rounding direction, with the code of that direction only. -/
/-- The flat square root in a literal direction is its specialization to that direction. -/
specialize_directions sqrt [a]

/--
The status number of an addition with a given word in one rounding direction, with the code of
that direction only.
-/
/-- The flat status of an addition with a given word in a literal direction is its
specialization to that direction. -/
specialize_directions addStatusWith [a b w]

/--
The status number of a subtraction with a given word in one rounding direction, with the code of
that direction only.
-/
/-- The flat status of a subtraction with a given word in a literal direction is its
specialization to that direction. -/
specialize_directions subStatusWith [a b w]

/--
The status number of a multiplication with a given word in one rounding direction, with the code of
that direction only.
-/
/-- The flat status of a multiplication with a given word in a literal direction is its
specialization to that direction. -/
specialize_directions mulStatusWith [a b w]

/--
The status number of a fused multiply-add with a given word in one rounding direction, with the
code of that direction only.
-/
/-- The flat status of a fused multiply-add with a given word in a literal direction is its
specialization to that direction. -/
specialize_directions fmaStatusWith [a b c w]

/--
The status number of a division with a given word in one rounding direction, with the code of
that direction only.
-/
/-- The flat status of a division with a given word in a literal direction is its
specialization to that direction. -/
specialize_directions divStatusWith [a b w]

/--
The status number of an integral rounding with a given word in one rounding direction, with the
code of that direction only.
-/
/-- The flat status of an integral rounding with a given word in a literal direction is its
specialization to that direction. -/
specialize_directions roundToIntegralStatusWith [a w]

end Flat

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
