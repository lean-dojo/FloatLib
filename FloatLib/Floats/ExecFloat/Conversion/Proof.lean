/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Conversion.Runtime

/-!
# Proof contracts for explicit conversion and mixed arithmetic

The preparation theorems compose the supplied decoder, exact-domain operations, and destination
quantization relation. They establish one quantizer call on successful preparation and preserve
preparation failures. Numerical preservation by `ExactMap`, arithmetic instances, and the
context-dependent addition and subtraction hooks requires the separate family-specific laws
described in `Conversion.Core`.

Runtime-only clients may import `Conversion.Runtime`; the public `Conversion` module exports
both execution and these contracts.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u v w x y z a b

namespace ConversionStatus

/-- The merged inexact flag is raised exactly when either input raised it. -/
@[simp, grind =] theorem merge_inexact (first second : ConversionStatus) :
    (first.merge second).inexact = (first.inexact || second.inexact) :=
  rfl

/-- The merged overflow flag is raised exactly when either input raised it. -/
@[simp, grind =] theorem merge_overflow (first second : ConversionStatus) :
    (first.merge second).overflow = (first.overflow || second.overflow) :=
  rfl

/-- The merged underflow flag is raised exactly when either input raised it. -/
@[simp, grind =] theorem merge_underflow (first second : ConversionStatus) :
    (first.merge second).underflow = (first.underflow || second.underflow) :=
  rfl

/-- The merged saturation flag is raised exactly when either input raised it. -/
@[simp, grind =] theorem merge_saturated (first second : ConversionStatus) :
    (first.merge second).saturated = (first.saturated || second.saturated) :=
  rfl

/-- The merged wrapping flag is raised exactly when either input raised it. -/
@[simp, grind =] theorem merge_wrapped (first second : ConversionStatus) :
    (first.merge second).wrapped = (first.wrapped || second.wrapped) :=
  rfl

/-- The merged special-value flag is raised exactly when either input raised it. -/
@[simp, grind =] theorem merge_mapped_special (first second : ConversionStatus) :
    (first.merge second).mappedSpecial =
      (first.mappedSpecial || second.mappedSpecial) :=
  rfl

/-- An empty first status contributes no flags. -/
@[simp, grind =] theorem empty_merge (status : ConversionStatus) :
    ({} : ConversionStatus).merge status = status := by
  cases status
  simp [merge]

/-- An empty second status contributes no flags. -/
@[simp, grind =] theorem merge_empty (status : ConversionStatus) :
    status.merge ({} : ConversionStatus) = status := by
  cases status
  simp [merge]

/-- Status accumulation is associative, so grouping a successful pipeline is irrelevant. -/
theorem merge_assoc (first second third : ConversionStatus) :
    (first.merge second).merge third = first.merge (second.merge third) := by
  cases first
  cases second
  cases third
  simp [merge, Bool.or_assoc]

end ConversionStatus

namespace ConversionOutcome

variable {α : Type u} {β : Type v}

/-- Mapping a successful outcome transforms only its value. -/
@[simp, grind =] theorem map_success (f : α → β) (value : α) (status : ConversionStatus) :
    map f (.success value status) = .success (f value) status :=
  rfl

/-- Mapping a failed outcome preserves its failure reason. -/
@[simp, grind =] theorem map_failure (f : α → β) (reason : ConversionFailure) :
    map f (.failure reason) = .failure reason :=
  rfl

/-- Binding a successful outcome runs the continuation and accumulates successful status. -/
@[simp, grind =] theorem bind_success (value : α) (status : ConversionStatus)
    (next : α → ConversionOutcome β) :
    bind (.success value status) next =
      match next value with
      | .success nextValue nextStatus =>
          .success nextValue (status.merge nextStatus)
      | .failure reason => .failure reason :=
  rfl

/-- Binding a failed outcome does not run the continuation. -/
@[simp, grind =] theorem bind_failure (reason : ConversionFailure)
    (next : α → ConversionOutcome β) :
    bind (.failure reason) next = .failure reason :=
  rfl

/-- A successful outcome with no prior flags binds exactly like direct continuation application. -/
@[grind =] theorem bind_success_empty (value : α)
    (next : α → ConversionOutcome β) :
    bind (.success value {}) next = next value := by
  cases h : next value <;> simp [bind, h]

/-- Extracting the value of a successful outcome returns that value. -/
@[simp, grind =] theorem value?_success (value : α) (status : ConversionStatus) :
    value? (.success value status) = some value :=
  rfl

/-- A failed outcome contains no successful value. -/
@[simp, grind =] theorem value?_failure (reason : ConversionFailure) :
    value? (α := α) (.failure reason) = none :=
  rfl

/-- Extracting status from a successful outcome returns its stored flags. -/
@[simp, grind =] theorem status?_success (value : α) (status : ConversionStatus) :
    status? (.success value status) = some status :=
  rfl

/-- A failed outcome contains no successful status. -/
@[simp, grind =] theorem status?_failure (reason : ConversionFailure) :
    status? (α := α) (.failure reason) = none :=
  rfl

/-- A successful outcome contains no failure reason. -/
@[simp, grind =] theorem failure?_success (value : α) (status : ConversionStatus) :
    failure? (.success value status) = none :=
  rfl

/-- Extracting failure information returns the stored reason. -/
@[simp, grind =] theorem failure?_failure (reason : ConversionFailure) :
    failure? (α := α) (.failure reason) = some reason :=
  rfl

/-- Mapping the identity function leaves an outcome unchanged. -/
@[simp, grind =] theorem map_id (outcome : ConversionOutcome α) :
    outcome.map id = outcome := by
  cases outcome <;> rfl

/-- Success-value maps compose without changing status or failure information. -/
@[simp, grind =] theorem map_comp (f : α → β) {γ : Type w} (g : β → γ)
    (outcome : ConversionOutcome α) :
    (outcome.map f).map g = outcome.map (g ∘ f) := by
  cases outcome <;> rfl

/-- Extracting a value after `map` agrees with mapping the extracted option. -/
@[simp, grind =] theorem value?_map (f : α → β) (outcome : ConversionOutcome α) :
    (outcome.map f).value? = outcome.value?.map f := by
  cases outcome <;> rfl

/-- Mapping a successful value does not alter its status. -/
@[simp, grind =] theorem status?_map (f : α → β) (outcome : ConversionOutcome α) :
    (outcome.map f).status? = outcome.status? := by
  cases outcome <;> rfl

/-- Mapping a successful value does not alter a failure reason. -/
@[simp, grind =] theorem failure?_map (f : α → β) (outcome : ConversionOutcome α) :
    (outcome.map f).failure? = outcome.failure? := by
  cases outcome <;> rfl

/-- Grouping consecutive successful binds does not change values, failures, or accumulated flags. -/
theorem bind_assoc {γ : Type w} (outcome : ConversionOutcome α)
    (next : α → ConversionOutcome β) (last : β → ConversionOutcome γ) :
    (outcome.bind next).bind last =
      outcome.bind (fun value => (next value).bind last) := by
  cases outcome with
  | failure reason => rfl
  | success value status =>
      cases hnext : next value with
      | failure reason =>
          simp [bind, hnext]
      | success nextValue nextStatus =>
          cases hlast : last nextValue with
          | failure reason =>
              simp [bind, hnext, hlast]
          | success lastValue lastStatus =>
              simp [bind, hnext, hlast, ConversionStatus.merge_assoc]

end ConversionOutcome

namespace ExactDecoder

variable {Source : Type u} {SourceExact : Type v} {TargetExact : Type w}

/-- Decoding a natural number for conversion produces that exact finite value. -/
@[simp, grind =] theorem run_natural (value : Nat) :
    run value = .finite value :=
  rfl

/-- Decoding an integer for conversion produces that exact finite value. -/
@[simp, grind =] theorem run_integer (value : Int) :
    run value = .finite value :=
  rfl

/-- Decoding a rational for conversion introduces no rounding. -/
@[simp, grind =] theorem run_rational (value : Rat) :
    run value = .finite value :=
  rfl

/-- Decoding a dyadic value for conversion preserves its exact binary representation. -/
@[simp, grind =] theorem run_dyadic (value : FloatLib.Numerics.Dyadic) :
    run value = .finite value :=
  rfl

/-- `decodeTo` is exact decoding followed by the selected finite-value embedding. -/
@[grind =] theorem decodeTo_eq [ExactDecoder Source SourceExact]
    [embedding : ExactMap SourceExact TargetExact] (value : Source) :
    decodeTo value = (run value).map embedding.map :=
  rfl

/-- Decoding into the source's own exact domain performs no semantic transformation. -/
@[simp, grind =] theorem decodeTo_self [ExactDecoder Source SourceExact] (value : Source) :
    decodeTo (TargetExact := SourceExact) value = run value := by
  change (run value).map id = run value
  exact NumericalValue.map_id _

end ExactDecoder

namespace Quantizer

variable {Destination : Type u} {Exact : Type v}

/-- The executable destination quantizer satisfies its declared relation. -/
theorem spec_quantize [self : Quantizer Destination Exact]
    (context : self.Context) (value : NumericalValue Exact) :
    self.spec context value (quantize context value) :=
  self.correct context value

end Quantizer

/-- Explicit generic conversion satisfies the destination's declared quantization relation. -/
theorem spec_convertWith {Source : Type u} {target : Type v}
    {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    (value : Source) (context : quantizer.Context) :
    quantizer.spec context (ExactDecoder.decodeTo value) (convertWith value context) :=
  quantizer.correct context (ExactDecoder.decodeTo value)

/-- Default-context generic conversion satisfies the declared quantization relation. -/
theorem spec_convert {Source : Type u} {target : Type v}
    {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    [defaults : DefaultQuantizer target TargetExact]
    (value : Source) :
    quantizer.spec defaults.defaultContext (ExactDecoder.decodeTo value)
      (convert (target := target) (SourceExact := SourceExact)
        (TargetExact := TargetExact) value) :=
  spec_convertWith (target := target) (SourceExact := SourceExact)
    (TargetExact := TargetExact) value defaults.defaultContext

/-- Explicit `ExecFloat` conversion satisfies the destination's declared relation. -/
theorem spec_castWith {F : Type u} [EncodedFormat F]
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder (FloatLib.Floats.ExecFloat F) SourceExact]
    [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    (value : FloatLib.Floats.ExecFloat F) (context : quantizer.Context) :
    quantizer.spec context (ExactDecoder.decodeTo value) (castWith value context) :=
  spec_convertWith value context

/-- Default-context `ExecFloat` conversion satisfies the declared relation. -/
theorem spec_cast {F : Type u} [EncodedFormat F]
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder (FloatLib.Floats.ExecFloat F) SourceExact]
    [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    [defaults : DefaultQuantizer target TargetExact]
    (value : FloatLib.Floats.ExecFloat F) :
    quantizer.spec defaults.defaultContext (ExactDecoder.decodeTo value)
      (cast (target := target) (SourceExact := SourceExact)
        (TargetExact := TargetExact) value) :=
  spec_convert (target := target) (SourceExact := SourceExact)
    (TargetExact := TargetExact) value

namespace Conversion

/-- A finite observation passes through preparation unchanged. -/
@[simp, grind =] theorem requireFinite_finite {Exact : Type u}
    (position : InputPosition) (value : Exact) :
    requireFinite position (.finite value) = .ok value :=
  rfl

/-- Infinity is rejected at the supplied operand position. -/
@[simp, grind =] theorem requireFinite_infinity {Exact : Type u}
    (position : InputPosition) (negative : Bool) :
    requireFinite (Exact := Exact) position (.infinity negative) =
      .error (.infinity position negative) :=
  rfl

/-- An exceptional observation is rejected at the supplied operand position. -/
@[simp, grind =] theorem requireFinite_exceptional {Exact : Type u}
    (position : InputPosition) (value : ExceptionalValue) :
    requireFinite (Exact := Exact) position (.exceptional value) =
      .error (.exceptional position value) :=
  rfl

/-- Finite exact division rejects any denominator satisfying the domain's zero predicate. -/
@[simp, grind =] theorem prepareDiv_finite_of_is_zero {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact]
    (left right : Exact) (hright : self.isZero right) :
    prepareDiv (.finite left) (.finite right) =
      (.error .divisionByZero : Except ConversionFailure (NumericalValue Exact)) := by
  have htest : ExactZero.test right = true :=
    (ExactZero.test_eq_true_iff right).2 hright
  change
    (if ExactZero.test right then
        .error .divisionByZero
      else
        .ok (.finite (left / right))) =
      (.error .divisionByZero : Except ConversionFailure (NumericalValue Exact))
  simp [htest]

/-- Finite exact division applies the domain's `/` when the denominator is not zero. -/
@[simp, grind =] theorem prepareDiv_finite_of_not_is_zero {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact]
    (left right : Exact) (hright : ¬self.isZero right) :
    prepareDiv (.finite left) (.finite right) =
      (.ok (.finite (left / right)) :
        Except ConversionFailure (NumericalValue Exact)) := by
  have htest : ExactZero.test right = false :=
    (ExactZero.test_eq_false_iff right).2 hright
  change
    (if ExactZero.test right then
        .error .divisionByZero
      else
        .ok (.finite (left / right))) =
      (.ok (.finite (left / right)) :
        Except ConversionFailure (NumericalValue Exact))
  simp [htest]

/-- Finite exact division reports division by zero exactly for declared-zero denominators. -/
@[simp, grind =] theorem prepareDiv_finite_eq_error_iff {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact]
    (left right : Exact) :
    prepareDiv (.finite left) (.finite right) =
        (.error .divisionByZero : Except ConversionFailure (NumericalValue Exact)) ↔
      self.isZero right := by
  change
    (if ExactZero.test right then
        .error .divisionByZero
      else
        .ok (.finite (left / right))) =
        (.error .divisionByZero : Except ConversionFailure (NumericalValue Exact)) ↔
      self.isZero right
  simp

section Quantization

variable {Destination : Type u} {Exact : Type v} [quantizer : Quantizer Destination Exact]

/-- A successfully prepared exact observation is passed to the destination quantizer. -/
@[simp, grind =] theorem quantizePrepared_ok
    (context : quantizer.Context) (value : NumericalValue Exact) :
    quantizePrepared context (.ok value) = quantizer.run context value :=
  rfl

/-- A preparation failure reaches the public outcome unchanged. -/
@[simp, grind =] theorem quantizePrepared_error
    (context : quantizer.Context) (reason : ConversionFailure) :
    quantizePrepared (Destination := Destination) (Exact := Exact)
        context (.error reason) =
      .failure reason :=
  rfl

/-- On successful preparation, `PreparedSpec` is exactly the destination relation. -/
@[simp, grind =] theorem preparedSpec_ok
    (context : quantizer.Context) (value : NumericalValue Exact)
    (outcome : ConversionOutcome Destination) :
    PreparedSpec context (.ok value) outcome ↔
      quantizer.spec context value outcome :=
  Iff.rfl

/-- On preparation failure, `PreparedSpec` requires the same public failure. -/
@[simp, grind =] theorem preparedSpec_error
    (context : quantizer.Context) (reason : ConversionFailure)
    (outcome : ConversionOutcome Destination) :
    PreparedSpec (Exact := Exact) context (.error reason) outcome ↔
      outcome = .failure reason :=
  Iff.rfl

/-- Preparation followed by the executable quantizer satisfies `PreparedSpec`. -/
theorem preparedSpec_quantizePrepared
    (context : quantizer.Context)
    (prepared : Except ConversionFailure (NumericalValue Exact)) :
    PreparedSpec context prepared (quantizePrepared context prepared) := by
  cases prepared with
  | ok value => exact quantizer.correct context value
  | error reason => rfl

end Quantization

end Conversion

namespace ExactExpression

/-- A finite decoded operand enters an exact expression unchanged. -/
theorem operand_eq_ok_of_decodeTo_eq_finite
    {Source : Type u} {SourceExact : Type v} {Exact : Type w}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact Exact]
    (index : Nat) (source : Source) (value : Exact)
    (hdecode : ExactDecoder.decodeTo (TargetExact := Exact) source = .finite value) :
    operand (Exact := Exact) index source = (.ok value : ExactExpression Exact) := by
  simp [operand, hdecode]

/-- A decoded infinity identifies the numbered operand that made the expression invalid. -/
theorem operand_eq_error_of_decodeTo_eq_infinity
    {Source : Type u} {SourceExact : Type v} {Exact : Type w}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact Exact]
    (index : Nat) (source : Source) (negative : Bool)
    (hdecode : ExactDecoder.decodeTo (TargetExact := Exact) source = .infinity negative) :
    operand (Exact := Exact) index source =
      (.error (.infinity (.operand index) negative) : ExactExpression Exact) := by
  simp [operand, hdecode]

/-- A decoded exceptional value identifies the numbered operand that caused rejection. -/
theorem operand_eq_error_of_decodeTo_eq_exceptional
    {Source : Type u} {SourceExact : Type v} {Exact : Type w}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact Exact]
    (index : Nat) (source : Source) (value : ExceptionalValue)
    (hdecode : ExactDecoder.decodeTo (TargetExact := Exact) source = .exceptional value) :
    operand (Exact := Exact) index source =
      (.error (.exceptional (.operand index) value) : ExactExpression Exact) := by
  simp [operand, hdecode]

/-- A successful exact expression becomes a finite input to the sole quantization step. -/
@[simp, grind =] theorem toPrepared_ok {Exact : Type u} (value : Exact) :
    toPrepared (.ok value : ExactExpression Exact) = .ok (.finite value) :=
  rfl

/-- An exact-expression failure is preserved before quantization. -/
@[simp, grind =] theorem toPrepared_error {Exact : Type u} (reason : ConversionFailure) :
    toPrepared (.error reason : ExactExpression Exact) = .error reason :=
  rfl

/-- Checked exact division rejects any denominator satisfying the domain's zero predicate. -/
@[simp, grind =] theorem div_of_is_zero {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact]
    (numerator denominator : Exact) (hdenominator : self.isZero denominator) :
    div numerator denominator =
      (.error .divisionByZero : ExactExpression Exact) := by
  have htest : ExactZero.test denominator = true :=
    (ExactZero.test_eq_true_iff denominator).2 hdenominator
  simp [div, htest]

/-- Checked exact division reports division by canonical zero. -/
@[simp, grind =] theorem div_zero {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact] (numerator : Exact) :
    div numerator 0 = (.error .divisionByZero : ExactExpression Exact) :=
  div_of_is_zero numerator 0 self.zero_is_zero

/--
Checked exact division applies the exact domain's `/` when the denominator is nonzero.

The premise uses the exact domain's declared zero proposition. A domain such as `SignedRat` can
therefore recognize several zero representations and prove a bridge from that proposition to its
numerical meaning.
-/
@[simp, grind =] theorem div_of_not_is_zero {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact]
    (numerator denominator : Exact) (hdenominator : ¬self.isZero denominator) :
    div numerator denominator =
      (.ok (numerator / denominator) : ExactExpression Exact) := by
  have htest : ExactZero.test denominator = false :=
    (ExactZero.test_eq_false_iff denominator).2 hdenominator
  simp [div, htest]

/-- Checked exact division reports division by zero exactly for declared-zero denominators. -/
@[simp, grind =] theorem div_eq_error_iff {Exact : Type u}
    [Zero Exact] [self : ExactZero Exact] [Div Exact]
    (numerator denominator : Exact) :
    div numerator denominator =
        (.error .divisionByZero : ExactExpression Exact) ↔
      self.isZero denominator := by
  simp [div, ExactZero.test_eq_true_iff]

end ExactExpression

namespace ConversionProof

variable {Left : Type u} {Right : Type v} {result : Type w}
  {LeftExact : Type x} {RightExact : Type y} {Exact : Type z}

/--
An exact expression followed by one explicit-context quantization satisfies the destination's
declared relation, or returns the expression's failure unchanged.
-/
theorem preparedSpec_roundOnceWith
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (expression : ExactExpression Exact) :
    Conversion.PreparedSpec context expression.toPrepared
      (roundOnceWith (result := result) context expression) :=
  Conversion.preparedSpec_quantizePrepared _ _

/--
An exact expression followed by the default quantization context satisfies the same composed
contract.
-/
theorem preparedSpec_roundOnce
    [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (expression : ExactExpression Exact) :
    Conversion.PreparedSpec defaults.defaultContext expression.toPrepared
      (roundOnce (result := result) expression) :=
  preparedSpec_roundOnceWith (result := result) defaults.defaultContext expression

/-- A successful expression is sent directly to the quantizer as one finite exact value. -/
@[simp, grind =] theorem roundOnceWith_ok
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (value : Exact) :
    roundOnceWith (result := result) context (.ok value) =
      quantizer.run context (.finite value) :=
  rfl

/-- An exact-expression failure bypasses the destination quantizer unchanged. -/
@[simp, grind =] theorem roundOnceWith_error
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (reason : ConversionFailure) :
    roundOnceWith (result := result) context (.error reason) = .failure reason :=
  rfl

section Binary

variable [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
  [ExactDecoder Right RightExact] [ExactMap RightExact Exact]

/-- The context's addition hook followed by one quantization satisfies the composed relation. -/
theorem preparedSpec_addAsWith
    [Add Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    Conversion.PreparedSpec context
      (Conversion.prepareBinary (quantizer.addExact context)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (addAsWith context left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- The default-context addition hook satisfies the same composed relation. -/
theorem preparedSpec_addAs
    [Add Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) :
    Conversion.PreparedSpec defaults.defaultContext
      (Conversion.prepareBinary (quantizer.addExact defaults.defaultContext)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (addAs (result := result) (LeftExact := LeftExact)
        (RightExact := RightExact) (Exact := Exact) left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- The context's subtraction hook followed by one quantization satisfies the composed relation. -/
theorem preparedSpec_subAsWith
    [Sub Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    Conversion.PreparedSpec context
      (Conversion.prepareBinary (quantizer.subExact context)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (subAsWith context left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- The default-context subtraction hook satisfies the same composed relation. -/
theorem preparedSpec_subAs
    [Sub Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) :
    Conversion.PreparedSpec defaults.defaultContext
      (Conversion.prepareBinary (quantizer.subExact defaults.defaultContext)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (subAs (result := result) (LeftExact := LeftExact)
        (RightExact := RightExact) (Exact := Exact) left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- Exact multiplication followed by one quantization satisfies the composed relational contract. -/
theorem preparedSpec_mulAsWith
    [Mul Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    Conversion.PreparedSpec context
      (Conversion.prepareBinary (· * ·)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (mulAsWith context left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- Default-context exact multiplication satisfies the composed relational contract. -/
theorem preparedSpec_mulAs
    [Mul Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) :
    Conversion.PreparedSpec defaults.defaultContext
      (Conversion.prepareBinary (· * ·)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (mulAs (result := result) (LeftExact := LeftExact)
        (RightExact := RightExact) (Exact := Exact) left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- Exact division followed by one quantization satisfies the composed relational contract. -/
theorem preparedSpec_divAsWith
    [Zero Exact] [ExactZero Exact] [Div Exact]
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    Conversion.PreparedSpec context
      (Conversion.prepareDiv (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (divAsWith context left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- Default-context exact division satisfies the same composed relational contract. -/
theorem preparedSpec_divAs
    [Zero Exact] [ExactZero Exact] [Div Exact]
    [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) :
    Conversion.PreparedSpec defaults.defaultContext
      (Conversion.prepareDiv (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right))
      (divAs (result := result) (LeftExact := LeftExact)
        (RightExact := RightExact) (Exact := Exact) left right) :=
  Conversion.preparedSpec_quantizePrepared _ _

end Binary

/-- Exact fused multiply-add followed by one quantization satisfies the composed contract. -/
theorem preparedSpec_fmaAsWith {Addend : Type a} {AddendExact : Type b}
    [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
    [ExactDecoder Right RightExact] [ExactMap RightExact Exact]
    [ExactDecoder Addend AddendExact] [ExactMap AddendExact Exact]
    [Mul Exact] [Add Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) (addend : Addend) :
    Conversion.PreparedSpec context
      (Conversion.prepareFmaWith (quantizer.addExact context)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)
        (ExactDecoder.decodeTo addend))
      (fmaAsWith context left right addend) :=
  Conversion.preparedSpec_quantizePrepared _ _

/-- Default-context exact fused multiply-add satisfies the same composed relational contract. -/
theorem preparedSpec_fmaAs {Addend : Type a} {AddendExact : Type b}
    [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
    [ExactDecoder Right RightExact] [ExactMap RightExact Exact]
    [ExactDecoder Addend AddendExact] [ExactMap AddendExact Exact]
    [Mul Exact] [Add Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) (addend : Addend) :
    Conversion.PreparedSpec defaults.defaultContext
      (Conversion.prepareFmaWith (quantizer.addExact defaults.defaultContext)
        (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)
        (ExactDecoder.decodeTo addend))
      (fmaAs (result := result) (LeftExact := LeftExact)
        (RightExact := RightExact) (AddendExact := AddendExact)
        (Exact := Exact) left right addend) :=
  Conversion.preparedSpec_quantizePrepared _ _

end ConversionProof
end ExecFloat
end FloatLib.Floats
