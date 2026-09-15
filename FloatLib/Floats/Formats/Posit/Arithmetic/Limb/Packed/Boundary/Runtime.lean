/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Packed two-limb operation boundaries

These small executable combinators centralize propagation of the unique Posit Standard NaR
condition after packed operands have been decoded. Range and semantic refinement laws live in
`Boundary.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.Boundary

/-- Select a unary result, returning `narResult` when the decoded input is NaR. -/
@[inline] def unaryResult {α : Type}
    (narResult : α)
    (operation : FloatLib.Numerics.Dyadic → α)
    (value : Option FloatLib.Numerics.Dyadic) : α :=
  match value with
  | some finite => operation finite
  | none => narResult

/-- Select a binary result, returning `narResult` when either decoded input is NaR. -/
@[inline] def binaryResult {α : Type}
    (narResult : α)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → α)
    (left right : Option FloatLib.Numerics.Dyadic) : α :=
  match left, right with
  | some leftValue, some rightValue => operation leftValue rightValue
  | _, _ => narResult

/-- Select a ternary result, returning `narResult` when any decoded input is NaR. -/
@[inline] def ternaryResult {α : Type}
    (narResult : α)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → α)
    (left right third : Option FloatLib.Numerics.Dyadic) : α :=
  match left, right, third with
  | some leftValue, some rightValue, some thirdValue =>
      operation leftValue rightValue thirdValue
  | _, _, _ => narResult

/-- Apply a finite unary code kernel, returning `narCode` for NaR. -/
@[inline] def unaryCode
    (narCode : Nat)
    (operation : FloatLib.Numerics.Dyadic → Nat)
    (value : Option FloatLib.Numerics.Dyadic) : Nat :=
  unaryResult narCode operation value

/-- Apply a finite binary code kernel, returning `narCode` if either input is NaR. -/
@[inline] def binaryCode
    (narCode : Nat)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Nat)
    (left right : Option FloatLib.Numerics.Dyadic) : Nat :=
  binaryResult narCode operation left right

/-- Apply a finite ternary code kernel, returning `narCode` if any input is NaR. -/
@[inline] def ternaryCode
    (narCode : Nat)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → Nat)
    (left right third : Option FloatLib.Numerics.Dyadic) : Nat :=
  ternaryResult narCode operation left right third

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.Boundary
