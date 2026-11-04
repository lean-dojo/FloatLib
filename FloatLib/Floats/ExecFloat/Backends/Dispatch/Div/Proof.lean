/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Div.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Div.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Division.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Division.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Division
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Agreement
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Division.Proof
/-!
# Correctness of division backends

`word_eq_spec` identifies the complete dispatcher with `Spec.div` for every descriptor and operand
pair, with rounding, signed zeros, infinities, and NaNs included. Each specialized kernel is a
refinement on the inputs it accepts, and when an operand or intermediate lies outside a kernel's
supported domain, the dispatcher uses `generic`, which is correct by `generic_eq_spec`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace DivBackend

/-- Compact generic division equals the exact-dyadic `Spec.div` on every input. -/
theorem generic_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    generic x y = Spec.div x y := by
  unfold generic Spec.div
  rw [FiniteKernel.divRuntime_eq, FiniteKernel.div_eq_spec]
  cases hx : toDyadic? x with
  | none => simp
  | some dx =>
    cases hy : toDyadic? y with
      | none => simp
      | some dy =>
          by_cases hyZero : dy.significand = 0
          · simp [hyZero]
          by_cases hxZero : dx.significand = 0 <;>
            simp [hyZero, hxZero]

/-- A quotient that the finite kernel accepts is the specification quotient. -/
private theorem eq_spec_of_finite {fmt : FloatFormat} {x y quotient : Model fmt}
    (hfinite : FiniteKernel.div? x y = some quotient) : quotient = Spec.div x y := by
  simpa [generic, FiniteKernel.divRuntime_eq, hfinite] using generic_eq_spec x y

/--
A kernel whose accepted quotients the finite kernel also returns, backed by a fallback equal to
`Spec.div` for the inputs it declines, computes `Spec.div`.
-/
private theorem fallback_eq_spec {fmt : FloatFormat} {x y fallback : Model fmt}
    {fast : Option (Model fmt)}
    (hfast : ∀ quotient, fast = some quotient → FiniteKernel.div? x y = some quotient)
    (hfallback : fallback = Spec.div x y) :
    (match (generalizing := false) fast with
      | some quotient => quotient
      | none => fallback) = Spec.div x y := by
  cases fast with
  | none => exact hfallback
  | some quotient => exact eq_spec_of_finite (hfast quotient rfl)

/--
Structurally selected specialized dispatch equals `Spec.div` for every descriptor and on every
input, exceptional values included.
-/
theorem word_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    word x y = Spec.div x y := by
  unfold word
  split
  · rename_i h32
    have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    simp [Spec.div, NativeBinary32.divFiniteWord_eq, NativeBinary32.divFinite_eq,
      generic_eq_spec]
    cases hx : toDyadic? x <;>
      cases hy : toDyadic? y <;>
      simp_all
  split
  · rename_i h64
    have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    subst fmt
    dsimp only
    split
    · rename_i quotient hquotient
      exact eq_spec_of_finite (by
        simpa [NativeBinary64.divFinite_eq_divFiniteComponents,
          NativeBinary64.divFiniteComponents_eq] using hquotient)
    · exact generic_eq_spec x y
  split
  · exact fallback_eq_spec (NativePair.divNormal_refines ‹_› x y) (generic_eq_spec x y)
  split
  · exact fallback_eq_spec (NativeSmallWordDiv.divNormal_refines_of_storage ‹_› x y)
      (generic_eq_spec x y)
  · exact generic_eq_spec x y

end DivBackend

end Model

end FloatLib.Floats.Formats.BinaryInterchange
