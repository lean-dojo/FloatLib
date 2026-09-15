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

`word_eq_spec` identifies the complete dispatcher with `Spec.div` for every descriptor and
operand pair. The equality includes rounding, signed zeros, infinities, and NaNs.

The specialized kernels provide refinements on their accepted inputs. When an operand or
intermediate lies outside a kernel's supported domain, the dispatcher uses `generic`, whose
correctness is established by `generic_eq_spec`. Runtime clients can import `Div.Runtime`
separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace DivBackend

/-- Compact generic division preserves the public exact-dyadic operation. -/
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

/-- Structurally selected specialized dispatch preserves logical format-generic division. -/
private theorem spec_div_eq_word :
    @Spec.div = @word := by
  funext fmt x y
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    simp [word, Spec.div, NativeBinary32.divFiniteImpl_eq,
      NativeBinary32.divFinite_eq, generic_eq_spec]
    cases hx : toDyadic? x <;>
      cases hy : toDyadic? y <;>
      simp_all
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      cases hfinite : FiniteKernel.div? x y with
      | none =>
          simp [word, h32, NativeBinary64.divFiniteFastImpl_eq,
            NativeBinary64.divFiniteImpl_eq, hfinite, generic_eq_spec]
      | some quotient =>
          have hquotient : quotient = Spec.div x y := by
            simpa [generic, FiniteKernel.divRuntime_eq, hfinite] using
              generic_eq_spec x y
          simp [word, h32, NativeBinary64.divFiniteFastImpl_eq,
            NativeBinary64.divFiniteImpl_eq, hfinite, hquotient,
            generic_eq_spec]
    · by_cases hpair : NativePair.Eligible fmt
      · cases hfast : NativePair.divNormal? x y with
        | none =>
            simp [word, h32, h64, hpair, hfast, generic_eq_spec]
        | some quotient =>
            have hrefines :=
              NativePair.divNormal_refines hpair x y quotient hfast
            have hquotient : quotient = Spec.div x y := by
              calc
                quotient = generic x y := by
                  simp [generic, FiniteKernel.divRuntime_eq, hrefines]
                _ = Spec.div x y := generic_eq_spec x y
            simp [word, h32, h64, hpair, hfast, hquotient]
      · by_cases heligible : NativeSmallWord.Eligible fmt
        · cases hnative : NativeSmallWordDiv.divNormal? x y with
          | none =>
              simp [word, h32, h64, hpair, heligible, hnative,
                generic_eq_spec]
          | some quotient =>
              have hrefines :=
                NativeSmallWordDiv.divNormal_refines
                  heligible x y quotient hnative
              have hquotient : quotient = Spec.div x y := by
                calc
                  quotient = generic x y := by
                    simp [generic, FiniteKernel.divRuntime_eq, hrefines]
                  _ = Spec.div x y := generic_eq_spec x y
              simp [word, h32, h64, hpair, heligible, hnative, hquotient]
        · simp [word, generic_eq_spec, h32, h64, hpair, heligible]

/-- Structurally selected specialized dispatch preserves format-generic division. -/
theorem word_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    word x y = Spec.div x y :=
  (congrFun (congrFun (congrFun spec_div_eq_word fmt) x) y).symm

end DivBackend

end Model

end FloatLib.Floats.Formats.BinaryInterchange
