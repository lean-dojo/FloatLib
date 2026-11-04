/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Add.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Addition.Proof
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Agreement
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Addition.Proof

/-!
# Correctness of addition and subtraction backends

Addition can take several paths: generic exact arithmetic, the one-word `UInt64` kernel of
`NativeSmallWordAdd`, native small-word decoding into the compiled component kernel, binary32,
binary64, and fixed limbs. All of them refine the same format-generic `Spec.add` and `Spec.sub`.
Accepted specialized results agree with the finite kernel and declined paths use `generic`, and
together these refinements give `word_eq_spec` and `subWord_eq_spec` for every descriptor and
operand pair, exceptional values included.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace AddBackend

/-- Compact generic addition equals the exact-dyadic `Spec.add` on every input. -/
theorem generic_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    generic x y = Spec.add x y := by
  unfold generic Spec.add
  rw [FiniteKernel.addRuntime_eq, FiniteKernel.add_eq_spec]
  cases toDyadic? x <;>
    cases toDyadic? y <;>
    simp <;>
    rfl

/-- A sum that the finite kernel accepts is the specification sum. -/
private theorem eq_spec_of_finite {fmt : FloatFormat} {x y sum : Model fmt}
    (hfinite : FiniteKernel.add? x y = some sum) : sum = Spec.add x y := by
  simpa [generic, FiniteKernel.addRuntime_eq, hfinite] using generic_eq_spec x y

/--
A kernel whose accepted sums the finite kernel also returns, backed by a fallback equal to
`Spec.add` for the inputs it declines, computes `Spec.add`.

Subtraction uses it with the negated right operand, since `Spec.sub x y = Spec.add x (neg y)`.
-/
private theorem fallback_eq_spec {fmt : FloatFormat} {x y fallback : Model fmt}
    {fast : Option (Model fmt)}
    (hfast : ∀ sum, fast = some sum → FiniteKernel.add? x y = some sum)
    (hfallback : fallback = Spec.add x y) :
    (match (generalizing := false) fast with
      | some sum => sum
      | none => fallback) = Spec.add x y := by
  cases fast with
  | none => exact hfallback
  | some sum => exact eq_spec_of_finite (hfast sum rfl)

/--
Native fixed-format and reusable one-word dispatch equals `Spec.add` for every descriptor and on
every input, exceptional values included.
-/
theorem word_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    word x y = Spec.add x y := by
  unfold word
  split
  · rename_i h32
    have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    simp [Spec.add, NativeBinary32.addFiniteWord_eq, NativeBinary32.addFinite_eq,
      generic_eq_spec]
    cases hx : toDyadic? x <;>
      cases hy : toDyadic? y <;>
      simp_all
  split
  · rename_i h64
    have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    subst fmt
    refine fallback_eq_spec (fun sum hsum => by
      simpa using NativeSmallWordAdd.addFinite_refines (by decide) x y sum false hsum) ?_
    dsimp only
    split
    · rename_i sum hsum
      exact eq_spec_of_finite (by
        simpa [NativeBinary64.addFinite_eq_addFiniteComponents,
          NativeBinary64.addFiniteComponents_eq] using hsum)
    · exact generic_eq_spec x y
  split
  · exact fallback_eq_spec (fun sum hsum => by rwa [NativePair.addFinite_eq ‹_›] at hsum)
      (generic_eq_spec x y)
  split
  · exact fallback_eq_spec (fun sum hsum => by
      simpa using NativeSmallWordAdd.addFinite_refines ‹_› x y sum false hsum)
      (generic_eq_spec x y)
  split
  · exact fallback_eq_spec
      (fun sum hsum => by rwa [NativeSmallWordFinite.addFinite_eq ‹_›] at hsum)
      (generic_eq_spec x y)
  · exact generic_eq_spec x y

/--
Native fixed-format and reusable one-word dispatch equals `Spec.sub` for every descriptor and on
every input, exceptional values included.
-/
theorem subWord_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    subWord x y = Spec.sub x y := by
  unfold subWord Spec.sub
  split
  · rename_i h32
    have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    simp [Spec.add, NativeBinary32.addFiniteWord_eq, NativeBinary32.addFinite_eq,
      generic_eq_spec]
    cases hx : toDyadic? x <;>
      cases hy : toDyadic? (neg y) <;>
      simp_all
  split
  · rename_i h64
    have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    subst fmt
    refine fallback_eq_spec (fun difference hdifference => by
      simpa using
        NativeSmallWordAdd.addFinite_refines (by decide) x y difference true hdifference) ?_
    dsimp only
    split
    · rename_i difference hdifference
      exact eq_spec_of_finite (by
        simpa [NativeBinary64.subFinite_eq_addFiniteComponents_negate,
          NativeBinary64.addFiniteComponents_eq] using hdifference)
    · exact generic_eq_spec x (neg y)
  split
  · exact fallback_eq_spec
      (fun difference hdifference => by rwa [NativePair.subFinite_eq ‹_›] at hdifference)
      (generic_eq_spec x (neg y))
  split
  · exact fallback_eq_spec (fun difference hdifference => by
      simpa using NativeSmallWordAdd.addFinite_refines ‹_› x y difference true hdifference)
      (generic_eq_spec x (neg y))
  split
  · exact fallback_eq_spec (fun difference hdifference => by
      rwa [NativeSmallWordFinite.addFinite_eq ‹_›] at hdifference)
      (generic_eq_spec x (neg y))
  · exact generic_eq_spec x (neg y)

end AddBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
