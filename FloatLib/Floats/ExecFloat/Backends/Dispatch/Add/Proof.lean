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
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Subtraction.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Agreement
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Addition.Proof

/-!
# Correctness of addition and subtraction backends

The dispatcher has several execution paths: generic exact arithmetic, the one-word `UInt64`
kernel of `NativeSmallWordAdd`, native small-word decoding into the compiled component kernel,
binary32, binary64, and fixed limbs. They all refine the same format-generic `Spec.add` and
`Spec.sub`.

Accepted specialized results agree with the finite kernel; declined paths use `generic`.
Together, these refinements give `word_eq_spec` and `subWord_eq_spec` for every descriptor and
operand pair, including exceptional values. Runtime clients can import `Add.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace AddBackend

/-- Compact generic addition preserves the exact-dyadic specification. -/
theorem generic_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    generic x y = Spec.add x y := by
  unfold generic Spec.add
  rw [FiniteKernel.addRuntime_eq, FiniteKernel.add_eq_spec]
  cases toDyadic? x <;>
    cases toDyadic? y <;>
    simp <;>
    rfl

private theorem spec_add_eq_word :
    @Spec.add = @word := by
  funext fmt x y
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    simp [word, Spec.add, NativeBinary32.addFiniteImpl_eq,
      NativeBinary32.addFinite_eq, generic_eq_spec]
    cases hx : toDyadic? x <;>
      cases hy : toDyadic? y <;>
      simp_all
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      cases hnative : NativeSmallWordAdd.addFinite? x y false with
      | some sum =>
          have hfinite : FiniteKernel.add? x y = some sum := by
            simpa using
              NativeSmallWordAdd.addFinite_refines (by decide) x y sum false hnative
          have hsum : sum = Spec.add x y := by
            simpa [generic, FiniteKernel.addRuntime_eq, hfinite] using
              generic_eq_spec x y
          simp [word, h32, hnative, hsum]
      | none =>
          cases hfinite : FiniteKernel.add? x y with
          | none =>
              simp [word, h32, hnative, NativeBinary64.addFiniteFastImpl_eq,
                NativeBinary64.addFiniteImpl_eq, hfinite, generic_eq_spec]
          | some sum =>
              have hsum : sum = Spec.add x y := by
                simpa [generic, FiniteKernel.addRuntime_eq, hfinite] using
                  generic_eq_spec x y
              simp [word, h32, hnative, NativeBinary64.addFiniteFastImpl_eq,
                NativeBinary64.addFiniteImpl_eq, hfinite, hsum, generic_eq_spec]
    · by_cases hpair : NativePair.Eligible fmt
      · cases hfinite : FiniteKernel.add? x y with
        | none =>
            simp [word, h32, h64, hpair, NativePair.addFinite_eq hpair, hfinite,
              generic_eq_spec]
        | some sum =>
            have hsum : sum = Spec.add x y := by
              simpa [generic, FiniteKernel.addRuntime_eq, hfinite] using
                generic_eq_spec x y
            simp [word, h32, h64, hpair, NativePair.addFinite_eq hpair, hfinite,
              hsum]
      · by_cases heligible : NativeSmallWordAdd.Eligible fmt
        · cases hnative : NativeSmallWordAdd.addFinite? x y false with
          | none =>
              simp [word, h32, h64, hpair, heligible, hnative,
                generic_eq_spec]
          | some sum =>
              have hfinite : FiniteKernel.add? x y = some sum := by
                simpa using
                  NativeSmallWordAdd.addFinite_refines heligible x y sum false hnative
              have hsum : sum = Spec.add x y := by
                calc
                  sum = generic x y := by
                    simp [generic, FiniteKernel.addRuntime_eq, hfinite]
                  _ = Spec.add x y := generic_eq_spec x y
              simp [word, h32, h64, hpair, heligible, hnative, hsum]
        · by_cases hstorage : NativeSmallWord.StorageEligible fmt
          · cases hnative : NativeSmallWordFinite.addFinite? x y with
            | none =>
                simp [word, h32, h64, hpair, heligible, hstorage, hnative,
                  generic_eq_spec]
            | some sum =>
                have hfinite : FiniteKernel.add? x y = some sum := by
                  rw [← NativeSmallWordFinite.addFinite_eq hstorage]
                  exact hnative
                have hsum : sum = Spec.add x y := by
                  calc
                    sum = generic x y := by
                      simp [generic, FiniteKernel.addRuntime_eq, hfinite]
                    _ = Spec.add x y := generic_eq_spec x y
                simp [word, h32, h64, hpair, heligible, hstorage, hnative, hsum]
          · simp [word, generic_eq_spec, h32, h64, hpair, heligible, hstorage]

/-- Native fixed-format and reusable one-word dispatch preserves addition. -/
theorem word_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    word x y = Spec.add x y :=
  (congrFun (congrFun (congrFun spec_add_eq_word fmt) x) y).symm

private theorem spec_sub_eq_subWord :
    @Spec.sub = @subWord := by
  funext fmt x y
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    simp [subWord, Spec.sub, Spec.add, NativeBinary32.addFiniteImpl_eq,
      NativeBinary32.addFinite_eq, generic_eq_spec]
    cases hx : toDyadic? x <;>
      cases hy : toDyadic? (neg y) <;>
      simp_all
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      cases hnative : NativeSmallWordAdd.addFinite? x y true with
      | some difference =>
          have hfinite : FiniteKernel.add? x (neg y) = some difference := by
            simpa using
              NativeSmallWordAdd.addFinite_refines (by decide) x y difference true hnative
          have hdifference : difference = Spec.sub x y := by
            calc
              difference = generic x (neg y) := by
                simp [generic, FiniteKernel.addRuntime_eq, hfinite]
              _ = Spec.add x (neg y) := generic_eq_spec x (neg y)
              _ = Spec.sub x y := rfl
          simp [subWord, h32, hnative, hdifference]
      | none =>
          cases hfinite : FiniteKernel.add? x (neg y) with
          | none =>
              simp [subWord, Spec.sub, h32, hnative, NativeBinary64.subFiniteFastImpl_eq,
                NativeBinary64.addFiniteImpl_eq, hfinite, generic_eq_spec]
          | some difference =>
              have hdifference : difference = Spec.add x (neg y) := by
                simpa [generic, FiniteKernel.addRuntime_eq, hfinite] using
                  generic_eq_spec x (neg y)
              simp [subWord, Spec.sub, h32, hnative, NativeBinary64.subFiniteFastImpl_eq,
                NativeBinary64.addFiniteImpl_eq, hfinite, hdifference,
                generic_eq_spec]
    · by_cases hpair : NativePair.Eligible fmt
      · cases hfinite : FiniteKernel.add? x (neg y) with
        | none =>
            simp [subWord, Spec.sub, h32, h64, hpair, NativePair.subFinite_eq hpair,
              hfinite, generic_eq_spec]
        | some difference =>
            have hdifference : difference = Spec.add x (neg y) := by
              simpa [generic, FiniteKernel.addRuntime_eq, hfinite] using
                generic_eq_spec x (neg y)
            simp [subWord, Spec.sub, h32, h64, hpair, NativePair.subFinite_eq hpair,
              hfinite, hdifference]
      · by_cases heligible : NativeSmallWordAdd.Eligible fmt
        · cases hnative : NativeSmallWordAdd.addFinite? x y true with
          | none =>
              simp [subWord, Spec.sub, h32, h64, hpair, heligible, hnative,
                generic_eq_spec]
          | some difference =>
              have hfinite :
                  FiniteKernel.add? x (neg y) = some difference := by
                simpa using
                  NativeSmallWordAdd.addFinite_refines heligible x y difference true hnative
              have hdifference : difference = Spec.sub x y := by
                calc
                  difference = generic x (neg y) := by
                    simp [generic, FiniteKernel.addRuntime_eq, hfinite]
                  _ = Spec.add x (neg y) := generic_eq_spec x (neg y)
                  _ = Spec.sub x y := rfl
              simp [subWord, h32, h64, hpair, heligible, hnative, hdifference]
        · by_cases hstorage : NativeSmallWord.StorageEligible fmt
          · cases hnative : NativeSmallWordFinite.addFinite? x (neg y) with
            | none =>
                simp [subWord, Spec.sub, h32, h64, hpair, heligible, hstorage, hnative,
                  generic_eq_spec]
            | some difference =>
                have hfinite :
                    FiniteKernel.add? x (neg y) = some difference := by
                  rw [← NativeSmallWordFinite.addFinite_eq hstorage]
                  exact hnative
                have hdifference : difference = Spec.sub x y := by
                  calc
                    difference = generic x (neg y) := by
                      simp [generic, FiniteKernel.addRuntime_eq, hfinite]
                    _ = Spec.add x (neg y) := generic_eq_spec x (neg y)
                    _ = Spec.sub x y := rfl
                simp [subWord, h32, h64, hpair, heligible, hstorage, hnative, hdifference]
          · simp [subWord, Spec.sub, generic_eq_spec, h32, h64, hpair,
              heligible, hstorage]

/-- Native fixed-format and reusable one-word dispatch preserves subtraction. -/
theorem subWord_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    subWord x y = Spec.sub x y :=
  (congrFun (congrFun (congrFun spec_sub_eq_subWord fmt) x) y).symm

end AddBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange
