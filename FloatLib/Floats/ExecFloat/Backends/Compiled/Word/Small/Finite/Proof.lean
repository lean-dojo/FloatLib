/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Compiled.Word.Small.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Compiled.Word.Small.Finite.Runtime

import FloatLib.Floats.ExecFloat.Backends.Compiled.Generic.Sqrt.Proof
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Correctness of native finite decoding for one-word formats

The decoder in `Finite.Runtime` extracts the same sign, significand, and stored exponent as the
format-generic decoder, and addition, fused multiply-add, and positive square root then reuse the
corresponding component kernels. With this bridge in one place, no operation proof has to deal with
storage masks and field shifts. Runtime imports stay small, and the later refinements reason about
exact dyadics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordFinite

open NativeSmallWord

/-- Native one-word decoding equals the width-generic compact decoder. -/
theorem decode_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x : Model fmt) :
    decode? x = FiniteKernel.decode? x := by
  rcases heligible with ⟨hieee, hwidth⟩
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  let fraction := NativeSmallWord.fractionField fmt bits
  let allOnes := NativeSmallWord.exponentMask fmt
  have hexponent :
      exponent.toNat = Model.expField x := by
    simpa [exponent, bits] using
      NativeSmallWord.exponentField_toNat hwidth x
  have hfraction :
      fraction.toNat = Model.fracField x := by
    simpa [fraction, bits] using
      NativeSmallWord.fractionField_toNat hwidth x
  have hallOnes :
      allOnes.toNat = fmt.expAllOnesNat := by
    simpa [allOnes] using
      NativeSmallWord.exponentMask_toNat (fmt := fmt) hwidth
  have hsign :
      NativeSmallWord.signField fmt bits = Model.signBit x := by
    simpa [bits] using NativeSmallWord.signField_eq hwidth x
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hnonfinite :
      (!Model.isFinite x) =
        (Model.expField x == fmt.expAllOnesNat) := by
    simp [Model.isFinite, hencoding, Model.IEEE.isFinite, bne]
  unfold decode? FiniteKernel.decode?
  dsimp only
  rw [hnonfinite]
  change
    (if exponent == allOnes then
        (none : Option FiniteKernel.Components)
      else
        some {
          sign := NativeSmallWord.signField fmt bits
          exponent := exponent.toNat
          mantissa := (finiteMantissa fmt exponent fraction).toNat }) =
      if Model.expField x == fmt.expAllOnesNat then
        (none : Option FiniteKernel.Components)
      else
        some {
          sign := Model.signBit x
          exponent := Model.expField x
          mantissa :=
            if Model.expField x == 0 then
              Model.fracField x
            else
              Model.pow2 fmt.fracWidth + Model.fracField x }
  by_cases hexceptional : exponent = allOnes
  · have hgenericExceptional : Model.expField x = fmt.expAllOnesNat :=
      (exponentField_eq_exponentMask_iff hwidth x).mp hexceptional
    simp [hexceptional, hgenericExceptional]
  · have hgenericFinite : Model.expField x ≠ fmt.expAllOnesNat :=
      fun h => hexceptional ((exponentField_eq_exponentMask_iff hwidth x).mpr h)
    have hgenericAllOnesPositive : 0 < fmt.expAllOnesNat := by
      unfold FloatFormat.expAllOnesNat
      have hpow : 1 < 2 ^ fmt.expWidth :=
        Nat.one_lt_two_pow (by
          have hwidth := fmt.expWidth_ge_two
          omega)
      omega
    have hallOnesNonzero : allOnes ≠ 0 := by
      intro h
      have hnat := congrArg UInt64.toNat h
      rw [hallOnes] at hnat
      simp only [UInt64.toNat_zero] at hnat
      omega
    by_cases hexponentZero : exponent = 0
    · have hgenericZero :
          Model.expField x = 0 := by
        rw [← hexponent, hexponentZero]
        rfl
      have hzeroAllOnes : (0 : UInt64) ≠ allOnes :=
        Ne.symm hallOnesNonzero
      have hzeroGenericAllOnes : 0 ≠ fmt.expAllOnesNat :=
        (Nat.ne_of_gt hgenericAllOnesPositive).symm
      simp [hexponentZero, hgenericZero, hzeroAllOnes,
        hzeroGenericAllOnes, hfraction, hsign, finiteMantissa]
    · have hgenericNonzero :
          Model.expField x ≠ 0 := by
        intro h
        apply hexponentZero
        apply UInt64.toNat_inj.mp
        rw [hexponent]
        exact h
      have hmantissa :
          (finiteMantissa fmt exponent fraction).toNat =
            2 ^ fmt.fracWidth + Model.fracField x := by
        simpa [finiteMantissa, hexponentZero, exponent, fraction, bits] using
          NativeSmallWord.normalMantissa_toNat hwidth x
      rw [hsign, hexponent, hmantissa]
      simp [hexceptional, hgenericFinite, hgenericNonzero,
        Model.pow2_eq_two_pow]

/--
Native-storage finite addition equals the generic compact finite kernel.

The runtime calls the compiled `Internal.addComponents`, and `Internal.addComponents_eq`
identifies it with the exact `addComponents` behind `FiniteKernel.add?`.
-/
theorem addFinite_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x y : Model fmt) :
    addFinite? x y = FiniteKernel.add? x y := by
  unfold addFinite? FiniteKernel.add?
  rw [decode_eq heligible x, decode_eq heligible y]
  cases FiniteKernel.decode? x <;> cases FiniteKernel.decode? y <;>
    simp [FiniteKernel.Internal.addComponents_eq]

private theorem internal_fmaComponents_eq_of_zero
    {fmt : FloatFormat} (hieee : fmt.isIEEE = true)
    (x y dz : FiniteKernel.Components) (z : Model fmt)
    (hdz : FiniteKernel.decode? z = some dz)
    (hzero : x.mantissa = 0 ∨ y.mantissa = 0)
    (hnonzero : dz.mantissa ≠ 0) :
    FiniteKernel.Internal.fmaComponents fmt x y dz = z := by
  have hdyadic : toDyadic? z = some (dz.toDyadic fmt) := by
    rw [FiniteKernel.toDyadic_eq_decode, hdz]
    rfl
  have hproduct : x.mantissa * y.mantissa = 0 := Nat.mul_eq_zero.mpr hzero
  have hsum :
      addDyadic (FiniteKernel.productDyadic fmt x y) (dz.toDyadic fmt) =
        dz.toDyadic fmt := by
    simp [FiniteKernel.productDyadic, addDyadic, Numerics.Dyadic.add,
      Numerics.Dyadic.addFields, FiniteKernel.Components.toDyadic,
      hproduct, hnonzero]
  rw [FiniteKernel.Internal.fmaComponents_eq, FiniteKernel.fmaComponents, hsum,
    ← roundDyadic_eq_internal]
  exact Internal.Directed.roundDyadic_toDyadic? hieee .nearest hdyadic

/-- Native-storage finite FMA, including the exact zero-product exit, equals the generic kernel. -/
theorem fmaFinite_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x y z : Model fmt) :
    fmaFinite? x y z = FiniteKernel.fma? x y z := by
  unfold fmaFinite? FiniteKernel.fma?
  rw [decode_eq heligible x, decode_eq heligible y, decode_eq heligible z]
  cases hx : FiniteKernel.decode? x <;> cases hy : FiniteKernel.decode? y <;>
    cases hz : FiniteKernel.decode? z <;> simp only
  rename_i dx dy dz
  split
  · next hzero =>
      have hzero : (dx.mantissa = 0 ∨ dy.mantissa = 0) ∧ dz.mantissa ≠ 0 := by
        simpa only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] using hzero
      rw [← internal_fmaComponents_eq_of_zero heligible.1 dx dy dz z hz hzero.1 hzero.2,
        FiniteKernel.Internal.fmaComponents_eq]
  · rw [FiniteKernel.Internal.fmaComponents_eq]

/-- Native-storage positive square root equals the generic compact finite kernel. -/
theorem sqrtPositive_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x : Model fmt) :
    sqrtPositive? x = FiniteSqrt.sqrtPositive? x := by
  unfold sqrtPositive? FiniteSqrt.sqrtPositive?
  rw [decode_eq heligible x]
  rfl

/--
The unchecked one-word positive square-root kernel agrees with the proof-guided generic kernel.
-/
theorem sqrtPositive_eq_runtime {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hpositive : signBit x = false) :
    sqrtPositive heligible x hfinite hnonzero hpositive =
      FiniteSqrt.sqrtPositiveRuntime x hfinite hnonzero hpositive := by
  rcases heligible with ⟨hieee, hwidth⟩
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  let fraction := NativeSmallWord.fractionField fmt bits
  let mantissa := finiteMantissa fmt exponent fraction
  let components : FiniteKernel.Components := {
    sign := NativeSmallWord.signField fmt bits
    exponent := exponent.toNat
    mantissa := mantissa.toNat }
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hfieldFinite :
      expField x ≠ FloatFormat.expAllOnesNat fmt := by
    simpa [isFinite, hencoding, IEEE.isFinite] using hfinite
  have hexceptional : exponent ≠ NativeSmallWord.exponentMask fmt :=
    fun heq => hfieldFinite ((exponentField_eq_exponentMask_iff hwidth x).mp heq)
  have hnativeDecode :
      decode? x = some components := by
    unfold decode?
    dsimp only
    rw [ite_eq_right (by simpa only [beq_iff_eq] using hexceptional)]
  have hgenericDecode :
      FiniteKernel.decode? x = some components :=
    (decode_eq ⟨hieee, hwidth⟩ x).symm.trans hnativeDecode
  have hdyadic :
      toDyadic? x = some (components.toDyadic fmt) := by
    rw [FiniteKernel.toDyadic_eq_decode, hgenericDecode]
    rfl
  have hmantissa : components.mantissa ≠ 0 := by
    intro hzero
    have hzeroSource :=
      isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdyadic (by
        simpa using hzero)
    rw [hnonzero] at hzeroSource
    contradiction
  have hvalue :
      finiteDyadic x hfinite = components.toDyadic fmt :=
    finiteDyadic_eq_of_toDyadic hfinite hdyadic
  rw [FiniteSqrt.sqrtPositiveRuntime_eq_finiteDyadic]
  unfold sqrtPositive
  simp only
  rw [hvalue]
  simp [components, mantissa, exponent, fraction, bits, hmantissa,
    FiniteKernel.Components.toDyadic_exp_of_mantissa_ne_zero]

end Model.NativeSmallWordFinite
namespace Model.NativeSmallWordAdd

open NativeSmallWord

/-! ## Storage-word decoding -/

/-- The generic finite decoder sees the fields the one-word kernel extracts from a finite word. -/
theorem decode_of_finite {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true) (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt)
    (hfinite : exponentField fmt (toWord x) ≠ exponentMask fmt) :
    FiniteKernel.decode? x =
      some {
        sign := signField fmt (toWord x)
        exponent := (exponentField fmt (toWord x)).toNat
        mantissa :=
          (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
            (fractionField fmt (toWord x))).toNat } := by
  rw [← NativeSmallWordFinite.decode_eq ⟨hieee, hwidth⟩ x]
  unfold NativeSmallWordFinite.decode?
  simp only [beq_iff_eq, hfinite, ite_false]

/-- Negating a finite word keeps its exponent and fraction fields and toggles its sign. -/
theorem decode_neg_of_finite {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true) (hwidth : fmt.bitWidth ≤ 64)
    (y : Model fmt)
    (hfinite : exponentField fmt (toWord y) ≠ exponentMask fmt) :
    FiniteKernel.decode? (neg y) =
      some {
        sign := !signField fmt (toWord y)
        exponent := (exponentField fmt (toWord y)).toNat
        mantissa :=
          (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord y))
            (fractionField fmt (toWord y))).toNat } := by
  have hexponent : exponentField fmt (toWord (neg y)) = exponentField fmt (toWord y) := by
    apply UInt64.toNat_inj.mp
    rw [exponentField_toNat hwidth, exponentField_toNat hwidth, expField_neg]
  have hfraction : fractionField fmt (toWord (neg y)) = fractionField fmt (toWord y) := by
    apply UInt64.toNat_inj.mp
    rw [fractionField_toNat hwidth, fractionField_toNat hwidth, fracField_neg]
  have hsign : signField fmt (toWord (neg y)) = !signField fmt (toWord y) := by
    rw [signField_eq hwidth, signField_eq hwidth, signBit_neg,
      ite_eq_left (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hieee)]
  rw [decode_of_finite hieee hwidth (neg y) (by rwa [hexponent]), hexponent, hfraction, hsign]

/-- The exponent field of a one-word value is a stored exponent. -/
theorem exponentField_toNat_lt {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (exponentField fmt (toWord x)).toNat < 2 ^ fmt.expWidth := by
  rw [exponentField_toNat hwidth]
  exact Model.expField_lt_pow2 x

/-- The finite significand of a one-word value has at most `fracWidth + 1` bits. -/
theorem finiteMantissa_toNat_lt {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (NativeSmallWordFinite.finiteMantissa fmt (exponentField fmt (toWord x))
      (fractionField fmt (toWord x))).toNat < 2 ^ (fmt.fracWidth + 1) := by
  unfold NativeSmallWordFinite.finiteMantissa
  split
  · rw [fractionField_toNat hwidth]
    exact (Model.fracField_lt_pow2 x).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  · exact (normalMantissa_bounds_of_width hwidth x).2

end Model.NativeSmallWordAdd
end FloatLib.Floats.Formats.BinaryInterchange
