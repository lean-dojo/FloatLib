/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime

/-!
# Native-word comparison of exact dyadic fields

Fixed-width numerical formats frequently decode a finite value to a machine-word significand and
an unbounded exponent. Converting that significand to `Nat` before every candidate comparison is
unnecessary when the one required alignment shift still fits in a word.

The recognizer is representation-independent:

* execute the comparison with `UInt64` shifts when the aligned operand provably fits;
* otherwise call the arbitrary-precision exact comparator.

The arbitrary-precision branch is part of the algorithm, not an exceptional or unverified path.
Consequently every format can reuse this primitive. Significand alignment and comparison use
native words whenever the capacity guards hold. The refinement theorem lives in
`DyadicCompare.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.DyadicCompare

/--
Whether shifting a nonnegative word significand left by `shift` preserves its exact value.

For a nonzero word, `log2 + shift < 64` is precisely the capacity condition needed by the native
left shift. The proposition is decidable from machine-word data; its proof is erased after
compilation.
-/
@[inline] def shiftFits (significand : UInt64) (shift : Nat) : Prop :=
  significand = 0 ∨ (log2Word significand).toNat + shift < 64

instance (significand : UInt64) (shift : Nat) :
    Decidable (shiftFits significand shift) := by
  unfold shiftFits
  infer_instance

/--
Whether shifting a two-limb significand left by `shift` preserves its exact value.

For a nonzero significand, `log2 + shift < 128` ensures that the shifted value fits in two limbs.
The proof argument is erased after compilation.
-/
@[inline] def shiftFits128 (significand : UInt128) (shift : Nat) : Prop :=
  significand = ⟨0, 0⟩ ∨ UInt128.log2 significand + shift < 128

instance (significand : UInt128) (shift : Nat) :
    Decidable (shiftFits128 significand shift) := by
  unfold shiftFits128
  infer_instance

/--
Compare two nonnegative exact dyadics whose significands are native words.

Only the operand with the larger dyadic exponent needs alignment. If that shift stays within one
word, significand alignment and comparison use native operations. Large exponent gaps and
over-wide aligned values use the exact `Nat` implementation; exponent arithmetic uses `Int`.
-/
@[inline] def compareNonnegative
    (leftSignificand : UInt64) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) : Ordering :=
  if leftSignificand == 0 && rightSignificand == 0 then
    .eq
  else if leftExponent ≤ rightExponent then
    let shift := Int.toNat (rightExponent - leftExponent)
    if _hshift : shift < 64 then
      if _hfit : shiftFits rightSignificand shift then
        Ord.compare leftSignificand
          (rightSignificand <<< UInt64.ofNat shift)
      else
        Dyadic.compareNonnegativeFields
          leftSignificand.toNat leftExponent
          rightSignificand.toNat rightExponent
    else
      Dyadic.compareNonnegativeFields
        leftSignificand.toNat leftExponent
        rightSignificand.toNat rightExponent
  else
    let shift := Int.toNat (leftExponent - rightExponent)
    if _hshift : shift < 64 then
      if _hfit : shiftFits leftSignificand shift then
        Ord.compare
          (leftSignificand <<< UInt64.ofNat shift)
          rightSignificand
      else
        Dyadic.compareNonnegativeFields
          leftSignificand.toNat leftExponent
          rightSignificand.toNat rightExponent
    else
      Dyadic.compareNonnegativeFields
        leftSignificand.toNat leftExponent
        rightSignificand.toNat rightExponent

/--
Compare a nonnegative two-word dyadic with a nonnegative one-word dyadic.

Values whose high limb is zero reuse `compareNonnegative`. For a nonzero high limb in the left
significand, the only possible alignment into the wider carrier is a shift of the right word.
The leading-bit capacity test recognizes exactly when that shift fits in 128 bits. If it does not
fit, the shifted right operand is necessarily larger than every `UInt128`; if the left exponent
is larger, the already-wide left operand is necessarily larger than the word target. Thus the
wide path keeps significands in fixed limbs. Exponent arithmetic still uses `Int`.
-/
@[inline] def compareNonnegative128ToWord
    (leftSignificand : UInt128) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) : Ordering :=
  if leftSignificand.hi == 0 then
    compareNonnegative leftSignificand.lo leftExponent
      rightSignificand rightExponent
  else if rightSignificand == 0 then
    .gt
  else if leftExponent ≤ rightExponent then
    let shift := Int.toNat (rightExponent - leftExponent)
    if _hshift : shift < 128 then
      if _hfit : (log2Word rightSignificand).toNat + shift < 128 then
        UInt128.compare leftSignificand
          (UInt128.shiftLeft { hi := 0, lo := rightSignificand } shift)
      else
        .lt
    else
      .lt
  else
    .gt

/--
Test whether a nonnegative word dyadic is strictly below an integral power of two.

For a nonzero significand, `exponent + log2 significand` is the exponent of its leading bit.
Comparing that scalar exponent avoids both alignment shifts and the arbitrary-precision branch
that a generic dyadic comparison needs when the exponent gap exceeds one machine word.
-/
@[inline] def isLessPowerOfTwo
    (significand : UInt64) (exponent power : Int) : Bool :=
  if significand == 0 then
    true
  else
    decide (exponent + Int.ofNat (log2Word significand).toNat < power)

/-- Strict comparison derived from the shared native-word ordering primitive. -/
@[inline] def isLessNonnegative
    (leftSignificand : UInt64) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) : Bool :=
  compareNonnegative leftSignificand leftExponent
      rightSignificand rightExponent == .lt

/-- Non-strict comparison derived by reversing the native-word strict comparison. -/
@[inline] def isLessOrEqualNonnegative
    (leftSignificand : UInt64) (leftExponent : Int)
    (rightSignificand : UInt64) (rightExponent : Int) : Bool :=
  !isLessNonnegative rightSignificand rightExponent
    leftSignificand leftExponent

end FloatLib.Numerics.FixedWord.DyadicCompare
