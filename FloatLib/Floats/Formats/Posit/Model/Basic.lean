/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Descriptor

/-!
# Posit words and exceptional encodings

The exact-width posit carrier, zero, and Not-a-Real words. These definitions support storage,
equality, and bitwise reasoning. Regime parsing and finite decoding are defined in later modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

/-- Exact-width proof model for one posit descriptor. -/
structure Model (format : Format) where
  /-- Complete encoded word. -/
  bits : BitVec format.bits
  deriving DecidableEq, Repr

namespace Model

variable {format : Format}

/-- Wrap an exact-width bit vector. -/
@[inline] def ofBits (bits : BitVec format.bits) : Model format :=
  ⟨bits⟩

/-- Encode the low `format.bits` bits of a natural number. -/
@[inline] def ofNatBits (bits : Nat) : Model format :=
  ofBits (BitVec.ofNat format.bits bits)

/-- Read the complete encoded word as a natural number. -/
@[inline] def toNatBits (value : Model format) : Nat :=
  value.bits.toNat

/-- Every exact-width posit word lies below its descriptor's modulus. -/
theorem toNatBits_lt_modulus (value : Model format) :
    value.toNatBits < format.modulus := by
  change value.bits.toNat < 2 ^ format.bits
  exact BitVec.toNat_lt_twoPow_of_le (Nat.le_refl format.bits)

/-- Re-encoding a model's exact bit pattern preserves it. -/
@[simp] theorem ofNatBits_toNatBits (value : Model format) :
    ofNatBits value.toNatBits = value := by
  cases value with
  | mk bits =>
      apply congrArg ofBits
      change BitVec.ofNat format.bits bits.toNat = bits
      rw [BitVec.ofNat_toNat]
      simp

/-- In-range natural bits are unchanged by exact-width encoding. -/
@[simp] theorem toNatBits_ofNatBits_of_lt (bits : Nat)
    (hbits : bits < format.modulus) :
    (ofNatBits (format := format) bits).toNatBits = bits := by
  change (BitVec.ofNat format.bits bits).toNat = bits
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  simpa [Format.modulus] using hbits

instance : Inhabited (Model format) where
  default := ofNatBits 0

/-- The unique zero encoding. -/
@[inline] def zero (format : Format) : Model format :=
  ofNatBits 0

/-- The unique Not-a-Real encoding, `100...0`. -/
@[inline] def nar (format : Format) : Model format :=
  ofNatBits format.signMaskNat

/-- The unique zero value encodes as the all-zero word. -/
@[simp] theorem zero_toNatBits (format : Format) :
    (zero format).toNatBits = 0 := by
  apply toNatBits_ofNatBits_of_lt
  exact Nat.two_pow_pos format.bits

/-- The unique NaR value encodes as the word containing only the sign bit. -/
@[simp] theorem nar_toNatBits (format : Format) :
    (nar format).toNatBits = format.signMaskNat :=
  toNatBits_ofNatBits_of_lt _ format.signMaskNat_lt_modulus

/-- Zero and NaR are distinct for every valid posit width. -/
theorem zero_ne_nar (format : Format) : zero format ≠ nar format := by
  intro equality
  have bitsEquality := congrArg toNatBits equality
  simp only [zero_toNatBits, nar_toNatBits] at bitsEquality
  exact (Nat.ne_of_gt (Nat.two_pow_pos format.signIndex)) bitsEquality.symm

/-- Whether this is the unique zero code. -/
@[inline] def isZero (value : Model format) : Bool :=
  value == zero format

/-- Whether this is the unique Not-a-Real code. -/
@[inline] def isNaR (value : Model format) : Bool :=
  value == nar format

/-- The zero predicate recognizes the canonical zero value. -/
@[simp] theorem isZero_zero (format : Format) : isZero (zero format) = true := by
  simp [isZero]

/-- The NaR predicate recognizes the canonical NaR value. -/
@[simp] theorem isNaR_nar (format : Format) : isNaR (nar format) = true := by
  simp [isNaR]

/-- The canonical zero value is not NaR. -/
@[simp] theorem isNaR_zero (format : Format) : isNaR (zero format) = false := by
  simp [isNaR, zero_ne_nar]

/-- The canonical NaR value is not zero. -/
@[simp] theorem isZero_nar (format : Format) : isZero (nar format) = false := by
  apply beq_eq_false_iff_ne.mpr
  exact Ne.symm (zero_ne_nar format)

/-- The NaR predicate recognizes exactly the standard's unique NaR word. -/
@[simp] theorem isNaR_eq_true_iff (value : Model format) :
    value.isNaR = true ↔ value = nar format := by
  simp [isNaR]

/-- The zero predicate recognizes exactly the standard's unique zero word. -/
@[simp] theorem isZero_eq_true_iff (value : Model format) :
    value.isZero = true ↔ value = zero format := by
  simp [isZero]

end Model
end FloatLib.Floats.Formats.Posit
