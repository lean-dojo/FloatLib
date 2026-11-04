/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.RoundTrip

/-!
# Exact widening of posit words

You widen a posit by appending zero bits, and as long as the destination is at least as wide as
the source, the decoded value doesn't change, zero and `NaR` included. So for a finite input,
rounding the exact source value at the destination gives back that extended word.

All the proof does is iterate the decoder's one-bit precision identity. Neither the storage backend
nor any particular width enters the argument.

## References

* [Posit Standard (2022)](https://posithub.org/docs/posit_standard-2.pdf), §6.1.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

private theorem format_eq_of_bits_eq {a b : Format} (h : a.bits = b.bits) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem modulus_mul_width (source target : Format) (hw : source.bits ≤ target.bits) :
    target.modulus = source.modulus * 2 ^ (target.bits - source.bits) := by
  simp only [Format.modulus, ← pow_add, Nat.add_sub_of_le hw]

private theorem signMask_mul_width (source target : Format) (hw : source.bits ≤ target.bits) :
    target.signMaskNat = source.signMaskNat * 2 ^ (target.bits - source.bits) := by
  simp only [Format.signMaskNat, Format.signIndex, ← pow_add]
  congr 1
  have := source.bits_ge_two
  omega

/-- The posit format with `extra` more bits than `source`. -/
private def widened (source : Format) (extra : Nat) : Format where
  bits := source.bits + extra
  bits_ge_two := by have := source.bits_ge_two; omega

private theorem nonnegativeRatAt_add_width (source : Format) (extra : Nat)
    {code : Nat} (hc : code < source.signMaskNat) :
    nonnegativeRatAt (widened source extra) (code * 2 ^ extra) =
      nonnegativeRatAt source code := by
  induction extra with
  | zero =>
      have hf : widened source 0 = source := format_eq_of_bits_eq rfl
      simp only [hf, pow_zero, Nat.mul_one]
  | succ extra ih =>
      let f := widened source extra
      have hf : widened source (extra + 1) = f.nextPrecision :=
        format_eq_of_bits_eq (by simp [f, widened, Format.nextPrecision, Nat.add_assoc])
      have hm : f.signMaskNat = source.signMaskNat * 2 ^ extra := by
        simpa [f, widened] using signMask_mul_width source f (by simp [f, widened])
      have hb : code * 2 ^ extra < f.signMaskNat := by
        rw [hm]
        exact Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos extra)
      rw [hf, pow_succ, show code * (2 ^ extra * 2) = 2 * (code * 2 ^ extra) by
          simp [Nat.mul_comm, Nat.mul_left_comm],
        nonnegativeRatAt_nextPrecision_two_mul f hb]
      exact ih

/-- Any number of appended zero bits preserves a nonnegative finite decoded value. -/
theorem nonnegativeRatAt_widen (source target : Format) (hwidth : source.bits ≤ target.bits)
    {code : Nat} (hcode : code < source.signMaskNat) :
    nonnegativeRatAt target (code * 2 ^ (target.bits - source.bits)) =
      nonnegativeRatAt source code := by
  have hf : widened source (target.bits - source.bits) = target :=
    format_eq_of_bits_eq (show source.bits + (target.bits - source.bits) = target.bits by omega)
  simpa only [hf] using nonnegativeRatAt_add_width source (target.bits - source.bits) hcode

/-- Zero-bit extension preserves exact decoding for every word, including negative values and NaR. -/
theorem toRat?_widen {source : Format} (target : Format) (hw : source.bits ≤ target.bits)
    (value : Model source) :
    (ofNatBits (format := target)
      (value.toNatBits * 2 ^ (target.bits - source.bits))).toRat? = value.toRat? := by
  let factor := 2 ^ (target.bits - source.bits)
  have hp : 0 < factor := Nat.two_pow_pos _
  have hm : target.modulus = source.modulus * factor := modulus_mul_width source target hw
  have hs : target.signMaskNat = source.signMaskNat * factor := signMask_mul_width source target hw
  let wide : Model target := ofNatBits (value.toNatBits * factor)
  have hc : wide.toNatBits = value.toNatBits * factor := by
    apply toNatBits_ofNatBits_of_lt
    rw [hm]
    exact Nat.mul_lt_mul_of_pos_right value.toNatBits_lt_modulus hp
  by_cases hn : value = nar source
  · subst value
    have hwid : wide = nar target := by
      dsimp [wide]
      rw [nar_toNatBits, ← hs]
      rfl
    change wide.toRat? = _
    simp only [hwid, toRat?_nar]
  have hwide : wide ≠ nar target := by
    intro h
    have he := congrArg toNatBits h
    rw [hc, nar_toNatBits, hs] at he
    exact hn ((toNatBits_eq_signMaskNat_iff value).1 (Nat.eq_of_mul_eq_mul_right hp he))
  have hsign : wide.signBit = value.signBit := by
    simp only [signBit_eq_decide, hc, hs, Nat.mul_le_mul_right_iff hp]
  have hmag : wide.magnitudeBits = value.magnitudeBits * factor := by
    simp only [magnitudeBits, hsign, hc, hm]
    split <;> simp [Nat.sub_mul]
  change wide.toRat? = value.toRat?
  rw [toRat?_eq_signed_magnitude wide hwide, toRat?_eq_signed_magnitude value hn,
    hsign, hmag, nonnegativeRatAt_widen source target hw
      (magnitudeBits_lt_signMask_of_ne_nar value hn)]

/-- Rounding a finite value into a wider descriptor just appends the additional zero bits. -/
theorem roundRat_widen {source : Format} (target : Format) (hw : source.bits ≤ target.bits)
    (value : Model source) (q : Rat) (hq : value.toRat? = some q) :
    roundRat target q =
      ofNatBits (value.toNatBits * 2 ^ (target.bits - source.bits)) := by
  apply roundRat_toRat?
  rw [toRat?_widen target hw value, hq]

end FloatLib.Floats.Formats.Posit.Model
