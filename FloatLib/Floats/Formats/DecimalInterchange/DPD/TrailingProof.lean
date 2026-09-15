/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Trailing
public import FloatLib.Floats.Formats.DecimalInterchange.DPD.DecletProof

/-!
# DPD trailing-field bounds and round trips

Packing `groups` declets produces a value below `1024 ^ groups`; decoding produces a coefficient
below `1000 ^ groups`. Encoding then decoding recovers every coefficient within that bound, and
canonicalization preserves the decoded trailing coefficient.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

theorem encodeTrailing_lt (groups n : Nat) : encodeTrailing groups n < 1024 ^ groups := by
  induction groups generalizing n with
  | zero => simp [encodeTrailing]
  | succ groups ih =>
    have hd := encodeDeclet_lt (n % 1000)
    have ht := ih (n / 1000)
    simp only [encodeTrailing, Nat.pow_succ]
    omega

theorem decodeTrailing_lt (groups n : Nat) : decodeTrailing groups n < 1000 ^ groups := by
  induction groups generalizing n with
  | zero => simp [decodeTrailing]
  | succ groups ih =>
    have hd := decodeDeclet_lt (n % 1024)
    have ht := ih (n / 1024)
    simp only [decodeTrailing, Nat.pow_succ]
    omega

/-- Packing followed by unpacking preserves every trailing decimal digit. -/
theorem decodeTrailing_encodeTrailing (groups n : Nat) (h : n < 1000 ^ groups) :
    decodeTrailing groups (encodeTrailing groups n) = n := by
  induction groups generalizing n with
  | zero => simp only [Nat.pow_zero] at h; simp [decodeTrailing, show n = 0 by omega]
  | succ groups ih =>
    have hd := encodeDeclet_lt (n % 1000)
    have ht : n / 1000 < 1000 ^ groups := by
      simp only [Nat.pow_succ] at h
      omega
    simp only [encodeTrailing, decodeTrailing, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hd, Nat.add_mul_div_left _ _ (by decide : 0 < 1024),
      Nat.div_eq_of_lt hd, Nat.zero_add, decodeDeclet_encodeDeclet _ (Nat.mod_lt _ (by decide)),
      ih _ ht]
    omega

/-- Canonicalizing redundant declets preserves the complete trailing coefficient. -/
theorem decodeTrailing_canonicalize (groups n : Nat) :
    decodeTrailing groups (encodeTrailing groups (decodeTrailing groups n)) =
      decodeTrailing groups n :=
  decodeTrailing_encodeTrailing _ _ (decodeTrailing_lt _ _)

end FloatLib.Floats.Formats.DecimalInterchange.DPD
