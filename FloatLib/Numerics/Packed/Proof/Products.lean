/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Range
public import FloatLib.Numerics.Packed.Proof.Reverse

/-!
# Convolution and autocorrelation of packed signed rows

Products of guarded signed rows represent Cauchy convolution when the stated l1 headroom bound
holds. Combining multiplication with reversal gives autocorrelation under the same explicit
storage bounds.

A biased row `u` of `n` lanes below `2 ^ (w * n)` stands for the value of its entries. In the other
direction a list whose entries fit comes back out of its value, padded with zeros. A range check
then bounds every entry, and the bound is what makes a product readable. Take two rows of `n` and
`m` entries below `2 ^ gx` and `2 ^ gy`. Their `l1` norms are at most `n * 2 ^ gx` and
`m * 2 ^ gy`, so every entry of their Cauchy product is at most `n * 2 ^ gx * (m * 2 ^ gy)`. With
`n = m = 1000` and `gx = gy = 64`, that is below `2 ^ 148`, so lanes of `150` bits hold the
product.

## References

* Henry S. Warren, Jr., *Hacker's Delight*, second edition, Addison-Wesley (2013), chapter 2,
  whose multibyte addition adds several fields of one word at once,
  <https://www.informit.com/store/hackers-delight-9780321842688>.
* Randall J. Fisher and Henry G. Dietz, *Compiling for SIMD within a register*, LCPC 1998,
  LNCS 1656 (1999), 290–305, <https://doi.org/10.1007/3-540-48319-5_19>.

-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- The product of two guarded rows. If the entries of `u` lie in `[-2 ^ gx, 2 ^ gx)`, those of `v`
in `[-2 ^ gy, 2 ^ gy)`, and `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)`, then the biased row of the
product of their integers holds the Cauchy product of their entries. -/
theorem entries_mul {w gx gy n m u v : Nat} (hu : guard w gx n u = true)
    (hv : guard w gy m v = true) (hroom : n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)) (hn : 0 < n)
    (hm : 0 < m) :
    entries w (n + m - 1) (ofInt w (n + m - 1) (toInt w n u * toInt w m v)) =
      conv (entries w n u) (entries w m v) := by
  obtain ⟨hgw, hu', hbu⟩ := guard_sound hu
  obtain ⟨-, hv', hbv⟩ := guard_sound hv
  have hw : 1 ≤ w := by omega
  -- the product of the two integers is the value of the Cauchy product, by Kronecker
  rw [← eval_entries hw hu', ← eval_entries hw hv', ← eval_conv]
  -- and the headroom keeps its `l1` norm, so every entry, below the bias
  have hl1 : l1 (conv (entries w n u) (entries w m v)) < 2 ^ (w - 1) := by
    have h1 := l1_le_of_bound hbu
    have h2 := l1_le_of_bound hbv
    rw [length_entries] at h1 h2
    have := l1_conv_le (entries w n u) (entries w m v)
    have := Nat.mul_le_mul h1 h2
    omega
  have hlen : (conv (entries w n u) (entries w m v)).length = n + m - 1 := by
    rw [length_conv (List.length_pos_iff.mp (by rw [length_entries]; exact hm))
      (List.length_pos_iff.mp (by rw [length_entries]; exact hn)), length_entries, length_entries]
  rw [entries_ofInt_eval hw (Nat.le_of_eq hlen) (fits_of_l1_lt hl1), hlen, Nat.sub_self,
    List.replicate_zero, List.append_nil]

/-- The autocorrelation of a guarded row. If the entries of `u` lie in `[-2 ^ g, 2 ^ g)` and
`n * 2 ^ g * (n * 2 ^ g) < 2 ^ (w - 1)`, the `2 * n - 1` entries of `autocorr w n u` are those of
`x ⋆ reverse x` for the entries `x`; the middle one, entry `n - 1`, is `∑ j, x[j] ^ 2`. -/
theorem entries_autocorr {w g n u : Nat} (hu : guard w g n u = true)
    (hroom : n * 2 ^ g * (n * 2 ^ g) < 2 ^ (w - 1)) (hn : 0 < n) :
    entries w (2 * n - 1) (ofInt w (2 * n - 1) (autocorr w n u)) =
      conv (entries w n u) (entries w n u).reverse := by
  obtain ⟨hgw, hu', hbu⟩ := guard_sound hu
  have hw : 1 ≤ w := by omega
  rw [autocorr_eq hw hu']
  have hl1 : l1 (conv (entries w n u) (entries w n u).reverse) < 2 ^ (w - 1) := by
    have h1 := l1_le_of_bound hbu
    rw [length_entries] at h1
    have := l1_conv_le (entries w n u) (entries w n u).reverse
    rw [l1_reverse] at this
    have := Nat.mul_le_mul h1 h1
    omega
  have hne : entries w n u ≠ [] := List.length_pos_iff.mp (by rw [length_entries]; exact hn)
  have hlen : (conv (entries w n u) (entries w n u).reverse).length = 2 * n - 1 := by
    rw [length_conv (by simpa using hne) hne, List.length_reverse, length_entries]; omega
  rw [entries_ofInt_eval hw (Nat.le_of_eq hlen) (fits_of_l1_lt hl1), hlen, Nat.sub_self,
    List.replicate_zero, List.append_nil]

end FloatLib.Numerics.Packed
