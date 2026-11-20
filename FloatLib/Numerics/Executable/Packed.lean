/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Conversion.Runtime
public import FloatLib.Util.Packed

/-!
# Packed rows of format values

A certificate about numbers that some program computed, such as the coefficients of a polynomial
in binary64, needs those numbers in a packed row. Every FloatLib value that has an exact rational
meaning decodes to it exactly through `ExactDecoder` and `ExactMap`: binary and decimal formats of
any width, the small ML formats, posits, fixed point, rationals and dyadics. A list of such values
with the common denominator `d` is an integer row divided by `d`, and `link w d vs u` checks in
the kernel that the biased row `u` of width `w` holds the decoded values `vs`, with the same
cross-multiplication `Packed.linked` that `interval` uses for coefficient bounds.

For example, the binary32 values `1.5`, `-0.25` and `3` are `6/4`, `-1/4` and `12/4`, so their
row is `[6, -1, 12]` with the denominator `4`.

## Main definitions

* `ExactLanes`: the exact lanes of a value, one for a scalar and one per position for a
  block-scaled tensor (the instance for `ExecFloat.Block`). A lane with no finite value, an
  infinity or a NaN, is `none`.
* `Packed.values xs`: the lanes of all the values in `xs`.
* `Packed.link w d vs u`: the kernel check that `u` holds `vs` at the denominator `d`.
* `packed_values r (width := w) := xs`: the command that decodes `xs` by kernel reduction, picks
  the least common denominator `d`, and adds the row `r` as a raw literal together with the theorem
  `r.link : link w d (values xs) r = true`, which the kernel checks once. It refuses a value with
  no finite meaning and an entry that does not fit.

## Main statements

* `Packed.link_sound`: what a passing `link` means. Every value is finite and is entry `k` of `u`
  divided by `d`, and `u` has no lanes beyond them.

## Implementation notes

The command reads the decoded values by kernel reduction, so it needs no compiled code and works
the same in a file that starts with `module`. In our measurements on Lean v4.36.0, reading costs
about 4 ms per binary64 value, and the kernel then checks the link at about 1.4 ms per rational
and 2 ms per binary64 value on rows of a few hundred values. Both are the cost of the decoders;
the checks on the row itself take milliseconds.

`interval` needs no packed row of the values: for a bound on a series with float coefficients it
reads them by kernel reduction and links them itself. `packed_values` is for certificates written
by hand, such as a defect row in `Coeff.Wiener.norm_one_sub_ofRow_mul_le`.

A row at denominator `d` can be rounded outward to the denominator `d / 2 ^ s` with
`Packed.shiftDown` and `Packed.low`, which give the rounded row and the remainders whose sum,
read by one `laneSum`, bounds the `l1` distance (`Packed.eval_shiftDown_add_low`,
`Packed.laneSum_low`).

## References

* *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>, for the binary and decimal formats whose exact
  values the lanes hold.

## Tags

packed row, exact decoding, floating point, certificate
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

open FloatLib.Numerics FloatLib.Numerics.Packed

universe u v

/-- The exact lanes of a value, one rational for each lane and `none` where a lane has no finite
value. Scalars have one lane, and blocks one lane per element. -/
class ExactLanes (Source : Type u) where
  /-- The exact rational value of each lane. -/
  lanes : Source → List (Option ℚ)

namespace ExactLanes

/-- A scalar has one lane, its decoded value. -/
instance (priority := low) scalar {Source : Type u} {Exact : Type v} [ExactDecoder Source Exact]
    [ExactMap Exact ℚ] : ExactLanes Source where
  lanes x := [(ExactDecoder.decodeTo x).finite?]

/-- A vector-valued exact decoder supplies one lane per entry. A nonfinite decoded value
supplies `m` absent lanes. This applies to any source with such a decoder. -/
instance block {Source : Type u} {Exact : Type v} {m : Nat} [ExactDecoder Source (Vector Exact m)]
    [ExactMap Exact ℚ] : ExactLanes Source where
  lanes x := match ExactDecoder.decode x with
    | .finite v => v.toList.map fun e => some (ExactMap.run e)
    | _ => List.replicate m none

end ExactLanes

namespace Packed

/-- The exact lanes of all the values in a list. -/
def values {Source : Type u} [ExactLanes Source] (xs : List Source) : List (Option ℚ) :=
  xs.flatMap ExactLanes.lanes

/-- The biased row `u` of width `w` holds the values `vs` at the common denominator `d`: every
value is finite, entry `k` is `vs[k] * d`, and `u` has no lanes beyond `vs.length`. -/
def link (w d : Nat) (vs : List (Option ℚ)) (u : Nat) : Bool :=
  Nat.blt 0 d && Nat.blt u (pow2 (Nat.mul w vs.length)) && vs.all Option.isSome &&
    linked w d u 0 (vs.map (·.getD 0))

/-- A passing `link` says that the row denotes the values: every lane has a finite value, entry
`k` of the row divided by `d`, and the row has no other lanes. -/
theorem link_sound {w d : Nat} {vs : List (Option ℚ)} {u : Nat} (h : link w d vs u = true) :
    u < 2 ^ (w * vs.length) ∧ ∀ k (hk : k < vs.length), vs[k] = some ((entry w k u : ℚ) / d) := by
  simp only [link, Bool.and_eq_true, Nat.blt_eq, pow2_eq, Nat.mul_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hd, hu⟩, hsome⟩, hlink⟩ := h
  refine ⟨hu, fun k hk => ?_⟩
  have e := linked_sound hlink k (by simpa using hk)
  simp only [List.getElem_map, zero_add] at e
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hsome _ (List.getElem_mem hk))
  rw [hq, Option.some_inj]
  rw [hq, Option.getD_some] at e
  rw [eq_div_iff (by exact_mod_cast hd.ne'), ← Rat.num_div_den q, div_mul_eq_mul_div,
    div_eq_iff (by exact_mod_cast q.den_pos.ne')]
  exact_mod_cast e

end Packed
end FloatLib.Floats.ExecFloat
