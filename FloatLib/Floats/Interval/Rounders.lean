/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Directed rounding (down/up) for Flocq-style formats

For interval propagation under a *discrete* numeric grid (float, fixed-point, quantization), one
typically wants **directed rounding** at interval endpoints:

- `down x` is a representable value with
  $\operatorname{down}(x)\le x$,
- `up x` is a representable value with
  $x\le\operatorname{up}(x)$.

In IEEE-754 hardware this corresponds to the rounding modes toward $-\infty$ and toward
$+\infty$. FloatLib represents these directions with Flocq-style
rounding on $\mathbb{R}$ via `round` together with
the floor/ceil rounding functions from `FloatLib/Floats/Formats/Flocq/Theory/Rounding/Core.lean`.

The rounders work for any radix $\beta$ and exponent selection
function `fexp` satisfying `ValidExp`.

References:
- IEEE 754-2019 (rounding modes; directed rounding).
- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.
- Flocq (rounded arithmetic on reals).
-/

@[expose] public section


namespace FloatLib.Floats.Interval

open FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Round down to the $(\beta,\mathtt{fexp})$ grid by taking the floor of the scaled mantissa. -/
noncomputable def roundDown (x : ℝ) : ℝ :=
  round (β := β) (fexp := fexp) floorRound x

/-- Round up to the $(\beta,\mathtt{fexp})$ grid by taking the ceiling of the scaled mantissa. -/
noncomputable def roundUp (x : ℝ) : ℝ :=
  round (β := β) (fexp := fexp) ceilRound x

/--
Correctness of directed rounding down: `roundDown x` is an enclosure **lower bound**.

This is the format-generic analogue of the IEEE-754 fact that rounding toward $-\infty$ never exceeds
the exact real value.
-/
theorem roundDown_le (x : ℝ) : roundDown (β := β) (fexp := fexp) x ≤ x := by
  -- The positive scale `β^e` preserves the floor bound on the mantissa.
  simp [roundDown, FloatLib.Floats.Formats.Flocq.round, FloatLib.Floats.Formats.Flocq.toReal]
  set s : ℝ := scaledMantissa β fexp x
  set e : ℤ := cexp β fexp x
  have hx : s * bpow β e = x := by
    simpa [s, e] using (FloatLib.Floats.Formats.Flocq.scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x)
  have hb : 0 ≤ bpow β e := bpow.nonneg β e
  have hf : (⌊s⌋ : ℝ) ≤ s := Int.floor_le s
  have : (⌊s⌋ : ℝ) * bpow β e ≤ s * bpow β e :=
    mul_le_mul_of_nonneg_right hf hb
  simpa [hx, s, e, floorRound] using this

/--
Correctness of directed rounding up: `roundUp x` is an enclosure **upper bound**.

This is the format-generic analogue of the IEEE-754 fact that rounding toward $+\infty$ is never below
the exact real value.
-/
theorem le_roundUp (x : ℝ) : x ≤ roundUp (β := β) (fexp := fexp) x := by
  simp [roundUp, FloatLib.Floats.Formats.Flocq.round, FloatLib.Floats.Formats.Flocq.toReal]
  set s : ℝ := scaledMantissa β fexp x
  set e : ℤ := cexp β fexp x
  have hx : s * bpow β e = x := by
    simpa [s, e] using (FloatLib.Floats.Formats.Flocq.scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x)
  have hb : 0 ≤ bpow β e := bpow.nonneg β e
  have hc : s ≤ (⌈s⌉ : ℝ) := Int.le_ceil s
  have : s * bpow β e ≤ (⌈s⌉ : ℝ) * bpow β e :=
    mul_le_mul_of_nonneg_right hc hb
  simpa [hx, s, e, ceilRound, mul_assoc, mul_left_comm, mul_comm] using this

/--
A pair of real maps bracketing every real number from below and above.

This is the only interface the enclosure proofs need: they use
$\operatorname{down}(x)\le x\le\operatorname{up}(x)$ and nothing else. In particular the structure
does not require `down x` or `up x` to lie on any representable grid, nor does it require
monotonicity; the identity maps satisfy both bounds. Representability is a property of a
particular instance such as `formatRounder`, whose outputs lie on the $(\beta,\mathtt{fexp})$ grid
by construction.
-/
structure Rounder where
  /-- A lower bound for an exact real value. -/
  down : ℝ → ℝ
  /-- An upper bound for an exact real value. -/
  up : ℝ → ℝ
  /-- Rounding down never exceeds the exact value. -/
  down_le : ∀ x, down x ≤ x
  /-- Rounding up never falls below the exact value. -/
  le_up : ∀ x, x ≤ up x

/--
Canonical rounder for the $(\beta,\mathtt{fexp})$ format via `roundDown`/`roundUp`.

The outputs are values of the Flocq generic format, which has an unbounded exponent range: there is
no overflow to infinity and no largest finite value, so this rounder models a binary format's
finite grid extended past its exponent limits rather than the encoded format itself.
-/
noncomputable def formatRounder (β : Numerics.Radix) (fexp : ℤ → ℤ) [ValidExp fexp] : Rounder :=
  { down := fun x => roundDown (β := β) (fexp := fexp) x
    up := fun x => roundUp (β := β) (fexp := fexp) x
    down_le := fun x => roundDown_le (β := β) (fexp := fexp) x
    le_up := fun x => le_roundUp (β := β) (fexp := fexp) x }

end FloatLib.Floats.Interval
