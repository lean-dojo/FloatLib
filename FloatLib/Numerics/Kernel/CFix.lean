/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.CBall

/-!
# Complex numbers in fixed point with an offset, for products in Lean's kernel

A `CFix` is a form for chains of products of numbers near the unit circle. Its midpoint
coordinates share one scale and offset, so multiplication avoids the scale alignment and signed
midpoint pairs of `CBall`. It is a complex number on a grid `2 ^ (-s)`, with the scale `s` given
to each operation:

* the parts are stored with the offset `2 * 2 ^ s`, so `re` stands for `(re - 2 * 2 ^ s) / 2 ^ s`
  and no sign is ever examined;
* one radius `rad`, in units of `2 ^ (-s)`, bounds the error of both parts;
* a flag `ok` records that no subtraction went below zero. The enclosure guarantees require this
  flag being true. Every operation propagates a false flag, so checking the final flag certifies
  that the preceding subtractions were valid.

A product is four products of naturals, one subtraction and one shift for each part, and the
radius `(|x| ρ + |y| r + 2 r ρ) / 2 ^ s + 2` for the magnitudes `|x|`, `|y|` of the midpoints
(the sums of the magnitudes of their parts) and the radii `r`, `ρ`.

`CSum` adds such numbers up with their offsets, and `FloatLib.Numerics.Kernel.CFixProof` proves
the enclosures in every ordered field.

## Main definitions

* `CFix.one`, `CFix.zero`, `CFix.bad`, `CFix.mul`, `CFix.conj`, `CFix.pow2`.
* `CFix.ofCBall s z`: a complex ball on the grid.
* `CSum.zero`, `CSum.push`, `CSum.add`, and `CSum.scale s z S`: a sum times a complex number.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
The complex numbers `a + i b` with `a` within `rad / 2 ^ s` of `(re - 2 * 2 ^ s) / 2 ^ s` and `b`
within the same distance of `(im - 2 * 2 ^ s) / 2 ^ s`, for the scale `s` of the operations that
made it. Its enclosure guarantee requires `ok = true`.
-/
structure CFix where
  /-- The real part plus two, in units of `2 ^ (-s)`. -/
  re : Nat
  /-- The imaginary part plus two, in units of `2 ^ (-s)`. -/
  im : Nat
  /-- The error bound of each part, in units of `2 ^ (-s)`. -/
  rad : Nat
  /-- Whether the enclosure guarantee is valid. -/
  ok : Bool
  deriving DecidableEq, Repr

namespace CFix

/-- The offset `2 * 2 ^ s` of both parts. -/
def offset (s : Nat) : Nat := Nat.shiftLeft 2 s

/-- A value with no enclosure guarantee. -/
def bad : CFix := ⟨0, 0, 0, false⟩

/-- The number one. -/
def one (s : Nat) : CFix := ⟨Nat.shiftLeft 3 s, Nat.shiftLeft 2 s, 0, true⟩

/-- The number zero. -/
def zero (s : Nat) : CFix := ⟨Nat.shiftLeft 2 s, Nat.shiftLeft 2 s, 0, true⟩

/-- The sum of the magnitudes of the two parts of the midpoint, in units of `2 ^ (-s)`. -/
def mag (s : Nat) (x : CFix) : Nat :=
  (fun o => Nat.add (Nat.add (Nat.sub x.re o) (Nat.sub o x.re))
    (Nat.add (Nat.sub x.im o) (Nat.sub o x.im))) (offset s)

/-- The conjugate: the imaginary part reflected in the offset. -/
def conj (s : Nat) (x : CFix) : CFix :=
  ⟨x.re, Nat.sub (Nat.shiftLeft 4 s) x.im, x.rad, Bool.and x.ok (Nat.ble x.im (Nat.shiftLeft 4 s))⟩

/-- The numerator with the offset of a real ball whose scale is at most `s`. -/
def partOf (s : Nat) (a : Ball) : Nat :=
  (fun l => Nat.sub (Nat.add (Nat.shiftLeft a.plus l) (offset s)) (Nat.shiftLeft a.minus l))
    (Nat.sub s a.scale)

/-- Whether the midpoint of a real ball whose scale is at most `s` is at least `-2`. -/
def partOk (s : Nat) (a : Ball) : Bool :=
  (fun l => Nat.ble (Nat.shiftLeft a.minus l) (Nat.add (Nat.shiftLeft a.plus l) (offset s)))
    (Nat.sub s a.scale)

/-- The radius of a real ball whose scale is at most `s`, in units of `2 ^ (-s)`. -/
def radOf (s : Nat) (a : Ball) : Nat := Nat.shiftLeft a.rad (Nat.sub s a.scale)

/--
A complex ball on the grid `2 ^ (-s)`: both parts rounded to the grid, and the larger of the two
radii. The flag records that both midpoints are at least `-2`.
-/
def ofCBall (s : Nat) (z : CBall) : CFix :=
  (fun (a b : Ball) =>
    (⟨partOf s a, partOf s b, maxNat (radOf s a) (radOf s b),
      Bool.and (partOk s a) (partOk s b)⟩ : CFix))
    (z.re.round s) (z.im.round s)

end CFix

/--
A sum of `count` values of `CFix`: the sums of their parts with the offsets, and of their radii.
The real part of the sum is `(re - count * 2 * 2 ^ s) / 2 ^ s`.
-/
structure CSum where
  /-- The sum of the real parts with their offsets. -/
  re : Nat
  /-- The sum of the imaginary parts with their offsets. -/
  im : Nat
  /-- The sum of the radii. -/
  rad : Nat
  /-- The number of values. -/
  count : Nat
  /-- Whether every input enclosure was valid. -/
  ok : Bool
  deriving DecidableEq, Repr

namespace CSum

/-- The empty sum. -/
def zero : CSum := ⟨0, 0, 0, 0, true⟩

/-- The sum of two sums. -/
def add (a b : CSum) : CSum :=
  ⟨Nat.add a.re b.re, Nat.add a.im b.im, Nat.add a.rad b.rad, Nat.add a.count b.count,
    Bool.and a.ok b.ok⟩

/-- A fixed-point value viewed as a sum with count one. -/
def single (z : CFix) : CSum := ⟨z.re, z.im, z.rad, 1, z.ok⟩

/-- One more value, added as a one-element sum. -/
def push (z : CFix) (a : CSum) : CSum := add (single z) a

/-- A sum with no enclosure guarantee. -/
def bad : CSum := ⟨0, 0, 0, 0, false⟩

/-- The sum of the magnitudes of the two parts of the midpoint of a sum, in units of
`2 ^ (-s)`. -/
def mag (s : Nat) (S : CSum) : Nat :=
  (fun o => Nat.add (Nat.add (Nat.sub S.re o) (Nat.sub o S.re))
    (Nat.add (Nat.sub S.im o) (Nat.sub o S.im))) (Nat.mul S.count (CFix.offset s))

/--
A sum times a complex number: the sum of `z * w` over the members `w` that were pushed into `S`,
by one product with their sum. With `Q = 2 ^ s`, `c` the count of `S`, `C = 2 c Q` its offset and
the parts `X`, `Y` of `z` and `U`, `V` of `S`, the real part of the product plus `2 c` is
`(X U + C Y + 2 Q V + C Q) - (Y V + C X + 2 Q U)` over `Q²`, and the imaginary part plus `2 c` is
`(X V + Y U + 5 C Q) - (C (X + Y) + 2 Q (U + V))` over `Q²`. The count stays `c`, the radius is
that of `CFix.mul` with the magnitude of the sum, and the flag records that neither subtraction
went below zero.
-/
def scale (s : Nat) (z : CFix) (S : CSum) : CSum :=
  (fun (co : Nat) =>
    (fun (P N P' N' : Nat) =>
      (⟨Nat.shiftRight (Nat.sub P N) s, Nat.shiftRight (Nat.sub P' N') s,
        Nat.add (Nat.shiftRight
          (Nat.add (Nat.add (Nat.mul (CFix.mag s z) S.rad) (Nat.mul (mag s S) z.rad))
            (Nat.mul (Nat.mul 2 z.rad) S.rad)) s) 2,
        S.count,
        Bool.and (Bool.and z.ok S.ok) (Bool.and (Nat.ble N P) (Nat.ble N' P'))⟩ : CSum))
      (Nat.add (Nat.add (Nat.add (Nat.mul z.re S.re) (Nat.mul co z.im))
        (Nat.shiftLeft S.im (Nat.succ s))) (Nat.shiftLeft co s))
      (Nat.add (Nat.add (Nat.mul z.im S.im) (Nat.mul co z.re)) (Nat.shiftLeft S.re (Nat.succ s)))
      (Nat.add (Nat.add (Nat.mul z.re S.im) (Nat.mul z.im S.re))
        (Nat.mul 5 (Nat.shiftLeft co s)))
      (Nat.add (Nat.mul co (Nat.add z.re z.im))
        (Nat.shiftLeft (Nat.add S.re S.im) (Nat.succ s))))
    (Nat.mul S.count (CFix.offset s))

end CSum

namespace CFix

/-- The product, computed by scaling a one-element sum. Both coordinates are rounded down
on the grid; the validity flag records that neither subtraction went below zero. -/
def mul (s : Nat) (x y : CFix) : CFix :=
  let S := CSum.scale s x (CSum.single y)
  ⟨S.re, S.im, S.rad, S.ok⟩

/-- The power `z ^ (2 ^ k)`, by `k` squarings. -/
noncomputable def pow2 (s k : Nat) (z : CFix) : CFix :=
  Nat.rec z (fun _ ih => mul s ih ih) k

end CFix

end FloatLib.Numerics.Kernel
