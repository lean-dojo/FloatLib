/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Cast
public import FloatLib.Numerics.Capabilities.Elementary
import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lanes
import FloatLib.Tactic.KernelShape

/-!
# Native binary16 and bfloat16 carriers

`Half` is IEEE 754 binary16 and `BFloat16` is the bfloat16 format of machine-learning hardware,
with binary32's exponent range and 8 significand bits. Each is its 16-bit interchange word, so
every value of the type is a value of the format, and `val` widens it to `Float32`: the binary32
word of the reference cast (`Carrier.val_eq_spec`). They are the fast native carriers of these
formats. The software models with the same words are
`FloatLib.Floats.Binary16` and `FloatLib.Floats.BFloat16` (`ExecFloat.Binary 5 10` and
`ExecFloat.Binary 8 7`), and the tests compare the two.

Each type has one NaN, the quiet NaN word with a zero sign and payload: `0x7E00` in binary16 and
`0x7FC0` in bfloat16. The structure carries the proof that its word is no other NaN word, `ofBits`
maps every NaN word to that one, and every conversion and operation that gives a NaN gives it. So
`ofBits x.toBits = x` for every value (`Half.ofBits_toBits`, `BFloat16.ofBits_toBits`), and
`(ofBits w).toBits = w` for every word that is not another NaN word.

Rounding works on interchange words. `Word.roundWord` uses the proved descriptor cast to round
once to nearest, ties to even, with the destination's subnormal, overflow and NaN rules.
`Word.roundWord_eq_spec` proves agreement with `Model.cast` for every pair of descriptors;
`Word.roundWord_toNat` proves that storage loses no bits when the destination fits in 64 bits.
The carrier then normalizes NaNs. `ofFloat` rounds the binary64 word directly. Rounding to binary32
first and then to the narrow format would round twice: a binary64 value just above a narrow
midpoint rounds to the midpoint in binary32, and the tie then goes to the even neighbour, which can
be the lower one. Rational constants round once through `Model.ofRat`.

Addition, subtraction, multiplication, division, and square root compute in binary32 and round the
binary32 result once more. That gives the correctly rounded result: binary32 carries 24
significand bits, at least `2p + 2` for both formats (`p = 11` for binary16, `p = 8` for
bfloat16), so the second rounding cannot move off the value a single rounding would give
(Figueroa, "When is double rounding innocuous?", 1995). This rests on the host `Float32` being IEEE
binary32 and is checked against the software models, not proved here. The transcendental functions
also compute in binary32 and round once; they carry no correctly-rounded guarantee.

`Carrier format` defines normalization, conversions and instances once. `Half` and `BFloat16`
are its named specializations. A `Format` carries what the instances rest on: the designated NaN
word is a NaN word, binary32 contains the format's exponent range and at least `2p + 2`
significand bits, and the widening function is the reference cast to binary32 on every word a
carrier holds. For the two named layouts the last law is checked by Lean's kernel on all 65,536
words. `Carrier.ofWord_eq_spec` proves conversion from every source descriptor, `ofFloat32_eq_spec`
and `ofFloat_eq_spec` specialize it to the two host word types, and `Carrier.val_eq_spec` proves
widening. So both conversions are proved; the arithmetic claim above is the part that remains
outside these proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Native

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics (MathFunctions)

namespace Word

/--
Round `bits`, decoded in `src`, once to `dst`, ties to even, through the proved kernel cast.

Decoding discards bits above the source width. NaN handling follows `Model.cast`; native
carriers normalize the resulting NaN separately. The result fits without truncation whenever
`dst.bitWidth ≤ 64`, as stated by `roundWord_toNat`.
-/
@[inline] def roundWord (src dst : FloatFormat) (bits : UInt64) : UInt64 :=
  (KernelPath.cast src dst .nearest
    (Model.ofNatBits (fmt := src) bits.toNat).toNatBits).toUInt64

/-- Word rounding agrees with the nearest-even reference cast for every pair of descriptors. -/
theorem roundWord_eq_spec (src dst : FloatFormat) (bits : UInt64) :
    roundWord src dst bits =
      (Model.cast src dst (Model.ofNatBits bits.toNat) .nearest).toNatBits.toUInt64 := by
  unfold roundWord
  rw [KernelPath.cast_eq_spec]

/-- A destination of at most 64 bits is stored without truncation. -/
theorem roundWord_toNat (src dst : FloatFormat) (bits : UInt64)
    (hwidth : dst.bitWidth ≤ 64) :
    (roundWord src dst bits).toNat =
      (Model.cast src dst (Model.ofNatBits bits.toNat) .nearest).toNatBits := by
  rw [roundWord_eq_spec, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt <| Nat.lt_of_lt_of_le (Model.toNatBits_lt_two_pow _)
    (Nat.pow_le_pow_right (by decide) hwidth)

/--
The binary32 word with the value of the binary16 word `bits`; a NaN word gives a NaN word.

The position of the leading bit of a subnormal fraction is counted with shifts and tests against
zero, which Lean's kernel evaluates, so that `widenHalfWord_eq_cast` can check every word.
-/
@[inline] def widenHalfWord (bits : UInt16) : UInt32 :=
  let word : UInt32 := bits.toUInt32
  let sign : UInt32 := (word &&& 0x8000) <<< 16
  let field : UInt32 := (word >>> 10) &&& 0x1F
  let stored : UInt32 := word &&& 0x3FF
  if field == 0x1F then sign ||| (0x7F800000 : UInt32) ||| (stored <<< 13)
  else if field != 0 then sign ||| ((field + 112) <<< 23) ||| (stored <<< 13)
  else if stored == 0 then sign
  else
    -- The subnormal `stored * 2 ^ -24` has its leading bit at `2 ^ (lead - 24)`, and `lead` is
    -- the number of `k` in `1 … 9` with `stored ≥ 2 ^ k`.
    let above (k : UInt32) : UInt32 := if (stored >>> k) != 0 then 1 else 0
    let lead : UInt32 :=
      above 1 + above 2 + above 3 + above 4 + above 5 + above 6 + above 7 + above 8 + above 9
    sign ||| ((lead + 103) <<< 23) ||| ((stored <<< (23 - lead)) &&& (0x7FFFFF : UInt32))

end Word

/-- A 16-bit IEEE layout and its native widening implementation.

The widths and NaN word determine normalization. Narrowing refines the reference cast, and the
widening function is required to be the reference cast to binary32 on every word a carrier
holds. The two range laws are the conditions under which computing in binary32 and rounding once
more can give the correctly rounded result; this structure is not a certificate for the host
arithmetic. -/
structure Format where
  /-- Number of exponent bits. -/
  exponent : Nat
  /-- Number of stored fraction bits. -/
  fraction : Nat
  /-- Word used to normalize NaNs; the named layouts choose a quiet NaN. -/
  nan : UInt16
  /-- An IEEE exponent field has at least two bits. -/
  exponent_ge_two : 2 ≤ exponent
  /-- Binary32's exponent range contains the format's, so every value widens exactly. -/
  exponent_le_eight : exponent ≤ 8
  /-- The stored fraction is nonempty. -/
  fraction_pos : 0 < fraction
  /-- Binary32's 24 significand bits are at least `2p + 2` for the precision `p = fraction + 1`:
  Figueroa's condition for a second rounding to be harmless. -/
  precision_le : 2 * (fraction + 1) + 2 ≤ 24
  /-- Sign, exponent and fraction occupy sixteen bits. -/
  width_eq : exponent + fraction = 15
  /-- The designated word is a NaN word: its magnitude bits lie above the infinity word. -/
  nan_isNaN : ((2 ^ exponent - 1) * 2 ^ fraction).toUInt16 < nan &&& 0x7FFF
  /-- Widen a word to binary32. -/
  widen : UInt16 → UInt32
  /-- On every word that is not a NaN, and on the designated NaN, widening is the nearest-even
  reference cast to binary32. Other NaN words are not carrier values. -/
  widen_eq : ∀ bits : UInt16,
    bits &&& 0x7FFF ≤ ((2 ^ exponent - 1) * 2 ^ fraction).toUInt16 ∨ bits = nan →
      widen bits =
        (Model.cast (FloatFormat.ieee exponent fraction exponent_ge_two fraction_pos)
          FloatFormat.binary32 (Model.ofNatBits bits.toNat) .nearest).toNatBits.toUInt32

/-- The software descriptor with these widths and the ordinary IEEE bias. -/
@[inline] def Format.model (format : Format) : FloatFormat :=
  FloatFormat.ieee format.exponent format.fraction format.exponent_ge_two format.fraction_pos

/-- The positive infinity word; all larger magnitude words encode NaNs. -/
@[inline] def Format.infinity (format : Format) : UInt16 :=
  ((2 ^ format.exponent - 1) * 2 ^ format.fraction).toUInt16

/-- The designated NaN word is a NaN word of the layout. -/
theorem Format.infinity_lt_nan (format : Format) : format.infinity < format.nan &&& 0x7FFF :=
  format.nan_isNaN

/-- One common representation for the native 16-bit carriers, with other NaNs excluded. -/
structure Carrier (format : Format) where
  /-- Construct a carrier from a word and a proof of its normalization invariant. -/
  mk ::
  /-- The interchange word. -/
  toBits : UInt16
  /-- A non-NaN word or the designated NaN. -/
  canonical : toBits &&& 0x7FFF ≤ format.infinity ∨ toBits = format.nan
  deriving DecidableEq

namespace Carrier

variable {format : Format}

/-- Retain non-NaN words and normalize all other words to the designated NaN. -/
@[inline] def ofBits (bits : UInt16) : Carrier format :=
  if h : bits &&& 0x7FFF ≤ format.infinity then ⟨bits, .inl h⟩
  else ⟨format.nan, .inr rfl⟩

/-- Normalization preserves every carrier value. -/
theorem ofBits_toBits (x : Carrier format) : ofBits x.toBits = x := by
  obtain ⟨bits, h⟩ := x
  unfold ofBits
  split
  · rfl
  · rename_i hNaN
    rcases h with h | h
    · exact absurd h hNaN
    · subst h
      rfl

/-- Every non-NaN word is preserved. -/
theorem toBits_ofBits (bits : UInt16) (h : bits &&& 0x7FFF ≤ format.infinity) :
    (ofBits (format := format) bits).toBits = bits := by
  simp [ofBits, h]

/-- The designated NaN word itself is preserved. -/
theorem toBits_ofBits_nan : (ofBits (format := format) format.nan).toBits = format.nan := by
  unfold ofBits
  split <;> rfl

/-- Normalization keeps the class of a word: a NaN word becomes the designated NaN word, which
is a NaN word, and every other word is kept. -/
theorem isNaNWord_ofBits_iff (bits : UInt16) :
    format.infinity < (ofBits (format := format) bits).toBits &&& 0x7FFF ↔
      format.infinity < bits &&& 0x7FFF := by
  unfold ofBits
  split
  · rfl
  · rename_i h
    exact ⟨fun _ => UInt16.not_le.mp h, fun _ => format.infinity_lt_nan⟩

/-- Widen through the format's binary32 implementation. -/
@[inline] def val (x : Carrier format) : Float32 :=
  Float32.ofBits (format.widen x.toBits)

/-- Widening is the nearest-even reference cast of the stored word to binary32. -/
theorem val_eq_spec (x : Carrier format) :
    x.val = Float32.ofBits (Model.cast format.model FloatFormat.binary32
      (Model.ofNatBits x.toBits.toNat) .nearest).toNatBits.toUInt32 :=
  congrArg Float32.ofBits (format.widen_eq x.toBits x.canonical)

/-- Round a source word to this carrier and normalize the resulting NaN. -/
@[inline] def ofWord (src : FloatFormat) (bits : UInt64) : Carrier format :=
  ofBits (Word.roundWord src format.model bits).toUInt16

/-- Every source descriptor uses the nearest-even model cast followed by carrier normalization. -/
theorem ofWord_eq_spec (src : FloatFormat) (bits : UInt64) :
    ofWord (format := format) src bits =
      ofBits (Model.cast src format.model
        (Model.ofNatBits bits.toNat) .nearest).toNatBits.toUInt16 := by
  unfold ofWord
  congr 1
  apply UInt16.toNat.inj
  rw [UInt64.toNat_toUInt16, Word.roundWord_toNat]
  · simp
  · change 1 + format.exponent + format.fraction ≤ 64
    have := format.width_eq
    omega

/-- Round a binary32 word with the proved nearest-even word rounder. -/
@[inline] def ofFloat32 (x : Float32) : Carrier format :=
  ofWord FloatFormat.binary32 x.toBits.toUInt64

/-- Round a binary64 word directly, without an intermediate binary32 rounding. -/
@[inline] def ofFloat (x : Float) : Carrier format :=
  ofWord FloatFormat.binary64 x.toBits

/-- Binary32 conversion is the reference cast of its interchange word, with NaNs normalized. -/
theorem ofFloat32_eq_spec (x : Float32) :
    ofFloat32 (format := format) x =
      ofBits (Model.cast FloatFormat.binary32 format.model
        (Model.ofNatBits x.toBits.toNat) .nearest).toNatBits.toUInt16 := by
  simpa [ofFloat32] using ofWord_eq_spec (format := format) FloatFormat.binary32 x.toBits.toUInt64

/-- Binary64 conversion rounds its interchange word directly, with NaNs normalized. -/
theorem ofFloat_eq_spec (x : Float) :
    ofFloat (format := format) x =
      ofBits (Model.cast FloatFormat.binary64 format.model
        (Model.ofNatBits x.toBits.toNat) .nearest).toNatBits.toUInt16 :=
  ofWord_eq_spec FloatFormat.binary64 x.toBits

/-- Round a rational through the corresponding software descriptor. -/
def ofRat (q : Rat) : Carrier format :=
  ofBits (Model.ofRat format.model q).toNatBits.toUInt16

/-- Widen the native binary32 value to binary64. -/
@[inline] def toFloat (x : Carrier format) : Float :=
  x.val.toFloat

/-- Whether the native value is a NaN. -/
@[inline] def isNaN (x : Carrier format) : Bool :=
  x.val.isNaN

instance : Inhabited (Carrier format) := ⟨ofBits 0⟩
instance : Zero (Carrier format) := ⟨ofBits 0⟩
instance : One (Carrier format) :=
  ⟨ofBits (((2 ^ (format.exponent - 1) - 1) * 2 ^ format.fraction).toUInt16)⟩
instance : Add (Carrier format) := ⟨fun x y => ofFloat32 (x.val + y.val)⟩
instance : Sub (Carrier format) := ⟨fun x y => ofFloat32 (x.val - y.val)⟩
instance : Mul (Carrier format) := ⟨fun x y => ofFloat32 (x.val * y.val)⟩
instance : Div (Carrier format) := ⟨fun x y => ofFloat32 (x.val / y.val)⟩
instance : Neg (Carrier format) := ⟨fun x => ofFloat32 (-x.val)⟩
instance : Pow (Carrier format) (Carrier format) := ⟨fun x y => ofFloat32 (x.val ^ y.val)⟩
/--
Lean's `max` on binary32, which since Lean 4.36 is `Float32.maximum`, the IEEE 754-2019 `maximum`:
a NaN when an operand is a NaN, and `-0` is below `+0`.
-/
instance : Max (Carrier format) := ⟨fun x y => ofFloat32 (max x.val y.val)⟩
/--
Lean's `min` on binary32, which since Lean 4.36 is `Float32.minimum`, the IEEE 754-2019 `minimum`:
a NaN when an operand is a NaN, and `-0` is below `+0`.
-/
instance : Min (Carrier format) := ⟨fun x y => ofFloat32 (min x.val y.val)⟩
/-- The host's binary32 equality: a NaN is unequal to every value and the two zeros are equal. -/
instance : BEq (Carrier format) := ⟨fun x y => x.val == y.val⟩
/-- The host's binary32 order: every comparison with a NaN is false. -/
instance : LT (Carrier format) := ⟨fun x y => x.val < y.val⟩
/-- The host's binary32 order: every comparison with a NaN is false. -/
instance : LE (Carrier format) := ⟨fun x y => x.val ≤ y.val⟩
instance (x y : Carrier format) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))
instance (x y : Carrier format) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))
instance : ToString (Carrier format) := ⟨fun x => toString x.val⟩
instance : Repr (Carrier format) := ⟨fun x precedence => reprPrec x.val precedence⟩

/-- Naturals below `2 ^ 53` are exact binary64 values; larger ones round from their exact value. -/
instance : NatCast (Carrier format) where
  natCast n := if n < 2 ^ 53 then ofFloat n.toFloat else ofRat n

/-- Native binary32 elementary functions, each followed by the common word rounder. -/
instance : MathFunctions (Carrier format) where
  exp x := ofFloat32 (Float32.exp x.val)
  tanh x := ofFloat32 (Float32.tanh x.val)
  cosh x := ofFloat32 (Float32.cosh x.val)
  sqrt x := ofFloat32 (Float32.sqrt x.val)
  abs x := ofFloat32 (Float32.abs x.val)
  log x := ofFloat32 (Float32.log x.val)
  pi := ofFloat 3.14159265358979323846
  cos x := ofFloat32 (Float32.cos x.val)
  sin x := ofFloat32 (Float32.sin x.val)
  sinh x := ofFloat32 (Float32.sinh x.val)

end Carrier

namespace Word

/--
`widenHalfWord` on the natural number of a word: the same shifts, masks and tests, with the
reductions modulo `2 ^ 32` of `UInt32` arithmetic written out (`widenHalfWord_toNat`). Lean's
kernel computes on natural numbers directly, so this is the form it evaluates on every word.
-/
private def widenHalfNat (bits : Nat) : Nat :=
  let sign : Nat := (bits &&& 0x8000) <<< 16 % 2 ^ 32
  let field : Nat := (bits >>> 10) &&& 0x1F
  let stored : Nat := bits &&& 0x3FF
  if field = 0x1F then sign ||| 0x7F800000 ||| (stored <<< 13 % 2 ^ 32)
  else if field ≠ 0 then
    sign ||| (((field + 112) % 2 ^ 32) <<< 23 % 2 ^ 32) ||| (stored <<< 13 % 2 ^ 32)
  else if stored = 0 then sign
  else
    let above (k : Nat) : Nat := if stored >>> k ≠ 0 then 1 else 0
    let lead : Nat :=
      ((((((((above 1 + above 2) % 2 ^ 32 + above 3) % 2 ^ 32 + above 4) % 2 ^ 32 +
        above 5) % 2 ^ 32 + above 6) % 2 ^ 32 + above 7) % 2 ^ 32 + above 8) % 2 ^ 32 +
        above 9) % 2 ^ 32
    sign ||| (((lead + 103) % 2 ^ 32) <<< 23 % 2 ^ 32) |||
      ((stored <<< ((2 ^ 32 - lead + 23) % 2 ^ 32 % 32) % 2 ^ 32) &&& 0x7FFFFF)

/-- The natural number of `widenHalfWord bits` is `widenHalfNat` of the natural number of `bits`. -/
private theorem widenHalfWord_toNat (bits : UInt16) :
    (widenHalfWord bits).toNat = widenHalfNat bits.toNat := by
  unfold widenHalfWord widenHalfNat
  simp only [apply_ite UInt32.toNat, UInt32.toNat_and, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt32.toNat_shiftRight, UInt32.toNat_add, UInt32.toNat_sub, UInt16.toNat_toUInt32,
    UInt32.toNat_ofNat, beq_iff_eq, bne_iff_ne, ne_eq, ← UInt32.toNat_inj, Nat.reduceMod,
    Nat.reducePow]

kernel_shape widenHalfNat

/-- A bfloat16 word in the high half of a binary32 word, on natural numbers. -/
private def shiftHighNat (word : Nat) : Nat := word <<< 16 % 2 ^ 32

kernel_shape shiftHighNat

/--
`value` at a word that a carrier holds, and zero at any other word: one whose low 15 bits are
above `infinity`, so that it is a NaN, and which is not the NaN `nan`.
-/
private def held (infinity nan word value : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.land word 0x7FFF) infinity)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq word nan) 0 value) value

/-- A widening on natural numbers that agrees with the kernel cast of `model` to binary32 at the
256 × 256 pairs of bytes, where a carrier holds the word, is the kernel cast at every 16-bit
word a carrier holds. -/
private theorem agrees_of_bytes {model : FloatFormat} {infinity nan : Nat} {widen : Nat → Nat}
    (h : ∀ high low : Fin 256,
      held infinity nan (Nat.add (Nat.mul high.val 256) low.val)
          (widen (Nat.add (Nat.mul high.val 256) low.val)) =
        held infinity nan (Nat.add (Nat.mul high.val 256) low.val)
          (KernelPath.cast model FloatFormat.binary32 .nearest
            (Nat.add (Nat.mul high.val 256) low.val)))
    (bits : UInt16) (hbits : bits.toNat &&& 0x7FFF ≤ infinity ∨ bits.toNat = nan) :
    widen bits.toNat = KernelPath.cast model FloatFormat.binary32 .nearest bits.toNat := by
  have hlt := bits.toNat_lt
  have hword := h ⟨bits.toNat / 256, by omega⟩ ⟨bits.toNat % 256, Nat.mod_lt _ (by decide)⟩
  have hsplit : Nat.add (Nat.mul (bits.toNat / 256) 256) (bits.toNat % 256) = bits.toNat :=
    Nat.div_add_mod' bits.toNat 256
  have hheld (value : Nat) : held infinity nan bits.toNat value = value := by
    unfold held
    rcases hbits with hle | heq
    · have hble : Nat.ble (Nat.land bits.toNat 0x7FFF) infinity = true :=
        Nat.ble_eq_true_of_le hle
      rw [hble]
    · rw [heq, Nat.beq_refl]
      cases Nat.ble (Nat.land nan 0x7FFF) infinity <;> rfl
  dsimp only at hword
  rwa [hsplit, hheld, hheld] at hword

/-- A widening function that agrees with the kernel cast on encodings is the reference cast, for
a 16-bit layout. -/
private theorem widen_eq_cast (model : FloatFormat) (hwidth : model.bitWidth = 16)
    (widen : UInt16 → UInt32) (bits : UInt16)
    (h : (widen bits).toNat =
      KernelPath.cast model FloatFormat.binary32 .nearest bits.toNat) :
    widen bits = (Model.cast model FloatFormat.binary32
      (Model.ofNatBits bits.toNat) .nearest).toNatBits.toUInt32 := by
  have hbits : (Model.ofNatBits (fmt := model) bits.toNat).toNatBits = bits.toNat :=
    Model.toNatBits_ofNatBits_of_lt _ (by rw [hwidth]; exact bits.toNat_lt)
  rw [← hbits, KernelPath.cast_eq_spec] at h
  apply UInt32.toNat.inj
  rw [h, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Model.toNatBits_lt_two_pow _)).symm

/-- `widenHalfNat` is the kernel cast of binary16 to binary32 on the words a carrier holds: one
run of both on the 65,536 lanes of a row (`lane_decide`). -/
private theorem widenHalfNat_lanes : ∀ high low : Fin 256,
    held 0x7C00 0x7E00 (Nat.add (Nat.mul high.val 256) low.val)
        (widenHalfNat.kernel (Nat.add (Nat.mul high.val 256) low.val)) =
      held 0x7C00 0x7E00 (Nat.add (Nat.mul high.val 256) low.val)
        (KernelPath.cast (FloatFormat.ieee 5 10 (by decide) (by decide)) FloatFormat.binary32
          .nearest (Nat.add (Nat.mul high.val 256) low.val)) := by
  lane_decide

/-- `shiftHighNat` is the kernel cast of bfloat16 to binary32 on the words a carrier holds. -/
private theorem shiftHighNat_lanes : ∀ high low : Fin 256,
    held 0x7F80 0x7FC0 (Nat.add (Nat.mul high.val 256) low.val)
        (shiftHighNat.kernel (Nat.add (Nat.mul high.val 256) low.val)) =
      held 0x7F80 0x7FC0 (Nat.add (Nat.mul high.val 256) low.val)
        (KernelPath.cast (FloatFormat.ieee 8 7 (by decide) (by decide)) FloatFormat.binary32
          .nearest (Nat.add (Nat.mul high.val 256) low.val)) := by
  lane_decide

/-- `widenHalfWord` is the reference cast of binary16 to binary32 on every word that is not a
NaN and on the quiet NaN `0x7E00`, checked by Lean's kernel on all 65,536 words. -/
theorem widenHalfWord_eq_cast (bits : UInt16) (h : bits &&& 0x7FFF ≤ 0x7C00 ∨ bits = 0x7E00) :
    widenHalfWord bits =
      (Model.cast (FloatFormat.ieee 5 10 (by decide) (by decide)) FloatFormat.binary32
        (Model.ofNatBits bits.toNat) .nearest).toNatBits.toUInt32 := by
  refine widen_eq_cast _ rfl _ bits ?_
  have hword : bits.toNat &&& 0x7FFF ≤ 0x7C00 ∨ bits.toNat = 0x7E00 :=
    h.imp (fun h => by simpa using UInt16.le_iff_toNat_le.mp h) (congrArg UInt16.toNat)
  rw [widenHalfWord_toNat, widenHalfNat.kernel_eq]
  exact agrees_of_bytes (widen := widenHalfNat.kernel) widenHalfNat_lanes bits hword

/-- Placing a bfloat16 word in the high half of a binary32 word is the reference cast of
bfloat16 to binary32 on every word that is not a NaN and on the quiet NaN `0x7FC0`, checked by
Lean's kernel on all 65,536 words. -/
theorem shiftLeft_eq_cast (bits : UInt16) (h : bits &&& 0x7FFF ≤ 0x7F80 ∨ bits = 0x7FC0) :
    bits.toUInt32 <<< 16 =
      (Model.cast (FloatFormat.ieee 8 7 (by decide) (by decide)) FloatFormat.binary32
        (Model.ofNatBits bits.toNat) .nearest).toNatBits.toUInt32 := by
  refine widen_eq_cast _ rfl (fun bits => bits.toUInt32 <<< 16) bits ?_
  have hword : bits.toNat &&& 0x7FFF ≤ 0x7F80 ∨ bits.toNat = 0x7FC0 :=
    h.imp (fun h => by simpa using UInt16.le_iff_toNat_le.mp h) (congrArg UInt16.toNat)
  have hshift : (bits.toUInt32 <<< 16).toNat = shiftHighNat.kernel bits.toNat := by
    rw [← shiftHighNat.kernel_eq]
    simp only [shiftHighNat, UInt32.toNat_shiftLeft, UInt16.toNat_toUInt32, UInt32.toNat_ofNat]
  rw [hshift]
  exact agrees_of_bytes (widen := shiftHighNat.kernel) shiftHighNat_lanes bits hword

end Word

end FloatLib.Floats.Native
