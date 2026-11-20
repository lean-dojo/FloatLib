/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Quantum
public import FloatLib.Floats.Formats.DecimalInterchange.Runtime

/-!
# Kernel path of the decimal encoding operations

IEEE 754-2019 §5.5.2 `encodeDecimal`, `decodeDecimal`, `encodeBinary` and `decodeBinary` map a
decimal datum to its interchange word and back, with the significand in the decimal encoding
(DPD) or in the binary encoding (BID). The reference works on a bit vector and branches on
decidable propositions.

`encodeNat? encoding f d` is the word of a valid datum as a natural number, and
`decodeNat encoding f word` the datum of a word, both with the fields cut by divisions and
remainders of natural numbers and with every branch a comparison of natural numbers. A declet is
packed and unpacked by `encodeDeclet` and `decodeDeclet`, the tables of the reference as
arithmetic on the three digits. `encode?_eq` and `decode_eq` prove the two equal to the
reference for both encodings, every format, every datum and every word, and the four operations
of the standard are rewritten by rules tagged `@[kernel_optimize]`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

/-- A branch on the order of two natural numbers. -/
theorem casesOn_lt {α : Type} (a b : Nat) (otherwise value : α) :
    Bool.casesOn (motive := fun _ => α) (Nat.ble (Nat.succ a) b) otherwise value =
      if a < b then value else otherwise := by
  rw [natBle_eq, casesOn_decide]
  rfl

/-- A branch on the equality of two natural numbers. -/
theorem casesOn_beq {α : Type} (a b : Nat) (otherwise value : α) :
    Bool.casesOn (motive := fun _ => α) (Nat.beq a b) otherwise value =
      if a = b then value else otherwise := by
  rw [natBeq_eq, casesOn_decide]

/-! ## Declets -/

/-- Three decimal digits as a ten-bit declet (`encodeDeclet_eq`). -/
def encodeDeclet (n : Nat) : Nat :=
  (fun a b c =>
    (fun x y z =>
      Nat.add
        (Nat.add (Nat.add (Nat.mul (Nat.mod a 2) 128) (Nat.mul (Nat.mod b 2) 16)) (Nat.mod c 2))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ a) 8)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ b) 8)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) 8) 110
              (Nat.add (Nat.mul z 256) 14))
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) 8)
              (Nat.add (Nat.mul y 256) 46)
              (Nat.add (Nat.add (Nat.mul z 256) (Nat.mul y 32)) 12)))
          (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ b) 8)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) 8)
              (Nat.add (Nat.mul x 256) 78)
              (Nat.add (Nat.add (Nat.mul x 256) (Nat.mul z 32)) 10))
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) 8)
              (Nat.add (Nat.add (Nat.mul x 256) (Nat.mul y 32)) 8)
              (Nat.add (Nat.add (Nat.mul x 256) (Nat.mul y 32)) (Nat.mul z 2))))))
      (Nat.div (Nat.mod a 8) 2) (Nat.div (Nat.mod b 8) 2) (Nat.div (Nat.mod c 8) 2))
    (Nat.div n 100) (Nat.mod (Nat.div n 10) 10) (Nat.mod n 10)

/-- A ten-bit declet as three decimal digits, redundant declets included (`decodeDeclet_eq`). -/
def decodeDeclet (n : Nat) : Nat :=
  (fun r u y pq st =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.mod (Nat.div n 8) 2) 0)
      ((fun selector =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq selector 0)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq selector 1)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq selector 2)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq st 2)
                (Bool.casesOn (motive := fun _ => Nat) (Nat.beq st 1)
                  (Bool.casesOn (motive := fun _ => Nat) (Nat.beq st 0)
                    (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add 8 r) 100)
                      (Nat.mul (Nat.add 8 u) 10)) 8) y)
                    (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add 8 r) 100)
                      (Nat.mul (Nat.add 8 u) 10)) (Nat.mul 2 pq)) y))
                  (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add 8 r) 100)
                    (Nat.mul (Nat.add (Nat.mul 2 pq) u) 10)) 8) y))
                (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add (Nat.mul 2 pq) r) 100)
                  (Nat.mul (Nat.add 8 u) 10)) 8) y))
              (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add 8 r) 100)
                (Nat.mul (Nat.add (Nat.mul 2 st) u) 10)) (Nat.mul 2 pq)) y))
            (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add (Nat.mul 2 pq) r) 100)
              (Nat.mul (Nat.add 8 u) 10)) (Nat.mul 2 st)) y))
          (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.add (Nat.mul 2 pq) r) 100)
            (Nat.mul (Nat.add (Nat.mul 2 st) u) 10)) 8) y))
        (Nat.mod (Nat.div n 2) 4))
      (Nat.add (Nat.add (Nat.mul (Nat.add (Nat.mul 2 pq) r) 100)
        (Nat.mul (Nat.add (Nat.mul 2 st) u) 10)) (Nat.mod n 8)))
    (Nat.mod (Nat.div n 128) 2) (Nat.mod (Nat.div n 16) 2) (Nat.mod n 2)
    (Nat.mod (Nat.div n 256) 4) (Nat.mod (Nat.div n 32) 4)

/-- `groups` groups of three digits as consecutive declets (`encodeTrailing_eq`). -/
def encodeTrailing : Nat → Nat → Nat
  | 0, _ => 0
  | groups + 1, n =>
      Nat.add (encodeDeclet (Nat.mod n 1000))
        (Nat.mul 1024 (encodeTrailing groups (Nat.div n 1000)))

/-- `groups` consecutive declets as a decimal coefficient (`decodeTrailing_eq`). -/
def decodeTrailing : Nat → Nat → Nat
  | 0, _ => 0
  | groups + 1, n =>
      Nat.add (decodeDeclet (Nat.mod n 1024))
        (Nat.mul 1000 (decodeTrailing groups (Nat.div n 1024)))

/-- `encodeDeclet` is the declet of the reference. -/
theorem encodeDeclet_eq (n : Nat) : encodeDeclet n = DPD.encodeDeclet n := by
  unfold encodeDeclet DPD.encodeDeclet
  simp only [casesOn_lt]
  rfl

/-- `decodeDeclet` reads a declet as the reference does. -/
theorem decodeDeclet_eq (n : Nat) : decodeDeclet n = DPD.decodeDeclet n := by
  unfold decodeDeclet DPD.decodeDeclet
  simp only [casesOn_beq]
  rfl

/-- `encodeTrailing` packs the trailing digits as the reference does. -/
theorem encodeTrailing_eq (groups n : Nat) :
    encodeTrailing groups n = DPD.encodeTrailing groups n := by
  induction groups generalizing n with
  | zero => rfl
  | succ groups ih =>
      change Nat.add (encodeDeclet (n % 1000)) (Nat.mul 1024 (encodeTrailing groups (n / 1000))) =
        DPD.encodeDeclet (n % 1000) + 1024 * DPD.encodeTrailing groups (n / 1000)
      rw [ih, encodeDeclet_eq]
      rfl

/-- `decodeTrailing` unpacks the trailing digits as the reference does. -/
theorem decodeTrailing_eq (groups n : Nat) :
    decodeTrailing groups n = DPD.decodeTrailing groups n := by
  induction groups generalizing n with
  | zero => rfl
  | succ groups ih =>
      change Nat.add (decodeDeclet (n % 1024)) (Nat.mul 1000 (decodeTrailing groups (n / 1024))) =
        DPD.decodeDeclet (n % 1024) + 1000 * DPD.decodeTrailing groups (n / 1024)
      rw [ih, decodeDeclet_eq]
      rfl

/-! ## Words -/

/--
Whether a datum is representable in a format (`valid_eq`): the coefficient below ten to the
precision and the biased exponent in range, or the payload of a NaN below its bound.
-/
def valid (f : Format) (d : Datum) : Bool :=
  Datum.casesOn (motive := fun _ => Bool) d
    (fun _ c q =>
      Bool.and (Nat.ble (Nat.succ c) (Nat.mul 10 (Nat.pow 1000 f.declets)))
        (offsets q f.bias fun above below =>
          Bool.and (Nat.beq below 0)
            (Nat.ble (Nat.succ above) (Nat.mul 3 (Nat.pow 2 f.exponentBits)))))
    (fun _ => true)
    (fun _ _ p => Nat.ble (Nat.succ p) (Nat.pow 1000 f.declets))

/--
The bits below the sign of a finite datum with coefficient `c` and biased exponent `e`
(`encodeFinite_eq`), in the binary or in the decimal encoding of the significand.
-/
def encodeFinite (encoding : Encoding) (f : Format) (c e : Nat) : Nat :=
  Encoding.casesOn (motive := fun _ => Nat) encoding
    ((fun trailing =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) (Nat.mul 8 trailing))
        (Nat.add (Nat.add (Nat.mul 24 (Nat.mul f.exponentBase trailing))
          (Nat.mul e (Nat.mul 2 trailing))) (Nat.sub c (Nat.mul 8 trailing)))
        (Nat.add (Nat.mul e (Nat.mul 8 trailing)) c))
      f.trailingBase)
    ((fun leading high =>
      Nat.add
        (Nat.add
          (Nat.mul
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ leading) 8)
              (Nat.add (Nat.add 24 (Nat.mul 2 high)) (Nat.sub leading 8))
              (Nat.add (Nat.mul 8 high) leading))
            (Nat.mul f.exponentBase f.trailingBase))
          (Nat.mul (Nat.mod e f.exponentBase) f.trailingBase))
        (encodeTrailing f.declets (Nat.mod c f.payloadBound)))
      (Nat.div c f.payloadBound) (Nat.div e f.exponentBase))

/-- The diagnostic payload of a NaN in the trailing field (`encodePayload_eq`). -/
def encodePayload (encoding : Encoding) (f : Format) (p : Nat) : Nat :=
  Encoding.casesOn (motive := fun _ => Nat) encoding p (encodeTrailing f.declets p)

/--
The interchange word of a datum as a natural number (`encode_eq`), without a test of its
validity.
-/
def encodeNat (encoding : Encoding) (f : Format) (d : Datum) : Nat :=
  (fun unit =>
    Datum.casesOn (motive := fun _ => Nat) d
      (fun s c q =>
        Nat.add (Bool.casesOn (motive := fun _ => Nat) s 0 f.signBase)
          (encodeFinite encoding f c (offsets q f.bias fun above _ => above)))
      (fun s =>
        Nat.add (Bool.casesOn (motive := fun _ => Nat) s 0 f.signBase) (Nat.mul 30 unit))
      (fun s signaling p =>
        Nat.add (Bool.casesOn (motive := fun _ => Nat) s 0 f.signBase)
          (Nat.add
            (Nat.add (Nat.mul 31 unit)
              (Bool.casesOn (motive := fun _ => Nat) signaling 0 (Nat.div unit 2)))
            (encodePayload encoding f p))))
    (Nat.mul f.exponentBase f.trailingBase)

/--
The interchange word of a datum that is valid for the format, as a natural number, and `none`
for a datum that is not (`encode?_eq`).
-/
def encodeNat? (encoding : Encoding) (f : Format) (d : Datum) : Option Nat :=
  Bool.casesOn (motive := fun _ => Option Nat) (valid f d) none (some (encodeNat encoding f d))

/--
The datum of the bits `n` below the sign of a finite word, with the sign `s`
(`decodeFinite_eq`), in the binary or in the decimal encoding of the significand.
-/
def decodeFinite (encoding : Encoding) (f : Format) (s : Bool) (n : Nat) : Datum :=
  Encoding.casesOn (motive := fun _ => Datum) encoding
    ((fun trailing =>
      (fun steering =>
        (fun c e =>
          Datum.ofBiased f s
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) f.coefficientBound) 0 c)
            e)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ n) steering)
            (Nat.add (Nat.mul 8 trailing) (Nat.mod (Nat.sub n steering) (Nat.mul 2 trailing)))
            (Nat.mod n (Nat.mul 8 trailing)))
          (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ n) steering)
            (Nat.div (Nat.sub n steering) (Nat.mul 2 trailing))
            (Nat.div n (Nat.mul 8 trailing))))
        (Nat.mul 24 (Nat.mul f.exponentBase trailing)))
      f.trailingBase)
    ((fun field =>
      Datum.ofBiased f s
        (Nat.add
          (Nat.mul
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ field) 24)
              (Nat.add 8 (Nat.mod field 2)) (Nat.mod field 8))
            f.payloadBound)
          (decodeTrailing f.declets (Nat.mod n f.trailingBase)))
        (Nat.add
          (Nat.mul
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ field) 24)
              (Nat.div (Nat.sub field 24) 2) (Nat.div field 8))
            f.exponentBase)
          (Nat.mod (Nat.div n f.trailingBase) f.exponentBase)))
      (Nat.div n (Nat.mul f.exponentBase f.trailingBase)))

/-- The diagnostic payload of a NaN read off the trailing field (`decodePayload_eq`). -/
def decodePayload (encoding : Encoding) (f : Format) (n : Nat) : Nat :=
  Encoding.casesOn (motive := fun _ => Nat) encoding
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ n) f.payloadBound) 0 n)
    (decodeTrailing f.declets n)

/--
The datum of an interchange word given as a natural number below `2 ^ bitWidth`
(`decode_eq`): its sign, and a finite datum, an infinity or a NaN by its combination field.
-/
def decodeNat (encoding : Encoding) (f : Format) (word : Nat) : Datum :=
  (fun unit =>
    (fun s n =>
      (fun combination =>
        Bool.casesOn (motive := fun _ => Datum) (Nat.ble (Nat.succ combination) 30)
          (Bool.casesOn (motive := fun _ => Datum) (Nat.beq combination 30)
            (.nan s (Nat.beq (Nat.mod (Nat.div n (Nat.div unit 2)) 2) 1)
              (decodePayload encoding f (Nat.mod n f.trailingBase)))
            (.infinity s))
          (decodeFinite encoding f s n))
        (Nat.div n unit))
      (Bool.not (Nat.beq (Nat.div word f.signBase) 0)) (Nat.mod word f.signBase))
    (Nat.mul f.exponentBase f.trailingBase)

/-- `valid` decides the validity of a datum for a format. -/
theorem valid_eq (f : Format) (d : Datum) : valid f d = decide (d.Valid f) := by
  rcases d with ⟨s, c, q⟩ | s | ⟨s, t, p⟩
  · change Bool.and (Nat.ble (Nat.succ c) (Nat.mul 10 (Nat.pow 1000 f.declets)))
        (offsets q f.bias fun above below =>
          Bool.and (Nat.beq below 0)
            (Nat.ble (Nat.succ above) (Nat.mul 3 (Nat.pow 2 f.exponentBits)))) =
      decide (c < f.coefficientBound ∧ 0 ≤ q + f.bias ∧ (q + f.bias).toNat < f.exponentBound)
    rw [offsets_eq, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, decide_eq_true_eq]
    change (c + 1 ≤ f.coefficientBound ∧ (-(q + f.bias)).toNat = 0 ∧
      (q + f.bias).toNat + 1 ≤ f.exponentBound) ↔ _
    omega
  · rfl
  · change Nat.ble (Nat.succ p) (Nat.pow 1000 f.declets) = decide (p < f.payloadBound)
    rw [natBle_eq]
    rfl

/-- `encodeFinite` is the finite encoding of the codec of each encoding. -/
theorem encodeFinite_eq (encoding : Encoding) (f : Format) (c e : Nat) :
    encodeFinite encoding f c e = encoding.codec.encodeFinite f c e := by
  cases encoding
  · change Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ c) (8 * f.trailingBase))
        (24 * (f.exponentBase * f.trailingBase) + e * (2 * f.trailingBase) +
          (c - 8 * f.trailingBase))
        (e * (8 * f.trailingBase) + c) = BID.encodeFinite f c e
    rw [casesOn_lt]
    rfl
  · change (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ (c / f.payloadBound)) 8)
          (24 + 2 * (e / f.exponentBase) + (c / f.payloadBound - 8))
          (8 * (e / f.exponentBase) + c / f.payloadBound)) *
          (f.exponentBase * f.trailingBase) + e % f.exponentBase * f.trailingBase +
        encodeTrailing f.declets (c % f.payloadBound) = DPD.encodeFinite f c e
    rw [casesOn_lt, encodeTrailing_eq]
    rfl

/-- `encodePayload` is the payload encoding of the codec of each encoding. -/
theorem encodePayload_eq (encoding : Encoding) (f : Format) (p : Nat) :
    encodePayload encoding f p = encoding.codec.encodePayload f p := by
  cases encoding
  · rfl
  · exact encodeTrailing_eq f.declets p

/-- The sign bit in front of the bits below it, as the reference packs them. -/
theorem pack_eq (f : Format) (negative : Bool) (payload : Nat) :
    BitVec.ofNat f.bitWidth
        (Nat.add (Bool.casesOn (motive := fun _ => Nat) negative 0 f.signBase) payload) =
      Bits.pack f negative payload := by
  cases negative <;> rfl

/-- `encodeNat` is the word that the reference assembles, for both encodings. -/
theorem encode_eq (encoding : Encoding) (f : Format) (d : Datum) :
    BitVec.ofNat f.bitWidth (encodeNat encoding f d) = encoding.codec.encode f d := by
  rcases d with ⟨s, c, q⟩ | s | ⟨s, t, p⟩
  · change BitVec.ofNat f.bitWidth
        (Nat.add (Bool.casesOn (motive := fun _ => Nat) s 0 f.signBase)
          (encodeFinite encoding f c (offsets q f.bias fun above _ => above))) = _
    rw [pack_eq, offsets_eq, encodeFinite_eq]
    rfl
  · exact pack_eq f s _
  · change BitVec.ofNat f.bitWidth
        (Nat.add (Bool.casesOn (motive := fun _ => Nat) s 0 f.signBase)
          (Nat.add
            (Nat.add (Nat.mul 31 (Nat.mul f.exponentBase f.trailingBase))
              (Bool.casesOn (motive := fun _ => Nat) t 0
                (Nat.div (Nat.mul f.exponentBase f.trailingBase) 2)))
            (encodePayload encoding f p))) = _
    rw [pack_eq, encodePayload_eq]
    cases t <;> rfl

/--
`encodeNat?` is the checked encoding of the reference, for both encodings, every format and
every datum.
-/
theorem encode?_eq (encoding : Encoding) (f : Format) (d : Datum) :
    encoding.encode? f d = (encodeNat? encoding f d).map (BitVec.ofNat f.bitWidth) := by
  change (if d.Valid f then some (encoding.codec.encode f d) else none) =
    (Bool.casesOn (motive := fun _ => Option Nat) (valid f d) none
      (some (encodeNat encoding f d))).map (BitVec.ofNat f.bitWidth)
  rw [valid_eq]
  by_cases hvalid : d.Valid f
  · rw [ite_eq_left hvalid, decide_eq_true hvalid]
    exact congrArg some (encode_eq encoding f d).symm
  · rw [ite_eq_right hvalid, decide_eq_false hvalid]
    rfl

/-- `decodeFinite` is the finite decoding of the codec of each encoding. -/
theorem decodeFinite_eq (encoding : Encoding) (f : Format) (s : Bool) (n : Nat) :
    decodeFinite encoding f s n =
      Datum.ofBiased f s (encoding.codec.decodeFinite f n).1
        (encoding.codec.decodeFinite f n).2 := by
  cases encoding
  · change Datum.ofBiased f s
        (Bool.casesOn (motive := fun _ => Nat)
          (Nat.ble
            (Nat.succ (Bool.casesOn (motive := fun _ => Nat)
              (Nat.ble (Nat.succ n) (24 * (f.exponentBase * f.trailingBase)))
              (8 * f.trailingBase +
                (n - 24 * (f.exponentBase * f.trailingBase)) % (2 * f.trailingBase))
              (n % (8 * f.trailingBase))))
            f.coefficientBound)
          0
          (Bool.casesOn (motive := fun _ => Nat)
            (Nat.ble (Nat.succ n) (24 * (f.exponentBase * f.trailingBase)))
            (8 * f.trailingBase +
              (n - 24 * (f.exponentBase * f.trailingBase)) % (2 * f.trailingBase))
            (n % (8 * f.trailingBase))))
        (Bool.casesOn (motive := fun _ => Nat)
          (Nat.ble (Nat.succ n) (24 * (f.exponentBase * f.trailingBase)))
          ((n - 24 * (f.exponentBase * f.trailingBase)) / (2 * f.trailingBase))
          (n / (8 * f.trailingBase))) = _
    simp only [casesOn_lt]
    rfl
  · change Datum.ofBiased f s
        ((Bool.casesOn (motive := fun _ => Nat)
            (Nat.ble (Nat.succ (n / (f.exponentBase * f.trailingBase))) 24)
            (8 + n / (f.exponentBase * f.trailingBase) % 2)
            (n / (f.exponentBase * f.trailingBase) % 8)) * f.payloadBound +
          decodeTrailing f.declets (n % f.trailingBase))
        ((Bool.casesOn (motive := fun _ => Nat)
            (Nat.ble (Nat.succ (n / (f.exponentBase * f.trailingBase))) 24)
            ((n / (f.exponentBase * f.trailingBase) - 24) / 2)
            (n / (f.exponentBase * f.trailingBase) / 8)) * f.exponentBase +
          n / f.trailingBase % f.exponentBase) = _
    simp only [casesOn_lt, decodeTrailing_eq]
    rfl

/-- `decodePayload` is the payload decoding of the codec of each encoding. -/
theorem decodePayload_eq (encoding : Encoding) (f : Format) (n : Nat) :
    decodePayload encoding f n = encoding.codec.decodePayload f n := by
  cases encoding
  · change Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ n) f.payloadBound) 0 n = _
    rw [casesOn_lt]
    rfl
  · exact decodeTrailing_eq f.declets n

/--
`decodeNat` is the decoding of the reference, for both encodings, every format and every
word.
-/
theorem decode_eq (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    encoding.decode f word = decodeNat encoding f word.toNat := by
  change _ = Bool.casesOn (motive := fun _ => Datum)
    (Nat.ble (Nat.succ (word.toNat % f.signBase / (f.exponentBase * f.trailingBase))) 30)
    (Bool.casesOn (motive := fun _ => Datum)
      (Nat.beq (word.toNat % f.signBase / (f.exponentBase * f.trailingBase)) 30)
      (.nan (!Nat.beq (word.toNat / f.signBase) 0)
        (Nat.beq (word.toNat % f.signBase / (f.exponentBase * f.trailingBase / 2) % 2) 1)
        (decodePayload encoding f (word.toNat % f.signBase % f.trailingBase)))
      (.infinity (!Nat.beq (word.toNat / f.signBase) 0)))
    (decodeFinite encoding f (!Nat.beq (word.toNat / f.signBase) 0) (word.toNat % f.signBase))
  rw [casesOn_lt, casesOn_beq, decodeFinite_eq, decodePayload_eq]
  rfl

/-! ## The operations of the standard -/

/-- `encodeDecimal` is the kernel encoding with the decimal encoding of the significand. -/
@[kernel_optimize] theorem encodeDecimal_eq (f : Format) (d : Datum) :
    encodeDecimal f d = (encodeNat? .dpd f d).map (BitVec.ofNat f.bitWidth) :=
  encode?_eq .dpd f d

/-- `encodeBinary` is the kernel encoding with the binary encoding of the significand. -/
@[kernel_optimize] theorem encodeBinary_eq (f : Format) (d : Datum) :
    encodeBinary f d = (encodeNat? .bid f d).map (BitVec.ofNat f.bitWidth) :=
  encode?_eq .bid f d

/-- `decodeDecimal` is the kernel decoding with the decimal encoding of the significand. -/
@[kernel_optimize] theorem decodeDecimal_eq (f : Format) (word : BitVec f.bitWidth) :
    decodeDecimal f word = decodeNat .dpd f word.toNat :=
  decode_eq .dpd f word

/-- `decodeBinary` is the kernel decoding with the binary encoding of the significand. -/
@[kernel_optimize] theorem decodeBinary_eq (f : Format) (word : BitVec f.bitWidth) :
    decodeBinary f word = decodeNat .bid f word.toNat :=
  decode_eq .bid f word

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
