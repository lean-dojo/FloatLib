/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits

/-!
# P3109 projection and arithmetic on natural-number encodings

P3109 Interim Report v4.1 (14 September 2026), §§4.7 and 4.10, an unapproved draft. These are
the decoding of a code, the projection of an exact value (precision rounding in each of the nine
modes, then saturation, then encoding) and the arithmetic operations as functions of the
encodings, written with the kernel's fast operations and `Bool.casesOn` only. A format is given
by four numbers: the width `K`, the precision `P`, `sg` (one for a signed format, zero for an
unsigned one) and `ex` (one for the extended domain with infinities, zero for the finite one).

* `classOf`, `signOf`, `magnitudeOf`, `significandOf`, `exponentOf`: the class of a code (zero
  finite, one `+∞`, two `-∞`, three NaN) and the fields of a finite code. A finite code denotes
  `(-1) ^ sign * significand * 2 ^ (exponent - exponentBias - trailingBits)`.
* `numeratorOf`, `denominatorOf`: the same value as a ratio of natural numbers with a power of
  two as its denominator, so that exact arithmetic on decoded operands is integer arithmetic on
  pairs, with no normalization.
* A rounding mode is the triple of `modeIndex` (zero to eight in the order of
  `RoundingMode`), the width `N` and the value `R` of the random word of a stochastic mode. A
  saturation mode is zero (finite), one (propagate) or two (none).
* `project K P sg ex mi N R si cls s n d` is the code of the projection of the closed value of
  class `cls`: for a finite class the ratio `(-1) ^ s * n / d`, rounded to the precision grid in
  the mode (`roundedOf`, with the quantum `quantumOf`), saturated at the finite endpoints
  (`exceeds`, `aboveCode`, `belowCode`) and encoded (`magnitudeCode`).
* `add`, `sub`, `mul`, `div`, `fma`, `neg`, `abs` and `convert` take the three parameters of
  each operand format and of the destination and return the code of the operation of §4.10,
  with the report's results for infinities and NaN.

`KernelPath.Proof` proves each of them equal to the reference operation, for every descriptor,
mode, saturation and operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics.Kernel

/-! ## Descriptor quantities -/

/-- The number of stored trailing significand bits, `P - 1`. -/
def trailingBits (P : Nat) : Nat := Nat.sub P 1

/-- The exponent bias `2 ^ (W - 1)`, with `W = K - P + 1 - sg` the exponent width. -/
def exponentBias (K P sg : Nat) : Nat :=
  Nat.shiftLeft 1 (Nat.sub (Nat.sub (Nat.succ K) (Nat.add P sg)) 1)

/-- The first code of the negative half of a signed format, `2 ^ (K - 1)`. -/
def signBoundary (K : Nat) : Nat := Nat.shiftLeft 1 (Nat.sub K 1)

/-- The code of NaN: the sign boundary of a signed format, the last code of an unsigned one. -/
def nanBits (K sg : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq sg 0)
    (signBoundary K) (Nat.sub (Nat.shiftLeft 1 K) 1)

/-- The code of `+∞` in an extended format. -/
def positiveInfinityBits (K sg : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq sg 0)
    (Nat.sub (signBoundary K) 1) (Nat.sub (Nat.shiftLeft 1 K) 2)

/-- The code of `-∞` in a signed extended format. -/
def negativeInfinityBits (K : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 K) 1

/-- The largest finite positive code. -/
def maxFiniteBits (K sg ex : Nat) : Nat := Nat.sub (positiveInfinityBits K sg) ex

/-! ## Decoding -/

/-- The class of a code: zero finite, one `+∞`, two `-∞`, three NaN. -/
def classOf (K sg ex a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq a (nanBits K sg))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ex 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq a (positiveInfinityBits K sg))
        (Bool.casesOn (motive := fun _ => Nat)
          (Bool.and (Nat.beq sg 1) (Nat.beq a (negativeInfinityBits K))) 0 2)
        1)
      0)
    3

/-- The sign bit of a finite code: one above the sign boundary of a signed format. -/
def signOf (K sg a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.and (Nat.beq sg 1) (Nat.ble (Nat.succ (signBoundary K)) a)) 0 1

/-- The magnitude code of a finite code. -/
def magnitudeOf (K sg a : Nat) : Nat := Nat.sub a (Nat.mul (signOf K sg a) (signBoundary K))

/-- The significand of a magnitude code: the trailing bits, with the leading one unless the
exponent field is zero. -/
def significandOf (P m : Nat) : Nat :=
  (fun T =>
    Nat.add (lowBits m T)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight m T) 0)
        (Nat.shiftLeft 1 T) 0))
    (trailingBits P)

/-- The biased exponent of a magnitude code: its exponent field, and one for a subnormal. -/
def exponentOf (P m : Nat) : Nat := maxNat (Nat.shiftRight m (trailingBits P)) 1

/-- The numerator of the value of a finite code as a ratio with a power of two below it. -/
def numeratorOf (K P sg a : Nat) : Nat :=
  (fun m =>
    Nat.shiftLeft (significandOf P m)
      (Nat.sub (exponentOf P m) (Nat.add (exponentBias K P sg) (trailingBits P))))
    (magnitudeOf K sg a)

/-- The denominator of the value of a finite code: a power of two. -/
def denominatorOf (K P sg a : Nat) : Nat :=
  Nat.shiftLeft 1
    (Nat.sub (Nat.add (exponentBias K P sg) (trailingBits P))
      (exponentOf P (magnitudeOf K sg a)))

/-! ## Rounding to the precision grid -/

/--
The quantum exponent of the ratio `n / d` plus the bias `log₂ d + 1 + B + P`, with `B` the
exponent bias: `max (⌊log₂ (n / d)⌋) (1 - B) - P + 1` in natural numbers.
-/
def quantumOf (B n d : Nat) : Nat :=
  (fun ln ld =>
    Nat.succ
      (maxNat
        (Nat.add
          (Nat.sub (Nat.succ ln)
            (Bool.casesOn (motive := fun _ => Nat)
              (Nat.ble (Nat.succ (Nat.shiftLeft n ld)) (Nat.shiftLeft d ln)) 0 1))
          B)
        (Nat.add ld 2)))
    (Nat.sub (size n) 1) (Nat.sub (size d) 1)

/-- The nearest integer to `a / b`, ties to even. -/
def nearestEven (a b : Nat) : Nat :=
  (fun q r =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.ble b (Nat.mul 2 r))
      q
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq b (Nat.mul 2 r))
        (Nat.succ q)
        (Nat.add q (Nat.land q 1))))
    (Nat.div a b) (Nat.mod a b)

/--
Whether rounding selects the integer above the floor `lower` of a scaled ratio with remainder
`rem` over `den`, as zero or one: the nine modes of P3109 interim report v4.1, §4.7.4. `even` is
    one when the code of
the floor is even, and `s` is the sign bit.
-/
def roundAway (mi N R s even rem den : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq rem 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 4)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 1)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 2)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 3)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 5)
                (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 6)
                  (Bool.casesOn (motive := fun _ => Nat) (Nat.beq mi 7)
                    -- stochasticC
                    (Bool.casesOn (motive := fun _ => Nat)
                      (Nat.ble (Nat.shiftLeft 1 N)
                        (Nat.add (nearestEven (Nat.shiftLeft rem N) den) R)) 0 1)
                    -- stochasticB
                    (Bool.casesOn (motive := fun _ => Nat)
                      (Nat.ble (Nat.shiftLeft 1 (Nat.succ N))
                        (Nat.add (Nat.div (Nat.shiftLeft rem (Nat.succ N)) den)
                          (Nat.succ (Nat.mul 2 R)))) 0 1))
                  -- stochasticA
                  (Bool.casesOn (motive := fun _ => Nat)
                    (Nat.ble (Nat.shiftLeft 1 N)
                      (Nat.add (Nat.div (Nat.shiftLeft rem N) den) R)) 0 1))
                -- toOdd
                even)
              -- nearestAway
              (Bool.casesOn (motive := fun _ => Nat) (Nat.ble den (Nat.mul 2 rem)) 0 1))
            -- down
            s)
          -- up
          (Nat.sub 1 s))
        -- towardZero
        0)
      -- nearest
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble den (Nat.mul 2 rem))
        0
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq den (Nat.mul 2 rem))
          1 (Nat.sub 1 even))))
    0

/--
The significand of the ratio `n / d` rounded to the precision grid: the floor of
`n / d / 2 ^ quantum` plus the decision of the mode. `Qb` is `quantumOf B n d`.
-/
def roundedOf (P B mi N R s n d Qb : Nat) : Nat :=
  (fun beta =>
    (fun num den =>
      (fun lower rem =>
        Nat.add lower
          (roundAway mi N R s
            (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 2 P)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq lower 0)
                (Nat.sub 1 (Nat.land (Nat.add (Nat.add Qb beta) B) 1)) 1)
              (Nat.sub 1 (Nat.land lower 1)))
            rem den))
        (Nat.div num den) (Nat.mod num den))
      (Nat.shiftLeft n (Nat.sub beta Qb)) (Nat.shiftLeft d (Nat.sub Qb beta)))
    (Nat.add (Nat.add (Nat.sub (size d) 1) 1) (Nat.add B P))

/-! ## Saturation and encoding -/

/-- The magnitude code of the rounded significand `r` at the quantum `Qb`, with the bias
`beta = log₂ d + 1 + B + P`: the report's encoding of a positive finite datum (§4.7.6). -/
def magnitudeCode (P B r Qb beta : Nat) : Nat :=
  (fun T =>
    (fun e =>
      (fun sig =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.shiftLeft 1 T) sig)
          (lowBits sig T)
          (Nat.add (lowBits sig T) (Nat.shiftLeft (Nat.sub (Nat.add e B) beta) T)))
        (Nat.shiftRight (Nat.shiftLeft r (Nat.sub (Nat.add Qb T) e)) (Nat.sub e (Nat.add Qb T))))
      (maxNat (Nat.add (Nat.sub (size r) 1) Qb) (Nat.sub (Nat.succ beta) B)))
    (trailingBits P)

/-- Whether the rounded magnitude `r * 2 ^ quantum` is above the largest finite value. -/
def exceeds (K P sg ex B r Qb beta : Nat) : Bool :=
  (fun m =>
    Nat.ble
      (Nat.succ (Nat.shiftLeft (significandOf P m) (Nat.add (exponentOf P m) beta)))
      (Nat.shiftLeft r (Nat.add (Nat.add Qb B) (trailingBits P))))
    (maxFiniteBits K sg ex)

/-- The code of the result above the finite range (§4.7.5). -/
def aboveCode (K sg ex mi si : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.or (Nat.ble si 1) (Bool.or (Nat.beq mi 0) (Nat.beq mi 2)))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ex 0)
      (positiveInfinityBits K sg) (nanBits K sg))
    (maxFiniteBits K sg ex)

/-- The code of the smallest finite value: the mirrored largest one, or zero when unsigned. -/
def minFiniteCode (K sg ex : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq sg 0)
    (Nat.add (signBoundary K) (maxFiniteBits K sg ex)) 0

/-- The code of the result below the finite range (§4.7.5). -/
def belowCode (K sg ex mi si : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.or (Nat.ble si 1) (Bool.or (Nat.beq mi 0) (Nat.beq mi 1)))
    (Bool.casesOn (motive := fun _ => Nat) (Bool.and (Nat.beq sg 1) (Nat.beq ex 1))
      (nanBits K sg) (negativeInfinityBits K))
    (minFiniteCode K sg ex)

/-- The code of the projection of the nonzero ratio `(-1) ^ s * n / d`. -/
def projectFinite (K P sg ex mi N R si s n d : Nat) : Nat :=
  (fun B =>
    (fun Qb beta =>
      (fun r =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq r 0)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq s 0)
            (Bool.casesOn (motive := fun _ => Nat)
              (Bool.or (Nat.beq sg 0) (exceeds K P sg ex B r Qb beta))
              (Nat.add (signBoundary K) (magnitudeCode P B r Qb beta))
              (belowCode K sg ex mi si))
            (Bool.casesOn (motive := fun _ => Nat) (exceeds K P sg ex B r Qb beta)
              (magnitudeCode P B r Qb beta)
              (aboveCode K sg ex mi si)))
          0)
        (roundedOf P B mi N R s n d Qb))
      (quantumOf B n d) (Nat.add (Nat.add (Nat.sub (size d) 1) 1) (Nat.add B P)))
    (exponentBias K P sg)

/--
The code of the projection of a closed value into the format `(K, P, sg, ex)`: class zero is the
ratio `(-1) ^ s * n / d` with `d ≠ 0`, one `+∞`, two `-∞`, three NaN (§4.7.3 to §4.7.6).
-/
def project (K P sg ex mi N R si cls s n d : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq cls 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cls 1)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cls 2)
        (nanBits K sg)
        -- -∞
        (Bool.casesOn (motive := fun _ => Nat)
          (Bool.and (Nat.ble 1 si) (Bool.and (Nat.beq sg 1) (Nat.beq ex 1)))
          (Bool.casesOn (motive := fun _ => Nat) (Nat.ble si 1)
            (nanBits K sg) (minFiniteCode K sg ex))
          (negativeInfinityBits K)))
      -- +∞
      (Bool.casesOn (motive := fun _ => Nat) (Bool.and (Nat.ble 1 si) (Nat.beq ex 1))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble si 1)
          (nanBits K sg) (maxFiniteBits K sg ex))
        (positiveInfinityBits K sg)))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq n 0)
      (projectFinite K P sg ex mi N R si s n d) 0)

/-! ## Exact closed arithmetic on classes and ratios -/

/-- The class of a negated closed value: the two infinities exchanged. -/
def negClass (c : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq c 1)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq c 2) c 1) 2

/-- The class of a sum (§4.10.3): NaN for a NaN operand and for opposite infinities. -/
def addClass (ca cb : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.ble 3 ca) (Nat.ble 3 cb))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ca 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cb 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ca cb) 3 ca)
        ca)
      cb)
    3

/-- The sign bit of the sum of `(-1) ^ sa * a` and `(-1) ^ sb * b`, for natural `a` and `b`. -/
def addSign (sa sb a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble b a) sb sa

/-- The magnitude of the sum of `(-1) ^ sa * a` and `(-1) ^ sb * b`. -/
def addMagnitude (sa sb a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb)
    (Nat.add (Nat.sub a b) (Nat.sub b a)) (Nat.add a b)

/-- The class of a product (§4.10.4): NaN for a NaN operand and for zero times infinity, and
the infinity with the product sign otherwise. `na` and `nb` are the numerators of the finite
operands and `sa` and `sb` their sign bits. -/
def mulClass (ca cb sa sb na nb : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.ble 3 ca) (Nat.ble 3 cb))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ca 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cb 0)
        (Nat.succ (Nat.xor (Nat.sub ca 1) (Nat.sub cb 1)))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nb 0)
          (Nat.succ (Nat.xor (Nat.sub ca 1) sb)) 3))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cb 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq na 0)
          (Nat.succ (Nat.xor (Nat.sub cb 1) sa)) 3)
        0))
    3

/-- The class of a quotient (§4.10.5): NaN for a NaN operand, for a zero divisor and for two
infinities, zero for a finite value over an infinity, and the signed infinity otherwise. -/
def divClass (ca cb sb nb : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Bool.or (Nat.ble 3 ca) (Nat.ble 3 cb))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cb 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ca 0) 3 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nb 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ca 0)
          (Nat.succ (Nat.xor (Nat.sub ca 1) sb)) 0)
        3))
    3

/-! ## The operations -/

/-- The code of the sum of the values of `a` and `b` (§4.10.3), or of their difference when
`flip` is one, projected once into the destination. -/
def add (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si flip a b : Nat) : Nat :=
  (fun ca cb sa sb na nb da db =>
    (fun x y =>
      project K P sg ex mi N R si (addClass ca cb) (addSign sa sb x y)
        (addMagnitude sa sb x y) (Nat.mul da db))
      (Nat.mul na db) (Nat.mul nb da))
    (classOf K₁ sg₁ ex₁ a)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq flip 0)
      (negClass (classOf K₂ sg₂ ex₂ b)) (classOf K₂ sg₂ ex₂ b))
    (signOf K₁ sg₁ a)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq flip 0)
      (Nat.sub 1 (signOf K₂ sg₂ b)) (signOf K₂ sg₂ b))
    (numeratorOf K₁ P₁ sg₁ a) (numeratorOf K₂ P₂ sg₂ b)
    (denominatorOf K₁ P₁ sg₁ a) (denominatorOf K₂ P₂ sg₂ b)

/-- The code of the product of the values of `a` and `b` (§4.10.4), projected once. -/
def mul (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  (fun ca cb sa sb na nb =>
    project K P sg ex mi N R si (mulClass ca cb sa sb na nb) (Nat.xor sa sb) (Nat.mul na nb)
      (Nat.mul (denominatorOf K₁ P₁ sg₁ a) (denominatorOf K₂ P₂ sg₂ b)))
    (classOf K₁ sg₁ ex₁ a) (classOf K₂ sg₂ ex₂ b) (signOf K₁ sg₁ a) (signOf K₂ sg₂ b)
    (numeratorOf K₁ P₁ sg₁ a) (numeratorOf K₂ P₂ sg₂ b)

/-- The code of the quotient of the values of `a` and `b` (§4.10.5), projected once. -/
def div (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  (fun ca cb sa sb na nb =>
    project K P sg ex mi N R si (divClass ca cb sb nb) (Nat.xor sa sb)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cb 0) 0
        (Nat.mul na (denominatorOf K₂ P₂ sg₂ b)))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq cb 0) 1
        (Nat.mul (denominatorOf K₁ P₁ sg₁ a) nb)))
    (classOf K₁ sg₁ ex₁ a) (classOf K₂ sg₂ ex₂ b) (signOf K₁ sg₁ a) (signOf K₂ sg₂ b)
    (numeratorOf K₁ P₁ sg₁ a) (numeratorOf K₂ P₂ sg₂ b)

/-- The code of `a * b + c` on the values (§4.10.6), projected once. -/
def fma (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) : Nat :=
  (fun ca cb sa sb na nb =>
    (fun cp sp np dp cc sc nc dc =>
      (fun x y =>
        project K P sg ex mi N R si (addClass cp cc) (addSign sp sc x y)
          (addMagnitude sp sc x y) (Nat.mul dp dc))
        (Nat.mul np dc) (Nat.mul nc dp))
      (mulClass ca cb sa sb na nb) (Nat.xor sa sb) (Nat.mul na nb)
      (Nat.mul (denominatorOf K₁ P₁ sg₁ a) (denominatorOf K₂ P₂ sg₂ b))
      (classOf K₃ sg₃ ex₃ c) (signOf K₃ sg₃ c) (numeratorOf K₃ P₃ sg₃ c)
      (denominatorOf K₃ P₃ sg₃ c))
    (classOf K₁ sg₁ ex₁ a) (classOf K₂ sg₂ ex₂ b) (signOf K₁ sg₁ a) (signOf K₂ sg₂ b)
    (numeratorOf K₁ P₁ sg₁ a) (numeratorOf K₂ P₂ sg₂ b)

/-- The code of the value of `a` in another format, negated when `flip` is one (§4.10.1), or
of its absolute value when `flip` is two, projected once. -/
def convert (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si flip a : Nat) : Nat :=
  (fun ca sa =>
    project K P sg ex mi N R si
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq flip 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq flip 1)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ca 2) ca 1)
          (negClass ca))
        ca)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq flip 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq flip 1) 0 (Nat.sub 1 sa))
        sa)
      (numeratorOf K₁ P₁ sg₁ a) (denominatorOf K₁ P₁ sg₁ a))
    (classOf K₁ sg₁ ex₁ a) (signOf K₁ sg₁ a)

end FloatLib.Floats.Formats.P3109.KernelPath
