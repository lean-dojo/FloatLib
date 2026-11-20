/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Numerics.Kernel.Bits.Shape

/-!
# Kernel path of decimal arithmetic

`Arithmetic.add`, `sub`, `mul` and `fma` are specified with exact rational intermediates: the
operands become rationals, the exact result is projected onto the format through `Nat.log`, a
rational quotient and a loop that strips trailing zeros. Lean's kernel computes natively only
on natural-number literals, so it spends milliseconds on one such operation.

This module computes the same outcomes on the fields of the data: the coefficients as natural
numbers, the quantum exponents as offsets from the least quantum of the format. `project` rounds
an exact value `coefficient × 10 ^ exponent` whose preferred quantum is its own exponent, which
is the case of a sum, a difference and a product. It needs one digit count (`decimalLength`), a
few powers of ten, one division with remainder when digits are dropped, and no loop: at its own
exponent the preferred cohort member has a closed form.

`add`, `sub` and `mul` handle two finite operands with it and leave every other case to the
specification, which is already a match on constructors. `fma` adds the third datum to the
exact product of the first two, which is a coefficient at an exponent like any other datum.

The theorems `add_eq`, `sub_eq`, `mul_eq` and `fma_eq` of `KernelPath.Proof` prove that these
functions are the specified operations for every format, rounding direction and operands, valid
or not. They are tagged `@[kernel_optimize]`, so `float_decide` rewrites with them.

The stages are written with `casesOn` and numerals, which Lean compiles. `kernel_shape` declares
each stage as Lean's kernel evaluates it best (`add.kernel` and its siblings: recursors, literals
and the kernel arithmetic of `Int`), and `float_decide` evaluates those.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics.Kernel (size)

/-- One for `true` and zero for `false`. -/
def flag (b : Bool) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) b 0 1

/-!
## Integers as pairs of naturals

The kernel computes on natural-number literals only, and an operation on `Int` costs it as much
as the rest of an addition. A quantum exponent is therefore read once, by cases on its
constructor, as its distance above and below a reference, and a result exponent is built once
from a natural offset.
-/

/--
`k (x + y).toNat (-(x + y)).toNat`, by cases on the constructors (`offsets_eq`): how far the
sum lies above zero and below zero, one of the two being zero.
-/
def offsets {α : Type} (x y : Int) (k : Nat → Nat → α) : α :=
  Int.casesOn (motive := fun _ => α) x
    (fun m => Int.casesOn (motive := fun _ => α) y
      (fun n => k (Nat.add m n) 0)
      (fun n => k (Nat.sub m (Nat.succ n)) (Nat.sub (Nat.succ n) m)))
    (fun m => Int.casesOn (motive := fun _ => α) y
      (fun n => k (Nat.sub n (Nat.succ m)) (Nat.sub (Nat.succ m) n))
      (fun n => k 0 (Nat.add (Nat.succ m) (Nat.succ n))))

/--
`k (x - y).toNat (y - x).toNat`, by cases on the constructors (`gaps_eq`): how far `x` lies
above `y` and below `y`, one of the two being zero.
-/
def gaps {α : Type} (x y : Int) (k : Nat → Nat → α) : α :=
  Int.casesOn (motive := fun _ => α) x
    (fun m => Int.casesOn (motive := fun _ => α) y
      (fun n => k (Nat.sub m n) (Nat.sub n m))
      (fun n => k (Nat.add m (Nat.succ n)) 0))
    (fun m => Int.casesOn (motive := fun _ => α) y
      (fun n => k 0 (Nat.add n (Nat.succ m)))
      (fun n => k (Nat.sub n m) (Nat.sub m n)))

/--
`k (x + y + z).toNat (-(x + y + z)).toNat`, by cases on the constructors (`offsets3_eq`): each
integer contributes to the positive or to the negative total, and the two totals are compared
once.
-/
def offsets3 {α : Type} (x y z : Int) (k : Nat → Nat → α) : α :=
  (fun (part : Int → Nat → Nat → (Nat → Nat → α) → α) =>
    part x 0 0 fun px nx => part y px nx fun py ny => part z py ny fun p n =>
      k (Nat.sub p n) (Nat.sub n p))
    (fun value positive negative next =>
      Int.casesOn (motive := fun _ => α) value
        (fun m => next (Nat.add positive m) negative)
        (fun m => next positive (Nat.add negative (Nat.succ m))))

/-- `offset - bias` as an integer, by cases on the constructor of `bias` (`quantumAt_eq`). -/
def quantumAt (offset : Nat) (bias : Int) : Int :=
  Int.casesOn (motive := fun _ => Int) bias
    (fun b => Int.subNatNat offset b) (fun b => Int.ofNat (Nat.add offset (Nat.succ b)))

/--
The number of decimal digits of a nonzero natural number, `Nat.log 10 c + 1`
(`decimalLength_eq`). The bit length gives an estimate `d`, and two comparisons with powers of
ten prove that the count is `d` or `d + 1`. An estimate that is further off, which needs a
number of thousands of bits, is replaced by the count through `Nat.log`.
-/
def decimalLength (c : Nat) : Nat :=
  (fun d =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.pow 10 d) c)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.pow 10 (Nat.sub d 1)) c)
        (Nat.succ (Nat.log 10 c)) d)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.pow 10 (Nat.succ d)) c)
        (Nat.succ d) (Nat.succ (Nat.log 10 c))))
    (Nat.shiftRight (Nat.mul (size c) 1233) 12)

/--
A bound on the number of decimal digits of `c` from its bit length alone, `c < 10 ^ digitBound c`
(`lt_ten_pow_digitBound`): the bit length times `1234 / 4096`, which is above `log₁₀ 2`, plus one.
It costs one bit length where the exact count `decimalLength` costs two more comparisons.
-/
def digitBound (c : Nat) : Nat :=
  Nat.succ (Nat.shiftRight (Nat.mul (size c) 1234) 12)

/--
The amount, zero or one, by which a coefficient whose dropped digits are `remainder` out of
`denominator` is incremented: the rule of `RoundingMode.roundMagnitude` on integers
(`roundMagnitude_natCast_div`). To nearest, the quotient of twice the remainder, plus the parity
of the coefficient when ties go to even, by the denominator is that amount.
-/
def increment (mode : RoundingMode) (negative : Bool) (lower remainder denominator : Nat) : Nat :=
  RoundingMode.casesOn (motive := fun _ => Nat) mode
    (Nat.div (Nat.add (Nat.mul 2 remainder) (Nat.mod lower 2)) (Nat.succ denominator))
    (Nat.div (Nat.mul 2 remainder) denominator)
    0
    (Bool.casesOn (motive := fun _ => Nat) negative (flag (Nat.ble 1 remainder)) 0)
    (Bool.casesOn (motive := fun _ => Nat) negative 0 (flag (Nat.ble 1 remainder)))

/-- The outcome of an overflow: the infinity or the largest finite value, by the direction. -/
def overflow (f : Format) (mode : RoundingMode) (negative : Bool) : Outcome :=
  { value := if mode.overflowToInfinity negative then .infinity negative else f.maxFinite negative
    status := { overflow := true, inexact := true } }

/--
The outcome of a rounded nonzero coefficient at the quantum `shift` above the least quantum: an
overflow when that quantum is beyond the exponent bound `bound`, and the datum with its flags
otherwise. `tiny` says whether the exact value is below the least normal magnitude.
-/
def deliver (f : Format) (mode : RoundingMode) (negative : Bool) (bound coefficient shift : Nat)
    (inexact tiny : Bool) : Outcome :=
  Bool.casesOn (motive := fun _ => Outcome) (Nat.ble bound shift)
    { value := .finite negative coefficient (quantumAt shift f.bias)
      status := { inexact := inexact, underflow := Bool.and tiny inexact } }
    (overflow f mode negative)

/--
The outcome of a nonzero value that loses `dropped` digits. `bound` is the exponent bound of the
format, `full` is ten to its precision, `shift` the rounding quantum above the least quantum and
`tiny` whether the exact value is below the least normal magnitude. A coefficient that rounds up
to `full` is delivered as its leading digit one quantum higher.
-/
def projectRounded (f : Format) (mode : RoundingMode) (negative : Bool) (coefficient : Nat)
    (bound full shift dropped : Nat) (tiny : Bool) : Outcome :=
  (fun denominator =>
    (fun lower remainder =>
      (fun rounded =>
        Bool.casesOn (motive := fun _ => Outcome) (Nat.beq rounded full)
          (deliver f mode negative bound rounded shift (Nat.ble 1 remainder) tiny)
          (deliver f mode negative bound (Nat.div full 10) (Nat.succ shift)
            (Nat.ble 1 remainder) tiny))
        (Nat.add lower (increment mode negative lower remainder denominator)))
      (Nat.div coefficient denominator) (Nat.mod coefficient denominator))
    (Nat.pow 10 dropped)

/--
The outcome of a nonzero value that does not fit at its own exponent: its digits are counted to
find the rounding quantum, and `projectRounded` drops the digits below it.
-/
def projectInexact (f : Format) (mode : RoundingMode) (negative : Bool) (coefficient : Nat)
    (above below bound full : Nat) : Outcome :=
  (fun digits precision =>
    (fun shift =>
      projectRounded f mode negative coefficient bound full shift
        (Nat.sub (Nat.add shift below) above)
        (Nat.ble (Nat.succ (Nat.add digits above)) (Nat.add precision below)))
      (Nat.sub (Nat.add (Nat.sub (Nat.add digits above) below)
        (flag (Nat.ble (Nat.add digits above) below))) precision))
    (decimalLength coefficient) (Nat.succ (Nat.mul 3 f.declets))

/--
The outcome of a nonzero value within the precision whose exponent lies above the largest
quantum: the coefficient is scaled to that quantum, and it overflows when it no longer fits.
-/
def projectAbove (f : Format) (mode : RoundingMode) (negative : Bool) (coefficient : Nat)
    (above bound full : Nat) : Outcome :=
  (fun scaled =>
    Bool.casesOn (motive := fun _ => Outcome) (Nat.ble (Nat.succ scaled) full)
      (overflow f mode negative)
      { value := .finite negative scaled (quantumAt (Nat.sub bound 1) f.bias) })
    (Nat.mul coefficient (Nat.pow 10 (Nat.sub above (Nat.sub bound 1))))

/-- The zero of sign `negative` at the quantum of the format nearest to `exponent`. -/
def projectZero (f : Format) (negative : Bool) (exponent : Int) (above below bound : Nat) :
    Outcome :=
  { value := .finite negative 0
      (Bool.casesOn (motive := fun _ => Int) (Nat.beq below 0)
        (quantumAt 0 f.bias)
        (Bool.casesOn (motive := fun _ => Int) (Nat.ble bound above)
          exponent (quantumAt (Nat.sub bound 1) f.bias))) }

/--
`project` with the exponent read as its offsets `above` and `below` the least quantum, the
exponent bound of the format and `full`, ten to its precision.

A coefficient within the precision at an exponent of the format is delivered as it is, after
three comparisons.
-/
def projectAt (f : Format) (mode : RoundingMode) (negative : Bool) (coefficient : Nat)
    (exponent : Int) (above below bound full : Nat) : Outcome :=
  Bool.casesOn (motive := fun _ => Outcome) (Nat.beq coefficient 0)
    (Bool.casesOn (motive := fun _ => Outcome) (Nat.beq below 0)
      (projectInexact f mode negative coefficient above below bound full)
      (Bool.casesOn (motive := fun _ => Outcome) (Nat.ble (Nat.succ coefficient) full)
        (projectInexact f mode negative coefficient above below bound full)
        (Bool.casesOn (motive := fun _ => Outcome) (Nat.ble bound above)
          { value := .finite negative coefficient exponent }
          (projectAbove f mode negative coefficient above bound full))))
    (projectZero f negative exponent above below bound)

/--
Round the exact value `coefficient × 10 ^ exponent` of sign `negative` into `f`, with its own
exponent as the preferred quantum: `projectMagnitude f mode negative (coefficient * 10 ^ exponent)
exponent` (`project_eq`).
-/
def project (f : Format) (mode : RoundingMode) (negative : Bool) (coefficient : Nat)
    (exponent : Int) : Outcome :=
  offsets exponent f.bias fun above below =>
    projectAt f mode negative coefficient exponent above below
      (Nat.mul 3 (Nat.pow 2 f.exponentBits)) (Nat.pow 10 (Nat.succ (Nat.mul 3 f.declets)))

/-- Whether the direction is toward negative infinity, the one that gives a cancellation a
negative zero. -/
def isDown : RoundingMode → Bool
  | .down => true
  | _ => false

/-- Whether two Booleans differ, `Bool.xor`, by cases. -/
def differ (x y : Bool) : Bool :=
  Bool.casesOn (motive := fun _ => Bool) x y (Bool.casesOn (motive := fun _ => Bool) y true false)

/--
Sum of two finite data whose exponents are `above` and `below` apart (one of the two is zero):
the coefficients are aligned at the smaller exponent, added or subtracted by their signs, and
the exact sum is projected at that exponent.
-/
def addFinite (f : Format) (mode : RoundingMode) (sx : Bool) (cx : Nat) (qx : Int)
    (sy : Bool) (cy : Nat) (qy : Int) (above below : Nat) : Outcome :=
  (fun a b exponent =>
    Bool.casesOn (motive := fun _ => Outcome) (differ sx sy)
      (project f mode sx (Nat.add a b) exponent)
      (Bool.casesOn (motive := fun _ => Outcome) (Nat.beq a b)
        (Bool.casesOn (motive := fun _ => Outcome) (Nat.ble b a)
          (project f mode sy (Nat.sub b a) exponent)
          (project f mode sx (Nat.sub a b) exponent))
        (project f mode (isDown mode) 0 exponent)))
    (Nat.mul cx (Nat.pow 10 above)) (Nat.mul cy (Nat.pow 10 below))
    (Bool.casesOn (motive := fun _ => Int) (Nat.beq below 0) qx qy)

/-- Sum of two finite data given by their fields: `addFinite` on the gaps of the exponents. -/
def addFields (f : Format) (mode : RoundingMode) (sx : Bool) (cx : Nat) (qx : Int)
    (sy : Bool) (cy : Nat) (qy : Int) : Outcome :=
  gaps qx qy fun above below => addFinite f mode sx cx qx sy cy qy above below

/--
Kernel form of `Arithmetic.add` (`add_eq`): two finite data are added on their fields by
`addFields`, and every other case is the specification.
-/
def add (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun sx cx qx => Datum.casesOn (motive := fun _ => Outcome) y
      (fun sy cy qy => addFields f mode sx cx qx sy cy qy)
      (fun _ => Arithmetic.add f mode x y) (fun _ _ _ => Arithmetic.add f mode x y))
    (fun _ => Arithmetic.add f mode x y) (fun _ _ _ => Arithmetic.add f mode x y)

/--
Kernel form of `Arithmetic.sub` (`sub_eq`): two finite data are subtracted as the sum with the
negated subtrahend, and every other case is the specification.
-/
def sub (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun sx cx qx => Datum.casesOn (motive := fun _ => Outcome) y
      (fun sy cy qy =>
        addFields f mode sx cx qx (Bool.casesOn (motive := fun _ => Bool) sy true false) cy qy)
      (fun _ => Arithmetic.sub f mode x y) (fun _ _ _ => Arithmetic.sub f mode x y))
    (fun _ => Arithmetic.sub f mode x y) (fun _ _ _ => Arithmetic.sub f mode x y)

/--
Kernel form of `Arithmetic.mul` (`mul_eq`): the product of two finite data is the product of
the coefficients at the sum of the exponents, and every other case is the specification. The
sum of the exponents is formed once, as its offsets from the least quantum.
-/
def mul (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun sx cx qx => Datum.casesOn (motive := fun _ => Outcome) y
      (fun sy cy qy =>
        offsets3 qx qy f.bias fun above below =>
          projectAt f mode (differ sx sy) (Nat.mul cx cy) (quantumAt above f.bias) above below
            (Nat.mul 3 (Nat.pow 2 f.exponentBits)) (Nat.pow 10 (Nat.succ (Nat.mul 3 f.declets))))
      (fun _ => Arithmetic.mul f mode x y) (fun _ _ _ => Arithmetic.mul f mode x y))
    (fun _ => Arithmetic.mul f mode x y) (fun _ _ _ => Arithmetic.mul f mode x y)

/--
Kernel form of `Arithmetic.fma` (`fma_eq`): for three finite data the exact product is the
product of the coefficients at the sum of the exponents, and `addFields` adds the third datum
to it with one rounding. Every other case is the specification.
-/
def fma (f : Format) (mode : RoundingMode) (x y z : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun sx cx qx => Datum.casesOn (motive := fun _ => Outcome) y
      (fun sy cy qy => Datum.casesOn (motive := fun _ => Outcome) z
        (fun sz cz qz =>
          addFields f mode (differ sx sy) (Nat.mul cx cy) (Int.add qx qy) sz cz qz)
        (fun _ => Arithmetic.fma f mode x y z) (fun _ _ _ => Arithmetic.fma f mode x y z))
      (fun _ => Arithmetic.fma f mode x y z) (fun _ _ _ => Arithmetic.fma f mode x y z))
    (fun _ => Arithmetic.fma f mode x y z) (fun _ _ _ => Arithmetic.fma f mode x y z)

/-- Whether two integers are equal, by cases on their constructors (`intBeq_eq`). -/
def intBeq (x y : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) x
    (fun m => Int.casesOn (motive := fun _ => Bool) y (fun n => Nat.beq m n) (fun _ => false))
    (fun m => Int.casesOn (motive := fun _ => Bool) y (fun _ => false) (fun n => Nat.beq m n))

/-- Whether two Booleans are equal. -/
def boolBeq (x y : Bool) : Bool :=
  Bool.casesOn (motive := fun _ => Bool) x (Bool.casesOn (motive := fun _ => Bool) y true false) y

/-- Whether two data are equal, field by field on naturals (`datumBeq_eq`). -/
def datumBeq (x y : Datum) : Bool :=
  Datum.casesOn (motive := fun _ => Bool) x
    (fun sx cx qx => Datum.casesOn (motive := fun _ => Bool) y
      (fun sy cy qy => Bool.casesOn (motive := fun _ => Bool) (Nat.beq cx cy) false
        (Bool.casesOn (motive := fun _ => Bool) (boolBeq sx sy) false (intBeq qx qy)))
      (fun _ => false) (fun _ _ _ => false))
    (fun sx => Datum.casesOn (motive := fun _ => Bool) y
      (fun _ _ _ => false) (fun sy => boolBeq sx sy) (fun _ _ _ => false))
    (fun sx tx px => Datum.casesOn (motive := fun _ => Bool) y
      (fun _ _ _ => false) (fun _ => false)
      (fun sy ty py => Bool.casesOn (motive := fun _ => Bool) (Nat.beq px py) false
        (Bool.casesOn (motive := fun _ => Bool) (boolBeq sx sy) false (boolBeq tx ty))))

/-! ## Kernel shapes -/

kernel_shape flag
kernel_shape offsets
kernel_shape gaps
kernel_shape offsets3
kernel_shape quantumAt
kernel_shape decimalLength
kernel_shape digitBound
kernel_shape increment
kernel_shape overflow
kernel_shape deliver
kernel_shape projectRounded
kernel_shape projectInexact
kernel_shape projectAbove
kernel_shape projectZero
kernel_shape projectAt
kernel_shape project
kernel_shape isDown
kernel_shape differ
kernel_shape addFinite
kernel_shape addFields
kernel_shape add
kernel_shape sub
kernel_shape mul
kernel_shape fma
kernel_shape intBeq
kernel_shape boolBeq
kernel_shape datumBeq

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
