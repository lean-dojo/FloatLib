/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Reference arithmetic timings

The six default operations on mixed operands and individual operand classes.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/ref.add[mixed]` -/
@[inline] def op533 (x y : Half) := ExecFloat.add x y
def timed533 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed533 xs ys k (mixQuick acc (Digest.quick (op533 xs[k]! ys[k]!)))
def full533 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full533 xs ys k (Digest.full (op533 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run533 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.add[mixed]" xs ys (mixFull dx dy) timed533 full533 trials reps

/-! ### `binary16/ref.sub[mixed]` -/
@[inline] def op534 (x y : Half) := ExecFloat.sub x y
def timed534 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed534 xs ys k (mixQuick acc (Digest.quick (op534 xs[k]! ys[k]!)))
def full534 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full534 xs ys k (Digest.full (op534 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run534 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.sub[mixed]" xs ys (mixFull dx dy) timed534 full534 trials reps

/-! ### `binary16/ref.mul[mixed]` -/
@[inline] def op535 (x y : Half) := ExecFloat.mul x y
def timed535 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed535 xs ys k (mixQuick acc (Digest.quick (op535 xs[k]! ys[k]!)))
def full535 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full535 xs ys k (Digest.full (op535 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run535 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.mul[mixed]" xs ys (mixFull dx dy) timed535 full535 trials reps

/-! ### `binary16/ref.div[mixed]` -/
@[inline] def op536 (x y : Half) := ExecFloat.div x y
def timed536 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed536 xs ys k (mixQuick acc (Digest.quick (op536 xs[k]! ys[k]!)))
def full536 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full536 xs ys k (Digest.full (op536 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run536 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.div[mixed]" xs ys (mixFull dx dy) timed536 full536 trials reps

/-! ### `binary16/ref.sqrt[mixed]` -/
@[inline] def op537 (x : Half) := ExecFloat.sqrt x
def timed537 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed537 xs k (mixQuick acc (Digest.quick (op537 xs[k]!)))
def full537 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full537 xs k (Digest.full (op537 xs[k]!) (mixFull h k.toUInt64))
def run537 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/ref.sqrt[mixed]" xs d timed537 full537 trials reps

/-! ### `binary16/ref.fma[mixed]` -/
@[inline] def op538 (x y z : Half) := ExecFloat.fma x y z
def timed538 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed538 xs ys zs k (mixQuick acc (Digest.quick (op538 xs[k]! ys[k]! zs[k]!)))
def full538 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full538 xs ys zs k (Digest.full (op538 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run538 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  let (zs, dz) := inHalf seedZ count
  runT "binary16/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed538 full538 trials reps

/-! ### `bfloat16/ref.add[mixed]` -/
@[inline] def op539 (x y : Brain) := ExecFloat.add x y
def timed539 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed539 xs ys k (mixQuick acc (Digest.quick (op539 xs[k]! ys[k]!)))
def full539 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full539 xs ys k (Digest.full (op539 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run539 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.add[mixed]" xs ys (mixFull dx dy) timed539 full539 trials reps

/-! ### `bfloat16/ref.sub[mixed]` -/
@[inline] def op540 (x y : Brain) := ExecFloat.sub x y
def timed540 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed540 xs ys k (mixQuick acc (Digest.quick (op540 xs[k]! ys[k]!)))
def full540 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full540 xs ys k (Digest.full (op540 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run540 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.sub[mixed]" xs ys (mixFull dx dy) timed540 full540 trials reps

/-! ### `bfloat16/ref.mul[mixed]` -/
@[inline] def op541 (x y : Brain) := ExecFloat.mul x y
def timed541 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed541 xs ys k (mixQuick acc (Digest.quick (op541 xs[k]! ys[k]!)))
def full541 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full541 xs ys k (Digest.full (op541 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run541 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.mul[mixed]" xs ys (mixFull dx dy) timed541 full541 trials reps

/-! ### `bfloat16/ref.div[mixed]` -/
@[inline] def op542 (x y : Brain) := ExecFloat.div x y
def timed542 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed542 xs ys k (mixQuick acc (Digest.quick (op542 xs[k]! ys[k]!)))
def full542 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full542 xs ys k (Digest.full (op542 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run542 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.div[mixed]" xs ys (mixFull dx dy) timed542 full542 trials reps

/-! ### `bfloat16/ref.sqrt[mixed]` -/
@[inline] def op543 (x : Brain) := ExecFloat.sqrt x
def timed543 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed543 xs k (mixQuick acc (Digest.quick (op543 xs[k]!)))
def full543 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full543 xs k (Digest.full (op543 xs[k]!) (mixFull h k.toUInt64))
def run543 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/ref.sqrt[mixed]" xs d timed543 full543 trials reps

/-! ### `bfloat16/ref.fma[mixed]` -/
@[inline] def op544 (x y z : Brain) := ExecFloat.fma x y z
def timed544 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed544 xs ys zs k (mixQuick acc (Digest.quick (op544 xs[k]! ys[k]! zs[k]!)))
def full544 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full544 xs ys zs k (Digest.full (op544 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run544 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  let (zs, dz) := inBrain seedZ count
  runT "bfloat16/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed544 full544 trials reps

/-! ### `binary32/ref.add[mixed]` -/
@[inline] def op545 (x y : Single) := ExecFloat.add x y
def timed545 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed545 xs ys k (mixQuick acc (Digest.quick (op545 xs[k]! ys[k]!)))
def full545 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full545 xs ys k (Digest.full (op545 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run545 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.add[mixed]" xs ys (mixFull dx dy) timed545 full545 trials reps

/-! ### `binary32/ref.sub[mixed]` -/
@[inline] def op546 (x y : Single) := ExecFloat.sub x y
def timed546 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed546 xs ys k (mixQuick acc (Digest.quick (op546 xs[k]! ys[k]!)))
def full546 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full546 xs ys k (Digest.full (op546 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run546 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.sub[mixed]" xs ys (mixFull dx dy) timed546 full546 trials reps

/-! ### `binary32/ref.mul[mixed]` -/
@[inline] def op547 (x y : Single) := ExecFloat.mul x y
def timed547 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed547 xs ys k (mixQuick acc (Digest.quick (op547 xs[k]! ys[k]!)))
def full547 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full547 xs ys k (Digest.full (op547 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run547 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.mul[mixed]" xs ys (mixFull dx dy) timed547 full547 trials reps

/-! ### `binary32/ref.div[mixed]` -/
@[inline] def op548 (x y : Single) := ExecFloat.div x y
def timed548 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed548 xs ys k (mixQuick acc (Digest.quick (op548 xs[k]! ys[k]!)))
def full548 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full548 xs ys k (Digest.full (op548 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run548 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.div[mixed]" xs ys (mixFull dx dy) timed548 full548 trials reps

/-! ### `binary32/ref.sqrt[mixed]` -/
@[inline] def op549 (x : Single) := ExecFloat.sqrt x
def timed549 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed549 xs k (mixQuick acc (Digest.quick (op549 xs[k]!)))
def full549 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full549 xs k (Digest.full (op549 xs[k]!) (mixFull h k.toUInt64))
def run549 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/ref.sqrt[mixed]" xs d timed549 full549 trials reps

/-! ### `binary32/ref.fma[mixed]` -/
@[inline] def op550 (x y z : Single) := ExecFloat.fma x y z
def timed550 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed550 xs ys zs k (mixQuick acc (Digest.quick (op550 xs[k]! ys[k]! zs[k]!)))
def full550 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full550 xs ys zs k (Digest.full (op550 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run550 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  let (zs, dz) := inSingle seedZ count
  runT "binary32/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed550 full550 trials reps

/-! ### `binary64/ref.add[mixed]` -/
@[inline] def op551 (x y : Double) := ExecFloat.add x y
def timed551 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed551 xs ys k (mixQuick acc (Digest.quick (op551 xs[k]! ys[k]!)))
def full551 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full551 xs ys k (Digest.full (op551 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run551 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.add[mixed]" xs ys (mixFull dx dy) timed551 full551 trials reps

/-! ### `binary64/ref.add[ordinary]` -/
@[inline] def op552 (x y : Double) := ExecFloat.add x y
def timed552 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed552 xs ys k (mixQuick acc (Digest.quick (op552 xs[k]! ys[k]!)))
def full552 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full552 xs ys k (Digest.full (op552 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run552 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.add[ordinary]" xs ys (mixFull dx dy) timed552 full552 trials reps

/-! ### `binary64/ref.add[tiny]` -/
@[inline] def op553 (x y : Double) := ExecFloat.add x y
def timed553 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed553 xs ys k (mixQuick acc (Digest.quick (op553 xs[k]! ys[k]!)))
def full553 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full553 xs ys k (Digest.full (op553 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run553 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.add[tiny]" xs ys (mixFull dx dy) timed553 full553 trials reps

/-! ### `binary64/ref.add[huge]` -/
@[inline] def op554 (x y : Double) := ExecFloat.add x y
def timed554 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed554 xs ys k (mixQuick acc (Digest.quick (op554 xs[k]! ys[k]!)))
def full554 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full554 xs ys k (Digest.full (op554 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run554 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.add[huge]" xs ys (mixFull dx dy) timed554 full554 trials reps

/-! ### `binary64/ref.add[subnormal]` -/
@[inline] def op555 (x y : Double) := ExecFloat.add x y
def timed555 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed555 xs ys k (mixQuick acc (Digest.quick (op555 xs[k]! ys[k]!)))
def full555 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full555 xs ys k (Digest.full (op555 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run555 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.add[subnormal]" xs ys (mixFull dx dy) timed555 full555 trials reps

/-! ### `binary64/ref.add[special]` -/
@[inline] def op556 (x y : Double) := ExecFloat.add x y
def timed556 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed556 xs ys k (mixQuick acc (Digest.quick (op556 xs[k]! ys[k]!)))
def full556 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full556 xs ys k (Digest.full (op556 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run556 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.add[special]" xs ys (mixFull dx dy) timed556 full556 trials reps

/-! ### `binary64/ref.sub[mixed]` -/
@[inline] def op557 (x y : Double) := ExecFloat.sub x y
def timed557 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed557 xs ys k (mixQuick acc (Digest.quick (op557 xs[k]! ys[k]!)))
def full557 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full557 xs ys k (Digest.full (op557 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run557 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.sub[mixed]" xs ys (mixFull dx dy) timed557 full557 trials reps

/-! ### `binary64/ref.sub[ordinary]` -/
@[inline] def op558 (x y : Double) := ExecFloat.sub x y
def timed558 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed558 xs ys k (mixQuick acc (Digest.quick (op558 xs[k]! ys[k]!)))
def full558 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full558 xs ys k (Digest.full (op558 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run558 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.sub[ordinary]" xs ys (mixFull dx dy) timed558 full558 trials reps

/-! ### `binary64/ref.sub[tiny]` -/
@[inline] def op559 (x y : Double) := ExecFloat.sub x y
def timed559 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed559 xs ys k (mixQuick acc (Digest.quick (op559 xs[k]! ys[k]!)))
def full559 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full559 xs ys k (Digest.full (op559 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run559 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.sub[tiny]" xs ys (mixFull dx dy) timed559 full559 trials reps

/-! ### `binary64/ref.sub[huge]` -/
@[inline] def op560 (x y : Double) := ExecFloat.sub x y
def timed560 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed560 xs ys k (mixQuick acc (Digest.quick (op560 xs[k]! ys[k]!)))
def full560 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full560 xs ys k (Digest.full (op560 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run560 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.sub[huge]" xs ys (mixFull dx dy) timed560 full560 trials reps

/-! ### `binary64/ref.sub[subnormal]` -/
@[inline] def op561 (x y : Double) := ExecFloat.sub x y
def timed561 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed561 xs ys k (mixQuick acc (Digest.quick (op561 xs[k]! ys[k]!)))
def full561 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full561 xs ys k (Digest.full (op561 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run561 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.sub[subnormal]" xs ys (mixFull dx dy) timed561 full561 trials reps

/-! ### `binary64/ref.sub[special]` -/
@[inline] def op562 (x y : Double) := ExecFloat.sub x y
def timed562 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed562 xs ys k (mixQuick acc (Digest.quick (op562 xs[k]! ys[k]!)))
def full562 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full562 xs ys k (Digest.full (op562 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run562 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.sub[special]" xs ys (mixFull dx dy) timed562 full562 trials reps

/-! ### `binary64/ref.mul[mixed]` -/
@[inline] def op563 (x y : Double) := ExecFloat.mul x y
def timed563 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed563 xs ys k (mixQuick acc (Digest.quick (op563 xs[k]! ys[k]!)))
def full563 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full563 xs ys k (Digest.full (op563 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run563 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.mul[mixed]" xs ys (mixFull dx dy) timed563 full563 trials reps

/-! ### `binary64/ref.mul[ordinary]` -/
@[inline] def op564 (x y : Double) := ExecFloat.mul x y
def timed564 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed564 xs ys k (mixQuick acc (Digest.quick (op564 xs[k]! ys[k]!)))
def full564 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full564 xs ys k (Digest.full (op564 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run564 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.mul[ordinary]" xs ys (mixFull dx dy) timed564 full564 trials reps

/-! ### `binary64/ref.mul[tiny]` -/
@[inline] def op565 (x y : Double) := ExecFloat.mul x y
def timed565 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed565 xs ys k (mixQuick acc (Digest.quick (op565 xs[k]! ys[k]!)))
def full565 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full565 xs ys k (Digest.full (op565 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run565 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.mul[tiny]" xs ys (mixFull dx dy) timed565 full565 trials reps

/-! ### `binary64/ref.mul[huge]` -/
@[inline] def op566 (x y : Double) := ExecFloat.mul x y
def timed566 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed566 xs ys k (mixQuick acc (Digest.quick (op566 xs[k]! ys[k]!)))
def full566 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full566 xs ys k (Digest.full (op566 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run566 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.mul[huge]" xs ys (mixFull dx dy) timed566 full566 trials reps

/-! ### `binary64/ref.mul[subnormal]` -/
@[inline] def op567 (x y : Double) := ExecFloat.mul x y
def timed567 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed567 xs ys k (mixQuick acc (Digest.quick (op567 xs[k]! ys[k]!)))
def full567 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full567 xs ys k (Digest.full (op567 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run567 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.mul[subnormal]" xs ys (mixFull dx dy) timed567 full567 trials reps

/-! ### `binary64/ref.mul[special]` -/
@[inline] def op568 (x y : Double) := ExecFloat.mul x y
def timed568 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed568 xs ys k (mixQuick acc (Digest.quick (op568 xs[k]! ys[k]!)))
def full568 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full568 xs ys k (Digest.full (op568 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run568 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.mul[special]" xs ys (mixFull dx dy) timed568 full568 trials reps

/-! ### `binary64/ref.div[mixed]` -/
@[inline] def op569 (x y : Double) := ExecFloat.div x y
def timed569 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed569 xs ys k (mixQuick acc (Digest.quick (op569 xs[k]! ys[k]!)))
def full569 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full569 xs ys k (Digest.full (op569 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run569 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.div[mixed]" xs ys (mixFull dx dy) timed569 full569 trials reps

/-! ### `binary64/ref.div[ordinary]` -/
@[inline] def op570 (x y : Double) := ExecFloat.div x y
def timed570 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed570 xs ys k (mixQuick acc (Digest.quick (op570 xs[k]! ys[k]!)))
def full570 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full570 xs ys k (Digest.full (op570 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run570 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.div[ordinary]" xs ys (mixFull dx dy) timed570 full570 trials reps

/-! ### `binary64/ref.div[tiny]` -/
@[inline] def op571 (x y : Double) := ExecFloat.div x y
def timed571 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed571 xs ys k (mixQuick acc (Digest.quick (op571 xs[k]! ys[k]!)))
def full571 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full571 xs ys k (Digest.full (op571 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run571 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.div[tiny]" xs ys (mixFull dx dy) timed571 full571 trials reps

/-! ### `binary64/ref.div[huge]` -/
@[inline] def op572 (x y : Double) := ExecFloat.div x y
def timed572 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed572 xs ys k (mixQuick acc (Digest.quick (op572 xs[k]! ys[k]!)))
def full572 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full572 xs ys k (Digest.full (op572 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run572 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.div[huge]" xs ys (mixFull dx dy) timed572 full572 trials reps

/-! ### `binary64/ref.div[subnormal]` -/
@[inline] def op573 (x y : Double) := ExecFloat.div x y
def timed573 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed573 xs ys k (mixQuick acc (Digest.quick (op573 xs[k]! ys[k]!)))
def full573 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full573 xs ys k (Digest.full (op573 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run573 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.div[subnormal]" xs ys (mixFull dx dy) timed573 full573 trials reps

/-! ### `binary64/ref.div[special]` -/
@[inline] def op574 (x y : Double) := ExecFloat.div x y
def timed574 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed574 xs ys k (mixQuick acc (Digest.quick (op574 xs[k]! ys[k]!)))
def full574 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full574 xs ys k (Digest.full (op574 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run574 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.div[special]" xs ys (mixFull dx dy) timed574 full574 trials reps

/-! ### `binary64/ref.sqrt[mixed]` -/
@[inline] def op575 (x : Double) := ExecFloat.sqrt x
def timed575 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed575 xs k (mixQuick acc (Digest.quick (op575 xs[k]!)))
def full575 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full575 xs k (Digest.full (op575 xs[k]!) (mixFull h k.toUInt64))
def run575 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/ref.sqrt[mixed]" xs d timed575 full575 trials reps

/-! ### `binary64/ref.sqrt[ordinary]` -/
@[inline] def op576 (x : Double) := ExecFloat.sqrt x
def timed576 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed576 xs k (mixQuick acc (Digest.quick (op576 xs[k]!)))
def full576 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full576 xs k (Digest.full (op576 xs[k]!) (mixFull h k.toUInt64))
def run576 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 0)
  runU "binary64/ref.sqrt[ordinary]" xs d timed576 full576 trials reps

/-! ### `binary64/ref.sqrt[tiny]` -/
@[inline] def op577 (x : Double) := ExecFloat.sqrt x
def timed577 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed577 xs k (mixQuick acc (Digest.quick (op577 xs[k]!)))
def full577 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full577 xs k (Digest.full (op577 xs[k]!) (mixFull h k.toUInt64))
def run577 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 45)
  runU "binary64/ref.sqrt[tiny]" xs d timed577 full577 trials reps

/-! ### `binary64/ref.sqrt[huge]` -/
@[inline] def op578 (x : Double) := ExecFloat.sqrt x
def timed578 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed578 xs k (mixQuick acc (Digest.quick (op578 xs[k]!)))
def full578 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full578 xs k (Digest.full (op578 xs[k]!) (mixFull h k.toUInt64))
def run578 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 55)
  runU "binary64/ref.sqrt[huge]" xs d timed578 full578 trials reps

/-! ### `binary64/ref.sqrt[subnormal]` -/
@[inline] def op579 (x : Double) := ExecFloat.sqrt x
def timed579 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed579 xs k (mixQuick acc (Digest.quick (op579 xs[k]!)))
def full579 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full579 xs k (Digest.full (op579 xs[k]!) (mixFull h k.toUInt64))
def run579 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 65)
  runU "binary64/ref.sqrt[subnormal]" xs d timed579 full579 trials reps

/-! ### `binary64/ref.sqrt[special]` -/
@[inline] def op580 (x : Double) := ExecFloat.sqrt x
def timed580 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed580 xs k (mixQuick acc (Digest.quick (op580 xs[k]!)))
def full580 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full580 xs k (Digest.full (op580 xs[k]!) (mixFull h k.toUInt64))
def run580 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 85)
  runU "binary64/ref.sqrt[special]" xs d timed580 full580 trials reps

/-! ### `binary64/ref.fma[mixed]` -/
@[inline] def op581 (x y z : Double) := ExecFloat.fma x y z
def timed581 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed581 xs ys zs k (mixQuick acc (Digest.quick (op581 xs[k]! ys[k]! zs[k]!)))
def full581 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full581 xs ys zs k (Digest.full (op581 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run581 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  let (zs, dz) := inDouble seedZ count
  runT "binary64/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed581 full581 trials reps

/-! ### `binary64/ref.fma[ordinary]` -/
@[inline] def op582 (x y z : Double) := ExecFloat.fma x y z
def timed582 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed582 xs ys zs k (mixQuick acc (Digest.quick (op582 xs[k]! ys[k]! zs[k]!)))
def full582 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full582 xs ys zs k (Digest.full (op582 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run582 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  let (zs, dz) := inDouble seedZ count (some 0)
  runT "binary64/ref.fma[ordinary]" xs ys zs (mixFull (mixFull dx dy) dz) timed582 full582 trials
    reps

/-! ### `binary64/ref.fma[tiny]` -/
@[inline] def op583 (x y z : Double) := ExecFloat.fma x y z
def timed583 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed583 xs ys zs k (mixQuick acc (Digest.quick (op583 xs[k]! ys[k]! zs[k]!)))
def full583 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full583 xs ys zs k (Digest.full (op583 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run583 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  let (zs, dz) := inDouble seedZ count (some 45)
  runT "binary64/ref.fma[tiny]" xs ys zs (mixFull (mixFull dx dy) dz) timed583 full583 trials reps

/-! ### `binary64/ref.fma[huge]` -/
@[inline] def op584 (x y z : Double) := ExecFloat.fma x y z
def timed584 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed584 xs ys zs k (mixQuick acc (Digest.quick (op584 xs[k]! ys[k]! zs[k]!)))
def full584 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full584 xs ys zs k (Digest.full (op584 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run584 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  let (zs, dz) := inDouble seedZ count (some 55)
  runT "binary64/ref.fma[huge]" xs ys zs (mixFull (mixFull dx dy) dz) timed584 full584 trials reps

/-! ### `binary64/ref.fma[subnormal]` -/
@[inline] def op585 (x y z : Double) := ExecFloat.fma x y z
def timed585 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed585 xs ys zs k (mixQuick acc (Digest.quick (op585 xs[k]! ys[k]! zs[k]!)))
def full585 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full585 xs ys zs k (Digest.full (op585 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run585 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  let (zs, dz) := inDouble seedZ count (some 65)
  runT "binary64/ref.fma[subnormal]" xs ys zs (mixFull (mixFull dx dy) dz) timed585 full585
    trials reps

/-! ### `binary64/ref.fma[special]` -/
@[inline] def op586 (x y z : Double) := ExecFloat.fma x y z
def timed586 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed586 xs ys zs k (mixQuick acc (Digest.quick (op586 xs[k]! ys[k]! zs[k]!)))
def full586 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full586 xs ys zs k (Digest.full (op586 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run586 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  let (zs, dz) := inDouble seedZ count (some 85)
  runT "binary64/ref.fma[special]" xs ys zs (mixFull (mixFull dx dy) dz) timed586 full586 trials
    reps

/-! ### `binary128/ref.add[mixed]` -/
@[inline] def op587 (x y : Quad) := ExecFloat.add x y
def timed587 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed587 xs ys k (mixQuick acc (Digest.quick (op587 xs[k]! ys[k]!)))
def full587 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full587 xs ys k (Digest.full (op587 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run587 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.add[mixed]" xs ys (mixFull dx dy) timed587 full587 trials reps

/-! ### `binary128/ref.add[ordinary]` -/
@[inline] def op588 (x y : Quad) := ExecFloat.add x y
def timed588 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed588 xs ys k (mixQuick acc (Digest.quick (op588 xs[k]! ys[k]!)))
def full588 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full588 xs ys k (Digest.full (op588 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run588 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.add[ordinary]" xs ys (mixFull dx dy) timed588 full588 trials reps

/-! ### `binary128/ref.add[tiny]` -/
@[inline] def op589 (x y : Quad) := ExecFloat.add x y
def timed589 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed589 xs ys k (mixQuick acc (Digest.quick (op589 xs[k]! ys[k]!)))
def full589 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full589 xs ys k (Digest.full (op589 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run589 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.add[tiny]" xs ys (mixFull dx dy) timed589 full589 trials reps

/-! ### `binary128/ref.add[huge]` -/
@[inline] def op590 (x y : Quad) := ExecFloat.add x y
def timed590 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed590 xs ys k (mixQuick acc (Digest.quick (op590 xs[k]! ys[k]!)))
def full590 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full590 xs ys k (Digest.full (op590 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run590 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.add[huge]" xs ys (mixFull dx dy) timed590 full590 trials reps

/-! ### `binary128/ref.add[subnormal]` -/
@[inline] def op591 (x y : Quad) := ExecFloat.add x y
def timed591 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed591 xs ys k (mixQuick acc (Digest.quick (op591 xs[k]! ys[k]!)))
def full591 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full591 xs ys k (Digest.full (op591 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run591 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.add[subnormal]" xs ys (mixFull dx dy) timed591 full591 trials reps

/-! ### `binary128/ref.add[special]` -/
@[inline] def op592 (x y : Quad) := ExecFloat.add x y
def timed592 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed592 xs ys k (mixQuick acc (Digest.quick (op592 xs[k]! ys[k]!)))
def full592 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full592 xs ys k (Digest.full (op592 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run592 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.add[special]" xs ys (mixFull dx dy) timed592 full592 trials reps

/-! ### `binary128/ref.sub[mixed]` -/
@[inline] def op593 (x y : Quad) := ExecFloat.sub x y
def timed593 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed593 xs ys k (mixQuick acc (Digest.quick (op593 xs[k]! ys[k]!)))
def full593 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full593 xs ys k (Digest.full (op593 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run593 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.sub[mixed]" xs ys (mixFull dx dy) timed593 full593 trials reps

/-! ### `binary128/ref.sub[ordinary]` -/
@[inline] def op594 (x y : Quad) := ExecFloat.sub x y
def timed594 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed594 xs ys k (mixQuick acc (Digest.quick (op594 xs[k]! ys[k]!)))
def full594 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full594 xs ys k (Digest.full (op594 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run594 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.sub[ordinary]" xs ys (mixFull dx dy) timed594 full594 trials reps

/-! ### `binary128/ref.sub[tiny]` -/
@[inline] def op595 (x y : Quad) := ExecFloat.sub x y
def timed595 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed595 xs ys k (mixQuick acc (Digest.quick (op595 xs[k]! ys[k]!)))
def full595 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full595 xs ys k (Digest.full (op595 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run595 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.sub[tiny]" xs ys (mixFull dx dy) timed595 full595 trials reps

/-! ### `binary128/ref.sub[huge]` -/
@[inline] def op596 (x y : Quad) := ExecFloat.sub x y
def timed596 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed596 xs ys k (mixQuick acc (Digest.quick (op596 xs[k]! ys[k]!)))
def full596 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full596 xs ys k (Digest.full (op596 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run596 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.sub[huge]" xs ys (mixFull dx dy) timed596 full596 trials reps

/-! ### `binary128/ref.sub[subnormal]` -/
@[inline] def op597 (x y : Quad) := ExecFloat.sub x y
def timed597 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed597 xs ys k (mixQuick acc (Digest.quick (op597 xs[k]! ys[k]!)))
def full597 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full597 xs ys k (Digest.full (op597 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run597 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.sub[subnormal]" xs ys (mixFull dx dy) timed597 full597 trials reps

/-! ### `binary128/ref.sub[special]` -/
@[inline] def op598 (x y : Quad) := ExecFloat.sub x y
def timed598 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed598 xs ys k (mixQuick acc (Digest.quick (op598 xs[k]! ys[k]!)))
def full598 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full598 xs ys k (Digest.full (op598 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run598 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.sub[special]" xs ys (mixFull dx dy) timed598 full598 trials reps

/-! ### `binary128/ref.mul[mixed]` -/
@[inline] def op599 (x y : Quad) := ExecFloat.mul x y
def timed599 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed599 xs ys k (mixQuick acc (Digest.quick (op599 xs[k]! ys[k]!)))
def full599 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full599 xs ys k (Digest.full (op599 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run599 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.mul[mixed]" xs ys (mixFull dx dy) timed599 full599 trials reps

/-! ### `binary128/ref.mul[ordinary]` -/
@[inline] def op600 (x y : Quad) := ExecFloat.mul x y
def timed600 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed600 xs ys k (mixQuick acc (Digest.quick (op600 xs[k]! ys[k]!)))
def full600 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full600 xs ys k (Digest.full (op600 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run600 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.mul[ordinary]" xs ys (mixFull dx dy) timed600 full600 trials reps

/-! ### `binary128/ref.mul[tiny]` -/
@[inline] def op601 (x y : Quad) := ExecFloat.mul x y
def timed601 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed601 xs ys k (mixQuick acc (Digest.quick (op601 xs[k]! ys[k]!)))
def full601 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full601 xs ys k (Digest.full (op601 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run601 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.mul[tiny]" xs ys (mixFull dx dy) timed601 full601 trials reps

/-! ### `binary128/ref.mul[huge]` -/
@[inline] def op602 (x y : Quad) := ExecFloat.mul x y
def timed602 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed602 xs ys k (mixQuick acc (Digest.quick (op602 xs[k]! ys[k]!)))
def full602 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full602 xs ys k (Digest.full (op602 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run602 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.mul[huge]" xs ys (mixFull dx dy) timed602 full602 trials reps

/-! ### `binary128/ref.mul[subnormal]` -/
@[inline] def op603 (x y : Quad) := ExecFloat.mul x y
def timed603 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed603 xs ys k (mixQuick acc (Digest.quick (op603 xs[k]! ys[k]!)))
def full603 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full603 xs ys k (Digest.full (op603 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run603 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.mul[subnormal]" xs ys (mixFull dx dy) timed603 full603 trials reps

/-! ### `binary128/ref.mul[special]` -/
@[inline] def op604 (x y : Quad) := ExecFloat.mul x y
def timed604 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed604 xs ys k (mixQuick acc (Digest.quick (op604 xs[k]! ys[k]!)))
def full604 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full604 xs ys k (Digest.full (op604 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run604 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.mul[special]" xs ys (mixFull dx dy) timed604 full604 trials reps

/-! ### `binary128/ref.div[mixed]` -/
@[inline] def op605 (x y : Quad) := ExecFloat.div x y
def timed605 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed605 xs ys k (mixQuick acc (Digest.quick (op605 xs[k]! ys[k]!)))
def full605 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full605 xs ys k (Digest.full (op605 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run605 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.div[mixed]" xs ys (mixFull dx dy) timed605 full605 trials reps

/-! ### `binary128/ref.div[ordinary]` -/
@[inline] def op606 (x y : Quad) := ExecFloat.div x y
def timed606 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed606 xs ys k (mixQuick acc (Digest.quick (op606 xs[k]! ys[k]!)))
def full606 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full606 xs ys k (Digest.full (op606 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run606 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.div[ordinary]" xs ys (mixFull dx dy) timed606 full606 trials reps

/-! ### `binary128/ref.div[tiny]` -/
@[inline] def op607 (x y : Quad) := ExecFloat.div x y
def timed607 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed607 xs ys k (mixQuick acc (Digest.quick (op607 xs[k]! ys[k]!)))
def full607 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full607 xs ys k (Digest.full (op607 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run607 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.div[tiny]" xs ys (mixFull dx dy) timed607 full607 trials reps

/-! ### `binary128/ref.div[huge]` -/
@[inline] def op608 (x y : Quad) := ExecFloat.div x y
def timed608 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed608 xs ys k (mixQuick acc (Digest.quick (op608 xs[k]! ys[k]!)))
def full608 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full608 xs ys k (Digest.full (op608 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run608 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.div[huge]" xs ys (mixFull dx dy) timed608 full608 trials reps

/-! ### `binary128/ref.div[subnormal]` -/
@[inline] def op609 (x y : Quad) := ExecFloat.div x y
def timed609 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed609 xs ys k (mixQuick acc (Digest.quick (op609 xs[k]! ys[k]!)))
def full609 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full609 xs ys k (Digest.full (op609 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run609 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.div[subnormal]" xs ys (mixFull dx dy) timed609 full609 trials reps

/-! ### `binary128/ref.div[special]` -/
@[inline] def op610 (x y : Quad) := ExecFloat.div x y
def timed610 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed610 xs ys k (mixQuick acc (Digest.quick (op610 xs[k]! ys[k]!)))
def full610 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full610 xs ys k (Digest.full (op610 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run610 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.div[special]" xs ys (mixFull dx dy) timed610 full610 trials reps

/-! ### `binary128/ref.sqrt[mixed]` -/
@[inline] def op611 (x : Quad) := ExecFloat.sqrt x
def timed611 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed611 xs k (mixQuick acc (Digest.quick (op611 xs[k]!)))
def full611 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full611 xs k (Digest.full (op611 xs[k]!) (mixFull h k.toUInt64))
def run611 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/ref.sqrt[mixed]" xs d timed611 full611 trials reps

/-! ### `binary128/ref.sqrt[ordinary]` -/
@[inline] def op612 (x : Quad) := ExecFloat.sqrt x
def timed612 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed612 xs k (mixQuick acc (Digest.quick (op612 xs[k]!)))
def full612 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full612 xs k (Digest.full (op612 xs[k]!) (mixFull h k.toUInt64))
def run612 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 0)
  runU "binary128/ref.sqrt[ordinary]" xs d timed612 full612 trials reps

/-! ### `binary128/ref.sqrt[tiny]` -/
@[inline] def op613 (x : Quad) := ExecFloat.sqrt x
def timed613 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed613 xs k (mixQuick acc (Digest.quick (op613 xs[k]!)))
def full613 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full613 xs k (Digest.full (op613 xs[k]!) (mixFull h k.toUInt64))
def run613 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 45)
  runU "binary128/ref.sqrt[tiny]" xs d timed613 full613 trials reps

/-! ### `binary128/ref.sqrt[huge]` -/
@[inline] def op614 (x : Quad) := ExecFloat.sqrt x
def timed614 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed614 xs k (mixQuick acc (Digest.quick (op614 xs[k]!)))
def full614 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full614 xs k (Digest.full (op614 xs[k]!) (mixFull h k.toUInt64))
def run614 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 55)
  runU "binary128/ref.sqrt[huge]" xs d timed614 full614 trials reps

/-! ### `binary128/ref.sqrt[subnormal]` -/
@[inline] def op615 (x : Quad) := ExecFloat.sqrt x
def timed615 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed615 xs k (mixQuick acc (Digest.quick (op615 xs[k]!)))
def full615 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full615 xs k (Digest.full (op615 xs[k]!) (mixFull h k.toUInt64))
def run615 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 65)
  runU "binary128/ref.sqrt[subnormal]" xs d timed615 full615 trials reps

/-! ### `binary128/ref.sqrt[special]` -/
@[inline] def op616 (x : Quad) := ExecFloat.sqrt x
def timed616 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed616 xs k (mixQuick acc (Digest.quick (op616 xs[k]!)))
def full616 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full616 xs k (Digest.full (op616 xs[k]!) (mixFull h k.toUInt64))
def run616 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 85)
  runU "binary128/ref.sqrt[special]" xs d timed616 full616 trials reps

/-! ### `binary128/ref.fma[mixed]` -/
@[inline] def op617 (x y z : Quad) := ExecFloat.fma x y z
def timed617 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed617 xs ys zs k (mixQuick acc (Digest.quick (op617 xs[k]! ys[k]! zs[k]!)))
def full617 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full617 xs ys zs k (Digest.full (op617 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run617 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  let (zs, dz) := inQuad seedZ count
  runT "binary128/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed617 full617 trials reps

/-! ### `binary128/ref.fma[ordinary]` -/
@[inline] def op618 (x y z : Quad) := ExecFloat.fma x y z
def timed618 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed618 xs ys zs k (mixQuick acc (Digest.quick (op618 xs[k]! ys[k]! zs[k]!)))
def full618 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full618 xs ys zs k (Digest.full (op618 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run618 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  let (zs, dz) := inQuad seedZ count (some 0)
  runT "binary128/ref.fma[ordinary]" xs ys zs (mixFull (mixFull dx dy) dz) timed618 full618
    trials reps

/-! ### `binary128/ref.fma[tiny]` -/
@[inline] def op619 (x y z : Quad) := ExecFloat.fma x y z
def timed619 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed619 xs ys zs k (mixQuick acc (Digest.quick (op619 xs[k]! ys[k]! zs[k]!)))
def full619 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full619 xs ys zs k (Digest.full (op619 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run619 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  let (zs, dz) := inQuad seedZ count (some 45)
  runT "binary128/ref.fma[tiny]" xs ys zs (mixFull (mixFull dx dy) dz) timed619 full619 trials reps

/-! ### `binary128/ref.fma[huge]` -/
@[inline] def op620 (x y z : Quad) := ExecFloat.fma x y z
def timed620 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed620 xs ys zs k (mixQuick acc (Digest.quick (op620 xs[k]! ys[k]! zs[k]!)))
def full620 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full620 xs ys zs k (Digest.full (op620 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run620 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  let (zs, dz) := inQuad seedZ count (some 55)
  runT "binary128/ref.fma[huge]" xs ys zs (mixFull (mixFull dx dy) dz) timed620 full620 trials reps

/-! ### `binary128/ref.fma[subnormal]` -/
@[inline] def op621 (x y z : Quad) := ExecFloat.fma x y z
def timed621 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed621 xs ys zs k (mixQuick acc (Digest.quick (op621 xs[k]! ys[k]! zs[k]!)))
def full621 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full621 xs ys zs k (Digest.full (op621 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run621 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  let (zs, dz) := inQuad seedZ count (some 65)
  runT "binary128/ref.fma[subnormal]" xs ys zs (mixFull (mixFull dx dy) dz) timed621 full621
    trials reps

/-! ### `binary128/ref.fma[special]` -/
@[inline] def op622 (x y z : Quad) := ExecFloat.fma x y z
def timed622 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed622 xs ys zs k (mixQuick acc (Digest.quick (op622 xs[k]! ys[k]! zs[k]!)))
def full622 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full622 xs ys zs k (Digest.full (op622 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run622 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  let (zs, dz) := inQuad seedZ count (some 85)
  runT "binary128/ref.fma[special]" xs ys zs (mixFull (mixFull dx dy) dz) timed622 full622 trials
    reps

/-! ### `posit32/ref.add[mixed]` -/
@[inline] def op623 (x y : P32) := ExecFloat.add x y
def timed623 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed623 xs ys k (mixQuick acc (Digest.quick (op623 xs[k]! ys[k]!)))
def full623 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full623 xs ys k (Digest.full (op623 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run623 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.add[mixed]" xs ys (mixFull dx dy) timed623 full623 trials reps

/-! ### `posit32/ref.sub[mixed]` -/
@[inline] def op624 (x y : P32) := ExecFloat.sub x y
def timed624 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed624 xs ys k (mixQuick acc (Digest.quick (op624 xs[k]! ys[k]!)))
def full624 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full624 xs ys k (Digest.full (op624 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run624 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.sub[mixed]" xs ys (mixFull dx dy) timed624 full624 trials reps

/-! ### `posit32/ref.mul[mixed]` -/
@[inline] def op625 (x y : P32) := ExecFloat.mul x y
def timed625 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed625 xs ys k (mixQuick acc (Digest.quick (op625 xs[k]! ys[k]!)))
def full625 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full625 xs ys k (Digest.full (op625 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run625 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.mul[mixed]" xs ys (mixFull dx dy) timed625 full625 trials reps

/-! ### `posit32/ref.div[mixed]` -/
@[inline] def op626 (x y : P32) := ExecFloat.div x y
def timed626 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed626 xs ys k (mixQuick acc (Digest.quick (op626 xs[k]! ys[k]!)))
def full626 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full626 xs ys k (Digest.full (op626 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run626 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.div[mixed]" xs ys (mixFull dx dy) timed626 full626 trials reps

/-! ### `posit32/ref.sqrt[mixed]` -/
@[inline] def op627 (x : P32) := ExecFloat.sqrt x
def timed627 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed627 xs k (mixQuick acc (Digest.quick (op627 xs[k]!)))
def full627 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full627 xs k (Digest.full (op627 xs[k]!) (mixFull h k.toUInt64))
def run627 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/ref.sqrt[mixed]" xs d timed627 full627 trials reps

/-! ### `posit32/ref.fma[mixed]` -/
@[inline] def op628 (x y z : P32) := ExecFloat.fma x y z
def timed628 (xs ys zs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed628 xs ys zs k (mixQuick acc (Digest.quick (op628 xs[k]! ys[k]! zs[k]!)))
def full628 (xs ys zs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full628 xs ys zs k (Digest.full (op628 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run628 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  let (zs, dz) := inP32 seedZ count
  runT "posit32/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed628 full628 trials reps

end FloatLibBenchmarks.Public.TimeOps
