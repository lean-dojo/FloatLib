/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Comparison and extremum timings

Ordered comparisons, total order, minimum and maximum on configured formats.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/compareLess` -/
@[inline] def op45 (x y : Half) := ExecFloat.compareLess x y
def timed45 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed45 xs ys k (mixQuick acc (Digest.quick (op45 xs[k]! ys[k]!)))
def full45 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full45 xs ys k (Digest.full (op45 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run45 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/compareLess" xs ys (mixFull dx dy) timed45 full45 trials reps

/-! ### `binary16/compareLessEqual` -/
@[inline] def op46 (x y : Half) := ExecFloat.compareLessEqual x y
def timed46 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed46 xs ys k (mixQuick acc (Digest.quick (op46 xs[k]! ys[k]!)))
def full46 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full46 xs ys k (Digest.full (op46 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run46 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/compareLessEqual" xs ys (mixFull dx dy) timed46 full46 trials reps

/-! ### `binary16/beq` -/
@[inline] def op47 (x y : Half) := x == y
def timed47 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed47 xs ys k (mixQuick acc (Digest.quick (op47 xs[k]! ys[k]!)))
def full47 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full47 xs ys k (Digest.full (op47 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run47 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/beq" xs ys (mixFull dx dy) timed47 full47 trials reps

/-! ### `binary16/compare` -/
@[inline] def op48 (x y : Half) := ExecFloat.compare x y
def timed48 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed48 xs ys k (mixQuick acc (Digest.quick (op48 xs[k]! ys[k]!)))
def full48 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full48 xs ys k (Digest.full (op48 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run48 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/compare" xs ys (mixFull dx dy) timed48 full48 trials reps

/-! ### `binary16/compareQuietLess` -/
@[inline] def op49 (x y : Half) := ExecFloat.Binary.compareQuiet .less x y
def timed49 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed49 xs ys k (mixQuick acc (Digest.quick (op49 xs[k]! ys[k]!)))
def full49 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full49 xs ys k (Digest.full (op49 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run49 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/compareQuietLess" xs ys (mixFull dx dy) timed49 full49 trials reps

/-! ### `binary16/compareQuietEqual` -/
@[inline] def op50 (x y : Half) := ExecFloat.Binary.compareQuiet .equal x y
def timed50 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed50 xs ys k (mixQuick acc (Digest.quick (op50 xs[k]! ys[k]!)))
def full50 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full50 xs ys k (Digest.full (op50 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run50 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/compareQuietEqual" xs ys (mixFull dx dy) timed50 full50 trials reps

/-! ### `binary16/compareSignalingLessEqual` -/
@[inline] def op51 (x y : Half) := ExecFloat.Binary.compareSignaling .lessEqual x y
def timed51 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed51 xs ys k (mixQuick acc (Digest.quick (op51 xs[k]! ys[k]!)))
def full51 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full51 xs ys k (Digest.full (op51 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run51 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/compareSignalingLessEqual" xs ys (mixFull dx dy) timed51 full51 trials reps

/-! ### `binary16/totalOrder` -/
@[inline] def op52 (x y : Half) := ExecFloat.Binary.totalOrder x y
def timed52 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed52 xs ys k (mixQuick acc (Digest.quick (op52 xs[k]! ys[k]!)))
def full52 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full52 xs ys k (Digest.full (op52 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run52 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/totalOrder" xs ys (mixFull dx dy) timed52 full52 trials reps

/-! ### `binary16/totalOrderMag` -/
@[inline] def op53 (x y : Half) := ExecFloat.Binary.totalOrderMag x y
def timed53 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed53 xs ys k (mixQuick acc (Digest.quick (op53 xs[k]! ys[k]!)))
def full53 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full53 xs ys k (Digest.full (op53 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run53 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/totalOrderMag" xs ys (mixFull dx dy) timed53 full53 trials reps

/-! ### `binary16/maximum` -/
@[inline] def op54 (x y : Half) := max x y
def timed54 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed54 xs ys k (mixQuick acc (Digest.quick (op54 xs[k]! ys[k]!)))
def full54 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full54 xs ys k (Digest.full (op54 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run54 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/maximum" xs ys (mixFull dx dy) timed54 full54 trials reps

/-! ### `binary16/minimum` -/
@[inline] def op55 (x y : Half) := min x y
def timed55 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed55 xs ys k (mixQuick acc (Digest.quick (op55 xs[k]! ys[k]!)))
def full55 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full55 xs ys k (Digest.full (op55 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run55 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/minimum" xs ys (mixFull dx dy) timed55 full55 trials reps

/-! ### `binary16/maxNum` -/
@[inline] def op56 (x y : Half) := (ExecFloat.Binary.ofModel (Model.maxNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Half)
def timed56 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed56 xs ys k (mixQuick acc (Digest.quick (op56 xs[k]! ys[k]!)))
def full56 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full56 xs ys k (Digest.full (op56 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run56 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/maxNum" xs ys (mixFull dx dy) timed56 full56 trials reps

/-! ### `binary16/minNum` -/
@[inline] def op57 (x y : Half) := (ExecFloat.Binary.ofModel (Model.minNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Half)
def timed57 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed57 xs ys k (mixQuick acc (Digest.quick (op57 xs[k]! ys[k]!)))
def full57 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full57 xs ys k (Digest.full (op57 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run57 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/minNum" xs ys (mixFull dx dy) timed57 full57 trials reps

/-! ### `binary16/maximumNumber` -/
@[inline] def op58 (x y : Half) := ExecFloat.Binary.maximumNumber x y
def timed58 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed58 xs ys k (mixQuick acc (Digest.quick (op58 xs[k]! ys[k]!)))
def full58 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full58 xs ys k (Digest.full (op58 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run58 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/maximumNumber" xs ys (mixFull dx dy) timed58 full58 trials reps

/-! ### `binary16/minimumNumber` -/
@[inline] def op59 (x y : Half) := ExecFloat.Binary.minimumNumber x y
def timed59 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed59 xs ys k (mixQuick acc (Digest.quick (op59 xs[k]! ys[k]!)))
def full59 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full59 xs ys k (Digest.full (op59 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run59 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/minimumNumber" xs ys (mixFull dx dy) timed59 full59 trials reps

/-! ### `bfloat16/compareLess` -/
@[inline] def op132 (x y : Brain) := ExecFloat.compareLess x y
def timed132 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed132 xs ys k (mixQuick acc (Digest.quick (op132 xs[k]! ys[k]!)))
def full132 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full132 xs ys k (Digest.full (op132 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run132 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/compareLess" xs ys (mixFull dx dy) timed132 full132 trials reps

/-! ### `bfloat16/compareLessEqual` -/
@[inline] def op133 (x y : Brain) := ExecFloat.compareLessEqual x y
def timed133 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed133 xs ys k (mixQuick acc (Digest.quick (op133 xs[k]! ys[k]!)))
def full133 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full133 xs ys k (Digest.full (op133 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run133 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/compareLessEqual" xs ys (mixFull dx dy) timed133 full133 trials reps

/-! ### `bfloat16/beq` -/
@[inline] def op134 (x y : Brain) := x == y
def timed134 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed134 xs ys k (mixQuick acc (Digest.quick (op134 xs[k]! ys[k]!)))
def full134 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full134 xs ys k (Digest.full (op134 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run134 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/beq" xs ys (mixFull dx dy) timed134 full134 trials reps

/-! ### `bfloat16/compare` -/
@[inline] def op135 (x y : Brain) := ExecFloat.compare x y
def timed135 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed135 xs ys k (mixQuick acc (Digest.quick (op135 xs[k]! ys[k]!)))
def full135 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full135 xs ys k (Digest.full (op135 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run135 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/compare" xs ys (mixFull dx dy) timed135 full135 trials reps

/-! ### `bfloat16/compareQuietLess` -/
@[inline] def op136 (x y : Brain) := ExecFloat.Binary.compareQuiet .less x y
def timed136 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed136 xs ys k (mixQuick acc (Digest.quick (op136 xs[k]! ys[k]!)))
def full136 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full136 xs ys k (Digest.full (op136 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run136 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/compareQuietLess" xs ys (mixFull dx dy) timed136 full136 trials reps

/-! ### `bfloat16/compareQuietEqual` -/
@[inline] def op137 (x y : Brain) := ExecFloat.Binary.compareQuiet .equal x y
def timed137 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed137 xs ys k (mixQuick acc (Digest.quick (op137 xs[k]! ys[k]!)))
def full137 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full137 xs ys k (Digest.full (op137 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run137 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/compareQuietEqual" xs ys (mixFull dx dy) timed137 full137 trials reps

/-! ### `bfloat16/compareSignalingLessEqual` -/
@[inline] def op138 (x y : Brain) := ExecFloat.Binary.compareSignaling .lessEqual x y
def timed138 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed138 xs ys k (mixQuick acc (Digest.quick (op138 xs[k]! ys[k]!)))
def full138 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full138 xs ys k (Digest.full (op138 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run138 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/compareSignalingLessEqual" xs ys (mixFull dx dy) timed138 full138 trials reps

/-! ### `bfloat16/totalOrder` -/
@[inline] def op139 (x y : Brain) := ExecFloat.Binary.totalOrder x y
def timed139 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed139 xs ys k (mixQuick acc (Digest.quick (op139 xs[k]! ys[k]!)))
def full139 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full139 xs ys k (Digest.full (op139 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run139 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/totalOrder" xs ys (mixFull dx dy) timed139 full139 trials reps

/-! ### `bfloat16/totalOrderMag` -/
@[inline] def op140 (x y : Brain) := ExecFloat.Binary.totalOrderMag x y
def timed140 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed140 xs ys k (mixQuick acc (Digest.quick (op140 xs[k]! ys[k]!)))
def full140 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full140 xs ys k (Digest.full (op140 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run140 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/totalOrderMag" xs ys (mixFull dx dy) timed140 full140 trials reps

/-! ### `bfloat16/maximum` -/
@[inline] def op141 (x y : Brain) := max x y
def timed141 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed141 xs ys k (mixQuick acc (Digest.quick (op141 xs[k]! ys[k]!)))
def full141 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full141 xs ys k (Digest.full (op141 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run141 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/maximum" xs ys (mixFull dx dy) timed141 full141 trials reps

/-! ### `bfloat16/minimum` -/
@[inline] def op142 (x y : Brain) := min x y
def timed142 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed142 xs ys k (mixQuick acc (Digest.quick (op142 xs[k]! ys[k]!)))
def full142 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full142 xs ys k (Digest.full (op142 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run142 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/minimum" xs ys (mixFull dx dy) timed142 full142 trials reps

/-! ### `bfloat16/maxNum` -/
@[inline] def op143 (x y : Brain) := (ExecFloat.Binary.ofModel (Model.maxNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Brain)
def timed143 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed143 xs ys k (mixQuick acc (Digest.quick (op143 xs[k]! ys[k]!)))
def full143 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full143 xs ys k (Digest.full (op143 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run143 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/maxNum" xs ys (mixFull dx dy) timed143 full143 trials reps

/-! ### `bfloat16/minNum` -/
@[inline] def op144 (x y : Brain) := (ExecFloat.Binary.ofModel (Model.minNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Brain)
def timed144 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed144 xs ys k (mixQuick acc (Digest.quick (op144 xs[k]! ys[k]!)))
def full144 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full144 xs ys k (Digest.full (op144 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run144 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/minNum" xs ys (mixFull dx dy) timed144 full144 trials reps

/-! ### `bfloat16/maximumNumber` -/
@[inline] def op145 (x y : Brain) := ExecFloat.Binary.maximumNumber x y
def timed145 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed145 xs ys k (mixQuick acc (Digest.quick (op145 xs[k]! ys[k]!)))
def full145 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full145 xs ys k (Digest.full (op145 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run145 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/maximumNumber" xs ys (mixFull dx dy) timed145 full145 trials reps

/-! ### `bfloat16/minimumNumber` -/
@[inline] def op146 (x y : Brain) := ExecFloat.Binary.minimumNumber x y
def timed146 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed146 xs ys k (mixQuick acc (Digest.quick (op146 xs[k]! ys[k]!)))
def full146 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full146 xs ys k (Digest.full (op146 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run146 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/minimumNumber" xs ys (mixFull dx dy) timed146 full146 trials reps

/-! ### `binary32/compareLess` -/
@[inline] def op219 (x y : Single) := ExecFloat.compareLess x y
def timed219 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed219 xs ys k (mixQuick acc (Digest.quick (op219 xs[k]! ys[k]!)))
def full219 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full219 xs ys k (Digest.full (op219 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run219 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/compareLess" xs ys (mixFull dx dy) timed219 full219 trials reps

/-! ### `binary32/compareLessEqual` -/
@[inline] def op220 (x y : Single) := ExecFloat.compareLessEqual x y
def timed220 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed220 xs ys k (mixQuick acc (Digest.quick (op220 xs[k]! ys[k]!)))
def full220 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full220 xs ys k (Digest.full (op220 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run220 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/compareLessEqual" xs ys (mixFull dx dy) timed220 full220 trials reps

/-! ### `binary32/beq` -/
@[inline] def op221 (x y : Single) := x == y
def timed221 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed221 xs ys k (mixQuick acc (Digest.quick (op221 xs[k]! ys[k]!)))
def full221 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full221 xs ys k (Digest.full (op221 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run221 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/beq" xs ys (mixFull dx dy) timed221 full221 trials reps

/-! ### `binary32/compare` -/
@[inline] def op222 (x y : Single) := ExecFloat.compare x y
def timed222 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed222 xs ys k (mixQuick acc (Digest.quick (op222 xs[k]! ys[k]!)))
def full222 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full222 xs ys k (Digest.full (op222 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run222 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/compare" xs ys (mixFull dx dy) timed222 full222 trials reps

/-! ### `binary32/compareQuietLess` -/
@[inline] def op223 (x y : Single) := ExecFloat.Binary.compareQuiet .less x y
def timed223 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed223 xs ys k (mixQuick acc (Digest.quick (op223 xs[k]! ys[k]!)))
def full223 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full223 xs ys k (Digest.full (op223 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run223 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/compareQuietLess" xs ys (mixFull dx dy) timed223 full223 trials reps

/-! ### `binary32/compareQuietEqual` -/
@[inline] def op224 (x y : Single) := ExecFloat.Binary.compareQuiet .equal x y
def timed224 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed224 xs ys k (mixQuick acc (Digest.quick (op224 xs[k]! ys[k]!)))
def full224 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full224 xs ys k (Digest.full (op224 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run224 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/compareQuietEqual" xs ys (mixFull dx dy) timed224 full224 trials reps

/-! ### `binary32/compareSignalingLessEqual` -/
@[inline] def op225 (x y : Single) := ExecFloat.Binary.compareSignaling .lessEqual x y
def timed225 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed225 xs ys k (mixQuick acc (Digest.quick (op225 xs[k]! ys[k]!)))
def full225 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full225 xs ys k (Digest.full (op225 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run225 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/compareSignalingLessEqual" xs ys (mixFull dx dy) timed225 full225 trials reps

/-! ### `binary32/totalOrder` -/
@[inline] def op226 (x y : Single) := ExecFloat.Binary.totalOrder x y
def timed226 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed226 xs ys k (mixQuick acc (Digest.quick (op226 xs[k]! ys[k]!)))
def full226 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full226 xs ys k (Digest.full (op226 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run226 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/totalOrder" xs ys (mixFull dx dy) timed226 full226 trials reps

/-! ### `binary32/totalOrderMag` -/
@[inline] def op227 (x y : Single) := ExecFloat.Binary.totalOrderMag x y
def timed227 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed227 xs ys k (mixQuick acc (Digest.quick (op227 xs[k]! ys[k]!)))
def full227 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full227 xs ys k (Digest.full (op227 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run227 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/totalOrderMag" xs ys (mixFull dx dy) timed227 full227 trials reps

/-! ### `binary32/maximum` -/
@[inline] def op228 (x y : Single) := max x y
def timed228 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed228 xs ys k (mixQuick acc (Digest.quick (op228 xs[k]! ys[k]!)))
def full228 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full228 xs ys k (Digest.full (op228 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run228 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/maximum" xs ys (mixFull dx dy) timed228 full228 trials reps

/-! ### `binary32/minimum` -/
@[inline] def op229 (x y : Single) := min x y
def timed229 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed229 xs ys k (mixQuick acc (Digest.quick (op229 xs[k]! ys[k]!)))
def full229 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full229 xs ys k (Digest.full (op229 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run229 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/minimum" xs ys (mixFull dx dy) timed229 full229 trials reps

/-! ### `binary32/maxNum` -/
@[inline] def op230 (x y : Single) := (ExecFloat.Binary.ofModel (Model.maxNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Single)
def timed230 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed230 xs ys k (mixQuick acc (Digest.quick (op230 xs[k]! ys[k]!)))
def full230 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full230 xs ys k (Digest.full (op230 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run230 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/maxNum" xs ys (mixFull dx dy) timed230 full230 trials reps

/-! ### `binary32/minNum` -/
@[inline] def op231 (x y : Single) := (ExecFloat.Binary.ofModel (Model.minNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Single)
def timed231 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed231 xs ys k (mixQuick acc (Digest.quick (op231 xs[k]! ys[k]!)))
def full231 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full231 xs ys k (Digest.full (op231 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run231 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/minNum" xs ys (mixFull dx dy) timed231 full231 trials reps

/-! ### `binary32/maximumNumber` -/
@[inline] def op232 (x y : Single) := ExecFloat.Binary.maximumNumber x y
def timed232 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed232 xs ys k (mixQuick acc (Digest.quick (op232 xs[k]! ys[k]!)))
def full232 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full232 xs ys k (Digest.full (op232 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run232 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/maximumNumber" xs ys (mixFull dx dy) timed232 full232 trials reps

/-! ### `binary32/minimumNumber` -/
@[inline] def op233 (x y : Single) := ExecFloat.Binary.minimumNumber x y
def timed233 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed233 xs ys k (mixQuick acc (Digest.quick (op233 xs[k]! ys[k]!)))
def full233 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full233 xs ys k (Digest.full (op233 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run233 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/minimumNumber" xs ys (mixFull dx dy) timed233 full233 trials reps

/-! ### `binary64/compareLess` -/
@[inline] def op306 (x y : Double) := ExecFloat.compareLess x y
def timed306 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed306 xs ys k (mixQuick acc (Digest.quick (op306 xs[k]! ys[k]!)))
def full306 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full306 xs ys k (Digest.full (op306 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run306 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/compareLess" xs ys (mixFull dx dy) timed306 full306 trials reps

/-! ### `binary64/compareLessEqual` -/
@[inline] def op307 (x y : Double) := ExecFloat.compareLessEqual x y
def timed307 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed307 xs ys k (mixQuick acc (Digest.quick (op307 xs[k]! ys[k]!)))
def full307 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full307 xs ys k (Digest.full (op307 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run307 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/compareLessEqual" xs ys (mixFull dx dy) timed307 full307 trials reps

/-! ### `binary64/beq` -/
@[inline] def op308 (x y : Double) := x == y
def timed308 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed308 xs ys k (mixQuick acc (Digest.quick (op308 xs[k]! ys[k]!)))
def full308 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full308 xs ys k (Digest.full (op308 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run308 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/beq" xs ys (mixFull dx dy) timed308 full308 trials reps

/-! ### `binary64/compare` -/
@[inline] def op309 (x y : Double) := ExecFloat.compare x y
def timed309 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed309 xs ys k (mixQuick acc (Digest.quick (op309 xs[k]! ys[k]!)))
def full309 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full309 xs ys k (Digest.full (op309 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run309 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/compare" xs ys (mixFull dx dy) timed309 full309 trials reps

/-! ### `binary64/compareQuietLess` -/
@[inline] def op310 (x y : Double) := ExecFloat.Binary.compareQuiet .less x y
def timed310 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed310 xs ys k (mixQuick acc (Digest.quick (op310 xs[k]! ys[k]!)))
def full310 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full310 xs ys k (Digest.full (op310 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run310 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/compareQuietLess" xs ys (mixFull dx dy) timed310 full310 trials reps

/-! ### `binary64/compareQuietEqual` -/
@[inline] def op311 (x y : Double) := ExecFloat.Binary.compareQuiet .equal x y
def timed311 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed311 xs ys k (mixQuick acc (Digest.quick (op311 xs[k]! ys[k]!)))
def full311 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full311 xs ys k (Digest.full (op311 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run311 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/compareQuietEqual" xs ys (mixFull dx dy) timed311 full311 trials reps

/-! ### `binary64/compareSignalingLessEqual` -/
@[inline] def op312 (x y : Double) := ExecFloat.Binary.compareSignaling .lessEqual x y
def timed312 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed312 xs ys k (mixQuick acc (Digest.quick (op312 xs[k]! ys[k]!)))
def full312 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full312 xs ys k (Digest.full (op312 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run312 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/compareSignalingLessEqual" xs ys (mixFull dx dy) timed312 full312 trials reps

/-! ### `binary64/totalOrder` -/
@[inline] def op313 (x y : Double) := ExecFloat.Binary.totalOrder x y
def timed313 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed313 xs ys k (mixQuick acc (Digest.quick (op313 xs[k]! ys[k]!)))
def full313 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full313 xs ys k (Digest.full (op313 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run313 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/totalOrder" xs ys (mixFull dx dy) timed313 full313 trials reps

/-! ### `binary64/totalOrderMag` -/
@[inline] def op314 (x y : Double) := ExecFloat.Binary.totalOrderMag x y
def timed314 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed314 xs ys k (mixQuick acc (Digest.quick (op314 xs[k]! ys[k]!)))
def full314 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full314 xs ys k (Digest.full (op314 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run314 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/totalOrderMag" xs ys (mixFull dx dy) timed314 full314 trials reps

/-! ### `binary64/maximum` -/
@[inline] def op315 (x y : Double) := max x y
def timed315 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed315 xs ys k (mixQuick acc (Digest.quick (op315 xs[k]! ys[k]!)))
def full315 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full315 xs ys k (Digest.full (op315 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run315 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/maximum" xs ys (mixFull dx dy) timed315 full315 trials reps

/-! ### `binary64/minimum` -/
@[inline] def op316 (x y : Double) := min x y
def timed316 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed316 xs ys k (mixQuick acc (Digest.quick (op316 xs[k]! ys[k]!)))
def full316 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full316 xs ys k (Digest.full (op316 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run316 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/minimum" xs ys (mixFull dx dy) timed316 full316 trials reps

/-! ### `binary64/maxNum` -/
@[inline] def op317 (x y : Double) := (ExecFloat.Binary.ofModel (Model.maxNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Double)
def timed317 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed317 xs ys k (mixQuick acc (Digest.quick (op317 xs[k]! ys[k]!)))
def full317 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full317 xs ys k (Digest.full (op317 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run317 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/maxNum" xs ys (mixFull dx dy) timed317 full317 trials reps

/-! ### `binary64/minNum` -/
@[inline] def op318 (x y : Double) := (ExecFloat.Binary.ofModel (Model.minNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Double)
def timed318 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed318 xs ys k (mixQuick acc (Digest.quick (op318 xs[k]! ys[k]!)))
def full318 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full318 xs ys k (Digest.full (op318 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run318 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/minNum" xs ys (mixFull dx dy) timed318 full318 trials reps

/-! ### `binary64/maximumNumber` -/
@[inline] def op319 (x y : Double) := ExecFloat.Binary.maximumNumber x y
def timed319 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed319 xs ys k (mixQuick acc (Digest.quick (op319 xs[k]! ys[k]!)))
def full319 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full319 xs ys k (Digest.full (op319 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run319 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/maximumNumber" xs ys (mixFull dx dy) timed319 full319 trials reps

/-! ### `binary64/minimumNumber` -/
@[inline] def op320 (x y : Double) := ExecFloat.Binary.minimumNumber x y
def timed320 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed320 xs ys k (mixQuick acc (Digest.quick (op320 xs[k]! ys[k]!)))
def full320 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full320 xs ys k (Digest.full (op320 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run320 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/minimumNumber" xs ys (mixFull dx dy) timed320 full320 trials reps

/-! ### `binary128/compareLess` -/
@[inline] def op393 (x y : Quad) := ExecFloat.compareLess x y
def timed393 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed393 xs ys k (mixQuick acc (Digest.quick (op393 xs[k]! ys[k]!)))
def full393 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full393 xs ys k (Digest.full (op393 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run393 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/compareLess" xs ys (mixFull dx dy) timed393 full393 trials reps

/-! ### `binary128/compareLessEqual` -/
@[inline] def op394 (x y : Quad) := ExecFloat.compareLessEqual x y
def timed394 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed394 xs ys k (mixQuick acc (Digest.quick (op394 xs[k]! ys[k]!)))
def full394 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full394 xs ys k (Digest.full (op394 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run394 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/compareLessEqual" xs ys (mixFull dx dy) timed394 full394 trials reps

/-! ### `binary128/beq` -/
@[inline] def op395 (x y : Quad) := x == y
def timed395 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed395 xs ys k (mixQuick acc (Digest.quick (op395 xs[k]! ys[k]!)))
def full395 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full395 xs ys k (Digest.full (op395 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run395 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/beq" xs ys (mixFull dx dy) timed395 full395 trials reps

/-! ### `binary128/compare` -/
@[inline] def op396 (x y : Quad) := ExecFloat.compare x y
def timed396 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed396 xs ys k (mixQuick acc (Digest.quick (op396 xs[k]! ys[k]!)))
def full396 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full396 xs ys k (Digest.full (op396 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run396 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/compare" xs ys (mixFull dx dy) timed396 full396 trials reps

/-! ### `binary128/compareQuietLess` -/
@[inline] def op397 (x y : Quad) := ExecFloat.Binary.compareQuiet .less x y
def timed397 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed397 xs ys k (mixQuick acc (Digest.quick (op397 xs[k]! ys[k]!)))
def full397 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full397 xs ys k (Digest.full (op397 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run397 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/compareQuietLess" xs ys (mixFull dx dy) timed397 full397 trials reps

/-! ### `binary128/compareQuietEqual` -/
@[inline] def op398 (x y : Quad) := ExecFloat.Binary.compareQuiet .equal x y
def timed398 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed398 xs ys k (mixQuick acc (Digest.quick (op398 xs[k]! ys[k]!)))
def full398 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full398 xs ys k (Digest.full (op398 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run398 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/compareQuietEqual" xs ys (mixFull dx dy) timed398 full398 trials reps

/-! ### `binary128/compareSignalingLessEqual` -/
@[inline] def op399 (x y : Quad) := ExecFloat.Binary.compareSignaling .lessEqual x y
def timed399 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed399 xs ys k (mixQuick acc (Digest.quick (op399 xs[k]! ys[k]!)))
def full399 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full399 xs ys k (Digest.full (op399 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run399 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/compareSignalingLessEqual" xs ys (mixFull dx dy) timed399 full399 trials reps

/-! ### `binary128/totalOrder` -/
@[inline] def op400 (x y : Quad) := ExecFloat.Binary.totalOrder x y
def timed400 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed400 xs ys k (mixQuick acc (Digest.quick (op400 xs[k]! ys[k]!)))
def full400 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full400 xs ys k (Digest.full (op400 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run400 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/totalOrder" xs ys (mixFull dx dy) timed400 full400 trials reps

/-! ### `binary128/totalOrderMag` -/
@[inline] def op401 (x y : Quad) := ExecFloat.Binary.totalOrderMag x y
def timed401 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed401 xs ys k (mixQuick acc (Digest.quick (op401 xs[k]! ys[k]!)))
def full401 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full401 xs ys k (Digest.full (op401 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run401 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/totalOrderMag" xs ys (mixFull dx dy) timed401 full401 trials reps

/-! ### `binary128/maximum` -/
@[inline] def op402 (x y : Quad) := max x y
def timed402 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed402 xs ys k (mixQuick acc (Digest.quick (op402 xs[k]! ys[k]!)))
def full402 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full402 xs ys k (Digest.full (op402 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run402 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/maximum" xs ys (mixFull dx dy) timed402 full402 trials reps

/-! ### `binary128/minimum` -/
@[inline] def op403 (x y : Quad) := min x y
def timed403 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed403 xs ys k (mixQuick acc (Digest.quick (op403 xs[k]! ys[k]!)))
def full403 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full403 xs ys k (Digest.full (op403 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run403 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/minimum" xs ys (mixFull dx dy) timed403 full403 trials reps

/-! ### `binary128/maxNum` -/
@[inline] def op404 (x y : Quad) := (ExecFloat.Binary.ofModel (Model.maxNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Quad)
def timed404 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed404 xs ys k (mixQuick acc (Digest.quick (op404 xs[k]! ys[k]!)))
def full404 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full404 xs ys k (Digest.full (op404 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run404 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/maxNum" xs ys (mixFull dx dy) timed404 full404 trials reps

/-! ### `binary128/minNum` -/
@[inline] def op405 (x y : Quad) := (ExecFloat.Binary.ofModel (Model.minNum
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Quad)
def timed405 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed405 xs ys k (mixQuick acc (Digest.quick (op405 xs[k]! ys[k]!)))
def full405 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full405 xs ys k (Digest.full (op405 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run405 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/minNum" xs ys (mixFull dx dy) timed405 full405 trials reps

/-! ### `binary128/maximumNumber` -/
@[inline] def op406 (x y : Quad) := ExecFloat.Binary.maximumNumber x y
def timed406 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed406 xs ys k (mixQuick acc (Digest.quick (op406 xs[k]! ys[k]!)))
def full406 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full406 xs ys k (Digest.full (op406 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run406 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/maximumNumber" xs ys (mixFull dx dy) timed406 full406 trials reps

/-! ### `binary128/minimumNumber` -/
@[inline] def op407 (x y : Quad) := ExecFloat.Binary.minimumNumber x y
def timed407 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed407 xs ys k (mixQuick acc (Digest.quick (op407 xs[k]! ys[k]!)))
def full407 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full407 xs ys k (Digest.full (op407 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run407 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/minimumNumber" xs ys (mixFull dx dy) timed407 full407 trials reps

/-! ### `binary256/compareLess` -/
@[inline] def op475 (x y : Oct) := ExecFloat.compareLess x y
def timed475 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed475 xs ys k (mixQuick acc (Digest.quick (op475 xs[k]! ys[k]!)))
def full475 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full475 xs ys k (Digest.full (op475 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run475 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/compareLess" xs ys (mixFull dx dy) timed475 full475 trials reps

/-! ### `binary256/compare` -/
@[inline] def op476 (x y : Oct) := ExecFloat.compare x y
def timed476 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed476 xs ys k (mixQuick acc (Digest.quick (op476 xs[k]! ys[k]!)))
def full476 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full476 xs ys k (Digest.full (op476 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run476 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/compare" xs ys (mixFull dx dy) timed476 full476 trials reps

/-! ### `binary256/totalOrder` -/
@[inline] def op477 (x y : Oct) := ExecFloat.Binary.totalOrder x y
def timed477 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed477 xs ys k (mixQuick acc (Digest.quick (op477 xs[k]! ys[k]!)))
def full477 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full477 xs ys k (Digest.full (op477 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run477 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/totalOrder" xs ys (mixFull dx dy) timed477 full477 trials reps

/-! ### `binary256/maximum` -/
@[inline] def op478 (x y : Oct) := max x y
def timed478 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed478 xs ys k (mixQuick acc (Digest.quick (op478 xs[k]! ys[k]!)))
def full478 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full478 xs ys k (Digest.full (op478 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run478 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/maximum" xs ys (mixFull dx dy) timed478 full478 trials reps

/-! ### `posit32/compareLess` -/
@[inline] def op499 (x y : P32) := ExecFloat.compareLess x y
def timed499 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed499 xs ys k (mixQuick acc (Digest.quick (op499 xs[k]! ys[k]!)))
def full499 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full499 xs ys k (Digest.full (op499 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run499 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/compareLess" xs ys (mixFull dx dy) timed499 full499 trials reps

/-! ### `posit32/compareLessEqual` -/
@[inline] def op500 (x y : P32) := ExecFloat.compareLessEqual x y
def timed500 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed500 xs ys k (mixQuick acc (Digest.quick (op500 xs[k]! ys[k]!)))
def full500 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full500 xs ys k (Digest.full (op500 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run500 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/compareLessEqual" xs ys (mixFull dx dy) timed500 full500 trials reps

/-! ### `posit32/beq` -/
@[inline] def op501 (x y : P32) := x == y
def timed501 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed501 xs ys k (mixQuick acc (Digest.quick (op501 xs[k]! ys[k]!)))
def full501 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full501 xs ys k (Digest.full (op501 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run501 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/beq" xs ys (mixFull dx dy) timed501 full501 trials reps

/-! ### `posit32/compare` -/
@[inline] def op502 (x y : P32) := ExecFloat.compare x y
def timed502 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed502 xs ys k (mixQuick acc (Digest.quick (op502 xs[k]! ys[k]!)))
def full502 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full502 xs ys k (Digest.full (op502 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run502 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/compare" xs ys (mixFull dx dy) timed502 full502 trials reps

end FloatLibBenchmarks.Public.TimeOps
