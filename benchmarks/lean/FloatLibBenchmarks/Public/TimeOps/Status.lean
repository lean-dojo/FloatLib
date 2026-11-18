/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Status-bearing arithmetic timings

Arithmetic loops returning values, flags and ternary rounding information.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/add[status]` -/
@[inline] def op99 (x y : Half) := ExecFloat.Binary.add x y (status := true)
def timed99 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed99 xs ys k (mixQuick acc (Digest.quick (op99 xs[k]! ys[k]!)))
def full99 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full99 xs ys k (Digest.full (op99 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run99 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/add[status]" xs ys (mixFull dx dy) timed99 full99 trials reps

/-! ### `binary16/sub[status]` -/
@[inline] def op100 (x y : Half) := ExecFloat.Binary.sub x y (status := true)
def timed100 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed100 xs ys k (mixQuick acc (Digest.quick (op100 xs[k]! ys[k]!)))
def full100 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full100 xs ys k (Digest.full (op100 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run100 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/sub[status]" xs ys (mixFull dx dy) timed100 full100 trials reps

/-! ### `binary16/mul[status]` -/
@[inline] def op101 (x y : Half) := ExecFloat.Binary.mul x y (status := true)
def timed101 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed101 xs ys k (mixQuick acc (Digest.quick (op101 xs[k]! ys[k]!)))
def full101 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full101 xs ys k (Digest.full (op101 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run101 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/mul[status]" xs ys (mixFull dx dy) timed101 full101 trials reps

/-! ### `binary16/div[status]` -/
@[inline] def op102 (x y : Half) := ExecFloat.Binary.div x y (status := true)
def timed102 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed102 xs ys k (mixQuick acc (Digest.quick (op102 xs[k]! ys[k]!)))
def full102 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full102 xs ys k (Digest.full (op102 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run102 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/div[status]" xs ys (mixFull dx dy) timed102 full102 trials reps

/-! ### `binary16/sqrt[status]` -/
@[inline] def op103 (x : Half) := ExecFloat.Binary.sqrt x (status := true)
def timed103 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed103 xs k (mixQuick acc (Digest.quick (op103 xs[k]!)))
def full103 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full103 xs k (Digest.full (op103 xs[k]!) (mixFull h k.toUInt64))
def run103 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/sqrt[status]" xs d timed103 full103 trials reps

/-! ### `binary16/fma[status]` -/
@[inline] def op104 (x y z : Half) := ExecFloat.Binary.fma x y z (status := true)
def timed104 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed104 xs ys zs k (mixQuick acc (Digest.quick (op104 xs[k]! ys[k]! zs[k]!)))
def full104 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full104 xs ys zs k (Digest.full (op104 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run104 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  let (zs, dz) := inHalf seedZ count
  runT "binary16/fma[status]" xs ys zs (mixFull (mixFull dx dy) dz) timed104 full104 trials reps

/-! ### `bfloat16/add[status]` -/
@[inline] def op186 (x y : Brain) := ExecFloat.Binary.add x y (status := true)
def timed186 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed186 xs ys k (mixQuick acc (Digest.quick (op186 xs[k]! ys[k]!)))
def full186 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full186 xs ys k (Digest.full (op186 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run186 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/add[status]" xs ys (mixFull dx dy) timed186 full186 trials reps

/-! ### `bfloat16/sub[status]` -/
@[inline] def op187 (x y : Brain) := ExecFloat.Binary.sub x y (status := true)
def timed187 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed187 xs ys k (mixQuick acc (Digest.quick (op187 xs[k]! ys[k]!)))
def full187 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full187 xs ys k (Digest.full (op187 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run187 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/sub[status]" xs ys (mixFull dx dy) timed187 full187 trials reps

/-! ### `bfloat16/mul[status]` -/
@[inline] def op188 (x y : Brain) := ExecFloat.Binary.mul x y (status := true)
def timed188 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed188 xs ys k (mixQuick acc (Digest.quick (op188 xs[k]! ys[k]!)))
def full188 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full188 xs ys k (Digest.full (op188 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run188 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/mul[status]" xs ys (mixFull dx dy) timed188 full188 trials reps

/-! ### `bfloat16/div[status]` -/
@[inline] def op189 (x y : Brain) := ExecFloat.Binary.div x y (status := true)
def timed189 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed189 xs ys k (mixQuick acc (Digest.quick (op189 xs[k]! ys[k]!)))
def full189 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full189 xs ys k (Digest.full (op189 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run189 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/div[status]" xs ys (mixFull dx dy) timed189 full189 trials reps

/-! ### `bfloat16/sqrt[status]` -/
@[inline] def op190 (x : Brain) := ExecFloat.Binary.sqrt x (status := true)
def timed190 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed190 xs k (mixQuick acc (Digest.quick (op190 xs[k]!)))
def full190 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full190 xs k (Digest.full (op190 xs[k]!) (mixFull h k.toUInt64))
def run190 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/sqrt[status]" xs d timed190 full190 trials reps

/-! ### `bfloat16/fma[status]` -/
@[inline] def op191 (x y z : Brain) := ExecFloat.Binary.fma x y z (status := true)
def timed191 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed191 xs ys zs k (mixQuick acc (Digest.quick (op191 xs[k]! ys[k]! zs[k]!)))
def full191 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full191 xs ys zs k (Digest.full (op191 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run191 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  let (zs, dz) := inBrain seedZ count
  runT "bfloat16/fma[status]" xs ys zs (mixFull (mixFull dx dy) dz) timed191 full191 trials reps

/-! ### `binary32/add[status]` -/
@[inline] def op273 (x y : Single) := ExecFloat.Binary.add x y (status := true)
def timed273 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed273 xs ys k (mixQuick acc (Digest.quick (op273 xs[k]! ys[k]!)))
def full273 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full273 xs ys k (Digest.full (op273 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run273 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/add[status]" xs ys (mixFull dx dy) timed273 full273 trials reps

/-! ### `binary32/sub[status]` -/
@[inline] def op274 (x y : Single) := ExecFloat.Binary.sub x y (status := true)
def timed274 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed274 xs ys k (mixQuick acc (Digest.quick (op274 xs[k]! ys[k]!)))
def full274 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full274 xs ys k (Digest.full (op274 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run274 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/sub[status]" xs ys (mixFull dx dy) timed274 full274 trials reps

/-! ### `binary32/mul[status]` -/
@[inline] def op275 (x y : Single) := ExecFloat.Binary.mul x y (status := true)
def timed275 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed275 xs ys k (mixQuick acc (Digest.quick (op275 xs[k]! ys[k]!)))
def full275 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full275 xs ys k (Digest.full (op275 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run275 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/mul[status]" xs ys (mixFull dx dy) timed275 full275 trials reps

/-! ### `binary32/div[status]` -/
@[inline] def op276 (x y : Single) := ExecFloat.Binary.div x y (status := true)
def timed276 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed276 xs ys k (mixQuick acc (Digest.quick (op276 xs[k]! ys[k]!)))
def full276 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full276 xs ys k (Digest.full (op276 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run276 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/div[status]" xs ys (mixFull dx dy) timed276 full276 trials reps

/-! ### `binary32/sqrt[status]` -/
@[inline] def op277 (x : Single) := ExecFloat.Binary.sqrt x (status := true)
def timed277 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed277 xs k (mixQuick acc (Digest.quick (op277 xs[k]!)))
def full277 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full277 xs k (Digest.full (op277 xs[k]!) (mixFull h k.toUInt64))
def run277 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/sqrt[status]" xs d timed277 full277 trials reps

/-! ### `binary32/fma[status]` -/
@[inline] def op278 (x y z : Single) := ExecFloat.Binary.fma x y z (status := true)
def timed278 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed278 xs ys zs k (mixQuick acc (Digest.quick (op278 xs[k]! ys[k]! zs[k]!)))
def full278 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full278 xs ys zs k (Digest.full (op278 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run278 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  let (zs, dz) := inSingle seedZ count
  runT "binary32/fma[status]" xs ys zs (mixFull (mixFull dx dy) dz) timed278 full278 trials reps

/-! ### `binary64/add[status]` -/
@[inline] def op360 (x y : Double) := ExecFloat.Binary.add x y (status := true)
def timed360 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed360 xs ys k (mixQuick acc (Digest.quick (op360 xs[k]! ys[k]!)))
def full360 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full360 xs ys k (Digest.full (op360 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run360 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/add[status]" xs ys (mixFull dx dy) timed360 full360 trials reps

/-! ### `binary64/sub[status]` -/
@[inline] def op361 (x y : Double) := ExecFloat.Binary.sub x y (status := true)
def timed361 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed361 xs ys k (mixQuick acc (Digest.quick (op361 xs[k]! ys[k]!)))
def full361 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full361 xs ys k (Digest.full (op361 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run361 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/sub[status]" xs ys (mixFull dx dy) timed361 full361 trials reps

/-! ### `binary64/mul[status]` -/
@[inline] def op362 (x y : Double) := ExecFloat.Binary.mul x y (status := true)
def timed362 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed362 xs ys k (mixQuick acc (Digest.quick (op362 xs[k]! ys[k]!)))
def full362 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full362 xs ys k (Digest.full (op362 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run362 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/mul[status]" xs ys (mixFull dx dy) timed362 full362 trials reps

/-! ### `binary64/div[status]` -/
@[inline] def op363 (x y : Double) := ExecFloat.Binary.div x y (status := true)
def timed363 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed363 xs ys k (mixQuick acc (Digest.quick (op363 xs[k]! ys[k]!)))
def full363 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full363 xs ys k (Digest.full (op363 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run363 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/div[status]" xs ys (mixFull dx dy) timed363 full363 trials reps

/-! ### `binary64/sqrt[status]` -/
@[inline] def op364 (x : Double) := ExecFloat.Binary.sqrt x (status := true)
def timed364 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed364 xs k (mixQuick acc (Digest.quick (op364 xs[k]!)))
def full364 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full364 xs k (Digest.full (op364 xs[k]!) (mixFull h k.toUInt64))
def run364 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/sqrt[status]" xs d timed364 full364 trials reps

/-! ### `binary64/fma[status]` -/
@[inline] def op365 (x y z : Double) := ExecFloat.Binary.fma x y z (status := true)
def timed365 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed365 xs ys zs k (mixQuick acc (Digest.quick (op365 xs[k]! ys[k]! zs[k]!)))
def full365 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full365 xs ys zs k (Digest.full (op365 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run365 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  let (zs, dz) := inDouble seedZ count
  runT "binary64/fma[status]" xs ys zs (mixFull (mixFull dx dy) dz) timed365 full365 trials reps

/-! ### `binary128/add[status]` -/
@[inline] def op447 (x y : Quad) := ExecFloat.Binary.add x y (status := true)
def timed447 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed447 xs ys k (mixQuick acc (Digest.quick (op447 xs[k]! ys[k]!)))
def full447 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full447 xs ys k (Digest.full (op447 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run447 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/add[status]" xs ys (mixFull dx dy) timed447 full447 trials reps

/-! ### `binary128/sub[status]` -/
@[inline] def op448 (x y : Quad) := ExecFloat.Binary.sub x y (status := true)
def timed448 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed448 xs ys k (mixQuick acc (Digest.quick (op448 xs[k]! ys[k]!)))
def full448 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full448 xs ys k (Digest.full (op448 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run448 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/sub[status]" xs ys (mixFull dx dy) timed448 full448 trials reps

/-! ### `binary128/mul[status]` -/
@[inline] def op449 (x y : Quad) := ExecFloat.Binary.mul x y (status := true)
def timed449 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed449 xs ys k (mixQuick acc (Digest.quick (op449 xs[k]! ys[k]!)))
def full449 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full449 xs ys k (Digest.full (op449 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run449 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/mul[status]" xs ys (mixFull dx dy) timed449 full449 trials reps

/-! ### `binary128/div[status]` -/
@[inline] def op450 (x y : Quad) := ExecFloat.Binary.div x y (status := true)
def timed450 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed450 xs ys k (mixQuick acc (Digest.quick (op450 xs[k]! ys[k]!)))
def full450 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full450 xs ys k (Digest.full (op450 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run450 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/div[status]" xs ys (mixFull dx dy) timed450 full450 trials reps

/-! ### `binary128/sqrt[status]` -/
@[inline] def op451 (x : Quad) := ExecFloat.Binary.sqrt x (status := true)
def timed451 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed451 xs k (mixQuick acc (Digest.quick (op451 xs[k]!)))
def full451 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full451 xs k (Digest.full (op451 xs[k]!) (mixFull h k.toUInt64))
def run451 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/sqrt[status]" xs d timed451 full451 trials reps

/-! ### `binary128/fma[status]` -/
@[inline] def op452 (x y z : Quad) := ExecFloat.Binary.fma x y z (status := true)
def timed452 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed452 xs ys zs k (mixQuick acc (Digest.quick (op452 xs[k]! ys[k]! zs[k]!)))
def full452 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full452 xs ys zs k (Digest.full (op452 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run452 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  let (zs, dz) := inQuad seedZ count
  runT "binary128/fma[status]" xs ys zs (mixFull (mixFull dx dy) dz) timed452 full452 trials reps

/-! ### `binary256/add[status]` -/
@[inline] def op493 (x y : Oct) := ExecFloat.Binary.add x y (status := true)
def timed493 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed493 xs ys k (mixQuick acc (Digest.quick (op493 xs[k]! ys[k]!)))
def full493 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full493 xs ys k (Digest.full (op493 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run493 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/add[status]" xs ys (mixFull dx dy) timed493 full493 trials reps

/-! ### Square root on a runtime format -/

/-- The timed projection of a descriptor-model outcome, as for a configured outcome. -/
@[inline] def modelOutcomeQuick {fmt : FloatFormat} (o : Model.IEEEOutcome fmt) : UInt64 :=
  o.value.toNatBits.toUInt64 ^^^ ((statusBits o.status <<< 17) ||| (orderingCode o.ternary <<< 22))

/-- The complete digest of a descriptor-model outcome, equal to that of the configured outcome. -/
@[inline] def modelOutcomeFull {fmt : FloatFormat} (o : Model.IEEEOutcome fmt) (h : UInt64) :
    UInt64 :=
  Digest.full o.ternary
    (Digest.full o.status (feedNatAll (mixFull (mixFull h 0x780) 0xC00) o.value.toNatBits))

/-- Nearest-even `Model.sqrt` with status on a format that is an argument of the compiled loop. -/
def timedSqrtRuntime (fmt : FloatFormat) (xs : Array (Model fmt)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc =>
      timedSqrtRuntime fmt xs k
        (mixQuick acc (modelOutcomeQuick (Model.sqrt xs[k]! (status := true))))
def fullSqrtRuntime (fmt : FloatFormat) (xs : Array (Model fmt)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h =>
      fullSqrtRuntime fmt xs k
        (modelOutcomeFull (Model.sqrt xs[k]! (status := true)) (mixFull h k.toUInt64))
def runSqrtRuntime (name : String) (fmt : FloatFormat) (e m : Nat)
    (count trials reps : Nat) : IO Unit := do
  let (xs, d) := binaryInputs (Model.ofNatBits : Nat → Model fmt) e m seedX count
  runU name xs d (timedSqrtRuntime fmt) (fullSqrtRuntime fmt) trials reps

end FloatLibBenchmarks.Public.TimeOps
