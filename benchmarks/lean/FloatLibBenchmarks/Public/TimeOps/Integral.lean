/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Integral rounding and remainder timings

Integral rounding and remainder cells with the same mixed-input protocol.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/roundToIntegral[nearest]` -/
@[inline] def op39 (x : Half) := ExecFloat.Binary.roundToIntegral x .nearest
def timed39 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed39 xs k (mixQuick acc (Digest.quick (op39 xs[k]!)))
def full39 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full39 xs k (Digest.full (op39 xs[k]!) (mixFull h k.toUInt64))
def run39 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/roundToIntegral[nearest]" xs d timed39 full39 trials reps

/-! ### `binary16/roundToIntegral[towardZero]` -/
@[inline] def op40 (x : Half) := ExecFloat.Binary.roundToIntegral x .towardZero
def timed40 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed40 xs k (mixQuick acc (Digest.quick (op40 xs[k]!)))
def full40 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full40 xs k (Digest.full (op40 xs[k]!) (mixFull h k.toUInt64))
def run40 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/roundToIntegral[towardZero]" xs d timed40 full40 trials reps

/-! ### `binary16/roundToIntegral[up]` -/
@[inline] def op41 (x : Half) := ExecFloat.Binary.roundToIntegral x .up
def timed41 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed41 xs k (mixQuick acc (Digest.quick (op41 xs[k]!)))
def full41 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full41 xs k (Digest.full (op41 xs[k]!) (mixFull h k.toUInt64))
def run41 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/roundToIntegral[up]" xs d timed41 full41 trials reps

/-! ### `binary16/roundToIntegral[down]` -/
@[inline] def op42 (x : Half) := ExecFloat.Binary.roundToIntegral x .down
def timed42 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed42 xs k (mixQuick acc (Digest.quick (op42 xs[k]!)))
def full42 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full42 xs k (Digest.full (op42 xs[k]!) (mixFull h k.toUInt64))
def run42 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/roundToIntegral[down]" xs d timed42 full42 trials reps

/-! ### `binary16/roundToIntegral[status]` -/
@[inline] def op43 (x : Half) := ExecFloat.Binary.roundToIntegral x .nearest (status := true)
def timed43 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed43 xs k (mixQuick acc (Digest.quick (op43 xs[k]!)))
def full43 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full43 xs k (Digest.full (op43 xs[k]!) (mixFull h k.toUInt64))
def run43 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/roundToIntegral[status]" xs d timed43 full43 trials reps

/-! ### `binary16/remainder` -/
@[inline] def op44 (x y : Half) := ExecFloat.Binary.remainder x y
def timed44 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed44 xs ys k (mixQuick acc (Digest.quick (op44 xs[k]! ys[k]!)))
def full44 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full44 xs ys k (Digest.full (op44 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run44 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/remainder" xs ys (mixFull dx dy) timed44 full44 trials reps

/-! ### `bfloat16/roundToIntegral[nearest]` -/
@[inline] def op126 (x : Brain) := ExecFloat.Binary.roundToIntegral x .nearest
def timed126 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed126 xs k (mixQuick acc (Digest.quick (op126 xs[k]!)))
def full126 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full126 xs k (Digest.full (op126 xs[k]!) (mixFull h k.toUInt64))
def run126 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/roundToIntegral[nearest]" xs d timed126 full126 trials reps

/-! ### `bfloat16/roundToIntegral[towardZero]` -/
@[inline] def op127 (x : Brain) := ExecFloat.Binary.roundToIntegral x .towardZero
def timed127 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed127 xs k (mixQuick acc (Digest.quick (op127 xs[k]!)))
def full127 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full127 xs k (Digest.full (op127 xs[k]!) (mixFull h k.toUInt64))
def run127 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/roundToIntegral[towardZero]" xs d timed127 full127 trials reps

/-! ### `bfloat16/roundToIntegral[up]` -/
@[inline] def op128 (x : Brain) := ExecFloat.Binary.roundToIntegral x .up
def timed128 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed128 xs k (mixQuick acc (Digest.quick (op128 xs[k]!)))
def full128 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full128 xs k (Digest.full (op128 xs[k]!) (mixFull h k.toUInt64))
def run128 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/roundToIntegral[up]" xs d timed128 full128 trials reps

/-! ### `bfloat16/roundToIntegral[down]` -/
@[inline] def op129 (x : Brain) := ExecFloat.Binary.roundToIntegral x .down
def timed129 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed129 xs k (mixQuick acc (Digest.quick (op129 xs[k]!)))
def full129 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full129 xs k (Digest.full (op129 xs[k]!) (mixFull h k.toUInt64))
def run129 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/roundToIntegral[down]" xs d timed129 full129 trials reps

/-! ### `bfloat16/roundToIntegral[status]` -/
@[inline] def op130 (x : Brain) := ExecFloat.Binary.roundToIntegral x .nearest (status := true)
def timed130 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed130 xs k (mixQuick acc (Digest.quick (op130 xs[k]!)))
def full130 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full130 xs k (Digest.full (op130 xs[k]!) (mixFull h k.toUInt64))
def run130 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/roundToIntegral[status]" xs d timed130 full130 trials reps

/-! ### `bfloat16/remainder` -/
@[inline] def op131 (x y : Brain) := ExecFloat.Binary.remainder x y
def timed131 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed131 xs ys k (mixQuick acc (Digest.quick (op131 xs[k]! ys[k]!)))
def full131 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full131 xs ys k (Digest.full (op131 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run131 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/remainder" xs ys (mixFull dx dy) timed131 full131 trials reps

/-! ### `binary32/roundToIntegral[nearest]` -/
@[inline] def op213 (x : Single) := ExecFloat.Binary.roundToIntegral x .nearest
def timed213 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed213 xs k (mixQuick acc (Digest.quick (op213 xs[k]!)))
def full213 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full213 xs k (Digest.full (op213 xs[k]!) (mixFull h k.toUInt64))
def run213 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/roundToIntegral[nearest]" xs d timed213 full213 trials reps

/-! ### `binary32/roundToIntegral[towardZero]` -/
@[inline] def op214 (x : Single) := ExecFloat.Binary.roundToIntegral x .towardZero
def timed214 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed214 xs k (mixQuick acc (Digest.quick (op214 xs[k]!)))
def full214 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full214 xs k (Digest.full (op214 xs[k]!) (mixFull h k.toUInt64))
def run214 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/roundToIntegral[towardZero]" xs d timed214 full214 trials reps

/-! ### `binary32/roundToIntegral[up]` -/
@[inline] def op215 (x : Single) := ExecFloat.Binary.roundToIntegral x .up
def timed215 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed215 xs k (mixQuick acc (Digest.quick (op215 xs[k]!)))
def full215 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full215 xs k (Digest.full (op215 xs[k]!) (mixFull h k.toUInt64))
def run215 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/roundToIntegral[up]" xs d timed215 full215 trials reps

/-! ### `binary32/roundToIntegral[down]` -/
@[inline] def op216 (x : Single) := ExecFloat.Binary.roundToIntegral x .down
def timed216 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed216 xs k (mixQuick acc (Digest.quick (op216 xs[k]!)))
def full216 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full216 xs k (Digest.full (op216 xs[k]!) (mixFull h k.toUInt64))
def run216 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/roundToIntegral[down]" xs d timed216 full216 trials reps

/-! ### `binary32/roundToIntegral[status]` -/
@[inline] def op217 (x : Single) := ExecFloat.Binary.roundToIntegral x .nearest (status := true)
def timed217 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed217 xs k (mixQuick acc (Digest.quick (op217 xs[k]!)))
def full217 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full217 xs k (Digest.full (op217 xs[k]!) (mixFull h k.toUInt64))
def run217 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/roundToIntegral[status]" xs d timed217 full217 trials reps

/-! ### `binary32/remainder` -/
@[inline] def op218 (x y : Single) := ExecFloat.Binary.remainder x y
def timed218 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed218 xs ys k (mixQuick acc (Digest.quick (op218 xs[k]! ys[k]!)))
def full218 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full218 xs ys k (Digest.full (op218 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run218 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/remainder" xs ys (mixFull dx dy) timed218 full218 trials reps

/-! ### `binary64/roundToIntegral[nearest]` -/
@[inline] def op300 (x : Double) := ExecFloat.Binary.roundToIntegral x .nearest
def timed300 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed300 xs k (mixQuick acc (Digest.quick (op300 xs[k]!)))
def full300 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full300 xs k (Digest.full (op300 xs[k]!) (mixFull h k.toUInt64))
def run300 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/roundToIntegral[nearest]" xs d timed300 full300 trials reps

/-! ### `binary64/roundToIntegral[towardZero]` -/
@[inline] def op301 (x : Double) := ExecFloat.Binary.roundToIntegral x .towardZero
def timed301 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed301 xs k (mixQuick acc (Digest.quick (op301 xs[k]!)))
def full301 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full301 xs k (Digest.full (op301 xs[k]!) (mixFull h k.toUInt64))
def run301 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/roundToIntegral[towardZero]" xs d timed301 full301 trials reps

/-! ### `binary64/roundToIntegral[up]` -/
@[inline] def op302 (x : Double) := ExecFloat.Binary.roundToIntegral x .up
def timed302 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed302 xs k (mixQuick acc (Digest.quick (op302 xs[k]!)))
def full302 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full302 xs k (Digest.full (op302 xs[k]!) (mixFull h k.toUInt64))
def run302 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/roundToIntegral[up]" xs d timed302 full302 trials reps

/-! ### `binary64/roundToIntegral[down]` -/
@[inline] def op303 (x : Double) := ExecFloat.Binary.roundToIntegral x .down
def timed303 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed303 xs k (mixQuick acc (Digest.quick (op303 xs[k]!)))
def full303 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full303 xs k (Digest.full (op303 xs[k]!) (mixFull h k.toUInt64))
def run303 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/roundToIntegral[down]" xs d timed303 full303 trials reps

/-! ### `binary64/roundToIntegral[status]` -/
@[inline] def op304 (x : Double) := ExecFloat.Binary.roundToIntegral x .nearest (status := true)
def timed304 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed304 xs k (mixQuick acc (Digest.quick (op304 xs[k]!)))
def full304 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full304 xs k (Digest.full (op304 xs[k]!) (mixFull h k.toUInt64))
def run304 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/roundToIntegral[status]" xs d timed304 full304 trials reps

/-! ### `binary64/remainder` -/
@[inline] def op305 (x y : Double) := ExecFloat.Binary.remainder x y
def timed305 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed305 xs ys k (mixQuick acc (Digest.quick (op305 xs[k]! ys[k]!)))
def full305 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full305 xs ys k (Digest.full (op305 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run305 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/remainder" xs ys (mixFull dx dy) timed305 full305 trials reps

/-! ### `binary128/roundToIntegral[nearest]` -/
@[inline] def op387 (x : Quad) := ExecFloat.Binary.roundToIntegral x .nearest
def timed387 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed387 xs k (mixQuick acc (Digest.quick (op387 xs[k]!)))
def full387 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full387 xs k (Digest.full (op387 xs[k]!) (mixFull h k.toUInt64))
def run387 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/roundToIntegral[nearest]" xs d timed387 full387 trials reps

/-! ### `binary128/roundToIntegral[towardZero]` -/
@[inline] def op388 (x : Quad) := ExecFloat.Binary.roundToIntegral x .towardZero
def timed388 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed388 xs k (mixQuick acc (Digest.quick (op388 xs[k]!)))
def full388 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full388 xs k (Digest.full (op388 xs[k]!) (mixFull h k.toUInt64))
def run388 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/roundToIntegral[towardZero]" xs d timed388 full388 trials reps

/-! ### `binary128/roundToIntegral[up]` -/
@[inline] def op389 (x : Quad) := ExecFloat.Binary.roundToIntegral x .up
def timed389 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed389 xs k (mixQuick acc (Digest.quick (op389 xs[k]!)))
def full389 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full389 xs k (Digest.full (op389 xs[k]!) (mixFull h k.toUInt64))
def run389 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/roundToIntegral[up]" xs d timed389 full389 trials reps

/-! ### `binary128/roundToIntegral[down]` -/
@[inline] def op390 (x : Quad) := ExecFloat.Binary.roundToIntegral x .down
def timed390 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed390 xs k (mixQuick acc (Digest.quick (op390 xs[k]!)))
def full390 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full390 xs k (Digest.full (op390 xs[k]!) (mixFull h k.toUInt64))
def run390 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/roundToIntegral[down]" xs d timed390 full390 trials reps

/-! ### `binary128/roundToIntegral[status]` -/
@[inline] def op391 (x : Quad) := ExecFloat.Binary.roundToIntegral x .nearest (status := true)
def timed391 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed391 xs k (mixQuick acc (Digest.quick (op391 xs[k]!)))
def full391 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full391 xs k (Digest.full (op391 xs[k]!) (mixFull h k.toUInt64))
def run391 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/roundToIntegral[status]" xs d timed391 full391 trials reps

/-! ### `binary128/remainder` -/
@[inline] def op392 (x y : Quad) := ExecFloat.Binary.remainder x y
def timed392 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed392 xs ys k (mixQuick acc (Digest.quick (op392 xs[k]! ys[k]!)))
def full392 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full392 xs ys k (Digest.full (op392 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run392 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/remainder" xs ys (mixFull dx dy) timed392 full392 trials reps

/-! ### `binary256/roundToIntegral[nearest]` -/
@[inline] def op472 (x : Oct) := ExecFloat.Binary.roundToIntegral x .nearest
def timed472 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed472 xs k (mixQuick acc (Digest.quick (op472 xs[k]!)))
def full472 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full472 xs k (Digest.full (op472 xs[k]!) (mixFull h k.toUInt64))
def run472 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/roundToIntegral[nearest]" xs d timed472 full472 trials reps

/-! ### `binary256/roundToIntegral[towardZero]` -/
@[inline] def op473 (x : Oct) := ExecFloat.Binary.roundToIntegral x .towardZero
def timed473 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed473 xs k (mixQuick acc (Digest.quick (op473 xs[k]!)))
def full473 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full473 xs k (Digest.full (op473 xs[k]!) (mixFull h k.toUInt64))
def run473 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/roundToIntegral[towardZero]" xs d timed473 full473 trials reps

/-! ### `binary256/remainder` -/
@[inline] def op474 (x y : Oct) := ExecFloat.Binary.remainder x y
def timed474 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed474 xs ys k (mixQuick acc (Digest.quick (op474 xs[k]! ys[k]!)))
def full474 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full474 xs ys k (Digest.full (op474 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run474 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/remainder" xs ys (mixFull dx dy) timed474 full474 trials reps

/-! ### `posit32/nearestInt` -/
@[inline] def op508 (x : P32) := ExecFloat.Posit.nearestInt x
def timed508 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed508 xs k (mixQuick acc (Digest.quick (op508 xs[k]!)))
def full508 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full508 xs k (Digest.full (op508 xs[k]!) (mixFull h k.toUInt64))
def run508 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/nearestInt" xs d timed508 full508 trials reps

/-! ### `posit32/ceil` -/
@[inline] def op509 (x : P32) := ExecFloat.Posit.ceil x
def timed509 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed509 xs k (mixQuick acc (Digest.quick (op509 xs[k]!)))
def full509 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full509 xs k (Digest.full (op509 xs[k]!) (mixFull h k.toUInt64))
def run509 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/ceil" xs d timed509 full509 trials reps

/-! ### `posit32/floor` -/
@[inline] def op510 (x : P32) := ExecFloat.Posit.floor x
def timed510 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed510 xs k (mixQuick acc (Digest.quick (op510 xs[k]!)))
def full510 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full510 xs k (Digest.full (op510 xs[k]!) (mixFull h k.toUInt64))
def run510 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/floor" xs d timed510 full510 trials reps

end FloatLibBenchmarks.Public.TimeOps
