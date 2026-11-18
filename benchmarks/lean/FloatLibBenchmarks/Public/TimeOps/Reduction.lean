/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Reduction timings

Eight-term sums, dot products and quire reductions.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/sum8` -/
@[inline] def op120 (a : Array Half) := ExecFloat.Binary.sum a .nearest
def timed120 (cs : Array (Array Half)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed120 cs k (mixQuick acc (Digest.quick (op120 cs[k]!)))
def full120 (cs : Array (Array Half)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full120 cs k (Digest.full (op120 cs[k]!) (mixFull h k.toUInt64))
def run120 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX (8 * count)
  runU "binary16/sum8" (chunk8 xs) d timed120 full120 trials reps

/-! ### `binary16/dot8` -/
@[inline] def op121 (a b : Array Half) := ExecFloat.Binary.dot a b .nearest
def timed121 (cs ds : Array (Array Half)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed121 cs ds k (mixQuick acc (Digest.quick (op121 cs[k]! ds[k]!)))
def full121 (cs ds : Array (Array Half)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full121 cs ds k (Digest.full (op121 cs[k]! ds[k]!) (mixFull h k.toUInt64))
def run121 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX (8 * count)
  let (ys, dy) := inHalf seedY (8 * count)
  runB "binary16/dot8" (chunk8 xs) (chunk8 ys) (mixFull dx dy) timed121 full121 trials reps

/-! ### `bfloat16/sum8` -/
@[inline] def op207 (a : Array Brain) := ExecFloat.Binary.sum a .nearest
def timed207 (cs : Array (Array Brain)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed207 cs k (mixQuick acc (Digest.quick (op207 cs[k]!)))
def full207 (cs : Array (Array Brain)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full207 cs k (Digest.full (op207 cs[k]!) (mixFull h k.toUInt64))
def run207 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX (8 * count)
  runU "bfloat16/sum8" (chunk8 xs) d timed207 full207 trials reps

/-! ### `bfloat16/dot8` -/
@[inline] def op208 (a b : Array Brain) := ExecFloat.Binary.dot a b .nearest
def timed208 (cs ds : Array (Array Brain)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed208 cs ds k (mixQuick acc (Digest.quick (op208 cs[k]! ds[k]!)))
def full208 (cs ds : Array (Array Brain)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full208 cs ds k (Digest.full (op208 cs[k]! ds[k]!) (mixFull h k.toUInt64))
def run208 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX (8 * count)
  let (ys, dy) := inBrain seedY (8 * count)
  runB "bfloat16/dot8" (chunk8 xs) (chunk8 ys) (mixFull dx dy) timed208 full208 trials reps

/-! ### `binary32/sum8` -/
@[inline] def op294 (a : Array Single) := ExecFloat.Binary.sum a .nearest
def timed294 (cs : Array (Array Single)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed294 cs k (mixQuick acc (Digest.quick (op294 cs[k]!)))
def full294 (cs : Array (Array Single)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full294 cs k (Digest.full (op294 cs[k]!) (mixFull h k.toUInt64))
def run294 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX (8 * count)
  runU "binary32/sum8" (chunk8 xs) d timed294 full294 trials reps

/-! ### `binary32/dot8` -/
@[inline] def op295 (a b : Array Single) := ExecFloat.Binary.dot a b .nearest
def timed295 (cs ds : Array (Array Single)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed295 cs ds k (mixQuick acc (Digest.quick (op295 cs[k]! ds[k]!)))
def full295 (cs ds : Array (Array Single)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full295 cs ds k (Digest.full (op295 cs[k]! ds[k]!) (mixFull h k.toUInt64))
def run295 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX (8 * count)
  let (ys, dy) := inSingle seedY (8 * count)
  runB "binary32/dot8" (chunk8 xs) (chunk8 ys) (mixFull dx dy) timed295 full295 trials reps

/-! ### `binary64/sum8` -/
@[inline] def op381 (a : Array Double) := ExecFloat.Binary.sum a .nearest
def timed381 (cs : Array (Array Double)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed381 cs k (mixQuick acc (Digest.quick (op381 cs[k]!)))
def full381 (cs : Array (Array Double)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full381 cs k (Digest.full (op381 cs[k]!) (mixFull h k.toUInt64))
def run381 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX (8 * count)
  runU "binary64/sum8" (chunk8 xs) d timed381 full381 trials reps

/-! ### `binary64/dot8` -/
@[inline] def op382 (a b : Array Double) := ExecFloat.Binary.dot a b .nearest
def timed382 (cs ds : Array (Array Double)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed382 cs ds k (mixQuick acc (Digest.quick (op382 cs[k]! ds[k]!)))
def full382 (cs ds : Array (Array Double)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full382 cs ds k (Digest.full (op382 cs[k]! ds[k]!) (mixFull h k.toUInt64))
def run382 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX (8 * count)
  let (ys, dy) := inDouble seedY (8 * count)
  runB "binary64/dot8" (chunk8 xs) (chunk8 ys) (mixFull dx dy) timed382 full382 trials reps

/-! ### `binary128/sum8` -/
@[inline] def op468 (a : Array Quad) := ExecFloat.Binary.sum a .nearest
def timed468 (cs : Array (Array Quad)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed468 cs k (mixQuick acc (Digest.quick (op468 cs[k]!)))
def full468 (cs : Array (Array Quad)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full468 cs k (Digest.full (op468 cs[k]!) (mixFull h k.toUInt64))
def run468 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX (8 * count)
  runU "binary128/sum8" (chunk8 xs) d timed468 full468 trials reps

/-! ### `binary128/dot8` -/
@[inline] def op469 (a b : Array Quad) := ExecFloat.Binary.dot a b .nearest
def timed469 (cs ds : Array (Array Quad)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed469 cs ds k (mixQuick acc (Digest.quick (op469 cs[k]! ds[k]!)))
def full469 (cs ds : Array (Array Quad)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full469 cs ds k (Digest.full (op469 cs[k]! ds[k]!) (mixFull h k.toUInt64))
def run469 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX (8 * count)
  let (ys, dy) := inQuad seedY (8 * count)
  runB "binary128/dot8" (chunk8 xs) (chunk8 ys) (mixFull dx dy) timed469 full469 trials reps

/-! ### `posit32/quireDot8` -/
@[inline] def op532 (a b : Array P32) := (ExecFloat.Posit.Quire.qToP ((a.zip b).foldl (fun q p =>
    ExecFloat.Posit.Quire.qMulAdd q p.1 p.2) (ExecFloat.Posit.Quire.pToQ (0 : P32))) : P32)
def timed532 (cs ds : Array (Array P32)) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed532 cs ds k (mixQuick acc (Digest.quick (op532 cs[k]! ds[k]!)))
def full532 (cs ds : Array (Array P32)) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full532 cs ds k (Digest.full (op532 cs[k]! ds[k]!) (mixFull h k.toUInt64))
def run532 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX (8 * count)
  let (ys, dy) := inP32 seedY (8 * count)
  runB "posit32/quireDot8" (chunk8 xs) (chunk8 ys) (mixFull dx dy) timed532 full532 trials reps

end FloatLibBenchmarks.Public.TimeOps
