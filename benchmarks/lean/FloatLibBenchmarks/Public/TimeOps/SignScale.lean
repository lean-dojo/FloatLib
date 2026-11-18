/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Sign, exponent and adjacent-value timings

Sign operations, binary scaling, exponent queries and adjacent values.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/nextUp` -/
@[inline] def op60 (x : Half) := ExecFloat.Binary.nextUp x
def timed60 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed60 xs k (mixQuick acc (Digest.quick (op60 xs[k]!)))
def full60 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full60 xs k (Digest.full (op60 xs[k]!) (mixFull h k.toUInt64))
def run60 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/nextUp" xs d timed60 full60 trials reps

/-! ### `binary16/nextDown` -/
@[inline] def op61 (x : Half) := ExecFloat.Binary.nextDown x
def timed61 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed61 xs k (mixQuick acc (Digest.quick (op61 xs[k]!)))
def full61 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full61 xs k (Digest.full (op61 xs[k]!) (mixFull h k.toUInt64))
def run61 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/nextDown" xs d timed61 full61 trials reps

/-! ### `binary16/scale` -/
@[inline] def op62 (x : Half) (n : Int) := ExecFloat.Binary.scale x n .nearest
def timed62 (xs : Array Half) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed62 xs ns k (mixQuick acc (Digest.quick (op62 xs[k]! ns[k]!)))
def full62 (xs : Array Half) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full62 xs ns k (Digest.full (op62 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run62 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ns, dn) := inScale count
  runXI "binary16/scale" xs ns (mixFull dx dn) timed62 full62 trials reps

/-! ### `binary16/logB` -/
@[inline] def op63 (x : Half) := ExecFloat.Binary.logB x
def timed63 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed63 xs k (mixQuick acc (Digest.quick (op63 xs[k]!)))
def full63 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full63 xs k (Digest.full (op63 xs[k]!) (mixFull h k.toUInt64))
def run63 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/logB" xs d timed63 full63 trials reps

/-! ### `binary16/logBInt` -/
@[inline] def op64 (x : Half) := ExecFloat.Binary.logBInt x
def timed64 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed64 xs k (mixQuick acc (Digest.quick (op64 xs[k]!)))
def full64 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full64 xs k (Digest.full (op64 xs[k]!) (mixFull h k.toUInt64))
def run64 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/logBInt" xs d timed64 full64 trials reps

/-! ### `binary16/negate` -/
@[inline] def op65 (x : Half) := -x
def timed65 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed65 xs k (mixQuick acc (Digest.quick (op65 xs[k]!)))
def full65 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full65 xs k (Digest.full (op65 xs[k]!) (mixFull h k.toUInt64))
def run65 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/negate" xs d timed65 full65 trials reps

/-! ### `binary16/abs` -/
@[inline] def op66 (x : Half) := ExecFloat.Binary.abs x
def timed66 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed66 xs k (mixQuick acc (Digest.quick (op66 xs[k]!)))
def full66 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full66 xs k (Digest.full (op66 xs[k]!) (mixFull h k.toUInt64))
def run66 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/abs" xs d timed66 full66 trials reps

/-! ### `binary16/copySign` -/
@[inline] def op67 (x y : Half) := ExecFloat.Binary.copySign x y
def timed67 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed67 xs ys k (mixQuick acc (Digest.quick (op67 xs[k]! ys[k]!)))
def full67 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full67 xs ys k (Digest.full (op67 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run67 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/copySign" xs ys (mixFull dx dy) timed67 full67 trials reps

/-! ### `bfloat16/nextUp` -/
@[inline] def op147 (x : Brain) := ExecFloat.Binary.nextUp x
def timed147 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed147 xs k (mixQuick acc (Digest.quick (op147 xs[k]!)))
def full147 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full147 xs k (Digest.full (op147 xs[k]!) (mixFull h k.toUInt64))
def run147 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/nextUp" xs d timed147 full147 trials reps

/-! ### `bfloat16/nextDown` -/
@[inline] def op148 (x : Brain) := ExecFloat.Binary.nextDown x
def timed148 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed148 xs k (mixQuick acc (Digest.quick (op148 xs[k]!)))
def full148 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full148 xs k (Digest.full (op148 xs[k]!) (mixFull h k.toUInt64))
def run148 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/nextDown" xs d timed148 full148 trials reps

/-! ### `bfloat16/scale` -/
@[inline] def op149 (x : Brain) (n : Int) := ExecFloat.Binary.scale x n .nearest
def timed149 (xs : Array Brain) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed149 xs ns k (mixQuick acc (Digest.quick (op149 xs[k]! ns[k]!)))
def full149 (xs : Array Brain) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full149 xs ns k (Digest.full (op149 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run149 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ns, dn) := inScale count
  runXI "bfloat16/scale" xs ns (mixFull dx dn) timed149 full149 trials reps

/-! ### `bfloat16/logB` -/
@[inline] def op150 (x : Brain) := ExecFloat.Binary.logB x
def timed150 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed150 xs k (mixQuick acc (Digest.quick (op150 xs[k]!)))
def full150 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full150 xs k (Digest.full (op150 xs[k]!) (mixFull h k.toUInt64))
def run150 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/logB" xs d timed150 full150 trials reps

/-! ### `bfloat16/logBInt` -/
@[inline] def op151 (x : Brain) := ExecFloat.Binary.logBInt x
def timed151 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed151 xs k (mixQuick acc (Digest.quick (op151 xs[k]!)))
def full151 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full151 xs k (Digest.full (op151 xs[k]!) (mixFull h k.toUInt64))
def run151 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/logBInt" xs d timed151 full151 trials reps

/-! ### `bfloat16/negate` -/
@[inline] def op152 (x : Brain) := -x
def timed152 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed152 xs k (mixQuick acc (Digest.quick (op152 xs[k]!)))
def full152 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full152 xs k (Digest.full (op152 xs[k]!) (mixFull h k.toUInt64))
def run152 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/negate" xs d timed152 full152 trials reps

/-! ### `bfloat16/abs` -/
@[inline] def op153 (x : Brain) := ExecFloat.Binary.abs x
def timed153 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed153 xs k (mixQuick acc (Digest.quick (op153 xs[k]!)))
def full153 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full153 xs k (Digest.full (op153 xs[k]!) (mixFull h k.toUInt64))
def run153 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/abs" xs d timed153 full153 trials reps

/-! ### `bfloat16/copySign` -/
@[inline] def op154 (x y : Brain) := ExecFloat.Binary.copySign x y
def timed154 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed154 xs ys k (mixQuick acc (Digest.quick (op154 xs[k]! ys[k]!)))
def full154 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full154 xs ys k (Digest.full (op154 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run154 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/copySign" xs ys (mixFull dx dy) timed154 full154 trials reps

/-! ### `binary32/nextUp` -/
@[inline] def op234 (x : Single) := ExecFloat.Binary.nextUp x
def timed234 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed234 xs k (mixQuick acc (Digest.quick (op234 xs[k]!)))
def full234 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full234 xs k (Digest.full (op234 xs[k]!) (mixFull h k.toUInt64))
def run234 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/nextUp" xs d timed234 full234 trials reps

/-! ### `binary32/nextDown` -/
@[inline] def op235 (x : Single) := ExecFloat.Binary.nextDown x
def timed235 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed235 xs k (mixQuick acc (Digest.quick (op235 xs[k]!)))
def full235 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full235 xs k (Digest.full (op235 xs[k]!) (mixFull h k.toUInt64))
def run235 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/nextDown" xs d timed235 full235 trials reps

/-! ### `binary32/scale` -/
@[inline] def op236 (x : Single) (n : Int) := ExecFloat.Binary.scale x n .nearest
def timed236 (xs : Array Single) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed236 xs ns k (mixQuick acc (Digest.quick (op236 xs[k]! ns[k]!)))
def full236 (xs : Array Single) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full236 xs ns k (Digest.full (op236 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run236 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ns, dn) := inScale count
  runXI "binary32/scale" xs ns (mixFull dx dn) timed236 full236 trials reps

/-! ### `binary32/logB` -/
@[inline] def op237 (x : Single) := ExecFloat.Binary.logB x
def timed237 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed237 xs k (mixQuick acc (Digest.quick (op237 xs[k]!)))
def full237 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full237 xs k (Digest.full (op237 xs[k]!) (mixFull h k.toUInt64))
def run237 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/logB" xs d timed237 full237 trials reps

/-! ### `binary32/logBInt` -/
@[inline] def op238 (x : Single) := ExecFloat.Binary.logBInt x
def timed238 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed238 xs k (mixQuick acc (Digest.quick (op238 xs[k]!)))
def full238 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full238 xs k (Digest.full (op238 xs[k]!) (mixFull h k.toUInt64))
def run238 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/logBInt" xs d timed238 full238 trials reps

/-! ### `binary32/negate` -/
@[inline] def op239 (x : Single) := -x
def timed239 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed239 xs k (mixQuick acc (Digest.quick (op239 xs[k]!)))
def full239 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full239 xs k (Digest.full (op239 xs[k]!) (mixFull h k.toUInt64))
def run239 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/negate" xs d timed239 full239 trials reps

/-! ### `binary32/abs` -/
@[inline] def op240 (x : Single) := ExecFloat.Binary.abs x
def timed240 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed240 xs k (mixQuick acc (Digest.quick (op240 xs[k]!)))
def full240 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full240 xs k (Digest.full (op240 xs[k]!) (mixFull h k.toUInt64))
def run240 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/abs" xs d timed240 full240 trials reps

/-! ### `binary32/copySign` -/
@[inline] def op241 (x y : Single) := ExecFloat.Binary.copySign x y
def timed241 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed241 xs ys k (mixQuick acc (Digest.quick (op241 xs[k]! ys[k]!)))
def full241 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full241 xs ys k (Digest.full (op241 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run241 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/copySign" xs ys (mixFull dx dy) timed241 full241 trials reps

/-! ### `binary64/nextUp` -/
@[inline] def op321 (x : Double) := ExecFloat.Binary.nextUp x
def timed321 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed321 xs k (mixQuick acc (Digest.quick (op321 xs[k]!)))
def full321 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full321 xs k (Digest.full (op321 xs[k]!) (mixFull h k.toUInt64))
def run321 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/nextUp" xs d timed321 full321 trials reps

/-! ### `binary64/nextDown` -/
@[inline] def op322 (x : Double) := ExecFloat.Binary.nextDown x
def timed322 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed322 xs k (mixQuick acc (Digest.quick (op322 xs[k]!)))
def full322 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full322 xs k (Digest.full (op322 xs[k]!) (mixFull h k.toUInt64))
def run322 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/nextDown" xs d timed322 full322 trials reps

/-! ### `binary64/scale` -/
@[inline] def op323 (x : Double) (n : Int) := ExecFloat.Binary.scale x n .nearest
def timed323 (xs : Array Double) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed323 xs ns k (mixQuick acc (Digest.quick (op323 xs[k]! ns[k]!)))
def full323 (xs : Array Double) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full323 xs ns k (Digest.full (op323 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run323 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ns, dn) := inScale count
  runXI "binary64/scale" xs ns (mixFull dx dn) timed323 full323 trials reps

/-! ### `binary64/logB` -/
@[inline] def op324 (x : Double) := ExecFloat.Binary.logB x
def timed324 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed324 xs k (mixQuick acc (Digest.quick (op324 xs[k]!)))
def full324 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full324 xs k (Digest.full (op324 xs[k]!) (mixFull h k.toUInt64))
def run324 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/logB" xs d timed324 full324 trials reps

/-! ### `binary64/logBInt` -/
@[inline] def op325 (x : Double) := ExecFloat.Binary.logBInt x
def timed325 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed325 xs k (mixQuick acc (Digest.quick (op325 xs[k]!)))
def full325 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full325 xs k (Digest.full (op325 xs[k]!) (mixFull h k.toUInt64))
def run325 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/logBInt" xs d timed325 full325 trials reps

/-! ### `binary64/negate` -/
@[inline] def op326 (x : Double) := -x
def timed326 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed326 xs k (mixQuick acc (Digest.quick (op326 xs[k]!)))
def full326 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full326 xs k (Digest.full (op326 xs[k]!) (mixFull h k.toUInt64))
def run326 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/negate" xs d timed326 full326 trials reps

/-! ### `binary64/abs` -/
@[inline] def op327 (x : Double) := ExecFloat.Binary.abs x
def timed327 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed327 xs k (mixQuick acc (Digest.quick (op327 xs[k]!)))
def full327 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full327 xs k (Digest.full (op327 xs[k]!) (mixFull h k.toUInt64))
def run327 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/abs" xs d timed327 full327 trials reps

/-! ### `binary64/copySign` -/
@[inline] def op328 (x y : Double) := ExecFloat.Binary.copySign x y
def timed328 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed328 xs ys k (mixQuick acc (Digest.quick (op328 xs[k]! ys[k]!)))
def full328 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full328 xs ys k (Digest.full (op328 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run328 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/copySign" xs ys (mixFull dx dy) timed328 full328 trials reps

/-! ### `binary128/nextUp` -/
@[inline] def op408 (x : Quad) := ExecFloat.Binary.nextUp x
def timed408 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed408 xs k (mixQuick acc (Digest.quick (op408 xs[k]!)))
def full408 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full408 xs k (Digest.full (op408 xs[k]!) (mixFull h k.toUInt64))
def run408 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/nextUp" xs d timed408 full408 trials reps

/-! ### `binary128/nextDown` -/
@[inline] def op409 (x : Quad) := ExecFloat.Binary.nextDown x
def timed409 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed409 xs k (mixQuick acc (Digest.quick (op409 xs[k]!)))
def full409 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full409 xs k (Digest.full (op409 xs[k]!) (mixFull h k.toUInt64))
def run409 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/nextDown" xs d timed409 full409 trials reps

/-! ### `binary128/scale` -/
@[inline] def op410 (x : Quad) (n : Int) := ExecFloat.Binary.scale x n .nearest
def timed410 (xs : Array Quad) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed410 xs ns k (mixQuick acc (Digest.quick (op410 xs[k]! ns[k]!)))
def full410 (xs : Array Quad) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full410 xs ns k (Digest.full (op410 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run410 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ns, dn) := inScale count
  runXI "binary128/scale" xs ns (mixFull dx dn) timed410 full410 trials reps

/-! ### `binary128/logB` -/
@[inline] def op411 (x : Quad) := ExecFloat.Binary.logB x
def timed411 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed411 xs k (mixQuick acc (Digest.quick (op411 xs[k]!)))
def full411 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full411 xs k (Digest.full (op411 xs[k]!) (mixFull h k.toUInt64))
def run411 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/logB" xs d timed411 full411 trials reps

/-! ### `binary128/logBInt` -/
@[inline] def op412 (x : Quad) := ExecFloat.Binary.logBInt x
def timed412 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed412 xs k (mixQuick acc (Digest.quick (op412 xs[k]!)))
def full412 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full412 xs k (Digest.full (op412 xs[k]!) (mixFull h k.toUInt64))
def run412 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/logBInt" xs d timed412 full412 trials reps

/-! ### `binary128/negate` -/
@[inline] def op413 (x : Quad) := -x
def timed413 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed413 xs k (mixQuick acc (Digest.quick (op413 xs[k]!)))
def full413 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full413 xs k (Digest.full (op413 xs[k]!) (mixFull h k.toUInt64))
def run413 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/negate" xs d timed413 full413 trials reps

/-! ### `binary128/abs` -/
@[inline] def op414 (x : Quad) := ExecFloat.Binary.abs x
def timed414 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed414 xs k (mixQuick acc (Digest.quick (op414 xs[k]!)))
def full414 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full414 xs k (Digest.full (op414 xs[k]!) (mixFull h k.toUInt64))
def run414 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/abs" xs d timed414 full414 trials reps

/-! ### `binary128/copySign` -/
@[inline] def op415 (x y : Quad) := ExecFloat.Binary.copySign x y
def timed415 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed415 xs ys k (mixQuick acc (Digest.quick (op415 xs[k]! ys[k]!)))
def full415 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full415 xs ys k (Digest.full (op415 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run415 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/copySign" xs ys (mixFull dx dy) timed415 full415 trials reps

/-! ### `binary256/nextUp` -/
@[inline] def op479 (x : Oct) := ExecFloat.Binary.nextUp x
def timed479 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed479 xs k (mixQuick acc (Digest.quick (op479 xs[k]!)))
def full479 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full479 xs k (Digest.full (op479 xs[k]!) (mixFull h k.toUInt64))
def run479 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/nextUp" xs d timed479 full479 trials reps

/-! ### `binary256/scale` -/
@[inline] def op480 (x : Oct) (n : Int) := ExecFloat.Binary.scale x n .nearest
def timed480 (xs : Array Oct) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed480 xs ns k (mixQuick acc (Digest.quick (op480 xs[k]! ns[k]!)))
def full480 (xs : Array Oct) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full480 xs ns k (Digest.full (op480 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run480 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ns, dn) := inScale count
  runXI "binary256/scale" xs ns (mixFull dx dn) timed480 full480 trials reps

/-! ### `binary256/logB` -/
@[inline] def op481 (x : Oct) := ExecFloat.Binary.logB x
def timed481 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed481 xs k (mixQuick acc (Digest.quick (op481 xs[k]!)))
def full481 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full481 xs k (Digest.full (op481 xs[k]!) (mixFull h k.toUInt64))
def run481 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/logB" xs d timed481 full481 trials reps

/-! ### `binary256/negate` -/
@[inline] def op482 (x : Oct) := -x
def timed482 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed482 xs k (mixQuick acc (Digest.quick (op482 xs[k]!)))
def full482 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full482 xs k (Digest.full (op482 xs[k]!) (mixFull h k.toUInt64))
def run482 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/negate" xs d timed482 full482 trials reps

/-! ### `binary256/abs` -/
@[inline] def op483 (x : Oct) := ExecFloat.Binary.abs x
def timed483 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed483 xs k (mixQuick acc (Digest.quick (op483 xs[k]!)))
def full483 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full483 xs k (Digest.full (op483 xs[k]!) (mixFull h k.toUInt64))
def run483 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/abs" xs d timed483 full483 trials reps

/-! ### `posit32/next` -/
@[inline] def op503 (x : P32) := ExecFloat.Posit.next x
def timed503 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed503 xs k (mixQuick acc (Digest.quick (op503 xs[k]!)))
def full503 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full503 xs k (Digest.full (op503 xs[k]!) (mixFull h k.toUInt64))
def run503 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/next" xs d timed503 full503 trials reps

/-! ### `posit32/prior` -/
@[inline] def op504 (x : P32) := ExecFloat.Posit.prior x
def timed504 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed504 xs k (mixQuick acc (Digest.quick (op504 xs[k]!)))
def full504 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full504 xs k (Digest.full (op504 xs[k]!) (mixFull h k.toUInt64))
def run504 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/prior" xs d timed504 full504 trials reps

/-! ### `posit32/negate` -/
@[inline] def op505 (x : P32) := -x
def timed505 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed505 xs k (mixQuick acc (Digest.quick (op505 xs[k]!)))
def full505 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full505 xs k (Digest.full (op505 xs[k]!) (mixFull h k.toUInt64))
def run505 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/negate" xs d timed505 full505 trials reps

/-! ### `posit32/abs` -/
@[inline] def op506 (x : P32) := ExecFloat.Posit.abs x
def timed506 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed506 xs k (mixQuick acc (Digest.quick (op506 xs[k]!)))
def full506 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full506 xs k (Digest.full (op506 xs[k]!) (mixFull h k.toUInt64))
def run506 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/abs" xs d timed506 full506 trials reps

/-! ### `posit32/sign` -/
@[inline] def op507 (x : P32) := ExecFloat.Posit.sign x
def timed507 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed507 xs k (mixQuick acc (Digest.quick (op507 xs[k]!)))
def full507 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full507 xs k (Digest.full (op507 xs[k]!) (mixFull h k.toUInt64))
def run507 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/sign" xs d timed507 full507 trials reps

end FloatLibBenchmarks.Public.TimeOps
