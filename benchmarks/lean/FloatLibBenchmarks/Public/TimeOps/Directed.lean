/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Directed arithmetic timings

Arithmetic loops at each nondefault IEEE rounding direction.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/add[up]` -/
@[inline] def op84 (x y : Half) := ExecFloat.Binary.add x y (mode := .up)
def timed84 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed84 xs ys k (mixQuick acc (Digest.quick (op84 xs[k]! ys[k]!)))
def full84 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full84 xs ys k (Digest.full (op84 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run84 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/add[up]" xs ys (mixFull dx dy) timed84 full84 trials reps

/-! ### `binary16/mul[up]` -/
@[inline] def op85 (x y : Half) := ExecFloat.Binary.mul x y (mode := .up)
def timed85 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed85 xs ys k (mixQuick acc (Digest.quick (op85 xs[k]! ys[k]!)))
def full85 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full85 xs ys k (Digest.full (op85 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run85 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/mul[up]" xs ys (mixFull dx dy) timed85 full85 trials reps

/-! ### `binary16/div[up]` -/
@[inline] def op86 (x y : Half) := ExecFloat.Binary.div x y (mode := .up)
def timed86 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed86 xs ys k (mixQuick acc (Digest.quick (op86 xs[k]! ys[k]!)))
def full86 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full86 xs ys k (Digest.full (op86 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run86 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/div[up]" xs ys (mixFull dx dy) timed86 full86 trials reps

/-! ### `binary16/sqrt[up]` -/
@[inline] def op87 (x : Half) := ExecFloat.Binary.sqrt x (mode := .up)
def timed87 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed87 xs k (mixQuick acc (Digest.quick (op87 xs[k]!)))
def full87 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full87 xs k (Digest.full (op87 xs[k]!) (mixFull h k.toUInt64))
def run87 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/sqrt[up]" xs d timed87 full87 trials reps

/-! ### `binary16/fma[up]` -/
@[inline] def op88 (x y z : Half) := ExecFloat.Binary.fma x y z (mode := .up)
def timed88 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed88 xs ys zs k (mixQuick acc (Digest.quick (op88 xs[k]! ys[k]! zs[k]!)))
def full88 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full88 xs ys zs k (Digest.full (op88 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run88 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  let (zs, dz) := inHalf seedZ count
  runT "binary16/fma[up]" xs ys zs (mixFull (mixFull dx dy) dz) timed88 full88 trials reps

/-! ### `binary16/add[down]` -/
@[inline] def op89 (x y : Half) := ExecFloat.Binary.add x y (mode := .down)
def timed89 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed89 xs ys k (mixQuick acc (Digest.quick (op89 xs[k]! ys[k]!)))
def full89 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full89 xs ys k (Digest.full (op89 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run89 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/add[down]" xs ys (mixFull dx dy) timed89 full89 trials reps

/-! ### `binary16/mul[down]` -/
@[inline] def op90 (x y : Half) := ExecFloat.Binary.mul x y (mode := .down)
def timed90 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed90 xs ys k (mixQuick acc (Digest.quick (op90 xs[k]! ys[k]!)))
def full90 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full90 xs ys k (Digest.full (op90 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run90 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/mul[down]" xs ys (mixFull dx dy) timed90 full90 trials reps

/-! ### `binary16/div[down]` -/
@[inline] def op91 (x y : Half) := ExecFloat.Binary.div x y (mode := .down)
def timed91 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed91 xs ys k (mixQuick acc (Digest.quick (op91 xs[k]! ys[k]!)))
def full91 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full91 xs ys k (Digest.full (op91 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run91 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/div[down]" xs ys (mixFull dx dy) timed91 full91 trials reps

/-! ### `binary16/sqrt[down]` -/
@[inline] def op92 (x : Half) := ExecFloat.Binary.sqrt x (mode := .down)
def timed92 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed92 xs k (mixQuick acc (Digest.quick (op92 xs[k]!)))
def full92 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full92 xs k (Digest.full (op92 xs[k]!) (mixFull h k.toUInt64))
def run92 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/sqrt[down]" xs d timed92 full92 trials reps

/-! ### `binary16/fma[down]` -/
@[inline] def op93 (x y z : Half) := ExecFloat.Binary.fma x y z (mode := .down)
def timed93 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed93 xs ys zs k (mixQuick acc (Digest.quick (op93 xs[k]! ys[k]! zs[k]!)))
def full93 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full93 xs ys zs k (Digest.full (op93 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run93 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  let (zs, dz) := inHalf seedZ count
  runT "binary16/fma[down]" xs ys zs (mixFull (mixFull dx dy) dz) timed93 full93 trials reps

/-! ### `binary16/add[towardZero]` -/
@[inline] def op94 (x y : Half) := ExecFloat.Binary.add x y (mode := .towardZero)
def timed94 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed94 xs ys k (mixQuick acc (Digest.quick (op94 xs[k]! ys[k]!)))
def full94 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full94 xs ys k (Digest.full (op94 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run94 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/add[towardZero]" xs ys (mixFull dx dy) timed94 full94 trials reps

/-! ### `binary16/mul[towardZero]` -/
@[inline] def op95 (x y : Half) := ExecFloat.Binary.mul x y (mode := .towardZero)
def timed95 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed95 xs ys k (mixQuick acc (Digest.quick (op95 xs[k]! ys[k]!)))
def full95 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full95 xs ys k (Digest.full (op95 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run95 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/mul[towardZero]" xs ys (mixFull dx dy) timed95 full95 trials reps

/-! ### `binary16/div[towardZero]` -/
@[inline] def op96 (x y : Half) := ExecFloat.Binary.div x y (mode := .towardZero)
def timed96 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed96 xs ys k (mixQuick acc (Digest.quick (op96 xs[k]! ys[k]!)))
def full96 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full96 xs ys k (Digest.full (op96 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run96 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/div[towardZero]" xs ys (mixFull dx dy) timed96 full96 trials reps

/-! ### `binary16/sqrt[towardZero]` -/
@[inline] def op97 (x : Half) := ExecFloat.Binary.sqrt x (mode := .towardZero)
def timed97 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed97 xs k (mixQuick acc (Digest.quick (op97 xs[k]!)))
def full97 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full97 xs k (Digest.full (op97 xs[k]!) (mixFull h k.toUInt64))
def run97 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/sqrt[towardZero]" xs d timed97 full97 trials reps

/-! ### `binary16/fma[towardZero]` -/
@[inline] def op98 (x y z : Half) := ExecFloat.Binary.fma x y z (mode := .towardZero)
def timed98 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed98 xs ys zs k (mixQuick acc (Digest.quick (op98 xs[k]! ys[k]! zs[k]!)))
def full98 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full98 xs ys zs k (Digest.full (op98 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run98 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  let (zs, dz) := inHalf seedZ count
  runT "binary16/fma[towardZero]" xs ys zs (mixFull (mixFull dx dy) dz) timed98 full98 trials reps

/-! ### `bfloat16/add[up]` -/
@[inline] def op171 (x y : Brain) := ExecFloat.Binary.add x y (mode := .up)
def timed171 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed171 xs ys k (mixQuick acc (Digest.quick (op171 xs[k]! ys[k]!)))
def full171 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full171 xs ys k (Digest.full (op171 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run171 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/add[up]" xs ys (mixFull dx dy) timed171 full171 trials reps

/-! ### `bfloat16/mul[up]` -/
@[inline] def op172 (x y : Brain) := ExecFloat.Binary.mul x y (mode := .up)
def timed172 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed172 xs ys k (mixQuick acc (Digest.quick (op172 xs[k]! ys[k]!)))
def full172 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full172 xs ys k (Digest.full (op172 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run172 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/mul[up]" xs ys (mixFull dx dy) timed172 full172 trials reps

/-! ### `bfloat16/div[up]` -/
@[inline] def op173 (x y : Brain) := ExecFloat.Binary.div x y (mode := .up)
def timed173 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed173 xs ys k (mixQuick acc (Digest.quick (op173 xs[k]! ys[k]!)))
def full173 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full173 xs ys k (Digest.full (op173 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run173 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/div[up]" xs ys (mixFull dx dy) timed173 full173 trials reps

/-! ### `bfloat16/sqrt[up]` -/
@[inline] def op174 (x : Brain) := ExecFloat.Binary.sqrt x (mode := .up)
def timed174 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed174 xs k (mixQuick acc (Digest.quick (op174 xs[k]!)))
def full174 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full174 xs k (Digest.full (op174 xs[k]!) (mixFull h k.toUInt64))
def run174 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/sqrt[up]" xs d timed174 full174 trials reps

/-! ### `bfloat16/fma[up]` -/
@[inline] def op175 (x y z : Brain) := ExecFloat.Binary.fma x y z (mode := .up)
def timed175 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed175 xs ys zs k (mixQuick acc (Digest.quick (op175 xs[k]! ys[k]! zs[k]!)))
def full175 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full175 xs ys zs k (Digest.full (op175 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run175 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  let (zs, dz) := inBrain seedZ count
  runT "bfloat16/fma[up]" xs ys zs (mixFull (mixFull dx dy) dz) timed175 full175 trials reps

/-! ### `bfloat16/add[down]` -/
@[inline] def op176 (x y : Brain) := ExecFloat.Binary.add x y (mode := .down)
def timed176 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed176 xs ys k (mixQuick acc (Digest.quick (op176 xs[k]! ys[k]!)))
def full176 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full176 xs ys k (Digest.full (op176 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run176 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/add[down]" xs ys (mixFull dx dy) timed176 full176 trials reps

/-! ### `bfloat16/mul[down]` -/
@[inline] def op177 (x y : Brain) := ExecFloat.Binary.mul x y (mode := .down)
def timed177 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed177 xs ys k (mixQuick acc (Digest.quick (op177 xs[k]! ys[k]!)))
def full177 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full177 xs ys k (Digest.full (op177 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run177 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/mul[down]" xs ys (mixFull dx dy) timed177 full177 trials reps

/-! ### `bfloat16/div[down]` -/
@[inline] def op178 (x y : Brain) := ExecFloat.Binary.div x y (mode := .down)
def timed178 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed178 xs ys k (mixQuick acc (Digest.quick (op178 xs[k]! ys[k]!)))
def full178 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full178 xs ys k (Digest.full (op178 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run178 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/div[down]" xs ys (mixFull dx dy) timed178 full178 trials reps

/-! ### `bfloat16/sqrt[down]` -/
@[inline] def op179 (x : Brain) := ExecFloat.Binary.sqrt x (mode := .down)
def timed179 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed179 xs k (mixQuick acc (Digest.quick (op179 xs[k]!)))
def full179 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full179 xs k (Digest.full (op179 xs[k]!) (mixFull h k.toUInt64))
def run179 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/sqrt[down]" xs d timed179 full179 trials reps

/-! ### `bfloat16/fma[down]` -/
@[inline] def op180 (x y z : Brain) := ExecFloat.Binary.fma x y z (mode := .down)
def timed180 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed180 xs ys zs k (mixQuick acc (Digest.quick (op180 xs[k]! ys[k]! zs[k]!)))
def full180 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full180 xs ys zs k (Digest.full (op180 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run180 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  let (zs, dz) := inBrain seedZ count
  runT "bfloat16/fma[down]" xs ys zs (mixFull (mixFull dx dy) dz) timed180 full180 trials reps

/-! ### `bfloat16/add[towardZero]` -/
@[inline] def op181 (x y : Brain) := ExecFloat.Binary.add x y (mode := .towardZero)
def timed181 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed181 xs ys k (mixQuick acc (Digest.quick (op181 xs[k]! ys[k]!)))
def full181 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full181 xs ys k (Digest.full (op181 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run181 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/add[towardZero]" xs ys (mixFull dx dy) timed181 full181 trials reps

/-! ### `bfloat16/mul[towardZero]` -/
@[inline] def op182 (x y : Brain) := ExecFloat.Binary.mul x y (mode := .towardZero)
def timed182 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed182 xs ys k (mixQuick acc (Digest.quick (op182 xs[k]! ys[k]!)))
def full182 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full182 xs ys k (Digest.full (op182 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run182 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/mul[towardZero]" xs ys (mixFull dx dy) timed182 full182 trials reps

/-! ### `bfloat16/div[towardZero]` -/
@[inline] def op183 (x y : Brain) := ExecFloat.Binary.div x y (mode := .towardZero)
def timed183 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed183 xs ys k (mixQuick acc (Digest.quick (op183 xs[k]! ys[k]!)))
def full183 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full183 xs ys k (Digest.full (op183 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run183 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/div[towardZero]" xs ys (mixFull dx dy) timed183 full183 trials reps

/-! ### `bfloat16/sqrt[towardZero]` -/
@[inline] def op184 (x : Brain) := ExecFloat.Binary.sqrt x (mode := .towardZero)
def timed184 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed184 xs k (mixQuick acc (Digest.quick (op184 xs[k]!)))
def full184 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full184 xs k (Digest.full (op184 xs[k]!) (mixFull h k.toUInt64))
def run184 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/sqrt[towardZero]" xs d timed184 full184 trials reps

/-! ### `bfloat16/fma[towardZero]` -/
@[inline] def op185 (x y z : Brain) := ExecFloat.Binary.fma x y z (mode := .towardZero)
def timed185 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed185 xs ys zs k (mixQuick acc (Digest.quick (op185 xs[k]! ys[k]! zs[k]!)))
def full185 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full185 xs ys zs k (Digest.full (op185 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run185 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  let (zs, dz) := inBrain seedZ count
  runT "bfloat16/fma[towardZero]" xs ys zs (mixFull (mixFull dx dy) dz) timed185 full185 trials reps

/-! ### `binary32/add[up]` -/
@[inline] def op258 (x y : Single) := ExecFloat.Binary.add x y (mode := .up)
def timed258 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed258 xs ys k (mixQuick acc (Digest.quick (op258 xs[k]! ys[k]!)))
def full258 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full258 xs ys k (Digest.full (op258 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run258 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/add[up]" xs ys (mixFull dx dy) timed258 full258 trials reps

/-! ### `binary32/mul[up]` -/
@[inline] def op259 (x y : Single) := ExecFloat.Binary.mul x y (mode := .up)
def timed259 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed259 xs ys k (mixQuick acc (Digest.quick (op259 xs[k]! ys[k]!)))
def full259 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full259 xs ys k (Digest.full (op259 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run259 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/mul[up]" xs ys (mixFull dx dy) timed259 full259 trials reps

/-! ### `binary32/div[up]` -/
@[inline] def op260 (x y : Single) := ExecFloat.Binary.div x y (mode := .up)
def timed260 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed260 xs ys k (mixQuick acc (Digest.quick (op260 xs[k]! ys[k]!)))
def full260 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full260 xs ys k (Digest.full (op260 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run260 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/div[up]" xs ys (mixFull dx dy) timed260 full260 trials reps

/-! ### `binary32/sqrt[up]` -/
@[inline] def op261 (x : Single) := ExecFloat.Binary.sqrt x (mode := .up)
def timed261 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed261 xs k (mixQuick acc (Digest.quick (op261 xs[k]!)))
def full261 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full261 xs k (Digest.full (op261 xs[k]!) (mixFull h k.toUInt64))
def run261 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/sqrt[up]" xs d timed261 full261 trials reps

/-! ### `binary32/fma[up]` -/
@[inline] def op262 (x y z : Single) := ExecFloat.Binary.fma x y z (mode := .up)
def timed262 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed262 xs ys zs k (mixQuick acc (Digest.quick (op262 xs[k]! ys[k]! zs[k]!)))
def full262 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full262 xs ys zs k (Digest.full (op262 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run262 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  let (zs, dz) := inSingle seedZ count
  runT "binary32/fma[up]" xs ys zs (mixFull (mixFull dx dy) dz) timed262 full262 trials reps

/-! ### `binary32/add[down]` -/
@[inline] def op263 (x y : Single) := ExecFloat.Binary.add x y (mode := .down)
def timed263 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed263 xs ys k (mixQuick acc (Digest.quick (op263 xs[k]! ys[k]!)))
def full263 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full263 xs ys k (Digest.full (op263 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run263 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/add[down]" xs ys (mixFull dx dy) timed263 full263 trials reps

/-! ### `binary32/mul[down]` -/
@[inline] def op264 (x y : Single) := ExecFloat.Binary.mul x y (mode := .down)
def timed264 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed264 xs ys k (mixQuick acc (Digest.quick (op264 xs[k]! ys[k]!)))
def full264 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full264 xs ys k (Digest.full (op264 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run264 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/mul[down]" xs ys (mixFull dx dy) timed264 full264 trials reps

/-! ### `binary32/div[down]` -/
@[inline] def op265 (x y : Single) := ExecFloat.Binary.div x y (mode := .down)
def timed265 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed265 xs ys k (mixQuick acc (Digest.quick (op265 xs[k]! ys[k]!)))
def full265 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full265 xs ys k (Digest.full (op265 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run265 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/div[down]" xs ys (mixFull dx dy) timed265 full265 trials reps

/-! ### `binary32/sqrt[down]` -/
@[inline] def op266 (x : Single) := ExecFloat.Binary.sqrt x (mode := .down)
def timed266 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed266 xs k (mixQuick acc (Digest.quick (op266 xs[k]!)))
def full266 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full266 xs k (Digest.full (op266 xs[k]!) (mixFull h k.toUInt64))
def run266 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/sqrt[down]" xs d timed266 full266 trials reps

/-! ### `binary32/fma[down]` -/
@[inline] def op267 (x y z : Single) := ExecFloat.Binary.fma x y z (mode := .down)
def timed267 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed267 xs ys zs k (mixQuick acc (Digest.quick (op267 xs[k]! ys[k]! zs[k]!)))
def full267 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full267 xs ys zs k (Digest.full (op267 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run267 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  let (zs, dz) := inSingle seedZ count
  runT "binary32/fma[down]" xs ys zs (mixFull (mixFull dx dy) dz) timed267 full267 trials reps

/-! ### `binary32/add[towardZero]` -/
@[inline] def op268 (x y : Single) := ExecFloat.Binary.add x y (mode := .towardZero)
def timed268 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed268 xs ys k (mixQuick acc (Digest.quick (op268 xs[k]! ys[k]!)))
def full268 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full268 xs ys k (Digest.full (op268 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run268 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/add[towardZero]" xs ys (mixFull dx dy) timed268 full268 trials reps

/-! ### `binary32/mul[towardZero]` -/
@[inline] def op269 (x y : Single) := ExecFloat.Binary.mul x y (mode := .towardZero)
def timed269 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed269 xs ys k (mixQuick acc (Digest.quick (op269 xs[k]! ys[k]!)))
def full269 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full269 xs ys k (Digest.full (op269 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run269 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/mul[towardZero]" xs ys (mixFull dx dy) timed269 full269 trials reps

/-! ### `binary32/div[towardZero]` -/
@[inline] def op270 (x y : Single) := ExecFloat.Binary.div x y (mode := .towardZero)
def timed270 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed270 xs ys k (mixQuick acc (Digest.quick (op270 xs[k]! ys[k]!)))
def full270 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full270 xs ys k (Digest.full (op270 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run270 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/div[towardZero]" xs ys (mixFull dx dy) timed270 full270 trials reps

/-! ### `binary32/sqrt[towardZero]` -/
@[inline] def op271 (x : Single) := ExecFloat.Binary.sqrt x (mode := .towardZero)
def timed271 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed271 xs k (mixQuick acc (Digest.quick (op271 xs[k]!)))
def full271 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full271 xs k (Digest.full (op271 xs[k]!) (mixFull h k.toUInt64))
def run271 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/sqrt[towardZero]" xs d timed271 full271 trials reps

/-! ### `binary32/fma[towardZero]` -/
@[inline] def op272 (x y z : Single) := ExecFloat.Binary.fma x y z (mode := .towardZero)
def timed272 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed272 xs ys zs k (mixQuick acc (Digest.quick (op272 xs[k]! ys[k]! zs[k]!)))
def full272 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full272 xs ys zs k (Digest.full (op272 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run272 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  let (zs, dz) := inSingle seedZ count
  runT "binary32/fma[towardZero]" xs ys zs (mixFull (mixFull dx dy) dz) timed272 full272 trials reps

/-! ### `binary64/add[up]` -/
@[inline] def op345 (x y : Double) := ExecFloat.Binary.add x y (mode := .up)
def timed345 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed345 xs ys k (mixQuick acc (Digest.quick (op345 xs[k]! ys[k]!)))
def full345 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full345 xs ys k (Digest.full (op345 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run345 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/add[up]" xs ys (mixFull dx dy) timed345 full345 trials reps

/-! ### `binary64/mul[up]` -/
@[inline] def op346 (x y : Double) := ExecFloat.Binary.mul x y (mode := .up)
def timed346 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed346 xs ys k (mixQuick acc (Digest.quick (op346 xs[k]! ys[k]!)))
def full346 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full346 xs ys k (Digest.full (op346 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run346 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/mul[up]" xs ys (mixFull dx dy) timed346 full346 trials reps

/-! ### `binary64/div[up]` -/
@[inline] def op347 (x y : Double) := ExecFloat.Binary.div x y (mode := .up)
def timed347 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed347 xs ys k (mixQuick acc (Digest.quick (op347 xs[k]! ys[k]!)))
def full347 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full347 xs ys k (Digest.full (op347 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run347 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/div[up]" xs ys (mixFull dx dy) timed347 full347 trials reps

/-! ### `binary64/sqrt[up]` -/
@[inline] def op348 (x : Double) := ExecFloat.Binary.sqrt x (mode := .up)
def timed348 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed348 xs k (mixQuick acc (Digest.quick (op348 xs[k]!)))
def full348 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full348 xs k (Digest.full (op348 xs[k]!) (mixFull h k.toUInt64))
def run348 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/sqrt[up]" xs d timed348 full348 trials reps

/-! ### `binary64/fma[up]` -/
@[inline] def op349 (x y z : Double) := ExecFloat.Binary.fma x y z (mode := .up)
def timed349 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed349 xs ys zs k (mixQuick acc (Digest.quick (op349 xs[k]! ys[k]! zs[k]!)))
def full349 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full349 xs ys zs k (Digest.full (op349 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run349 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  let (zs, dz) := inDouble seedZ count
  runT "binary64/fma[up]" xs ys zs (mixFull (mixFull dx dy) dz) timed349 full349 trials reps

/-! ### `binary64/add[down]` -/
@[inline] def op350 (x y : Double) := ExecFloat.Binary.add x y (mode := .down)
def timed350 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed350 xs ys k (mixQuick acc (Digest.quick (op350 xs[k]! ys[k]!)))
def full350 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full350 xs ys k (Digest.full (op350 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run350 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/add[down]" xs ys (mixFull dx dy) timed350 full350 trials reps

/-! ### `binary64/mul[down]` -/
@[inline] def op351 (x y : Double) := ExecFloat.Binary.mul x y (mode := .down)
def timed351 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed351 xs ys k (mixQuick acc (Digest.quick (op351 xs[k]! ys[k]!)))
def full351 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full351 xs ys k (Digest.full (op351 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run351 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/mul[down]" xs ys (mixFull dx dy) timed351 full351 trials reps

/-! ### `binary64/div[down]` -/
@[inline] def op352 (x y : Double) := ExecFloat.Binary.div x y (mode := .down)
def timed352 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed352 xs ys k (mixQuick acc (Digest.quick (op352 xs[k]! ys[k]!)))
def full352 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full352 xs ys k (Digest.full (op352 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run352 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/div[down]" xs ys (mixFull dx dy) timed352 full352 trials reps

/-! ### `binary64/sqrt[down]` -/
@[inline] def op353 (x : Double) := ExecFloat.Binary.sqrt x (mode := .down)
def timed353 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed353 xs k (mixQuick acc (Digest.quick (op353 xs[k]!)))
def full353 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full353 xs k (Digest.full (op353 xs[k]!) (mixFull h k.toUInt64))
def run353 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/sqrt[down]" xs d timed353 full353 trials reps

/-! ### `binary64/fma[down]` -/
@[inline] def op354 (x y z : Double) := ExecFloat.Binary.fma x y z (mode := .down)
def timed354 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed354 xs ys zs k (mixQuick acc (Digest.quick (op354 xs[k]! ys[k]! zs[k]!)))
def full354 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full354 xs ys zs k (Digest.full (op354 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run354 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  let (zs, dz) := inDouble seedZ count
  runT "binary64/fma[down]" xs ys zs (mixFull (mixFull dx dy) dz) timed354 full354 trials reps

/-! ### `binary64/add[towardZero]` -/
@[inline] def op355 (x y : Double) := ExecFloat.Binary.add x y (mode := .towardZero)
def timed355 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed355 xs ys k (mixQuick acc (Digest.quick (op355 xs[k]! ys[k]!)))
def full355 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full355 xs ys k (Digest.full (op355 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run355 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/add[towardZero]" xs ys (mixFull dx dy) timed355 full355 trials reps

/-! ### `binary64/mul[towardZero]` -/
@[inline] def op356 (x y : Double) := ExecFloat.Binary.mul x y (mode := .towardZero)
def timed356 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed356 xs ys k (mixQuick acc (Digest.quick (op356 xs[k]! ys[k]!)))
def full356 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full356 xs ys k (Digest.full (op356 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run356 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/mul[towardZero]" xs ys (mixFull dx dy) timed356 full356 trials reps

/-! ### `binary64/div[towardZero]` -/
@[inline] def op357 (x y : Double) := ExecFloat.Binary.div x y (mode := .towardZero)
def timed357 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed357 xs ys k (mixQuick acc (Digest.quick (op357 xs[k]! ys[k]!)))
def full357 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full357 xs ys k (Digest.full (op357 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run357 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/div[towardZero]" xs ys (mixFull dx dy) timed357 full357 trials reps

/-! ### `binary64/sqrt[towardZero]` -/
@[inline] def op358 (x : Double) := ExecFloat.Binary.sqrt x (mode := .towardZero)
def timed358 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed358 xs k (mixQuick acc (Digest.quick (op358 xs[k]!)))
def full358 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full358 xs k (Digest.full (op358 xs[k]!) (mixFull h k.toUInt64))
def run358 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/sqrt[towardZero]" xs d timed358 full358 trials reps

/-! ### `binary64/fma[towardZero]` -/
@[inline] def op359 (x y z : Double) := ExecFloat.Binary.fma x y z (mode := .towardZero)
def timed359 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed359 xs ys zs k (mixQuick acc (Digest.quick (op359 xs[k]! ys[k]! zs[k]!)))
def full359 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full359 xs ys zs k (Digest.full (op359 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run359 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  let (zs, dz) := inDouble seedZ count
  runT "binary64/fma[towardZero]" xs ys zs (mixFull (mixFull dx dy) dz) timed359 full359 trials reps

/-! ### `binary128/add[up]` -/
@[inline] def op432 (x y : Quad) := ExecFloat.Binary.add x y (mode := .up)
def timed432 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed432 xs ys k (mixQuick acc (Digest.quick (op432 xs[k]! ys[k]!)))
def full432 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full432 xs ys k (Digest.full (op432 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run432 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/add[up]" xs ys (mixFull dx dy) timed432 full432 trials reps

/-! ### `binary128/mul[up]` -/
@[inline] def op433 (x y : Quad) := ExecFloat.Binary.mul x y (mode := .up)
def timed433 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed433 xs ys k (mixQuick acc (Digest.quick (op433 xs[k]! ys[k]!)))
def full433 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full433 xs ys k (Digest.full (op433 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run433 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/mul[up]" xs ys (mixFull dx dy) timed433 full433 trials reps

/-! ### `binary128/div[up]` -/
@[inline] def op434 (x y : Quad) := ExecFloat.Binary.div x y (mode := .up)
def timed434 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed434 xs ys k (mixQuick acc (Digest.quick (op434 xs[k]! ys[k]!)))
def full434 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full434 xs ys k (Digest.full (op434 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run434 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/div[up]" xs ys (mixFull dx dy) timed434 full434 trials reps

/-! ### `binary128/sqrt[up]` -/
@[inline] def op435 (x : Quad) := ExecFloat.Binary.sqrt x (mode := .up)
def timed435 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed435 xs k (mixQuick acc (Digest.quick (op435 xs[k]!)))
def full435 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full435 xs k (Digest.full (op435 xs[k]!) (mixFull h k.toUInt64))
def run435 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/sqrt[up]" xs d timed435 full435 trials reps

/-! ### `binary128/fma[up]` -/
@[inline] def op436 (x y z : Quad) := ExecFloat.Binary.fma x y z (mode := .up)
def timed436 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed436 xs ys zs k (mixQuick acc (Digest.quick (op436 xs[k]! ys[k]! zs[k]!)))
def full436 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full436 xs ys zs k (Digest.full (op436 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run436 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  let (zs, dz) := inQuad seedZ count
  runT "binary128/fma[up]" xs ys zs (mixFull (mixFull dx dy) dz) timed436 full436 trials reps

/-! ### `binary128/add[down]` -/
@[inline] def op437 (x y : Quad) := ExecFloat.Binary.add x y (mode := .down)
def timed437 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed437 xs ys k (mixQuick acc (Digest.quick (op437 xs[k]! ys[k]!)))
def full437 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full437 xs ys k (Digest.full (op437 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run437 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/add[down]" xs ys (mixFull dx dy) timed437 full437 trials reps

/-! ### `binary128/mul[down]` -/
@[inline] def op438 (x y : Quad) := ExecFloat.Binary.mul x y (mode := .down)
def timed438 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed438 xs ys k (mixQuick acc (Digest.quick (op438 xs[k]! ys[k]!)))
def full438 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full438 xs ys k (Digest.full (op438 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run438 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/mul[down]" xs ys (mixFull dx dy) timed438 full438 trials reps

/-! ### `binary128/div[down]` -/
@[inline] def op439 (x y : Quad) := ExecFloat.Binary.div x y (mode := .down)
def timed439 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed439 xs ys k (mixQuick acc (Digest.quick (op439 xs[k]! ys[k]!)))
def full439 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full439 xs ys k (Digest.full (op439 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run439 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/div[down]" xs ys (mixFull dx dy) timed439 full439 trials reps

/-! ### `binary128/sqrt[down]` -/
@[inline] def op440 (x : Quad) := ExecFloat.Binary.sqrt x (mode := .down)
def timed440 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed440 xs k (mixQuick acc (Digest.quick (op440 xs[k]!)))
def full440 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full440 xs k (Digest.full (op440 xs[k]!) (mixFull h k.toUInt64))
def run440 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/sqrt[down]" xs d timed440 full440 trials reps

/-! ### `binary128/fma[down]` -/
@[inline] def op441 (x y z : Quad) := ExecFloat.Binary.fma x y z (mode := .down)
def timed441 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed441 xs ys zs k (mixQuick acc (Digest.quick (op441 xs[k]! ys[k]! zs[k]!)))
def full441 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full441 xs ys zs k (Digest.full (op441 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run441 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  let (zs, dz) := inQuad seedZ count
  runT "binary128/fma[down]" xs ys zs (mixFull (mixFull dx dy) dz) timed441 full441 trials reps

/-! ### `binary128/add[towardZero]` -/
@[inline] def op442 (x y : Quad) := ExecFloat.Binary.add x y (mode := .towardZero)
def timed442 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed442 xs ys k (mixQuick acc (Digest.quick (op442 xs[k]! ys[k]!)))
def full442 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full442 xs ys k (Digest.full (op442 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run442 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/add[towardZero]" xs ys (mixFull dx dy) timed442 full442 trials reps

/-! ### `binary128/mul[towardZero]` -/
@[inline] def op443 (x y : Quad) := ExecFloat.Binary.mul x y (mode := .towardZero)
def timed443 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed443 xs ys k (mixQuick acc (Digest.quick (op443 xs[k]! ys[k]!)))
def full443 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full443 xs ys k (Digest.full (op443 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run443 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/mul[towardZero]" xs ys (mixFull dx dy) timed443 full443 trials reps

/-! ### `binary128/div[towardZero]` -/
@[inline] def op444 (x y : Quad) := ExecFloat.Binary.div x y (mode := .towardZero)
def timed444 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed444 xs ys k (mixQuick acc (Digest.quick (op444 xs[k]! ys[k]!)))
def full444 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full444 xs ys k (Digest.full (op444 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run444 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/div[towardZero]" xs ys (mixFull dx dy) timed444 full444 trials reps

/-! ### `binary128/sqrt[towardZero]` -/
@[inline] def op445 (x : Quad) := ExecFloat.Binary.sqrt x (mode := .towardZero)
def timed445 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed445 xs k (mixQuick acc (Digest.quick (op445 xs[k]!)))
def full445 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full445 xs k (Digest.full (op445 xs[k]!) (mixFull h k.toUInt64))
def run445 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/sqrt[towardZero]" xs d timed445 full445 trials reps

/-! ### `binary128/fma[towardZero]` -/
@[inline] def op446 (x y z : Quad) := ExecFloat.Binary.fma x y z (mode := .towardZero)
def timed446 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed446 xs ys zs k (mixQuick acc (Digest.quick (op446 xs[k]! ys[k]! zs[k]!)))
def full446 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full446 xs ys zs k (Digest.full (op446 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run446 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  let (zs, dz) := inQuad seedZ count
  runT "binary128/fma[towardZero]" xs ys zs (mixFull (mixFull dx dy) dz) timed446 full446 trials
    reps

/-! ### `binary256/add[up]` -/
@[inline] def op488 (x y : Oct) := ExecFloat.Binary.add x y (mode := .up)
def timed488 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed488 xs ys k (mixQuick acc (Digest.quick (op488 xs[k]! ys[k]!)))
def full488 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full488 xs ys k (Digest.full (op488 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run488 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/add[up]" xs ys (mixFull dx dy) timed488 full488 trials reps

/-! ### `binary256/mul[up]` -/
@[inline] def op489 (x y : Oct) := ExecFloat.Binary.mul x y (mode := .up)
def timed489 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed489 xs ys k (mixQuick acc (Digest.quick (op489 xs[k]! ys[k]!)))
def full489 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full489 xs ys k (Digest.full (op489 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run489 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/mul[up]" xs ys (mixFull dx dy) timed489 full489 trials reps

/-! ### `binary256/div[up]` -/
@[inline] def op490 (x y : Oct) := ExecFloat.Binary.div x y (mode := .up)
def timed490 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed490 xs ys k (mixQuick acc (Digest.quick (op490 xs[k]! ys[k]!)))
def full490 (xs ys : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full490 xs ys k (Digest.full (op490 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run490 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  runB "binary256/div[up]" xs ys (mixFull dx dy) timed490 full490 trials reps

/-! ### `binary256/sqrt[up]` -/
@[inline] def op491 (x : Oct) := ExecFloat.Binary.sqrt x (mode := .up)
def timed491 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed491 xs k (mixQuick acc (Digest.quick (op491 xs[k]!)))
def full491 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full491 xs k (Digest.full (op491 xs[k]!) (mixFull h k.toUInt64))
def run491 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/sqrt[up]" xs d timed491 full491 trials reps

/-! ### `binary256/fma[up]` -/
@[inline] def op492 (x y z : Oct) := ExecFloat.Binary.fma x y z (mode := .up)
def timed492 (xs ys zs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed492 xs ys zs k (mixQuick acc (Digest.quick (op492 xs[k]! ys[k]! zs[k]!)))
def full492 (xs ys zs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full492 xs ys zs k (Digest.full (op492 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run492 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inOct seedX count
  let (ys, dy) := inOct seedY count
  let (zs, dz) := inOct seedZ count
  runT "binary256/fma[up]" xs ys zs (mixFull (mixFull dx dy) dz) timed492 full492 trials reps

end FloatLibBenchmarks.Public.TimeOps
