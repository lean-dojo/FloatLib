/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Conversion timings

Monomorphic timing cells for casts between formats and integer conversion.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary64->binary32/cast` -/
@[inline] def op0 (x : Double) := ExecFloat.cast (target := Single) x
def timed0 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed0 xs k (mixQuick acc (Digest.quick (op0 xs[k]!)))
def full0 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full0 xs k (Digest.full (op0 xs[k]!) (mixFull h k.toUInt64))
def run0 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary32/cast" xs d timed0 full0 trials reps

/-! ### `binary64->binary32/Model.cast` -/
@[inline] def op1 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Single)
def timed1 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed1 xs k (mixQuick acc (Digest.quick (op1 xs[k]!)))
def full1 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full1 xs k (Digest.full (op1 xs[k]!) (mixFull h k.toUInt64))
def run1 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary32/Model.cast" xs d timed1 full1 trials reps

/-! ### `binary32->binary64/cast` -/
@[inline] def op2 (x : Single) := ExecFloat.cast (target := Double) x
def timed2 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed2 xs k (mixQuick acc (Digest.quick (op2 xs[k]!)))
def full2 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full2 xs k (Digest.full (op2 xs[k]!) (mixFull h k.toUInt64))
def run2 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32->binary64/cast" xs d timed2 full2 trials reps

/-! ### `binary32->binary64/Model.cast` -/
@[inline] def op3 (x : Single) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Double)
def timed3 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed3 xs k (mixQuick acc (Digest.quick (op3 xs[k]!)))
def full3 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full3 xs k (Digest.full (op3 xs[k]!) (mixFull h k.toUInt64))
def run3 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32->binary64/Model.cast" xs d timed3 full3 trials reps

/-! ### `binary64->binary16/cast` -/
@[inline] def op4 (x : Double) := ExecFloat.cast (target := Half) x
def timed4 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed4 xs k (mixQuick acc (Digest.quick (op4 xs[k]!)))
def full4 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full4 xs k (Digest.full (op4 xs[k]!) (mixFull h k.toUInt64))
def run4 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary16/cast" xs d timed4 full4 trials reps

/-! ### `binary64->binary16/Model.cast` -/
@[inline] def op5 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Half)
def timed5 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed5 xs k (mixQuick acc (Digest.quick (op5 xs[k]!)))
def full5 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full5 xs k (Digest.full (op5 xs[k]!) (mixFull h k.toUInt64))
def run5 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary16/Model.cast" xs d timed5 full5 trials reps

/-! ### `binary16->binary64/cast` -/
@[inline] def op6 (x : Half) := ExecFloat.cast (target := Double) x
def timed6 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed6 xs k (mixQuick acc (Digest.quick (op6 xs[k]!)))
def full6 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full6 xs k (Digest.full (op6 xs[k]!) (mixFull h k.toUInt64))
def run6 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16->binary64/cast" xs d timed6 full6 trials reps

/-! ### `binary16->binary64/Model.cast` -/
@[inline] def op7 (x : Half) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Double)
def timed7 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed7 xs k (mixQuick acc (Digest.quick (op7 xs[k]!)))
def full7 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full7 xs k (Digest.full (op7 xs[k]!) (mixFull h k.toUInt64))
def run7 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16->binary64/Model.cast" xs d timed7 full7 trials reps

/-! ### `binary64->binary128/cast` -/
@[inline] def op8 (x : Double) := ExecFloat.cast (target := Quad) x
def timed8 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed8 xs k (mixQuick acc (Digest.quick (op8 xs[k]!)))
def full8 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full8 xs k (Digest.full (op8 xs[k]!) (mixFull h k.toUInt64))
def run8 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary128/cast" xs d timed8 full8 trials reps

/-! ### `binary64->binary128/Model.cast` -/
@[inline] def op9 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Quad)
def timed9 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed9 xs k (mixQuick acc (Digest.quick (op9 xs[k]!)))
def full9 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full9 xs k (Digest.full (op9 xs[k]!) (mixFull h k.toUInt64))
def run9 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary128/Model.cast" xs d timed9 full9 trials reps

/-! ### `binary128->binary64/cast` -/
@[inline] def op10 (x : Quad) := ExecFloat.cast (target := Double) x
def timed10 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed10 xs k (mixQuick acc (Digest.quick (op10 xs[k]!)))
def full10 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full10 xs k (Digest.full (op10 xs[k]!) (mixFull h k.toUInt64))
def run10 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128->binary64/cast" xs d timed10 full10 trials reps

/-! ### `binary128->binary64/Model.cast` -/
@[inline] def op11 (x : Quad) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Double)
def timed11 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed11 xs k (mixQuick acc (Digest.quick (op11 xs[k]!)))
def full11 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full11 xs k (Digest.full (op11 xs[k]!) (mixFull h k.toUInt64))
def run11 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128->binary64/Model.cast" xs d timed11 full11 trials reps

/-! ### `binary64->bfloat16/cast` -/
@[inline] def op12 (x : Double) := ExecFloat.cast (target := Brain) x
def timed12 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed12 xs k (mixQuick acc (Digest.quick (op12 xs[k]!)))
def full12 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full12 xs k (Digest.full (op12 xs[k]!) (mixFull h k.toUInt64))
def run12 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->bfloat16/cast" xs d timed12 full12 trials reps

/-! ### `binary64->bfloat16/Model.cast` -/
@[inline] def op13 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Brain)
def timed13 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed13 xs k (mixQuick acc (Digest.quick (op13 xs[k]!)))
def full13 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full13 xs k (Digest.full (op13 xs[k]!) (mixFull h k.toUInt64))
def run13 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->bfloat16/Model.cast" xs d timed13 full13 trials reps

/-! ### `bfloat16->binary32/cast` -/
@[inline] def op14 (x : Brain) := ExecFloat.cast (target := Single) x
def timed14 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed14 xs k (mixQuick acc (Digest.quick (op14 xs[k]!)))
def full14 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full14 xs k (Digest.full (op14 xs[k]!) (mixFull h k.toUInt64))
def run14 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16->binary32/cast" xs d timed14 full14 trials reps

/-! ### `bfloat16->binary32/Model.cast` -/
@[inline] def op15 (x : Brain) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Single)
def timed15 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed15 xs k (mixQuick acc (Digest.quick (op15 xs[k]!)))
def full15 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full15 xs k (Digest.full (op15 xs[k]!) (mixFull h k.toUInt64))
def run15 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16->binary32/Model.cast" xs d timed15 full15 trials reps

/-! ### `binary32->binary16/cast` -/
@[inline] def op16 (x : Single) := ExecFloat.cast (target := Half) x
def timed16 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed16 xs k (mixQuick acc (Digest.quick (op16 xs[k]!)))
def full16 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full16 xs k (Digest.full (op16 xs[k]!) (mixFull h k.toUInt64))
def run16 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32->binary16/cast" xs d timed16 full16 trials reps

/-! ### `binary32->binary16/Model.cast` -/
@[inline] def op17 (x : Single) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Half)
def timed17 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed17 xs k (mixQuick acc (Digest.quick (op17 xs[k]!)))
def full17 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full17 xs k (Digest.full (op17 xs[k]!) (mixFull h k.toUInt64))
def run17 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32->binary16/Model.cast" xs d timed17 full17 trials reps

/-! ### `binary16->binary32/cast` -/
@[inline] def op18 (x : Half) := ExecFloat.cast (target := Single) x
def timed18 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed18 xs k (mixQuick acc (Digest.quick (op18 xs[k]!)))
def full18 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full18 xs k (Digest.full (op18 xs[k]!) (mixFull h k.toUInt64))
def run18 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16->binary32/cast" xs d timed18 full18 trials reps

/-! ### `binary16->binary32/Model.cast` -/
@[inline] def op19 (x : Half) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Single)
def timed19 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed19 xs k (mixQuick acc (Digest.quick (op19 xs[k]!)))
def full19 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full19 xs k (Digest.full (op19 xs[k]!) (mixFull h k.toUInt64))
def run19 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16->binary32/Model.cast" xs d timed19 full19 trials reps

/-! ### `binary32->bfloat16/cast` -/
@[inline] def op20 (x : Single) := ExecFloat.cast (target := Brain) x
def timed20 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed20 xs k (mixQuick acc (Digest.quick (op20 xs[k]!)))
def full20 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full20 xs k (Digest.full (op20 xs[k]!) (mixFull h k.toUInt64))
def run20 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32->bfloat16/cast" xs d timed20 full20 trials reps

/-! ### `binary32->bfloat16/Model.cast` -/
@[inline] def op21 (x : Single) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Brain)
def timed21 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed21 xs k (mixQuick acc (Digest.quick (op21 xs[k]!)))
def full21 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full21 xs k (Digest.full (op21 xs[k]!) (mixFull h k.toUInt64))
def run21 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32->bfloat16/Model.cast" xs d timed21 full21 trials reps

/-! ### `binary128->binary32/cast` -/
@[inline] def op22 (x : Quad) := ExecFloat.cast (target := Single) x
def timed22 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed22 xs k (mixQuick acc (Digest.quick (op22 xs[k]!)))
def full22 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full22 xs k (Digest.full (op22 xs[k]!) (mixFull h k.toUInt64))
def run22 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128->binary32/cast" xs d timed22 full22 trials reps

/-! ### `binary128->binary32/Model.cast` -/
@[inline] def op23 (x : Quad) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Single)
def timed23 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed23 xs k (mixQuick acc (Digest.quick (op23 xs[k]!)))
def full23 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full23 xs k (Digest.full (op23 xs[k]!) (mixFull h k.toUInt64))
def run23 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128->binary32/Model.cast" xs d timed23 full23 trials reps

/-! ### `binary256->binary64/cast` -/
@[inline] def op24 (x : Oct) := ExecFloat.cast (target := Double) x
def timed24 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed24 xs k (mixQuick acc (Digest.quick (op24 xs[k]!)))
def full24 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full24 xs k (Digest.full (op24 xs[k]!) (mixFull h k.toUInt64))
def run24 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256->binary64/cast" xs d timed24 full24 trials reps

/-! ### `binary256->binary64/Model.cast` -/
@[inline] def op25 (x : Oct) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Double)
def timed25 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed25 xs k (mixQuick acc (Digest.quick (op25 xs[k]!)))
def full25 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full25 xs k (Digest.full (op25 xs[k]!) (mixFull h k.toUInt64))
def run25 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256->binary64/Model.cast" xs d timed25 full25 trials reps

/-! ### `binary64->binary256/cast` -/
@[inline] def op26 (x : Double) := ExecFloat.cast (target := Oct) x
def timed26 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed26 xs k (mixQuick acc (Digest.quick (op26 xs[k]!)))
def full26 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full26 xs k (Digest.full (op26 xs[k]!) (mixFull h k.toUInt64))
def run26 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary256/cast" xs d timed26 full26 trials reps

/-! ### `binary64->binary256/Model.cast` -/
@[inline] def op27 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Oct)
def timed27 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed27 xs k (mixQuick acc (Digest.quick (op27 xs[k]!)))
def full27 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full27 xs k (Digest.full (op27 xs[k]!) (mixFull h k.toUInt64))
def run27 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->binary256/Model.cast" xs d timed27 full27 trials reps

/-! ### `binary128->binary256/cast` -/
@[inline] def op28 (x : Quad) := ExecFloat.cast (target := Oct) x
def timed28 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed28 xs k (mixQuick acc (Digest.quick (op28 xs[k]!)))
def full28 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full28 xs k (Digest.full (op28 xs[k]!) (mixFull h k.toUInt64))
def run28 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128->binary256/cast" xs d timed28 full28 trials reps

/-! ### `binary128->binary256/Model.cast` -/
@[inline] def op29 (x : Quad) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Oct)
def timed29 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed29 xs k (mixQuick acc (Digest.quick (op29 xs[k]!)))
def full29 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full29 xs k (Digest.full (op29 xs[k]!) (mixFull h k.toUInt64))
def run29 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128->binary256/Model.cast" xs d timed29 full29 trials reps

/-! ### `binary256->binary128/cast` -/
@[inline] def op30 (x : Oct) := ExecFloat.cast (target := Quad) x
def timed30 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed30 xs k (mixQuick acc (Digest.quick (op30 xs[k]!)))
def full30 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full30 xs k (Digest.full (op30 xs[k]!) (mixFull h k.toUInt64))
def run30 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256->binary128/cast" xs d timed30 full30 trials reps

/-! ### `binary256->binary128/Model.cast` -/
@[inline] def op31 (x : Oct) := (ExecFloat.Binary.ofModel (Model.cast _ _
    (ExecFloat.Binary.toModel x)) : Quad)
def timed31 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed31 xs k (mixQuick acc (Digest.quick (op31 xs[k]!)))
def full31 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full31 xs k (Digest.full (op31 xs[k]!) (mixFull h k.toUInt64))
def run31 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256->binary128/Model.cast" xs d timed31 full31 trials reps

/-! ### `posit32->binary64/cast` -/
@[inline] def op32 (x : P32) := ExecFloat.cast (target := Double) x
def timed32 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed32 xs k (mixQuick acc (Digest.quick (op32 xs[k]!)))
def full32 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full32 xs k (Digest.full (op32 xs[k]!) (mixFull h k.toUInt64))
def run32 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32->binary64/cast" xs d timed32 full32 trials reps

/-! ### `binary64->posit32/cast` -/
@[inline] def op33 (x : Double) := ExecFloat.cast (target := P32) x
def timed33 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed33 xs k (mixQuick acc (Digest.quick (op33 xs[k]!)))
def full33 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full33 xs k (Digest.full (op33 xs[k]!) (mixFull h k.toUInt64))
def run33 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64->posit32/cast" xs d timed33 full33 trials reps

/-! ### `posit32->binary32/cast` -/
@[inline] def op34 (x : P32) := ExecFloat.cast (target := Single) x
def timed34 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed34 xs k (mixQuick acc (Digest.quick (op34 xs[k]!)))
def full34 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full34 xs k (Digest.full (op34 xs[k]!) (mixFull h k.toUInt64))
def run34 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32->binary32/cast" xs d timed34 full34 trials reps

/-! ### `binary16/convertFromInt64` -/
@[inline] def op35 (n : Int) := (ExecFloat.convert (target := Half) (SourceExact := Int)
    (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed35 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed35 ns k (mixQuick acc (Digest.quick (op35 ns[k]!)))
def full35 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full35 ns k (Digest.full (op35 ns[k]!) (mixFull h k.toUInt64))
def run35 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary16/convertFromInt64" ns d timed35 full35 trials reps

/-! ### `binary16/convertFromInt64` -/
@[inline] def op36 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _ (FixedInt.ofInt
    n : FixedInt 64) .nearest) : Half)
def timed36 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed36 ns k (mixQuick acc (Digest.quick (op36 ns[k]!)))
def full36 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full36 ns k (Digest.full (op36 ns[k]!) (mixFull h k.toUInt64))
def run36 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary16/convertFromInt64" ns d timed36 full36 trials reps

/-! ### `binary16/convertToIntegerExact64[nearest]` -/
@[inline] def op37 (x : Half) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel x)
    .nearest
def timed37 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed37 xs k (mixQuick acc (Digest.quick (op37 xs[k]!)))
def full37 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full37 xs k (Digest.full (op37 xs[k]!) (mixFull h k.toUInt64))
def run37 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/convertToIntegerExact64[nearest]" xs d timed37 full37 trials reps

/-! ### `binary16/convertToIntegerExact64[towardZero]` -/
@[inline] def op38 (x : Half) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel x)
    .towardZero
def timed38 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed38 xs k (mixQuick acc (Digest.quick (op38 xs[k]!)))
def full38 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full38 xs k (Digest.full (op38 xs[k]!) (mixFull h k.toUInt64))
def run38 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/convertToIntegerExact64[towardZero]" xs d timed38 full38 trials reps

/-! ### `bfloat16/convertFromInt64` -/
@[inline] def op122 (n : Int) := (ExecFloat.convert (target := Brain) (SourceExact := Int)
    (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed122 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed122 ns k (mixQuick acc (Digest.quick (op122 ns[k]!)))
def full122 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full122 ns k (Digest.full (op122 ns[k]!) (mixFull h k.toUInt64))
def run122 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "bfloat16/convertFromInt64" ns d timed122 full122 trials reps

/-! ### `bfloat16/convertFromInt64` -/
@[inline] def op123 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _
    (FixedInt.ofInt n : FixedInt 64) .nearest) : Brain)
def timed123 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed123 ns k (mixQuick acc (Digest.quick (op123 ns[k]!)))
def full123 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full123 ns k (Digest.full (op123 ns[k]!) (mixFull h k.toUInt64))
def run123 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "bfloat16/convertFromInt64" ns d timed123 full123 trials reps

/-! ### `bfloat16/convertToIntegerExact64[nearest]` -/
@[inline] def op124 (x : Brain) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel
    x) .nearest
def timed124 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed124 xs k (mixQuick acc (Digest.quick (op124 xs[k]!)))
def full124 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full124 xs k (Digest.full (op124 xs[k]!) (mixFull h k.toUInt64))
def run124 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/convertToIntegerExact64[nearest]" xs d timed124 full124 trials reps

/-! ### `bfloat16/convertToIntegerExact64[towardZero]` -/
@[inline] def op125 (x : Brain) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel
    x) .towardZero
def timed125 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed125 xs k (mixQuick acc (Digest.quick (op125 xs[k]!)))
def full125 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full125 xs k (Digest.full (op125 xs[k]!) (mixFull h k.toUInt64))
def run125 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/convertToIntegerExact64[towardZero]" xs d timed125 full125 trials reps

/-! ### `binary32/convertFromInt64` -/
@[inline] def op209 (n : Int) := (ExecFloat.convert (target := Single) (SourceExact := Int)
    (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed209 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed209 ns k (mixQuick acc (Digest.quick (op209 ns[k]!)))
def full209 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full209 ns k (Digest.full (op209 ns[k]!) (mixFull h k.toUInt64))
def run209 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary32/convertFromInt64" ns d timed209 full209 trials reps

/-! ### `binary32/convertFromInt64` -/
@[inline] def op210 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _
    (FixedInt.ofInt n : FixedInt 64) .nearest) : Single)
def timed210 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed210 ns k (mixQuick acc (Digest.quick (op210 ns[k]!)))
def full210 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full210 ns k (Digest.full (op210 ns[k]!) (mixFull h k.toUInt64))
def run210 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary32/convertFromInt64" ns d timed210 full210 trials reps

/-! ### `binary32/convertToIntegerExact64[nearest]` -/
@[inline] def op211 (x : Single) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel
    x) .nearest
def timed211 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed211 xs k (mixQuick acc (Digest.quick (op211 xs[k]!)))
def full211 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full211 xs k (Digest.full (op211 xs[k]!) (mixFull h k.toUInt64))
def run211 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/convertToIntegerExact64[nearest]" xs d timed211 full211 trials reps

/-! ### `binary32/convertToIntegerExact64[towardZero]` -/
@[inline] def op212 (x : Single) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel
    x) .towardZero
def timed212 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed212 xs k (mixQuick acc (Digest.quick (op212 xs[k]!)))
def full212 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full212 xs k (Digest.full (op212 xs[k]!) (mixFull h k.toUInt64))
def run212 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/convertToIntegerExact64[towardZero]" xs d timed212 full212 trials reps

/-! ### `binary64/convertFromInt64` -/
@[inline] def op296 (n : Int) := (ExecFloat.convert (target := Double) (SourceExact := Int)
    (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed296 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed296 ns k (mixQuick acc (Digest.quick (op296 ns[k]!)))
def full296 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full296 ns k (Digest.full (op296 ns[k]!) (mixFull h k.toUInt64))
def run296 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary64/convertFromInt64" ns d timed296 full296 trials reps

/-! ### `binary64/convertFromInt64` -/
@[inline] def op297 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _
    (FixedInt.ofInt n : FixedInt 64) .nearest) : Double)
def timed297 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed297 ns k (mixQuick acc (Digest.quick (op297 ns[k]!)))
def full297 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full297 ns k (Digest.full (op297 ns[k]!) (mixFull h k.toUInt64))
def run297 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary64/convertFromInt64" ns d timed297 full297 trials reps

/-! ### `binary64/convertToIntegerExact64[nearest]` -/
@[inline] def op298 (x : Double) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel
    x) .nearest
def timed298 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed298 xs k (mixQuick acc (Digest.quick (op298 xs[k]!)))
def full298 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full298 xs k (Digest.full (op298 xs[k]!) (mixFull h k.toUInt64))
def run298 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/convertToIntegerExact64[nearest]" xs d timed298 full298 trials reps

/-! ### `binary64/convertToIntegerExact64[towardZero]` -/
@[inline] def op299 (x : Double) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel
    x) .towardZero
def timed299 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed299 xs k (mixQuick acc (Digest.quick (op299 xs[k]!)))
def full299 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full299 xs k (Digest.full (op299 xs[k]!) (mixFull h k.toUInt64))
def run299 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/convertToIntegerExact64[towardZero]" xs d timed299 full299 trials reps

/-! ### `binary128/convertFromInt64` -/
@[inline] def op383 (n : Int) := (ExecFloat.convert (target := Quad) (SourceExact := Int)
    (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed383 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed383 ns k (mixQuick acc (Digest.quick (op383 ns[k]!)))
def full383 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full383 ns k (Digest.full (op383 ns[k]!) (mixFull h k.toUInt64))
def run383 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary128/convertFromInt64" ns d timed383 full383 trials reps

/-! ### `binary128/convertFromInt64` -/
@[inline] def op384 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _
    (FixedInt.ofInt n : FixedInt 64) .nearest) : Quad)
def timed384 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed384 ns k (mixQuick acc (Digest.quick (op384 ns[k]!)))
def full384 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full384 ns k (Digest.full (op384 ns[k]!) (mixFull h k.toUInt64))
def run384 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary128/convertFromInt64" ns d timed384 full384 trials reps

/-! ### `binary128/convertToIntegerExact64[nearest]` -/
@[inline] def op385 (x : Quad) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel x)
    .nearest
def timed385 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed385 xs k (mixQuick acc (Digest.quick (op385 xs[k]!)))
def full385 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full385 xs k (Digest.full (op385 xs[k]!) (mixFull h k.toUInt64))
def run385 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/convertToIntegerExact64[nearest]" xs d timed385 full385 trials reps

/-! ### `binary128/convertToIntegerExact64[towardZero]` -/
@[inline] def op386 (x : Quad) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel x)
    .towardZero
def timed386 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed386 xs k (mixQuick acc (Digest.quick (op386 xs[k]!)))
def full386 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full386 xs k (Digest.full (op386 xs[k]!) (mixFull h k.toUInt64))
def run386 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/convertToIntegerExact64[towardZero]" xs d timed386 full386 trials reps

/-! ### `binary256/convertFromInt64` -/
@[inline] def op470 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.convertFromInt _
    (FixedInt.ofInt n : FixedInt 64) .nearest) : Oct)
def timed470 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed470 ns k (mixQuick acc (Digest.quick (op470 ns[k]!)))
def full470 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full470 ns k (Digest.full (op470 ns[k]!) (mixFull h k.toUInt64))
def run470 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary256/convertFromInt64" ns d timed470 full470 trials reps

/-! ### `binary256/convertToIntegerExact64[nearest]` -/
@[inline] def op471 (x : Oct) := ExecDType.convertToIntegerExact (width := 64) (ExecFloat.Binary.toModel x)
    .nearest
def timed471 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed471 xs k (mixQuick acc (Digest.quick (op471 xs[k]!)))
def full471 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full471 xs k (Digest.full (op471 xs[k]!) (mixFull h k.toUInt64))
def run471 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/convertToIntegerExact64[nearest]" xs d timed471 full471 trials reps

/-! ### `posit32/ofFixedInt64` -/
@[inline] def op496 (n : Int) := (ExecFloat.Posit.ofFixedInt (FixedInt.ofInt n : FixedInt 64) : P32)
def timed496 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed496 ns k (mixQuick acc (Digest.quick (op496 ns[k]!)))
def full496 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full496 ns k (Digest.full (op496 ns[k]!) (mixFull h k.toUInt64))
def run496 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "posit32/ofFixedInt64" ns d timed496 full496 trials reps

/-! ### `posit32/toFixedInt64` -/
@[inline] def op497 (x : P32) := ExecFloat.Posit.toFixedInt 64 x
def timed497 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed497 xs k (mixQuick acc (Digest.quick (op497 xs[k]!)))
def full497 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full497 xs k (Digest.full (op497 xs[k]!) (mixFull h k.toUInt64))
def run497 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/toFixedInt64" xs d timed497 full497 trials reps

/-! ### `posit32/convertFromInt64` -/
@[inline] def op498 (n : Int) := (ExecFloat.convert (target := P32) (SourceExact := Int)
    (TargetExact := Rat) n)
def timed498 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed498 ns k (mixQuick acc (Digest.quick (op498 ns[k]!)))
def full498 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full498 ns k (Digest.full (op498 ns[k]!) (mixFull h k.toUInt64))
def run498 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "posit32/convertFromInt64" ns d timed498 full498 trials reps

end FloatLibBenchmarks.Public.TimeOps
