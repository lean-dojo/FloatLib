/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Text conversion timings

Parsing and display cells with complete string and floating-point result digests.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/format[scientific]` -/
@[inline] def op78 (x : Half) := ExecFloat.Binary.format x (style := .scientific 4)
def timed78 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed78 xs k (mixQuick acc (Digest.quick (op78 xs[k]!)))
def full78 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full78 xs k (Digest.full (op78 xs[k]!) (mixFull h k.toUInt64))
def run78 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/format[scientific]" xs d timed78 full78 trials reps

/-! ### `binary16/format[exact]` -/
@[inline] def op79 (x : Half) := ExecFloat.Binary.format x (style := .exact)
def timed79 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed79 xs k (mixQuick acc (Digest.quick (op79 xs[k]!)))
def full79 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full79 xs k (Digest.full (op79 xs[k]!) (mixFull h k.toUInt64))
def run79 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/format[exact]" xs d timed79 full79 trials reps

/-! ### `binary16/format[hex]` -/
@[inline] def op80 (x : Half) := ExecFloat.Binary.format x (style := .hex)
def timed80 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed80 xs k (mixQuick acc (Digest.quick (op80 xs[k]!)))
def full80 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full80 xs k (Digest.full (op80 xs[k]!) (mixFull h k.toUInt64))
def run80 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/format[hex]" xs d timed80 full80 trials reps

/-! ### `binary16/toString` -/
@[inline] def op81 (x : Half) := toString x
def timed81 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed81 xs k (mixQuick acc (Digest.quick (op81 xs[k]!)))
def full81 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full81 xs k (Digest.full (op81 xs[k]!) (mixFull h k.toUInt64))
def run81 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/toString" xs d timed81 full81 trials reps

/-! ### `binary16/parse` -/
@[inline] def op82 (s : String) := (ExecFloat.Binary.parse s : Except Model.ParseError Half)
def timed82 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed82 ss k (mixQuick acc (Digest.quick (op82 ss[k]!)))
def full82 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full82 ss k (Digest.full (op82 ss[k]!) (mixFull h k.toUInt64))
def run82 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inHalf seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 4))
  runS "binary16/parse" ss (digestStrings ss) timed82 full82 trials reps

/-! ### `binary16/parse[status]` -/
@[inline] def op83 (s : String) := (ExecFloat.Binary.parse s (status := true)).map fun outcome =>
  ((outcome.value : Half), outcome.status, outcome.ternary)
def timed83 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed83 ss k (mixQuick acc (Digest.quick (op83 ss[k]!)))
def full83 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full83 ss k (Digest.full (op83 ss[k]!) (mixFull h k.toUInt64))
def run83 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inHalf seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 4))
  runS "binary16/parse[status]" ss (digestStrings ss) timed83 full83 trials reps

/-! ### `bfloat16/format[scientific]` -/
@[inline] def op165 (x : Brain) := ExecFloat.Binary.format x (style := .scientific 3)
def timed165 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed165 xs k (mixQuick acc (Digest.quick (op165 xs[k]!)))
def full165 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full165 xs k (Digest.full (op165 xs[k]!) (mixFull h k.toUInt64))
def run165 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/format[scientific]" xs d timed165 full165 trials reps

/-! ### `bfloat16/format[exact]` -/
@[inline] def op166 (x : Brain) := ExecFloat.Binary.format x (style := .exact)
def timed166 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed166 xs k (mixQuick acc (Digest.quick (op166 xs[k]!)))
def full166 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full166 xs k (Digest.full (op166 xs[k]!) (mixFull h k.toUInt64))
def run166 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/format[exact]" xs d timed166 full166 trials reps

/-! ### `bfloat16/format[hex]` -/
@[inline] def op167 (x : Brain) := ExecFloat.Binary.format x (style := .hex)
def timed167 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed167 xs k (mixQuick acc (Digest.quick (op167 xs[k]!)))
def full167 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full167 xs k (Digest.full (op167 xs[k]!) (mixFull h k.toUInt64))
def run167 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/format[hex]" xs d timed167 full167 trials reps

/-! ### `bfloat16/toString` -/
@[inline] def op168 (x : Brain) := toString x
def timed168 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed168 xs k (mixQuick acc (Digest.quick (op168 xs[k]!)))
def full168 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full168 xs k (Digest.full (op168 xs[k]!) (mixFull h k.toUInt64))
def run168 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/toString" xs d timed168 full168 trials reps

/-! ### `bfloat16/parse` -/
@[inline] def op169 (s : String) := (ExecFloat.Binary.parse s : Except Model.ParseError Brain)
def timed169 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed169 ss k (mixQuick acc (Digest.quick (op169 ss[k]!)))
def full169 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full169 ss k (Digest.full (op169 ss[k]!) (mixFull h k.toUInt64))
def run169 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inBrain seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 3))
  runS "bfloat16/parse" ss (digestStrings ss) timed169 full169 trials reps

/-! ### `bfloat16/parse[status]` -/
@[inline] def op170 (s : String) := (ExecFloat.Binary.parse s (status := true)).map fun outcome =>
  ((outcome.value : Brain), outcome.status, outcome.ternary)
def timed170 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed170 ss k (mixQuick acc (Digest.quick (op170 ss[k]!)))
def full170 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full170 ss k (Digest.full (op170 ss[k]!) (mixFull h k.toUInt64))
def run170 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inBrain seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 3))
  runS "bfloat16/parse[status]" ss (digestStrings ss) timed170 full170 trials reps

/-! ### `binary32/format[scientific]` -/
@[inline] def op252 (x : Single) := ExecFloat.Binary.format x (style := .scientific 8)
def timed252 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed252 xs k (mixQuick acc (Digest.quick (op252 xs[k]!)))
def full252 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full252 xs k (Digest.full (op252 xs[k]!) (mixFull h k.toUInt64))
def run252 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/format[scientific]" xs d timed252 full252 trials reps

/-! ### `binary32/format[exact]` -/
@[inline] def op253 (x : Single) := ExecFloat.Binary.format x (style := .exact)
def timed253 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed253 xs k (mixQuick acc (Digest.quick (op253 xs[k]!)))
def full253 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full253 xs k (Digest.full (op253 xs[k]!) (mixFull h k.toUInt64))
def run253 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/format[exact]" xs d timed253 full253 trials reps

/-! ### `binary32/format[hex]` -/
@[inline] def op254 (x : Single) := ExecFloat.Binary.format x (style := .hex)
def timed254 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed254 xs k (mixQuick acc (Digest.quick (op254 xs[k]!)))
def full254 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full254 xs k (Digest.full (op254 xs[k]!) (mixFull h k.toUInt64))
def run254 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/format[hex]" xs d timed254 full254 trials reps

/-! ### `binary32/toString` -/
@[inline] def op255 (x : Single) := toString x
def timed255 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed255 xs k (mixQuick acc (Digest.quick (op255 xs[k]!)))
def full255 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full255 xs k (Digest.full (op255 xs[k]!) (mixFull h k.toUInt64))
def run255 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/toString" xs d timed255 full255 trials reps

/-! ### `binary32/parse` -/
@[inline] def op256 (s : String) := (ExecFloat.Binary.parse s : Except Model.ParseError Single)
def timed256 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed256 ss k (mixQuick acc (Digest.quick (op256 ss[k]!)))
def full256 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full256 ss k (Digest.full (op256 ss[k]!) (mixFull h k.toUInt64))
def run256 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inSingle seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 8))
  runS "binary32/parse" ss (digestStrings ss) timed256 full256 trials reps

/-! ### `binary32/parse[status]` -/
@[inline] def op257 (s : String) := (ExecFloat.Binary.parse s (status := true)).map fun outcome =>
  ((outcome.value : Single), outcome.status, outcome.ternary)
def timed257 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed257 ss k (mixQuick acc (Digest.quick (op257 ss[k]!)))
def full257 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full257 ss k (Digest.full (op257 ss[k]!) (mixFull h k.toUInt64))
def run257 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inSingle seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 8))
  runS "binary32/parse[status]" ss (digestStrings ss) timed257 full257 trials reps

/-! ### `binary64/format[scientific]` -/
@[inline] def op339 (x : Double) := ExecFloat.Binary.format x (style := .scientific 16)
def timed339 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed339 xs k (mixQuick acc (Digest.quick (op339 xs[k]!)))
def full339 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full339 xs k (Digest.full (op339 xs[k]!) (mixFull h k.toUInt64))
def run339 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/format[scientific]" xs d timed339 full339 trials reps

/-! ### `binary64/format[exact]` -/
@[inline] def op340 (x : Double) := ExecFloat.Binary.format x (style := .exact)
def timed340 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed340 xs k (mixQuick acc (Digest.quick (op340 xs[k]!)))
def full340 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full340 xs k (Digest.full (op340 xs[k]!) (mixFull h k.toUInt64))
def run340 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/format[exact]" xs d timed340 full340 trials reps

/-! ### `binary64/format[hex]` -/
@[inline] def op341 (x : Double) := ExecFloat.Binary.format x (style := .hex)
def timed341 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed341 xs k (mixQuick acc (Digest.quick (op341 xs[k]!)))
def full341 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full341 xs k (Digest.full (op341 xs[k]!) (mixFull h k.toUInt64))
def run341 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/format[hex]" xs d timed341 full341 trials reps

/-! ### `binary64/toString` -/
@[inline] def op342 (x : Double) := toString x
def timed342 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed342 xs k (mixQuick acc (Digest.quick (op342 xs[k]!)))
def full342 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full342 xs k (Digest.full (op342 xs[k]!) (mixFull h k.toUInt64))
def run342 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/toString" xs d timed342 full342 trials reps

/-! ### `binary64/parse` -/
@[inline] def op343 (s : String) := (ExecFloat.Binary.parse s : Except Model.ParseError Double)
def timed343 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed343 ss k (mixQuick acc (Digest.quick (op343 ss[k]!)))
def full343 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full343 ss k (Digest.full (op343 ss[k]!) (mixFull h k.toUInt64))
def run343 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inDouble seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 16))
  runS "binary64/parse" ss (digestStrings ss) timed343 full343 trials reps

/-! ### `binary64/parse[status]` -/
@[inline] def op344 (s : String) := (ExecFloat.Binary.parse s (status := true)).map fun outcome =>
  ((outcome.value : Double), outcome.status, outcome.ternary)
def timed344 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed344 ss k (mixQuick acc (Digest.quick (op344 ss[k]!)))
def full344 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full344 ss k (Digest.full (op344 ss[k]!) (mixFull h k.toUInt64))
def run344 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inDouble seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 16))
  runS "binary64/parse[status]" ss (digestStrings ss) timed344 full344 trials reps

/-! ### `binary128/format[scientific]` -/
@[inline] def op426 (x : Quad) := ExecFloat.Binary.format x (style := .scientific 35)
def timed426 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed426 xs k (mixQuick acc (Digest.quick (op426 xs[k]!)))
def full426 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full426 xs k (Digest.full (op426 xs[k]!) (mixFull h k.toUInt64))
def run426 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/format[scientific]" xs d timed426 full426 trials reps

/-! ### `binary128/format[exact]` -/
@[inline] def op427 (x : Quad) := ExecFloat.Binary.format x (style := .exact)
def timed427 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed427 xs k (mixQuick acc (Digest.quick (op427 xs[k]!)))
def full427 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full427 xs k (Digest.full (op427 xs[k]!) (mixFull h k.toUInt64))
def run427 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/format[exact]" xs d timed427 full427 trials reps

/-! ### `binary128/format[hex]` -/
@[inline] def op428 (x : Quad) := ExecFloat.Binary.format x (style := .hex)
def timed428 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed428 xs k (mixQuick acc (Digest.quick (op428 xs[k]!)))
def full428 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full428 xs k (Digest.full (op428 xs[k]!) (mixFull h k.toUInt64))
def run428 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/format[hex]" xs d timed428 full428 trials reps

/-! ### `binary128/toString` -/
@[inline] def op429 (x : Quad) := toString x
def timed429 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed429 xs k (mixQuick acc (Digest.quick (op429 xs[k]!)))
def full429 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full429 xs k (Digest.full (op429 xs[k]!) (mixFull h k.toUInt64))
def run429 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/toString" xs d timed429 full429 trials reps

/-! ### `binary128/parse` -/
@[inline] def op430 (s : String) := (ExecFloat.Binary.parse s : Except Model.ParseError Quad)
def timed430 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed430 ss k (mixQuick acc (Digest.quick (op430 ss[k]!)))
def full430 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full430 ss k (Digest.full (op430 ss[k]!) (mixFull h k.toUInt64))
def run430 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inQuad seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 35))
  runS "binary128/parse" ss (digestStrings ss) timed430 full430 trials reps

/-! ### `binary128/parse[status]` -/
@[inline] def op431 (s : String) := (ExecFloat.Binary.parse s (status := true)).map fun outcome =>
  ((outcome.value : Quad), outcome.status, outcome.ternary)
def timed431 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed431 ss k (mixQuick acc (Digest.quick (op431 ss[k]!)))
def full431 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full431 ss k (Digest.full (op431 ss[k]!) (mixFull h k.toUInt64))
def run431 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inQuad seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 35))
  runS "binary128/parse[status]" ss (digestStrings ss) timed431 full431 trials reps

/-! ### `binary256/format[scientific]` -/
@[inline] def op486 (x : Oct) := ExecFloat.Binary.format x (style := .scientific 72)
def timed486 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed486 xs k (mixQuick acc (Digest.quick (op486 xs[k]!)))
def full486 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full486 xs k (Digest.full (op486 xs[k]!) (mixFull h k.toUInt64))
def run486 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/format[scientific]" xs d timed486 full486 trials reps

/-! ### `binary256/parse` -/
@[inline] def op487 (s : String) := (ExecFloat.Binary.parse s : Except Model.ParseError Oct)
def timed487 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed487 ss k (mixQuick acc (Digest.quick (op487 ss[k]!)))
def full487 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full487 ss k (Digest.full (op487 ss[k]!) (mixFull h k.toUInt64))
def run487 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inOct seedX count
  let ss := xs.map (fun x => ExecFloat.Binary.format x (style := .scientific 72))
  runS "binary256/parse" ss (digestStrings ss) timed487 full487 trials reps

/-! ### `posit32/display` -/
@[inline] def op513 (x : P32) := ExecFloat.Posit.display x
def timed513 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed513 xs k (mixQuick acc (Digest.quick (op513 xs[k]!)))
def full513 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full513 xs k (Digest.full (op513 xs[k]!) (mixFull h k.toUInt64))
def run513 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/display" xs d timed513 full513 trials reps

/-! ### `posit32/parse` -/
@[inline] def op514 (s : String) := (ExecFloat.Posit.parse s : Except
    Formats.Posit.Model.ParseError P32)
def timed514 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed514 ss k (mixQuick acc (Digest.quick (op514 ss[k]!)))
def full514 (ss : Array String) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full514 ss k (Digest.full (op514 ss[k]!) (mixFull h k.toUInt64))
def run514 (count trials reps : Nat) : IO Unit := do
  let (xs, _) := inP32 seedX count
  let ss := xs.map (fun x => ExecFloat.Posit.display x)
  runS "posit32/parse" ss (digestStrings ss) timed514 full514 trials reps

end FloatLibBenchmarks.Public.TimeOps
