/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Classification timings

Predicates and classification on finite values, infinities and NaNs.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/isNaN` -/
@[inline] def op68 (x : Half) := ExecFloat.Binary.isNaN x
def timed68 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed68 xs k (mixQuick acc (Digest.quick (op68 xs[k]!)))
def full68 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full68 xs k (Digest.full (op68 xs[k]!) (mixFull h k.toUInt64))
def run68 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isNaN" xs d timed68 full68 trials reps

/-! ### `binary16/isNormal` -/
@[inline] def op69 (x : Half) := ExecFloat.Binary.isNormal x
def timed69 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed69 xs k (mixQuick acc (Digest.quick (op69 xs[k]!)))
def full69 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full69 xs k (Digest.full (op69 xs[k]!) (mixFull h k.toUInt64))
def run69 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isNormal" xs d timed69 full69 trials reps

/-! ### `binary16/isSubnormal` -/
@[inline] def op70 (x : Half) := ExecFloat.Binary.isSubnormal x
def timed70 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed70 xs k (mixQuick acc (Digest.quick (op70 xs[k]!)))
def full70 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full70 xs k (Digest.full (op70 xs[k]!) (mixFull h k.toUInt64))
def run70 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isSubnormal" xs d timed70 full70 trials reps

/-! ### `binary16/isZero` -/
@[inline] def op71 (x : Half) := ExecFloat.Binary.isZero x
def timed71 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed71 xs k (mixQuick acc (Digest.quick (op71 xs[k]!)))
def full71 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full71 xs k (Digest.full (op71 xs[k]!) (mixFull h k.toUInt64))
def run71 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isZero" xs d timed71 full71 trials reps

/-! ### `binary16/isFinite` -/
@[inline] def op72 (x : Half) := ExecFloat.Binary.isFinite x
def timed72 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed72 xs k (mixQuick acc (Digest.quick (op72 xs[k]!)))
def full72 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full72 xs k (Digest.full (op72 xs[k]!) (mixFull h k.toUInt64))
def run72 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isFinite" xs d timed72 full72 trials reps

/-! ### `binary16/isInfinite` -/
@[inline] def op73 (x : Half) := ExecFloat.Binary.isInfinite x
def timed73 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed73 xs k (mixQuick acc (Digest.quick (op73 xs[k]!)))
def full73 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full73 xs k (Digest.full (op73 xs[k]!) (mixFull h k.toUInt64))
def run73 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isInfinite" xs d timed73 full73 trials reps

/-! ### `binary16/isSignalingNaN` -/
@[inline] def op74 (x : Half) := ExecFloat.Binary.isSignaling x
def timed74 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed74 xs k (mixQuick acc (Digest.quick (op74 xs[k]!)))
def full74 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full74 xs k (Digest.full (op74 xs[k]!) (mixFull h k.toUInt64))
def run74 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isSignalingNaN" xs d timed74 full74 trials reps

/-! ### `binary16/signBit` -/
@[inline] def op75 (x : Half) := ExecFloat.Binary.signBit x
def timed75 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed75 xs k (mixQuick acc (Digest.quick (op75 xs[k]!)))
def full75 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full75 xs k (Digest.full (op75 xs[k]!) (mixFull h k.toUInt64))
def run75 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/signBit" xs d timed75 full75 trials reps

/-! ### `binary16/classify` -/
@[inline] def op76 (x : Half) := ExecFloat.Binary.classify x
def timed76 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed76 xs k (mixQuick acc (Digest.quick (op76 xs[k]!)))
def full76 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full76 xs k (Digest.full (op76 xs[k]!) (mixFull h k.toUInt64))
def run76 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/classify" xs d timed76 full76 trials reps

/-! ### `binary16/isCanonical` -/
@[inline] def op77 (x : Half) := ExecFloat.Binary.isCanonical x
def timed77 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed77 xs k (mixQuick acc (Digest.quick (op77 xs[k]!)))
def full77 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full77 xs k (Digest.full (op77 xs[k]!) (mixFull h k.toUInt64))
def run77 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/isCanonical" xs d timed77 full77 trials reps

/-! ### `bfloat16/isNaN` -/
@[inline] def op155 (x : Brain) := ExecFloat.Binary.isNaN x
def timed155 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed155 xs k (mixQuick acc (Digest.quick (op155 xs[k]!)))
def full155 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full155 xs k (Digest.full (op155 xs[k]!) (mixFull h k.toUInt64))
def run155 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isNaN" xs d timed155 full155 trials reps

/-! ### `bfloat16/isNormal` -/
@[inline] def op156 (x : Brain) := ExecFloat.Binary.isNormal x
def timed156 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed156 xs k (mixQuick acc (Digest.quick (op156 xs[k]!)))
def full156 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full156 xs k (Digest.full (op156 xs[k]!) (mixFull h k.toUInt64))
def run156 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isNormal" xs d timed156 full156 trials reps

/-! ### `bfloat16/isSubnormal` -/
@[inline] def op157 (x : Brain) := ExecFloat.Binary.isSubnormal x
def timed157 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed157 xs k (mixQuick acc (Digest.quick (op157 xs[k]!)))
def full157 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full157 xs k (Digest.full (op157 xs[k]!) (mixFull h k.toUInt64))
def run157 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isSubnormal" xs d timed157 full157 trials reps

/-! ### `bfloat16/isZero` -/
@[inline] def op158 (x : Brain) := ExecFloat.Binary.isZero x
def timed158 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed158 xs k (mixQuick acc (Digest.quick (op158 xs[k]!)))
def full158 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full158 xs k (Digest.full (op158 xs[k]!) (mixFull h k.toUInt64))
def run158 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isZero" xs d timed158 full158 trials reps

/-! ### `bfloat16/isFinite` -/
@[inline] def op159 (x : Brain) := ExecFloat.Binary.isFinite x
def timed159 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed159 xs k (mixQuick acc (Digest.quick (op159 xs[k]!)))
def full159 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full159 xs k (Digest.full (op159 xs[k]!) (mixFull h k.toUInt64))
def run159 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isFinite" xs d timed159 full159 trials reps

/-! ### `bfloat16/isInfinite` -/
@[inline] def op160 (x : Brain) := ExecFloat.Binary.isInfinite x
def timed160 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed160 xs k (mixQuick acc (Digest.quick (op160 xs[k]!)))
def full160 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full160 xs k (Digest.full (op160 xs[k]!) (mixFull h k.toUInt64))
def run160 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isInfinite" xs d timed160 full160 trials reps

/-! ### `bfloat16/isSignalingNaN` -/
@[inline] def op161 (x : Brain) := ExecFloat.Binary.isSignaling x
def timed161 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed161 xs k (mixQuick acc (Digest.quick (op161 xs[k]!)))
def full161 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full161 xs k (Digest.full (op161 xs[k]!) (mixFull h k.toUInt64))
def run161 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isSignalingNaN" xs d timed161 full161 trials reps

/-! ### `bfloat16/signBit` -/
@[inline] def op162 (x : Brain) := ExecFloat.Binary.signBit x
def timed162 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed162 xs k (mixQuick acc (Digest.quick (op162 xs[k]!)))
def full162 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full162 xs k (Digest.full (op162 xs[k]!) (mixFull h k.toUInt64))
def run162 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/signBit" xs d timed162 full162 trials reps

/-! ### `bfloat16/classify` -/
@[inline] def op163 (x : Brain) := ExecFloat.Binary.classify x
def timed163 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed163 xs k (mixQuick acc (Digest.quick (op163 xs[k]!)))
def full163 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full163 xs k (Digest.full (op163 xs[k]!) (mixFull h k.toUInt64))
def run163 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/classify" xs d timed163 full163 trials reps

/-! ### `bfloat16/isCanonical` -/
@[inline] def op164 (x : Brain) := ExecFloat.Binary.isCanonical x
def timed164 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed164 xs k (mixQuick acc (Digest.quick (op164 xs[k]!)))
def full164 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full164 xs k (Digest.full (op164 xs[k]!) (mixFull h k.toUInt64))
def run164 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/isCanonical" xs d timed164 full164 trials reps

/-! ### `binary32/isNaN` -/
@[inline] def op242 (x : Single) := ExecFloat.Binary.isNaN x
def timed242 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed242 xs k (mixQuick acc (Digest.quick (op242 xs[k]!)))
def full242 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full242 xs k (Digest.full (op242 xs[k]!) (mixFull h k.toUInt64))
def run242 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isNaN" xs d timed242 full242 trials reps

/-! ### `binary32/isNormal` -/
@[inline] def op243 (x : Single) := ExecFloat.Binary.isNormal x
def timed243 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed243 xs k (mixQuick acc (Digest.quick (op243 xs[k]!)))
def full243 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full243 xs k (Digest.full (op243 xs[k]!) (mixFull h k.toUInt64))
def run243 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isNormal" xs d timed243 full243 trials reps

/-! ### `binary32/isSubnormal` -/
@[inline] def op244 (x : Single) := ExecFloat.Binary.isSubnormal x
def timed244 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed244 xs k (mixQuick acc (Digest.quick (op244 xs[k]!)))
def full244 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full244 xs k (Digest.full (op244 xs[k]!) (mixFull h k.toUInt64))
def run244 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isSubnormal" xs d timed244 full244 trials reps

/-! ### `binary32/isZero` -/
@[inline] def op245 (x : Single) := ExecFloat.Binary.isZero x
def timed245 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed245 xs k (mixQuick acc (Digest.quick (op245 xs[k]!)))
def full245 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full245 xs k (Digest.full (op245 xs[k]!) (mixFull h k.toUInt64))
def run245 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isZero" xs d timed245 full245 trials reps

/-! ### `binary32/isFinite` -/
@[inline] def op246 (x : Single) := ExecFloat.Binary.isFinite x
def timed246 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed246 xs k (mixQuick acc (Digest.quick (op246 xs[k]!)))
def full246 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full246 xs k (Digest.full (op246 xs[k]!) (mixFull h k.toUInt64))
def run246 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isFinite" xs d timed246 full246 trials reps

/-! ### `binary32/isInfinite` -/
@[inline] def op247 (x : Single) := ExecFloat.Binary.isInfinite x
def timed247 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed247 xs k (mixQuick acc (Digest.quick (op247 xs[k]!)))
def full247 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full247 xs k (Digest.full (op247 xs[k]!) (mixFull h k.toUInt64))
def run247 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isInfinite" xs d timed247 full247 trials reps

/-! ### `binary32/isSignalingNaN` -/
@[inline] def op248 (x : Single) := ExecFloat.Binary.isSignaling x
def timed248 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed248 xs k (mixQuick acc (Digest.quick (op248 xs[k]!)))
def full248 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full248 xs k (Digest.full (op248 xs[k]!) (mixFull h k.toUInt64))
def run248 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isSignalingNaN" xs d timed248 full248 trials reps

/-! ### `binary32/signBit` -/
@[inline] def op249 (x : Single) := ExecFloat.Binary.signBit x
def timed249 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed249 xs k (mixQuick acc (Digest.quick (op249 xs[k]!)))
def full249 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full249 xs k (Digest.full (op249 xs[k]!) (mixFull h k.toUInt64))
def run249 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/signBit" xs d timed249 full249 trials reps

/-! ### `binary32/classify` -/
@[inline] def op250 (x : Single) := ExecFloat.Binary.classify x
def timed250 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed250 xs k (mixQuick acc (Digest.quick (op250 xs[k]!)))
def full250 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full250 xs k (Digest.full (op250 xs[k]!) (mixFull h k.toUInt64))
def run250 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/classify" xs d timed250 full250 trials reps

/-! ### `binary32/isCanonical` -/
@[inline] def op251 (x : Single) := ExecFloat.Binary.isCanonical x
def timed251 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed251 xs k (mixQuick acc (Digest.quick (op251 xs[k]!)))
def full251 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full251 xs k (Digest.full (op251 xs[k]!) (mixFull h k.toUInt64))
def run251 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/isCanonical" xs d timed251 full251 trials reps

/-! ### `binary64/isNaN` -/
@[inline] def op329 (x : Double) := ExecFloat.Binary.isNaN x
def timed329 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed329 xs k (mixQuick acc (Digest.quick (op329 xs[k]!)))
def full329 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full329 xs k (Digest.full (op329 xs[k]!) (mixFull h k.toUInt64))
def run329 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isNaN" xs d timed329 full329 trials reps

/-! ### `binary64/isNormal` -/
@[inline] def op330 (x : Double) := ExecFloat.Binary.isNormal x
def timed330 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed330 xs k (mixQuick acc (Digest.quick (op330 xs[k]!)))
def full330 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full330 xs k (Digest.full (op330 xs[k]!) (mixFull h k.toUInt64))
def run330 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isNormal" xs d timed330 full330 trials reps

/-! ### `binary64/isSubnormal` -/
@[inline] def op331 (x : Double) := ExecFloat.Binary.isSubnormal x
def timed331 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed331 xs k (mixQuick acc (Digest.quick (op331 xs[k]!)))
def full331 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full331 xs k (Digest.full (op331 xs[k]!) (mixFull h k.toUInt64))
def run331 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isSubnormal" xs d timed331 full331 trials reps

/-! ### `binary64/isZero` -/
@[inline] def op332 (x : Double) := ExecFloat.Binary.isZero x
def timed332 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed332 xs k (mixQuick acc (Digest.quick (op332 xs[k]!)))
def full332 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full332 xs k (Digest.full (op332 xs[k]!) (mixFull h k.toUInt64))
def run332 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isZero" xs d timed332 full332 trials reps

/-! ### `binary64/isFinite` -/
@[inline] def op333 (x : Double) := ExecFloat.Binary.isFinite x
def timed333 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed333 xs k (mixQuick acc (Digest.quick (op333 xs[k]!)))
def full333 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full333 xs k (Digest.full (op333 xs[k]!) (mixFull h k.toUInt64))
def run333 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isFinite" xs d timed333 full333 trials reps

/-! ### `binary64/isInfinite` -/
@[inline] def op334 (x : Double) := ExecFloat.Binary.isInfinite x
def timed334 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed334 xs k (mixQuick acc (Digest.quick (op334 xs[k]!)))
def full334 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full334 xs k (Digest.full (op334 xs[k]!) (mixFull h k.toUInt64))
def run334 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isInfinite" xs d timed334 full334 trials reps

/-! ### `binary64/isSignalingNaN` -/
@[inline] def op335 (x : Double) := ExecFloat.Binary.isSignaling x
def timed335 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed335 xs k (mixQuick acc (Digest.quick (op335 xs[k]!)))
def full335 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full335 xs k (Digest.full (op335 xs[k]!) (mixFull h k.toUInt64))
def run335 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isSignalingNaN" xs d timed335 full335 trials reps

/-! ### `binary64/signBit` -/
@[inline] def op336 (x : Double) := ExecFloat.Binary.signBit x
def timed336 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed336 xs k (mixQuick acc (Digest.quick (op336 xs[k]!)))
def full336 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full336 xs k (Digest.full (op336 xs[k]!) (mixFull h k.toUInt64))
def run336 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/signBit" xs d timed336 full336 trials reps

/-! ### `binary64/classify` -/
@[inline] def op337 (x : Double) := ExecFloat.Binary.classify x
def timed337 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed337 xs k (mixQuick acc (Digest.quick (op337 xs[k]!)))
def full337 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full337 xs k (Digest.full (op337 xs[k]!) (mixFull h k.toUInt64))
def run337 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/classify" xs d timed337 full337 trials reps

/-! ### `binary64/isCanonical` -/
@[inline] def op338 (x : Double) := ExecFloat.Binary.isCanonical x
def timed338 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed338 xs k (mixQuick acc (Digest.quick (op338 xs[k]!)))
def full338 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full338 xs k (Digest.full (op338 xs[k]!) (mixFull h k.toUInt64))
def run338 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/isCanonical" xs d timed338 full338 trials reps

/-! ### `binary128/isNaN` -/
@[inline] def op416 (x : Quad) := ExecFloat.Binary.isNaN x
def timed416 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed416 xs k (mixQuick acc (Digest.quick (op416 xs[k]!)))
def full416 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full416 xs k (Digest.full (op416 xs[k]!) (mixFull h k.toUInt64))
def run416 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isNaN" xs d timed416 full416 trials reps

/-! ### `binary128/isNormal` -/
@[inline] def op417 (x : Quad) := ExecFloat.Binary.isNormal x
def timed417 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed417 xs k (mixQuick acc (Digest.quick (op417 xs[k]!)))
def full417 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full417 xs k (Digest.full (op417 xs[k]!) (mixFull h k.toUInt64))
def run417 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isNormal" xs d timed417 full417 trials reps

/-! ### `binary128/isSubnormal` -/
@[inline] def op418 (x : Quad) := ExecFloat.Binary.isSubnormal x
def timed418 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed418 xs k (mixQuick acc (Digest.quick (op418 xs[k]!)))
def full418 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full418 xs k (Digest.full (op418 xs[k]!) (mixFull h k.toUInt64))
def run418 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isSubnormal" xs d timed418 full418 trials reps

/-! ### `binary128/isZero` -/
@[inline] def op419 (x : Quad) := ExecFloat.Binary.isZero x
def timed419 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed419 xs k (mixQuick acc (Digest.quick (op419 xs[k]!)))
def full419 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full419 xs k (Digest.full (op419 xs[k]!) (mixFull h k.toUInt64))
def run419 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isZero" xs d timed419 full419 trials reps

/-! ### `binary128/isFinite` -/
@[inline] def op420 (x : Quad) := ExecFloat.Binary.isFinite x
def timed420 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed420 xs k (mixQuick acc (Digest.quick (op420 xs[k]!)))
def full420 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full420 xs k (Digest.full (op420 xs[k]!) (mixFull h k.toUInt64))
def run420 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isFinite" xs d timed420 full420 trials reps

/-! ### `binary128/isInfinite` -/
@[inline] def op421 (x : Quad) := ExecFloat.Binary.isInfinite x
def timed421 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed421 xs k (mixQuick acc (Digest.quick (op421 xs[k]!)))
def full421 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full421 xs k (Digest.full (op421 xs[k]!) (mixFull h k.toUInt64))
def run421 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isInfinite" xs d timed421 full421 trials reps

/-! ### `binary128/isSignalingNaN` -/
@[inline] def op422 (x : Quad) := ExecFloat.Binary.isSignaling x
def timed422 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed422 xs k (mixQuick acc (Digest.quick (op422 xs[k]!)))
def full422 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full422 xs k (Digest.full (op422 xs[k]!) (mixFull h k.toUInt64))
def run422 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isSignalingNaN" xs d timed422 full422 trials reps

/-! ### `binary128/signBit` -/
@[inline] def op423 (x : Quad) := ExecFloat.Binary.signBit x
def timed423 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed423 xs k (mixQuick acc (Digest.quick (op423 xs[k]!)))
def full423 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full423 xs k (Digest.full (op423 xs[k]!) (mixFull h k.toUInt64))
def run423 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/signBit" xs d timed423 full423 trials reps

/-! ### `binary128/classify` -/
@[inline] def op424 (x : Quad) := ExecFloat.Binary.classify x
def timed424 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed424 xs k (mixQuick acc (Digest.quick (op424 xs[k]!)))
def full424 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full424 xs k (Digest.full (op424 xs[k]!) (mixFull h k.toUInt64))
def run424 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/classify" xs d timed424 full424 trials reps

/-! ### `binary128/isCanonical` -/
@[inline] def op425 (x : Quad) := ExecFloat.Binary.isCanonical x
def timed425 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed425 xs k (mixQuick acc (Digest.quick (op425 xs[k]!)))
def full425 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full425 xs k (Digest.full (op425 xs[k]!) (mixFull h k.toUInt64))
def run425 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/isCanonical" xs d timed425 full425 trials reps

/-! ### `binary256/isNaN` -/
@[inline] def op484 (x : Oct) := ExecFloat.Binary.isNaN x
def timed484 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed484 xs k (mixQuick acc (Digest.quick (op484 xs[k]!)))
def full484 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full484 xs k (Digest.full (op484 xs[k]!) (mixFull h k.toUInt64))
def run484 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/isNaN" xs d timed484 full484 trials reps

/-! ### `binary256/classify` -/
@[inline] def op485 (x : Oct) := ExecFloat.Binary.classify x
def timed485 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed485 xs k (mixQuick acc (Digest.quick (op485 xs[k]!)))
def full485 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full485 xs k (Digest.full (op485 xs[k]!) (mixFull h k.toUInt64))
def run485 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/classify" xs d timed485 full485 trials reps

/-! ### `posit32/isNaR` -/
@[inline] def op511 (x : P32) := ExecFloat.Posit.isNaR x
def timed511 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed511 xs k (mixQuick acc (Digest.quick (op511 xs[k]!)))
def full511 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full511 xs k (Digest.full (op511 xs[k]!) (mixFull h k.toUInt64))
def run511 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/isNaR" xs d timed511 full511 trials reps

/-! ### `posit32/isZero` -/
@[inline] def op512 (x : P32) := ExecFloat.Posit.isZero x
def timed512 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed512 xs k (mixQuick acc (Digest.quick (op512 xs[k]!)))
def full512 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full512 xs k (Digest.full (op512 xs[k]!) (mixFull h k.toUInt64))
def run512 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/isZero" xs d timed512 full512 trials reps

end FloatLibBenchmarks.Public.TimeOps
