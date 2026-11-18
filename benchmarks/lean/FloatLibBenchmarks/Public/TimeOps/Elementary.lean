/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.TimeOps.Support

/-!
# Elementary function timings

Elementary functions and certified evaluations on the shared operands.
Each loop retains its concrete format and operation for specialization.
-/

@[expose] public section

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ### `binary16/square` -/
@[inline] def op105 (x : Half) := ExecFloat.Binary.square x
def timed105 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed105 xs k (mixQuick acc (Digest.quick (op105 xs[k]!)))
def full105 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full105 xs k (Digest.full (op105 xs[k]!) (mixFull h k.toUInt64))
def run105 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/square" xs d timed105 full105 trials reps

/-! ### `binary16/exp` -/
@[inline] def op106 (x : Half) := ExecFloat.Binary.exp x
def timed106 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed106 xs k (mixQuick acc (Digest.quick (op106 xs[k]!)))
def full106 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full106 xs k (Digest.full (op106 xs[k]!) (mixFull h k.toUInt64))
def run106 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/exp" xs d timed106 full106 trials reps

/-! ### `binary16/log` -/
@[inline] def op107 (x : Half) := ExecFloat.Binary.log x
def timed107 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed107 xs k (mixQuick acc (Digest.quick (op107 xs[k]!)))
def full107 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full107 xs k (Digest.full (op107 xs[k]!) (mixFull h k.toUInt64))
def run107 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/log" xs d timed107 full107 trials reps

/-! ### `binary16/sin` -/
@[inline] def op108 (x : Half) := ExecFloat.Binary.sin x
def timed108 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed108 xs k (mixQuick acc (Digest.quick (op108 xs[k]!)))
def full108 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full108 xs k (Digest.full (op108 xs[k]!) (mixFull h k.toUInt64))
def run108 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/sin" xs d timed108 full108 trials reps

/-! ### `binary16/pow` -/
@[inline] def op109 (x y : Half) := ExecFloat.Binary.pow x y
def timed109 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed109 xs ys k (mixQuick acc (Digest.quick (op109 xs[k]! ys[k]!)))
def full109 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full109 xs ys k (Digest.full (op109 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run109 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/pow" xs ys (mixFull dx dy) timed109 full109 trials reps

/-! ### `binary16/pown` -/
@[inline] def op110 (x : Half) (n : Int) := ExecFloat.Binary.pown x n
def timed110 (xs : Array Half) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed110 xs ns k (mixQuick acc (Digest.quick (op110 xs[k]! ns[k]!)))
def full110 (xs : Array Half) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full110 xs ns k (Digest.full (op110 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run110 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ns, dn) := inPow count
  runXI "binary16/pown" xs ns (mixFull dx dn) timed110 full110 trials reps

/-! ### `binary16/rSqrt` -/
@[inline] def op111 (x : Half) := ExecFloat.Binary.rSqrt x
def timed111 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed111 xs k (mixQuick acc (Digest.quick (op111 xs[k]!)))
def full111 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full111 xs k (Digest.full (op111 xs[k]!) (mixFull h k.toUInt64))
def run111 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/rSqrt" xs d timed111 full111 trials reps

/-! ### `binary16/hypot` -/
@[inline] def op112 (x y : Half) := ExecFloat.Binary.hypot x y
def timed112 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed112 xs ys k (mixQuick acc (Digest.quick (op112 xs[k]! ys[k]!)))
def full112 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full112 xs ys k (Digest.full (op112 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run112 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/hypot" xs ys (mixFull dx dy) timed112 full112 trials reps

/-! ### `binary16/rootn3` -/
@[inline] def op113 (x : Half) := ExecFloat.Binary.rootn x 3
def timed113 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed113 xs k (mixQuick acc (Digest.quick (op113 xs[k]!)))
def full113 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full113 xs k (Digest.full (op113 xs[k]!) (mixFull h k.toUInt64))
def run113 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/rootn3" xs d timed113 full113 trials reps

/-! ### `binary16/exp[certify]` -/
@[inline] def op114 (x : Half) := (ExecFloat.Binary.Certified.exp x).toOption
def timed114 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed114 xs k (mixQuick acc (Digest.quick (op114 xs[k]!)))
def full114 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full114 xs k (Digest.full (op114 xs[k]!) (mixFull h k.toUInt64))
def run114 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/exp[certify]" xs d timed114 full114 trials reps

/-! ### `binary16/log[certify]` -/
@[inline] def op115 (x : Half) := (ExecFloat.Binary.Certified.log x).toOption
def timed115 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed115 xs k (mixQuick acc (Digest.quick (op115 xs[k]!)))
def full115 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full115 xs k (Digest.full (op115 xs[k]!) (mixFull h k.toUInt64))
def run115 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/log[certify]" xs d timed115 full115 trials reps

/-! ### `binary16/cos` -/
@[inline] def op116 (x : Half) := ExecFloat.Binary.cos x
def timed116 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed116 xs k (mixQuick acc (Digest.quick (op116 xs[k]!)))
def full116 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full116 xs k (Digest.full (op116 xs[k]!) (mixFull h k.toUInt64))
def run116 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/cos" xs d timed116 full116 trials reps

/-! ### `binary16/tanh` -/
@[inline] def op117 (x : Half) := ExecFloat.Binary.tanh x
def timed117 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed117 xs k (mixQuick acc (Digest.quick (op117 xs[k]!)))
def full117 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full117 xs k (Digest.full (op117 xs[k]!) (mixFull h k.toUInt64))
def run117 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/tanh" xs d timed117 full117 trials reps

/-! ### `binary16/expm1` -/
@[inline] def op118 (x : Half) := (ExecFloat.Binary.Certified.expm1 x).toOption
def timed118 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed118 xs k (mixQuick acc (Digest.quick (op118 xs[k]!)))
def full118 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full118 xs k (Digest.full (op118 xs[k]!) (mixFull h k.toUInt64))
def run118 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/expm1" xs d timed118 full118 trials reps

/-! ### `binary16/logp1` -/
@[inline] def op119 (x : Half) := (ExecFloat.Binary.Certified.logp1 x).toOption
def timed119 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed119 xs k (mixQuick acc (Digest.quick (op119 xs[k]!)))
def full119 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full119 xs k (Digest.full (op119 xs[k]!) (mixFull h k.toUInt64))
def run119 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/logp1" xs d timed119 full119 trials reps

/-! ### `bfloat16/square` -/
@[inline] def op192 (x : Brain) := ExecFloat.Binary.square x
def timed192 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed192 xs k (mixQuick acc (Digest.quick (op192 xs[k]!)))
def full192 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full192 xs k (Digest.full (op192 xs[k]!) (mixFull h k.toUInt64))
def run192 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/square" xs d timed192 full192 trials reps

/-! ### `bfloat16/exp` -/
@[inline] def op193 (x : Brain) := ExecFloat.Binary.exp x
def timed193 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed193 xs k (mixQuick acc (Digest.quick (op193 xs[k]!)))
def full193 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full193 xs k (Digest.full (op193 xs[k]!) (mixFull h k.toUInt64))
def run193 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/exp" xs d timed193 full193 trials reps

/-! ### `bfloat16/log` -/
@[inline] def op194 (x : Brain) := ExecFloat.Binary.log x
def timed194 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed194 xs k (mixQuick acc (Digest.quick (op194 xs[k]!)))
def full194 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full194 xs k (Digest.full (op194 xs[k]!) (mixFull h k.toUInt64))
def run194 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/log" xs d timed194 full194 trials reps

/-! ### `bfloat16/sin` -/
@[inline] def op195 (x : Brain) := ExecFloat.Binary.sin x
def timed195 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed195 xs k (mixQuick acc (Digest.quick (op195 xs[k]!)))
def full195 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full195 xs k (Digest.full (op195 xs[k]!) (mixFull h k.toUInt64))
def run195 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/sin" xs d timed195 full195 trials reps

/-! ### `bfloat16/pow` -/
@[inline] def op196 (x y : Brain) := ExecFloat.Binary.pow x y
def timed196 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed196 xs ys k (mixQuick acc (Digest.quick (op196 xs[k]! ys[k]!)))
def full196 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full196 xs ys k (Digest.full (op196 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run196 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/pow" xs ys (mixFull dx dy) timed196 full196 trials reps

/-! ### `bfloat16/pown` -/
@[inline] def op197 (x : Brain) (n : Int) := ExecFloat.Binary.pown x n
def timed197 (xs : Array Brain) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed197 xs ns k (mixQuick acc (Digest.quick (op197 xs[k]! ns[k]!)))
def full197 (xs : Array Brain) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full197 xs ns k (Digest.full (op197 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run197 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ns, dn) := inPow count
  runXI "bfloat16/pown" xs ns (mixFull dx dn) timed197 full197 trials reps

/-! ### `bfloat16/rSqrt` -/
@[inline] def op198 (x : Brain) := ExecFloat.Binary.rSqrt x
def timed198 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed198 xs k (mixQuick acc (Digest.quick (op198 xs[k]!)))
def full198 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full198 xs k (Digest.full (op198 xs[k]!) (mixFull h k.toUInt64))
def run198 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/rSqrt" xs d timed198 full198 trials reps

/-! ### `bfloat16/hypot` -/
@[inline] def op199 (x y : Brain) := ExecFloat.Binary.hypot x y
def timed199 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed199 xs ys k (mixQuick acc (Digest.quick (op199 xs[k]! ys[k]!)))
def full199 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full199 xs ys k (Digest.full (op199 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run199 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/hypot" xs ys (mixFull dx dy) timed199 full199 trials reps

/-! ### `bfloat16/rootn3` -/
@[inline] def op200 (x : Brain) := ExecFloat.Binary.rootn x 3
def timed200 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed200 xs k (mixQuick acc (Digest.quick (op200 xs[k]!)))
def full200 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full200 xs k (Digest.full (op200 xs[k]!) (mixFull h k.toUInt64))
def run200 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/rootn3" xs d timed200 full200 trials reps

/-! ### `bfloat16/exp[certify]` -/
@[inline] def op201 (x : Brain) := (ExecFloat.Binary.Certified.exp x).toOption
def timed201 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed201 xs k (mixQuick acc (Digest.quick (op201 xs[k]!)))
def full201 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full201 xs k (Digest.full (op201 xs[k]!) (mixFull h k.toUInt64))
def run201 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/exp[certify]" xs d timed201 full201 trials reps

/-! ### `bfloat16/log[certify]` -/
@[inline] def op202 (x : Brain) := (ExecFloat.Binary.Certified.log x).toOption
def timed202 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed202 xs k (mixQuick acc (Digest.quick (op202 xs[k]!)))
def full202 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full202 xs k (Digest.full (op202 xs[k]!) (mixFull h k.toUInt64))
def run202 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/log[certify]" xs d timed202 full202 trials reps

/-! ### `bfloat16/cos` -/
@[inline] def op203 (x : Brain) := ExecFloat.Binary.cos x
def timed203 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed203 xs k (mixQuick acc (Digest.quick (op203 xs[k]!)))
def full203 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full203 xs k (Digest.full (op203 xs[k]!) (mixFull h k.toUInt64))
def run203 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/cos" xs d timed203 full203 trials reps

/-! ### `bfloat16/tanh` -/
@[inline] def op204 (x : Brain) := ExecFloat.Binary.tanh x
def timed204 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed204 xs k (mixQuick acc (Digest.quick (op204 xs[k]!)))
def full204 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full204 xs k (Digest.full (op204 xs[k]!) (mixFull h k.toUInt64))
def run204 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/tanh" xs d timed204 full204 trials reps

/-! ### `bfloat16/expm1` -/
@[inline] def op205 (x : Brain) := (ExecFloat.Binary.Certified.expm1 x).toOption
def timed205 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed205 xs k (mixQuick acc (Digest.quick (op205 xs[k]!)))
def full205 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full205 xs k (Digest.full (op205 xs[k]!) (mixFull h k.toUInt64))
def run205 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/expm1" xs d timed205 full205 trials reps

/-! ### `bfloat16/logp1` -/
@[inline] def op206 (x : Brain) := (ExecFloat.Binary.Certified.logp1 x).toOption
def timed206 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed206 xs k (mixQuick acc (Digest.quick (op206 xs[k]!)))
def full206 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full206 xs k (Digest.full (op206 xs[k]!) (mixFull h k.toUInt64))
def run206 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/logp1" xs d timed206 full206 trials reps

/-! ### `binary32/square` -/
@[inline] def op279 (x : Single) := ExecFloat.Binary.square x
def timed279 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed279 xs k (mixQuick acc (Digest.quick (op279 xs[k]!)))
def full279 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full279 xs k (Digest.full (op279 xs[k]!) (mixFull h k.toUInt64))
def run279 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/square" xs d timed279 full279 trials reps

/-! ### `binary32/exp` -/
@[inline] def op280 (x : Single) := ExecFloat.Binary.exp x
def timed280 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed280 xs k (mixQuick acc (Digest.quick (op280 xs[k]!)))
def full280 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full280 xs k (Digest.full (op280 xs[k]!) (mixFull h k.toUInt64))
def run280 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/exp" xs d timed280 full280 trials reps

/-! ### `binary32/log` -/
@[inline] def op281 (x : Single) := ExecFloat.Binary.log x
def timed281 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed281 xs k (mixQuick acc (Digest.quick (op281 xs[k]!)))
def full281 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full281 xs k (Digest.full (op281 xs[k]!) (mixFull h k.toUInt64))
def run281 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/log" xs d timed281 full281 trials reps

/-! ### `binary32/sin` -/
@[inline] def op282 (x : Single) := ExecFloat.Binary.sin x
def timed282 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed282 xs k (mixQuick acc (Digest.quick (op282 xs[k]!)))
def full282 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full282 xs k (Digest.full (op282 xs[k]!) (mixFull h k.toUInt64))
def run282 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/sin" xs d timed282 full282 trials reps

/-! ### `binary32/pow` -/
@[inline] def op283 (x y : Single) := ExecFloat.Binary.pow x y
def timed283 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed283 xs ys k (mixQuick acc (Digest.quick (op283 xs[k]! ys[k]!)))
def full283 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full283 xs ys k (Digest.full (op283 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run283 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/pow" xs ys (mixFull dx dy) timed283 full283 trials reps

/-! ### `binary32/pown` -/
@[inline] def op284 (x : Single) (n : Int) := ExecFloat.Binary.pown x n
def timed284 (xs : Array Single) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed284 xs ns k (mixQuick acc (Digest.quick (op284 xs[k]! ns[k]!)))
def full284 (xs : Array Single) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full284 xs ns k (Digest.full (op284 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run284 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ns, dn) := inPow count
  runXI "binary32/pown" xs ns (mixFull dx dn) timed284 full284 trials reps

/-! ### `binary32/rSqrt` -/
@[inline] def op285 (x : Single) := ExecFloat.Binary.rSqrt x
def timed285 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed285 xs k (mixQuick acc (Digest.quick (op285 xs[k]!)))
def full285 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full285 xs k (Digest.full (op285 xs[k]!) (mixFull h k.toUInt64))
def run285 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/rSqrt" xs d timed285 full285 trials reps

/-! ### `binary32/hypot` -/
@[inline] def op286 (x y : Single) := ExecFloat.Binary.hypot x y
def timed286 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed286 xs ys k (mixQuick acc (Digest.quick (op286 xs[k]! ys[k]!)))
def full286 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full286 xs ys k (Digest.full (op286 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run286 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/hypot" xs ys (mixFull dx dy) timed286 full286 trials reps

/-! ### `binary32/rootn3` -/
@[inline] def op287 (x : Single) := ExecFloat.Binary.rootn x 3
def timed287 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed287 xs k (mixQuick acc (Digest.quick (op287 xs[k]!)))
def full287 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full287 xs k (Digest.full (op287 xs[k]!) (mixFull h k.toUInt64))
def run287 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/rootn3" xs d timed287 full287 trials reps

/-! ### `binary32/exp[certify]` -/
@[inline] def op288 (x : Single) := (ExecFloat.Binary.Certified.exp x).toOption
def timed288 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed288 xs k (mixQuick acc (Digest.quick (op288 xs[k]!)))
def full288 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full288 xs k (Digest.full (op288 xs[k]!) (mixFull h k.toUInt64))
def run288 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/exp[certify]" xs d timed288 full288 trials reps

/-! ### `binary32/log[certify]` -/
@[inline] def op289 (x : Single) := (ExecFloat.Binary.Certified.log x).toOption
def timed289 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed289 xs k (mixQuick acc (Digest.quick (op289 xs[k]!)))
def full289 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full289 xs k (Digest.full (op289 xs[k]!) (mixFull h k.toUInt64))
def run289 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/log[certify]" xs d timed289 full289 trials reps

/-! ### `binary32/cos` -/
@[inline] def op290 (x : Single) := ExecFloat.Binary.cos x
def timed290 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed290 xs k (mixQuick acc (Digest.quick (op290 xs[k]!)))
def full290 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full290 xs k (Digest.full (op290 xs[k]!) (mixFull h k.toUInt64))
def run290 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/cos" xs d timed290 full290 trials reps

/-! ### `binary32/tanh` -/
@[inline] def op291 (x : Single) := ExecFloat.Binary.tanh x
def timed291 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed291 xs k (mixQuick acc (Digest.quick (op291 xs[k]!)))
def full291 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full291 xs k (Digest.full (op291 xs[k]!) (mixFull h k.toUInt64))
def run291 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/tanh" xs d timed291 full291 trials reps

/-! ### `binary32/expm1` -/
@[inline] def op292 (x : Single) := (ExecFloat.Binary.Certified.expm1 x).toOption
def timed292 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed292 xs k (mixQuick acc (Digest.quick (op292 xs[k]!)))
def full292 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full292 xs k (Digest.full (op292 xs[k]!) (mixFull h k.toUInt64))
def run292 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/expm1" xs d timed292 full292 trials reps

/-! ### `binary32/logp1` -/
@[inline] def op293 (x : Single) := (ExecFloat.Binary.Certified.logp1 x).toOption
def timed293 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed293 xs k (mixQuick acc (Digest.quick (op293 xs[k]!)))
def full293 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full293 xs k (Digest.full (op293 xs[k]!) (mixFull h k.toUInt64))
def run293 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/logp1" xs d timed293 full293 trials reps

/-! ### `binary64/square` -/
@[inline] def op366 (x : Double) := ExecFloat.Binary.square x
def timed366 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed366 xs k (mixQuick acc (Digest.quick (op366 xs[k]!)))
def full366 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full366 xs k (Digest.full (op366 xs[k]!) (mixFull h k.toUInt64))
def run366 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/square" xs d timed366 full366 trials reps

/-! ### `binary64/exp` -/
@[inline] def op367 (x : Double) := ExecFloat.Binary.exp x
def timed367 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed367 xs k (mixQuick acc (Digest.quick (op367 xs[k]!)))
def full367 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full367 xs k (Digest.full (op367 xs[k]!) (mixFull h k.toUInt64))
def run367 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/exp" xs d timed367 full367 trials reps

/-! ### `binary64/log` -/
@[inline] def op368 (x : Double) := ExecFloat.Binary.log x
def timed368 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed368 xs k (mixQuick acc (Digest.quick (op368 xs[k]!)))
def full368 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full368 xs k (Digest.full (op368 xs[k]!) (mixFull h k.toUInt64))
def run368 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/log" xs d timed368 full368 trials reps

/-! ### `binary64/sin` -/
@[inline] def op369 (x : Double) := ExecFloat.Binary.sin x
def timed369 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed369 xs k (mixQuick acc (Digest.quick (op369 xs[k]!)))
def full369 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full369 xs k (Digest.full (op369 xs[k]!) (mixFull h k.toUInt64))
def run369 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/sin" xs d timed369 full369 trials reps

/-! ### `binary64/pow` -/
@[inline] def op370 (x y : Double) := ExecFloat.Binary.pow x y
def timed370 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed370 xs ys k (mixQuick acc (Digest.quick (op370 xs[k]! ys[k]!)))
def full370 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full370 xs ys k (Digest.full (op370 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run370 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/pow" xs ys (mixFull dx dy) timed370 full370 trials reps

/-! ### `binary64/pown` -/
@[inline] def op371 (x : Double) (n : Int) := ExecFloat.Binary.pown x n
def timed371 (xs : Array Double) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed371 xs ns k (mixQuick acc (Digest.quick (op371 xs[k]! ns[k]!)))
def full371 (xs : Array Double) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full371 xs ns k (Digest.full (op371 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run371 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ns, dn) := inPow count
  runXI "binary64/pown" xs ns (mixFull dx dn) timed371 full371 trials reps

/-! ### `binary64/rSqrt` -/
@[inline] def op372 (x : Double) := ExecFloat.Binary.rSqrt x
def timed372 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed372 xs k (mixQuick acc (Digest.quick (op372 xs[k]!)))
def full372 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full372 xs k (Digest.full (op372 xs[k]!) (mixFull h k.toUInt64))
def run372 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/rSqrt" xs d timed372 full372 trials reps

/-! ### `binary64/hypot` -/
@[inline] def op373 (x y : Double) := ExecFloat.Binary.hypot x y
def timed373 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed373 xs ys k (mixQuick acc (Digest.quick (op373 xs[k]! ys[k]!)))
def full373 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full373 xs ys k (Digest.full (op373 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run373 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/hypot" xs ys (mixFull dx dy) timed373 full373 trials reps

/-! ### `binary64/rootn3` -/
@[inline] def op374 (x : Double) := ExecFloat.Binary.rootn x 3
def timed374 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed374 xs k (mixQuick acc (Digest.quick (op374 xs[k]!)))
def full374 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full374 xs k (Digest.full (op374 xs[k]!) (mixFull h k.toUInt64))
def run374 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/rootn3" xs d timed374 full374 trials reps

/-! ### `binary64/exp[certify]` -/
@[inline] def op375 (x : Double) := (ExecFloat.Binary.Certified.exp x).toOption
def timed375 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed375 xs k (mixQuick acc (Digest.quick (op375 xs[k]!)))
def full375 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full375 xs k (Digest.full (op375 xs[k]!) (mixFull h k.toUInt64))
def run375 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/exp[certify]" xs d timed375 full375 trials reps

/-! ### `binary64/log[certify]` -/
@[inline] def op376 (x : Double) := (ExecFloat.Binary.Certified.log x).toOption
def timed376 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed376 xs k (mixQuick acc (Digest.quick (op376 xs[k]!)))
def full376 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full376 xs k (Digest.full (op376 xs[k]!) (mixFull h k.toUInt64))
def run376 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/log[certify]" xs d timed376 full376 trials reps

/-! ### `binary64/cos` -/
@[inline] def op377 (x : Double) := ExecFloat.Binary.cos x
def timed377 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed377 xs k (mixQuick acc (Digest.quick (op377 xs[k]!)))
def full377 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full377 xs k (Digest.full (op377 xs[k]!) (mixFull h k.toUInt64))
def run377 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/cos" xs d timed377 full377 trials reps

/-! ### `binary64/tanh` -/
@[inline] def op378 (x : Double) := ExecFloat.Binary.tanh x
def timed378 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed378 xs k (mixQuick acc (Digest.quick (op378 xs[k]!)))
def full378 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full378 xs k (Digest.full (op378 xs[k]!) (mixFull h k.toUInt64))
def run378 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/tanh" xs d timed378 full378 trials reps

/-! ### `binary64/expm1` -/
@[inline] def op379 (x : Double) := (ExecFloat.Binary.Certified.expm1 x).toOption
def timed379 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed379 xs k (mixQuick acc (Digest.quick (op379 xs[k]!)))
def full379 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full379 xs k (Digest.full (op379 xs[k]!) (mixFull h k.toUInt64))
def run379 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/expm1" xs d timed379 full379 trials reps

/-! ### `binary64/logp1` -/
@[inline] def op380 (x : Double) := (ExecFloat.Binary.Certified.logp1 x).toOption
def timed380 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed380 xs k (mixQuick acc (Digest.quick (op380 xs[k]!)))
def full380 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full380 xs k (Digest.full (op380 xs[k]!) (mixFull h k.toUInt64))
def run380 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/logp1" xs d timed380 full380 trials reps

/-! ### `binary128/square` -/
@[inline] def op453 (x : Quad) := ExecFloat.Binary.square x
def timed453 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed453 xs k (mixQuick acc (Digest.quick (op453 xs[k]!)))
def full453 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full453 xs k (Digest.full (op453 xs[k]!) (mixFull h k.toUInt64))
def run453 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/square" xs d timed453 full453 trials reps

/-! ### `binary128/exp` -/
@[inline] def op454 (x : Quad) := ExecFloat.Binary.exp x
def timed454 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed454 xs k (mixQuick acc (Digest.quick (op454 xs[k]!)))
def full454 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full454 xs k (Digest.full (op454 xs[k]!) (mixFull h k.toUInt64))
def run454 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/exp" xs d timed454 full454 trials reps

/-! ### `binary128/log` -/
@[inline] def op455 (x : Quad) := ExecFloat.Binary.log x
def timed455 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed455 xs k (mixQuick acc (Digest.quick (op455 xs[k]!)))
def full455 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full455 xs k (Digest.full (op455 xs[k]!) (mixFull h k.toUInt64))
def run455 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/log" xs d timed455 full455 trials reps

/-! ### `binary128/sin` -/
@[inline] def op456 (x : Quad) := ExecFloat.Binary.sin x
def timed456 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed456 xs k (mixQuick acc (Digest.quick (op456 xs[k]!)))
def full456 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full456 xs k (Digest.full (op456 xs[k]!) (mixFull h k.toUInt64))
def run456 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/sin" xs d timed456 full456 trials reps

/-! ### `binary128/pow` -/
@[inline] def op457 (x y : Quad) := ExecFloat.Binary.pow x y
def timed457 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed457 xs ys k (mixQuick acc (Digest.quick (op457 xs[k]! ys[k]!)))
def full457 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full457 xs ys k (Digest.full (op457 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run457 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/pow" xs ys (mixFull dx dy) timed457 full457 trials reps

/-! ### `binary128/pown` -/
@[inline] def op458 (x : Quad) (n : Int) := ExecFloat.Binary.pown x n
def timed458 (xs : Array Quad) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed458 xs ns k (mixQuick acc (Digest.quick (op458 xs[k]! ns[k]!)))
def full458 (xs : Array Quad) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full458 xs ns k (Digest.full (op458 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run458 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ns, dn) := inPow count
  runXI "binary128/pown" xs ns (mixFull dx dn) timed458 full458 trials reps

/-! ### `binary128/rSqrt` -/
@[inline] def op459 (x : Quad) := ExecFloat.Binary.rSqrt x
def timed459 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed459 xs k (mixQuick acc (Digest.quick (op459 xs[k]!)))
def full459 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full459 xs k (Digest.full (op459 xs[k]!) (mixFull h k.toUInt64))
def run459 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/rSqrt" xs d timed459 full459 trials reps

/-! ### `binary128/hypot` -/
@[inline] def op460 (x y : Quad) := ExecFloat.Binary.hypot x y
def timed460 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed460 xs ys k (mixQuick acc (Digest.quick (op460 xs[k]! ys[k]!)))
def full460 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full460 xs ys k (Digest.full (op460 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run460 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/hypot" xs ys (mixFull dx dy) timed460 full460 trials reps

/-! ### `binary128/rootn3` -/
@[inline] def op461 (x : Quad) := ExecFloat.Binary.rootn x 3
def timed461 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed461 xs k (mixQuick acc (Digest.quick (op461 xs[k]!)))
def full461 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full461 xs k (Digest.full (op461 xs[k]!) (mixFull h k.toUInt64))
def run461 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/rootn3" xs d timed461 full461 trials reps

/-! ### `binary128/exp[certify]` -/
@[inline] def op462 (x : Quad) := (ExecFloat.Binary.Certified.exp x).toOption
def timed462 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed462 xs k (mixQuick acc (Digest.quick (op462 xs[k]!)))
def full462 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full462 xs k (Digest.full (op462 xs[k]!) (mixFull h k.toUInt64))
def run462 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/exp[certify]" xs d timed462 full462 trials reps

/-! ### `binary128/log[certify]` -/
@[inline] def op463 (x : Quad) := (ExecFloat.Binary.Certified.log x).toOption
def timed463 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed463 xs k (mixQuick acc (Digest.quick (op463 xs[k]!)))
def full463 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full463 xs k (Digest.full (op463 xs[k]!) (mixFull h k.toUInt64))
def run463 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/log[certify]" xs d timed463 full463 trials reps

/-! ### `binary128/cos` -/
@[inline] def op464 (x : Quad) := ExecFloat.Binary.cos x
def timed464 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed464 xs k (mixQuick acc (Digest.quick (op464 xs[k]!)))
def full464 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full464 xs k (Digest.full (op464 xs[k]!) (mixFull h k.toUInt64))
def run464 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/cos" xs d timed464 full464 trials reps

/-! ### `binary128/tanh` -/
@[inline] def op465 (x : Quad) := ExecFloat.Binary.tanh x
def timed465 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed465 xs k (mixQuick acc (Digest.quick (op465 xs[k]!)))
def full465 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full465 xs k (Digest.full (op465 xs[k]!) (mixFull h k.toUInt64))
def run465 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/tanh" xs d timed465 full465 trials reps

/-! ### `binary128/expm1` -/
@[inline] def op466 (x : Quad) := (ExecFloat.Binary.Certified.expm1 x).toOption
def timed466 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed466 xs k (mixQuick acc (Digest.quick (op466 xs[k]!)))
def full466 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full466 xs k (Digest.full (op466 xs[k]!) (mixFull h k.toUInt64))
def run466 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/expm1" xs d timed466 full466 trials reps

/-! ### `binary128/logp1` -/
@[inline] def op467 (x : Quad) := (ExecFloat.Binary.Certified.logp1 x).toOption
def timed467 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed467 xs k (mixQuick acc (Digest.quick (op467 xs[k]!)))
def full467 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full467 xs k (Digest.full (op467 xs[k]!) (mixFull h k.toUInt64))
def run467 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/logp1" xs d timed467 full467 trials reps

/-! ### `binary256/square` -/
@[inline] def op494 (x : Oct) := ExecFloat.Binary.square x
def timed494 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed494 xs k (mixQuick acc (Digest.quick (op494 xs[k]!)))
def full494 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full494 xs k (Digest.full (op494 xs[k]!) (mixFull h k.toUInt64))
def run494 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/square" xs d timed494 full494 trials reps

/-! ### `binary256/exp` -/
@[inline] def op495 (x : Oct) := ExecFloat.Binary.exp x
def timed495 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed495 xs k (mixQuick acc (Digest.quick (op495 xs[k]!)))
def full495 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full495 xs k (Digest.full (op495 xs[k]!) (mixFull h k.toUInt64))
def run495 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/exp" xs d timed495 full495 trials reps

/-! ### `posit32/exp` -/
@[inline] def op515 (x : P32) := ExecFloat.Posit.exp x
def timed515 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed515 xs k (mixQuick acc (Digest.quick (op515 xs[k]!)))
def full515 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full515 xs k (Digest.full (op515 xs[k]!) (mixFull h k.toUInt64))
def run515 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/exp" xs d timed515 full515 trials reps

/-! ### `posit32/log` -/
@[inline] def op516 (x : P32) := ExecFloat.Posit.log x
def timed516 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed516 xs k (mixQuick acc (Digest.quick (op516 xs[k]!)))
def full516 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full516 xs k (Digest.full (op516 xs[k]!) (mixFull h k.toUInt64))
def run516 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/log" xs d timed516 full516 trials reps

/-! ### `posit32/sin` -/
@[inline] def op517 (x : P32) := ExecFloat.Posit.sin x
def timed517 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed517 xs k (mixQuick acc (Digest.quick (op517 xs[k]!)))
def full517 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full517 xs k (Digest.full (op517 xs[k]!) (mixFull h k.toUInt64))
def run517 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/sin" xs d timed517 full517 trials reps

/-! ### `posit32/log2` -/
@[inline] def op518 (x : P32) := ExecFloat.Posit.log2 x
def timed518 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed518 xs k (mixQuick acc (Digest.quick (op518 xs[k]!)))
def full518 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full518 xs k (Digest.full (op518 xs[k]!) (mixFull h k.toUInt64))
def run518 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/log2" xs d timed518 full518 trials reps

/-! ### `posit32/rSqrt` -/
@[inline] def op519 (x : P32) := ExecFloat.Posit.rSqrt x
def timed519 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed519 xs k (mixQuick acc (Digest.quick (op519 xs[k]!)))
def full519 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full519 xs k (Digest.full (op519 xs[k]!) (mixFull h k.toUInt64))
def run519 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/rSqrt" xs d timed519 full519 trials reps

/-! ### `posit32/hypot` -/
@[inline] def op520 (x y : P32) := ExecFloat.Posit.hypot x y
def timed520 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed520 xs ys k (mixQuick acc (Digest.quick (op520 xs[k]! ys[k]!)))
def full520 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full520 xs ys k (Digest.full (op520 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run520 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/hypot" xs ys (mixFull dx dy) timed520 full520 trials reps

/-! ### `posit32/pown` -/
@[inline] def op521 (x : P32) (n : Int) := ExecFloat.Posit.powInt x n
def timed521 (xs : Array P32) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed521 xs ns k (mixQuick acc (Digest.quick (op521 xs[k]! ns[k]!)))
def full521 (xs : Array P32) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full521 xs ns k (Digest.full (op521 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run521 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ns, dn) := inPow count
  runXI "posit32/pown" xs ns (mixFull dx dn) timed521 full521 trials reps

/-! ### `posit32/cos` -/
@[inline] def op522 (x : P32) := ExecFloat.Posit.cos x
def timed522 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed522 xs k (mixQuick acc (Digest.quick (op522 xs[k]!)))
def full522 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full522 xs k (Digest.full (op522 xs[k]!) (mixFull h k.toUInt64))
def run522 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/cos" xs d timed522 full522 trials reps

/-! ### `posit32/tan` -/
@[inline] def op523 (x : P32) := ExecFloat.Posit.tan x
def timed523 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed523 xs k (mixQuick acc (Digest.quick (op523 xs[k]!)))
def full523 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full523 xs k (Digest.full (op523 xs[k]!) (mixFull h k.toUInt64))
def run523 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/tan" xs d timed523 full523 trials reps

/-! ### `posit32/arcTan` -/
@[inline] def op524 (x : P32) := ExecFloat.Posit.arcTan x
def timed524 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed524 xs k (mixQuick acc (Digest.quick (op524 xs[k]!)))
def full524 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full524 xs k (Digest.full (op524 xs[k]!) (mixFull h k.toUInt64))
def run524 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/arcTan" xs d timed524 full524 trials reps

/-! ### `posit32/expm1` -/
@[inline] def op525 (x : P32) := ExecFloat.Posit.expMinus1 x
def timed525 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed525 xs k (mixQuick acc (Digest.quick (op525 xs[k]!)))
def full525 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full525 xs k (Digest.full (op525 xs[k]!) (mixFull h k.toUInt64))
def run525 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/expm1" xs d timed525 full525 trials reps

/-! ### `posit32/logp1` -/
@[inline] def op526 (x : P32) := ExecFloat.Posit.logPlus1 x
def timed526 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed526 xs k (mixQuick acc (Digest.quick (op526 xs[k]!)))
def full526 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full526 xs k (Digest.full (op526 xs[k]!) (mixFull h k.toUInt64))
def run526 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/logp1" xs d timed526 full526 trials reps

/-! ### `posit32/log10` -/
@[inline] def op527 (x : P32) := ExecFloat.Posit.log10 x
def timed527 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed527 xs k (mixQuick acc (Digest.quick (op527 xs[k]!)))
def full527 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full527 xs k (Digest.full (op527 xs[k]!) (mixFull h k.toUInt64))
def run527 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/log10" xs d timed527 full527 trials reps

/-! ### `posit32/tanH` -/
@[inline] def op528 (x : P32) := ExecFloat.Posit.tanH x
def timed528 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed528 xs k (mixQuick acc (Digest.quick (op528 xs[k]!)))
def full528 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full528 xs k (Digest.full (op528 xs[k]!) (mixFull h k.toUInt64))
def run528 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/tanH" xs d timed528 full528 trials reps

/-! ### `posit32/rootn3` -/
@[inline] def op529 (x : P32) := ExecFloat.Posit.rootN x 3
def timed529 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed529 xs k (mixQuick acc (Digest.quick (op529 xs[k]!)))
def full529 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full529 xs k (Digest.full (op529 xs[k]!) (mixFull h k.toUInt64))
def run529 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/rootn3" xs d timed529 full529 trials reps

/-! ### `posit32/compound` -/
@[inline] def op530 (x : P32) (n : Int) := ExecFloat.Posit.compound x n
def timed530 (xs : Array P32) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed530 xs ns k (mixQuick acc (Digest.quick (op530 xs[k]! ns[k]!)))
def full530 (xs : Array P32) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full530 xs ns k (Digest.full (op530 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run530 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ns, dn) := inPow count
  runXI "posit32/compound" xs ns (mixFull dx dn) timed530 full530 trials reps

/-! ### `posit32/fMM` -/
@[inline] def op531 (x y z : P32) := ExecFloat.Posit.fMM x y z
def timed531 (xs ys zs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed531 xs ys zs k (mixQuick acc (Digest.quick (op531 xs[k]! ys[k]! zs[k]!)))
def full531 (xs ys zs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full531 xs ys zs k (Digest.full (op531 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run531 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  let (zs, dz) := inP32 seedZ count
  runT "posit32/fMM" xs ys zs (mixFull (mixFull dx dy) dz) timed531 full531 trials reps

end FloatLibBenchmarks.Public.TimeOps
