/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLibBenchmarks.Support.Posit
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast

/-!
# Timing of the public operations beyond the six arithmetic kernels

Every cell times one public operation of a configured binary format (`ExecFloat.Binary`) or of
`ExecFloat.Posit 32`: conversions between formats and to and from 64-bit integers, integral
rounding, remainder, comparisons, minimum and maximum, adjacent values, `scale` and
`binaryExponent`, sign operations, classification, text output and input, directed-rounding and
status-bearing arithmetic, squaring, and the elementary functions.

Operands come from a fixed-seed SplitMix64 generator that mixes ordinary magnitudes, tiny and huge
normals, subnormals, integers and half-integers, signed zeros, infinities, quiet and signaling
NaNs, extreme finite values, and uniformly random words. Operands are decoded once before timing.
Each timed loop is monomorphic in its format and operation and folds the result into a `UInt64`.
An untimed pass first folds the complete result (every encoding bit, every status flag, and the
ternary value of a status-bearing result) into a position-sensitive hash, so two builds can be
compared for identical results.

Cells named `ref.OP[CATEGORY]` time the six default operations themselves (`ExecFloat.add`,
`sub`, `mul`, `div`, `sqrt`, `fma`) on the same mixed operands, or on one operand category, as a
reference for the other cells.

Cells named `OP[MODE]` and `OP[status]` time an operation with `(mode := MODE)` or with
`(status := true)`. Cells named `sqrt[status,runtime]` call `Model.sqrt x (status := true)` from a
loop that receives the format as an argument, so they time the compiled generic body rather than a
copy specialized to a closed format. Their operands and complete digest are those of the
configured `sqrt[status]` cell of the same format, so both cells report the same hash.

`execFloatTimeOps list` prints the cell names, and `execFloatTimeOps run CELL COUNT TRIALS REPS`
runs one cell on `COUNT` operands, repeating the loop `REPS` times in each of `TRIALS` trials.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Representations

namespace FloatLibBenchmarks.Public.TimeOps

/-! ## Deterministic operands -/

/-- SplitMix64 generator state. -/
structure Rng where
  state : UInt64

@[inline] def Rng.next (rng : Rng) : UInt64 × Rng :=
  let s := rng.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A uniformly random natural number below `2 ^ bits`. -/
def Rng.bits (rng : Rng) (bits : Nat) : Nat × Rng := Id.run do
  let mut r := rng
  let mut acc := 0
  let mut filled := 0
  while filled < bits do
    let (w, r') := r.next
    r := r'
    acc := acc ||| (w.toNat <<< filled)
    filled := filled + 64
  return (acc % 2 ^ bits, r)

/-- A draw below a small positive bound: the next generator word modulo the bound.
The residues are not quite uniform when the bound does not divide `2 ^ 64`. -/
@[inline] def Rng.below (rng : Rng) (bound : Nat) : Nat × Rng :=
  let (w, r) := rng.next
  (w.toNat % max bound 1, r)

/--
One binary encoding with `e` exponent and `m` fraction bits: 40% ordinary magnitudes within
`2^±20` of one, 10% tiny normals, 10% huge normals, 10% subnormals, 10% integers and
half-integers, 10% special values, and 10% uniformly random words. A `forced` category value
(0, 45, 55, 65, 75, 85, or 95) draws every operand from that one category instead.
-/
def binaryPatternIn (forced : Option Nat) (e m : Nat) (rng : Rng) : Nat × Rng :=
  let allOnes := 2 ^ e - 1
  let bias := 2 ^ (e - 1) - 1
  let (category, rng) := rng.below 100
  let category := forced.getD category
  let (signWord, rng) := rng.next
  let sign := (signWord &&& 1).toNat
  let (fraction, rng) := rng.bits m
  let pack := fun (exponent field : Nat) => (sign <<< (e + m)) ||| (exponent <<< m) ||| field
  if category < 40 then
    let span := min 20 (bias - 1)
    let (d, rng) := rng.below (2 * span + 1)
    (pack (bias + d - span) fraction, rng)
  else if category < 50 then
    let (d, rng) := rng.below (min 8 (bias - 1))
    (pack (1 + d) fraction, rng)
  else if category < 60 then
    let (d, rng) := rng.below (min 8 (bias - 1))
    (pack (allOnes - 1 - d) fraction, rng)
  else if category < 70 then
    (pack 0 (if fraction = 0 then 1 else fraction), rng)
  else if category < 80 then
    let (k, rng) := rng.below (min (m + 1) 31)
    let keep := k + 1
    let field := if m ≤ keep then fraction else (fraction >>> (m - keep)) <<< (m - keep)
    (pack (bias + k) field, rng)
  else if category < 90 then
    let (which, rng) := rng.below 12
    let quiet := 2 ^ (m - 1)
    let word :=
      match which with
      | 0 => pack 0 0
      | 1 => pack allOnes 0
      | 2 => pack allOnes (quiet ||| fraction % quiet)
      | 3 => pack allOnes (max 1 (fraction % quiet))
      | 4 => pack (allOnes - 1) (2 ^ m - 1)
      | 5 => pack 1 0
      | 6 => pack 0 1
      | 7 => pack bias 0
      | 8 => pack (bias - 1) 0
      | 9 => pack (bias + 1) quiet
      | 10 => pack 0 (2 ^ m - 1)
      | _ => pack (bias + 1) 0
    (word, rng)
  else
    rng.bits (1 + e + m)

/-- The mixed operand distribution described at `binaryPatternIn`. -/
def binaryPattern (e m : Nat) (rng : Rng) : Nat × Rng := binaryPatternIn none e m rng

/--
One `n`-bit posit word: 35% regimes of length one to three, 15% tiny, 15% huge, 10% special
values (zero, NaR, maxpos, minpos, one, and four), and 25% uniformly random words.
-/
def positPattern (n : Nat) (rng : Rng) : Nat × Rng :=
  let modulus := 2 ^ n
  let top := 2 ^ (n - 1)
  let (category, rng) := rng.below 100
  let (word, rng) := rng.bits n
  let (negative, rng) := rng.below 2
  let signed := fun (v : Nat) => if negative = 1 then (modulus - v) % modulus else v
  if category < 35 then
    (signed (2 ^ (n - 4) + word % (top - 2 ^ (n - 3))), rng)
  else if category < 50 then
    (signed (1 + word % 2 ^ (n - 8)), rng)
  else if category < 65 then
    (signed (top - 1 - word % 2 ^ (n - 8)), rng)
  else if category < 75 then
    let (which, rng) := rng.below 6
    let v :=
      match which with
      | 0 => 0
      | 1 => top
      | 2 => top - 1
      | 3 => 1
      | 4 => 2 ^ (n - 2)
      | _ => 2 ^ (n - 2) + 2 ^ (n - 4)
    (if which < 2 then v else signed v, rng)
  else
    (word, rng)

/-- One signed 64-bit integer: small, 31-bit, near `2^53`, boundary, or uniformly random. -/
def int64Value (rng : Rng) : Int × Rng :=
  let (category, rng) := rng.below 100
  let (word, rng) := rng.next
  let (negative, rng) := rng.below 2
  let signed := fun (v : Nat) => if negative = 1 then -(v : Int) else (v : Int)
  if category < 30 then
    (signed (word.toNat % 1024), rng)
  else if category < 50 then
    (signed (word.toNat % 2 ^ 31), rng)
  else if category < 65 then
    (signed (2 ^ 53 - 32 + word.toNat % 64), rng)
  else if category < 75 then
    let (which, rng) := rng.below 8
    let v : Int :=
      match which with
      | 0 => 0
      | 1 => 1
      | 2 => -1
      | 3 => 2 ^ 63 - 1
      | 4 => -(2 ^ 63)
      | 5 => 2 ^ 24 + 1
      | 6 => 2 ^ 31 - 1
      | _ => -(2 ^ 31)
    (v, rng)
  else
    let w := word.toNat
    (if w < 2 ^ 63 then (w : Int) else (w : Int) - 2 ^ 64, rng)

/-- One `scale` exponent: 80% in `[-64, 64]`, 20% in `[-20000, 20000]`. -/
def scaleValue (rng : Rng) : Int × Rng :=
  let (category, rng) := rng.below 100
  let (w, rng) := rng.next
  if category < 80 then
    (((w.toNat % 129 : Nat) : Int) - 64, rng)
  else
    (((w.toNat % 40001 : Nat) : Int) - 20000, rng)

/-- One integer power exponent in `[-8, 8]`. -/
def powExponent (rng : Rng) : Int × Rng :=
  let (w, rng) := rng.next
  (((w.toNat % 17 : Nat) : Int) - 8, rng)

def generate {α : Type} (seed : UInt64) (count : Nat) (step : Rng → α × Rng) : Array α :=
  Id.run do
    let mut rng : Rng := ⟨seed⟩
    let mut out : Array α := Array.mkEmpty count
    for _ in [0:count] do
      let (value, next) := step rng
      rng := next
      out := out.push value
    return out

def seedX : UInt64 := 0x0123456789ABCDEF
def seedY : UInt64 := 0x1F2E3D4C5B6A7988
def seedZ : UInt64 := 0x7A5B3C1D9E8F6A4B
def seedN : UInt64 := 0x243F6A8885A308D3

/-! ## Result digests -/

@[inline] def mixQuick (acc word : UInt64) : UInt64 := ((acc <<< 1) ||| (acc >>> 63)) ^^^ word

@[inline] def mixFull (h word : UInt64) : UInt64 := (h ^^^ word) * 0x100000001b3

def feedNat (h : UInt64) (n : Nat) : Nat → UInt64
  | 0 => mixFull h 0xFEED
  | fuel + 1 => if n = 0 then mixFull h 0xFEED else feedNat (mixFull h n.toUInt64) (n >>> 64) fuel

def feedNatAll (h : UInt64) (n : Nat) : UInt64 := feedNat h n 4096

@[inline] def intBits (i : Int) : UInt64 :=
  if i < 0 then ~~~ ((-i - 1).toNat.toUInt64) else i.toNat.toUInt64

def feedInt (h : UInt64) (i : Int) : UInt64 :=
  feedNatAll (mixFull h (if i < 0 then 1 else 0)) i.natAbs

/-- A cheap timed projection and a complete untimed digest of one result. -/
class Digest (α : Type) where
  quick : α → UInt64
  full : α → UInt64 → UInt64

instance : Digest Bool where
  quick b := if b then 1 else 0
  full b h := mixFull h (if b then 1 else 2)

@[inline] def statusBits (s : FloatLib.Numerics.IEEEStatus) : UInt64 :=
  (if s.invalid then 1 else 0) ||| (if s.divideByZero then 2 else 0) |||
    (if s.overflow then 4 else 0) ||| (if s.underflow then 8 else 0) |||
    (if s.inexact then 16 else 0)

instance : Digest FloatLib.Numerics.IEEEStatus where
  quick s := statusBits s
  full s h := mixFull h (0x100 ||| statusBits s)

instance : Digest FloatLib.Numerics.IEEEComparison.Result where
  quick r := (if r.value then (1 : UInt64) else 0) ||| (statusBits r.status <<< 1)
  full r h :=
    mixFull h ((0x200 : UInt64) ||| (if r.value then (1 : UInt64) else 0) ||| (statusBits r.status <<< 1))

@[inline] def orderingCode : Ordering → UInt64
  | .lt => 0
  | .eq => 1
  | .gt => 2

instance : Digest Ordering where
  quick o := orderingCode o
  full o h := mixFull h (0x300 ||| orderingCode o)

@[inline] def classCode : FloatLib.Numerics.IEEEClass → UInt64
  | .signalingNaN => 0
  | .quietNaN => 1
  | .negativeInfinity => 2
  | .negativeNormal => 3
  | .negativeSubnormal => 4
  | .negativeZero => 5
  | .positiveZero => 6
  | .positiveSubnormal => 7
  | .positiveNormal => 8
  | .positiveInfinity => 9

instance : Digest FloatLib.Numerics.IEEEClass where
  quick c := classCode c
  full c h := mixFull h (0x400 ||| classCode c)

instance : Digest String where
  quick s := s.utf8ByteSize.toUInt64
  full s h := mixFull (mixFull h 0x480) (hash s)

instance : Digest Int where
  quick i := intBits i
  full i h := feedInt (mixFull h 0x500) i

instance {w : Nat} : Digest (FixedInt w) where
  quick v := v.toNatBits.toUInt64
  full v h := feedNatAll (mixFull h 0x600) v.toNatBits

instance {α β : Type} [Digest α] [Digest β] : Digest (α × β) where
  quick p := Digest.quick p.1 ^^^ ((Digest.quick p.2 <<< 17) ||| (Digest.quick p.2 >>> 47))
  full p h := Digest.full p.2 (Digest.full p.1 (mixFull h 0x700))

instance {α : Type} [Digest α] : Digest (Option α) where
  quick o := match o with
    | some a => Digest.quick a
    | none => 0x9E3779B97F4A7C15
  full o h := match o with
    | some a => Digest.full a (mixFull h 0x801)
    | none => mixFull h 0x800

instance {ε α : Type} [Digest ε] [Digest α] : Digest (Except ε α) where
  quick r := match r with
    | .ok a => Digest.quick a
    | .error e => Digest.quick e ^^^ 0xC2B2AE3D27D4EB4F
  full r h := match r with
    | .ok a => Digest.full a (mixFull h 0x901)
    | .error e => Digest.full e (mixFull h 0x900)

instance : Digest Model.ParseError where
  quick _ := 0xE
  full e h := mixFull (mixFull h 0x980) (hash e.message)

instance : Digest Formats.Posit.Model.ParseError where
  quick _ := 0xE
  full e h := mixFull (mixFull h 0x990) (hash e.message)

@[inline] def conversionStatusBits (s : ExecFloat.ConversionStatus) : UInt64 :=
  (if s.inexact then 1 else 0) ||| (if s.overflow then 2 else 0) |||
    (if s.underflow then 4 else 0) ||| (if s.saturated then 8 else 0) |||
    (if s.wrapped then 16 else 0) ||| (if s.mappedSpecial then 32 else 0) |||
    (if s.invalid then 64 else 0)

@[inline] def failureCode : ExecFloat.ConversionFailure → UInt64
  | .infinity _ negative => if negative then 0xF1 else 0xF0
  | .exceptional _ _ => 0xF2
  | .divisionByZero => 0xF3
  | .outOfRange => 0xF4
  | .unsupportedPolicy => 0xF5

instance {α : Type} [Digest α] : Digest (ExecFloat.ConversionOutcome α) where
  quick o := match o with
    | .success v s => Digest.quick v ^^^ (conversionStatusBits s <<< 57)
    | .failure f => failureCode f
  full o h := match o with
    | .success v s => mixFull (Digest.full v (mixFull h 0xA00)) (conversionStatusBits s)
    | .failure f => mixFull (mixFull h 0xA01) (hash (reprStr f))

instance : Digest Model.IntegerExponentOutcome where
  quick o := intBits o.value ^^^ (statusBits o.status <<< 59)
  full o h := mixFull (feedInt (mixFull h 0xB00) o.value) (statusBits o.status)

instance : Digest FloatLib.Numerics.ReductionError where
  quick _ := 0x77
  full _ h := mixFull h 0x77

instance binaryDigest {format : FloatFormat} {plan : Configured.StoragePlan format}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Configured.Code plan)] :
    Digest (ExecFloat (Configured.Family format (Configured.Code plan) plan)) where
  quick v := FloatLibBenchmarks.Public.Sweep.resultBits v
  full v h := feedNatAll (mixFull h 0xC00) (Configured.Family.toModel v).toNatBits

/-- A configured status-bearing result: its value, all five flags, and its ternary value. -/
instance binaryOutcomeDigest {format : FloatFormat} {plan : Configured.StoragePlan format}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Configured.Code plan)] :
    Digest (ExecFloat.Binary.IEEEOutcome (format := format) (plan := plan)
      (code := Configured.Code plan)) where
  quick o :=
    Digest.quick o.value ^^^ ((statusBits o.status <<< 17) ||| (orderingCode o.ternary <<< 22))
  full o h := Digest.full o.ternary (Digest.full o.status (Digest.full o.value (mixFull h 0x780)))

instance positDigest {format : Formats.Posit.Format}
    {plan : Formats.Posit.Configured.StoragePlan format} :
    Digest (ExecFloat
      (Formats.Posit.Configured.Family format (Formats.Posit.Configured.Code plan) plan)) where
  quick v := FloatLibBenchmarks.Support.Posit.resultBits v
  full v h := feedNatAll (mixFull h 0xD00) (ExecFloat.Posit.toNatBits v)

/-! ## Driver -/

def digestNats (values : Array Nat) : UInt64 :=
  values.foldl (fun h v => feedNatAll h v) 0x84222325CBF29CE4

def digestInts (values : Array Int) : UInt64 :=
  values.foldl (fun h v => feedInt h v) 0x2545F4914F6CDD1D

def digestStrings (values : Array String) : UInt64 :=
  values.foldl (fun h s => mixFull h (hash s)) 0x9E6C63D0676A9A99

/--
Run the untimed complete-digest pass, then `trials` timed trials of `reps` loops each, and print
the best and median time per operation.
-/
def runCore (name : String) (count trials reps : Nat) (inputDigest : UInt64)
    (timed : Nat → UInt64 → UInt64) (full : Nat → UInt64 → UInt64) : IO Unit := do
  let f0 ← IO.monoNanosNow
  let fullHash ← IO.lazyPure fun _ => full count 0xCBF29CE484222325
  let f1 ← IO.monoNanosNow
  let mut times : Array Float := #[]
  let mut check : UInt64 := 0
  for t in [0:max trials 1] do
    let t0 ← IO.monoNanosNow
    let mut acc : UInt64 := t.toUInt64
    for r in [0:max reps 1] do
      let seed := acc + r.toUInt64
      acc ← IO.lazyPure fun _ => timed count seed
    let t1 ← IO.monoNanosNow
    check := check * 0x9E3779B97F4A7C15 + acc
    times := times.push ((t1 - t0).toFloat / (count * max reps 1).toFloat)
  let sorted := times.qsort (· < ·)
  IO.println (s!"cell={name} n={count} trials={max trials 1} reps={max reps 1} " ++
    s!"best_ns={sorted[0]!} median_ns={sorted[sorted.size / 2]!} " ++
    s!"first_pass_ns={(f1 - f0).toFloat / count.toFloat} input={inputDigest} " ++
    s!"hash={fullHash} check={check} all={times.toList}")

def runU {T : Type} (name : String) (xs : Array T) (din : UInt64)
    (timed full : Array T → Nat → UInt64 → UInt64) (trials reps : Nat) : IO Unit :=
  runCore name xs.size trials reps din (timed xs) (full xs)

def runB {T : Type} (name : String) (xs ys : Array T) (din : UInt64)
    (timed full : Array T → Array T → Nat → UInt64 → UInt64) (trials reps : Nat) : IO Unit :=
  runCore name xs.size trials reps din (timed xs ys) (full xs ys)

def runT {T : Type} (name : String) (xs ys zs : Array T) (din : UInt64)
    (timed full : Array T → Array T → Array T → Nat → UInt64 → UInt64) (trials reps : Nat) :
    IO Unit :=
  runCore name xs.size trials reps din (timed xs ys zs) (full xs ys zs)

def runXI {T : Type} (name : String) (xs : Array T) (ns : Array Int) (din : UInt64)
    (timed full : Array T → Array Int → Nat → UInt64 → UInt64) (trials reps : Nat) : IO Unit :=
  runCore name xs.size trials reps din (timed xs ns) (full xs ns)

def runI (name : String) (ns : Array Int) (din : UInt64)
    (timed full : Array Int → Nat → UInt64 → UInt64) (trials reps : Nat) : IO Unit :=
  runCore name ns.size trials reps din (timed ns) (full ns)

def runS (name : String) (ss : Array String) (din : UInt64)
    (timed full : Array String → Nat → UInt64 → UInt64) (trials reps : Nat) : IO Unit :=
  runCore name ss.size trials reps din (timed ss) (full ss)

/-! ## Formats -/

abbrev Half := ExecFloat.Binary 5 10
abbrev Brain := ExecFloat.Binary 8 7
abbrev Single := ExecFloat.Binary 8 23
abbrev Double := ExecFloat.Binary 11 52
abbrev Quad := ExecFloat.Binary 15 112
abbrev Oct := ExecFloat.Binary 19 236
abbrev P32 := ExecFloat.Posit 32

def binaryInputs {T : Type} (ofBits : Nat → T) (e m : Nat) (seed : UInt64) (count : Nat)
    (forced : Option Nat := none) : Array T × UInt64 :=
  let bits := generate seed count (binaryPatternIn forced e m)
  (bits.map ofBits, digestNats bits)

def inHalf (seed : UInt64) (count : Nat) (forced : Option Nat := none) :
    Array Half × UInt64 :=
  binaryInputs (ExecFloat.Binary.ofNatBits : Nat → Half) 5 10 seed count forced
def inBrain (seed : UInt64) (count : Nat) (forced : Option Nat := none) :
    Array Brain × UInt64 :=
  binaryInputs (ExecFloat.Binary.ofNatBits : Nat → Brain) 8 7 seed count forced
def inSingle (seed : UInt64) (count : Nat) (forced : Option Nat := none) :
    Array Single × UInt64 :=
  binaryInputs (ExecFloat.Binary.ofNatBits : Nat → Single) 8 23 seed count forced
def inDouble (seed : UInt64) (count : Nat) (forced : Option Nat := none) :
    Array Double × UInt64 :=
  binaryInputs (ExecFloat.Binary.ofNatBits : Nat → Double) 11 52 seed count forced
def inQuad (seed : UInt64) (count : Nat) (forced : Option Nat := none) :
    Array Quad × UInt64 :=
  binaryInputs (ExecFloat.Binary.ofNatBits : Nat → Quad) 15 112 seed count forced
def inOct (seed : UInt64) (count : Nat) (forced : Option Nat := none) :
    Array Oct × UInt64 :=
  binaryInputs (ExecFloat.Binary.ofNatBits : Nat → Oct) 19 236 seed count forced
def inP32 (seed : UInt64) (count : Nat) : Array P32 × UInt64 :=
  let bits := generate seed count (positPattern 32)
  (bits.map (ExecFloat.Posit.ofNatBits : Nat → P32), digestNats bits)

/-- Consecutive groups of eight operands, for the reductions. -/
def chunk8 {T : Type} (xs : Array T) : Array (Array T) := Id.run do
  let mut out : Array (Array T) := #[]
  let mut i := 0
  while i + 8 ≤ xs.size do
    out := out.push (xs.extract i (i + 8))
    i := i + 8
  return out

def inInt64 (count : Nat) : Array Int × UInt64 :=
  let values := generate seedN count int64Value
  (values, digestInts values)
def inScale (count : Nat) : Array Int × UInt64 :=
  let values := generate seedN count scaleValue
  (values, digestInts values)
def inPow (count : Nat) : Array Int × UInt64 :=
  let values := generate seedN count powExponent
  (values, digestInts values)

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
@[inline] def op1 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Single)
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
@[inline] def op3 (x : Single) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Double)
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
@[inline] def op5 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Half)
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
@[inline] def op7 (x : Half) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Double)
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
@[inline] def op9 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Quad)
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
@[inline] def op11 (x : Quad) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Double)
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
@[inline] def op13 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Brain)
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
@[inline] def op15 (x : Brain) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Single)
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
@[inline] def op17 (x : Single) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Half)
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
@[inline] def op19 (x : Half) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Single)
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
@[inline] def op21 (x : Single) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Brain)
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
@[inline] def op23 (x : Quad) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Single)
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
@[inline] def op25 (x : Oct) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Double)
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
@[inline] def op27 (x : Double) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Oct)
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
@[inline] def op29 (x : Quad) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Oct)
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
@[inline] def op31 (x : Oct) := (ExecFloat.Binary.ofModel (Model.cast _ _ (ExecFloat.Binary.toModel x)) : Quad)
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
@[inline] def op35 (n : Int) := (ExecFloat.convert (target := Half) (SourceExact := Int) (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed35 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed35 ns k (mixQuick acc (Digest.quick (op35 ns[k]!)))
def full35 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full35 ns k (Digest.full (op35 ns[k]!) (mixFull h k.toUInt64))
def run35 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary16/convertFromInt64" ns d timed35 full35 trials reps

/-! ### `binary16/intToFloat64` -/
@[inline] def op36 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.intToFloat _ (FixedInt.ofInt n : FixedInt 64) .nearest) : Half)
def timed36 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed36 ns k (mixQuick acc (Digest.quick (op36 ns[k]!)))
def full36 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full36 ns k (Digest.full (op36 ns[k]!) (mixFull h k.toUInt64))
def run36 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary16/intToFloat64" ns d timed36 full36 trials reps

/-! ### `binary16/floatToInt64[nearest]` -/
@[inline] def op37 (x : Half) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .nearest
def timed37 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed37 xs k (mixQuick acc (Digest.quick (op37 xs[k]!)))
def full37 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full37 xs k (Digest.full (op37 xs[k]!) (mixFull h k.toUInt64))
def run37 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/floatToInt64[nearest]" xs d timed37 full37 trials reps

/-! ### `binary16/floatToInt64[towardZero]` -/
@[inline] def op38 (x : Half) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .towardZero
def timed38 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed38 xs k (mixQuick acc (Digest.quick (op38 xs[k]!)))
def full38 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full38 xs k (Digest.full (op38 xs[k]!) (mixFull h k.toUInt64))
def run38 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/floatToInt64[towardZero]" xs d timed38 full38 trials reps

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
@[inline] def op49 (x y : Half) := ExecFloat.Binary.compareQuietLess x y
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
@[inline] def op50 (x y : Half) := ExecFloat.Binary.compareQuietEqual x y
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
@[inline] def op51 (x y : Half) := ExecFloat.Binary.compareSignalingLessEqual x y
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
@[inline] def op56 (x y : Half) := ExecFloat.Binary.maxNum x y
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
@[inline] def op57 (x y : Half) := ExecFloat.Binary.minNum x y
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
@[inline] def op58 (x y : Half) := (ExecFloat.Binary.ofModel (Model.maximumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Half)
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
@[inline] def op59 (x y : Half) := (ExecFloat.Binary.ofModel (Model.minimumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Half)
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

/-! ### `binary16/binaryExponent` -/
@[inline] def op63 (x : Half) := ExecFloat.Binary.binaryExponent x
def timed63 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed63 xs k (mixQuick acc (Digest.quick (op63 xs[k]!)))
def full63 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full63 xs k (Digest.full (op63 xs[k]!) (mixFull h k.toUInt64))
def run63 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/binaryExponent" xs d timed63 full63 trials reps

/-! ### `binary16/binaryExponentInt` -/
@[inline] def op64 (x : Half) := ExecFloat.Binary.binaryExponentInt x
def timed64 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed64 xs k (mixQuick acc (Digest.quick (op64 xs[k]!)))
def full64 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full64 xs k (Digest.full (op64 xs[k]!) (mixFull h k.toUInt64))
def run64 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/binaryExponentInt" xs d timed64 full64 trials reps

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
@[inline] def op74 (x : Half) := ExecFloat.Binary.isSignalingNaN x
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

/-! ### `binary16/powInt` -/
@[inline] def op110 (x : Half) (n : Int) := ExecFloat.Binary.powInt x n
def timed110 (xs : Array Half) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed110 xs ns k (mixQuick acc (Digest.quick (op110 xs[k]! ns[k]!)))
def full110 (xs : Array Half) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full110 xs ns k (Digest.full (op110 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run110 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ns, dn) := inPow count
  runXI "binary16/powInt" xs ns (mixFull dx dn) timed110 full110 trials reps

/-! ### `binary16/rsqrt` -/
@[inline] def op111 (x : Half) := ExecFloat.Binary.rsqrt x
def timed111 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed111 xs k (mixQuick acc (Digest.quick (op111 xs[k]!)))
def full111 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full111 xs k (Digest.full (op111 xs[k]!) (mixFull h k.toUInt64))
def run111 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/rsqrt" xs d timed111 full111 trials reps

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

/-! ### `binary16/rootN3` -/
@[inline] def op113 (x : Half) := ExecFloat.Binary.rootN x 3
def timed113 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed113 xs k (mixQuick acc (Digest.quick (op113 xs[k]!)))
def full113 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full113 xs k (Digest.full (op113 xs[k]!) (mixFull h k.toUInt64))
def run113 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/rootN3" xs d timed113 full113 trials reps

/-! ### `binary16/exp[certify]` -/
@[inline] def op114 (x : Half) := (ExecFloat.Binary.exp x (certify := true)).toOption
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
@[inline] def op115 (x : Half) := (ExecFloat.Binary.log x (certify := true)).toOption
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

/-! ### `binary16/expMinus1` -/
@[inline] def op118 (x : Half) := (ExecFloat.Binary.expMinus1 x).toOption
def timed118 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed118 xs k (mixQuick acc (Digest.quick (op118 xs[k]!)))
def full118 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full118 xs k (Digest.full (op118 xs[k]!) (mixFull h k.toUInt64))
def run118 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/expMinus1" xs d timed118 full118 trials reps

/-! ### `binary16/logPlus1` -/
@[inline] def op119 (x : Half) := (ExecFloat.Binary.logPlus1 x).toOption
def timed119 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed119 xs k (mixQuick acc (Digest.quick (op119 xs[k]!)))
def full119 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full119 xs k (Digest.full (op119 xs[k]!) (mixFull h k.toUInt64))
def run119 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/logPlus1" xs d timed119 full119 trials reps

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

/-! ### `bfloat16/convertFromInt64` -/
@[inline] def op122 (n : Int) := (ExecFloat.convert (target := Brain) (SourceExact := Int) (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed122 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed122 ns k (mixQuick acc (Digest.quick (op122 ns[k]!)))
def full122 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full122 ns k (Digest.full (op122 ns[k]!) (mixFull h k.toUInt64))
def run122 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "bfloat16/convertFromInt64" ns d timed122 full122 trials reps

/-! ### `bfloat16/intToFloat64` -/
@[inline] def op123 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.intToFloat _ (FixedInt.ofInt n : FixedInt 64) .nearest) : Brain)
def timed123 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed123 ns k (mixQuick acc (Digest.quick (op123 ns[k]!)))
def full123 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full123 ns k (Digest.full (op123 ns[k]!) (mixFull h k.toUInt64))
def run123 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "bfloat16/intToFloat64" ns d timed123 full123 trials reps

/-! ### `bfloat16/floatToInt64[nearest]` -/
@[inline] def op124 (x : Brain) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .nearest
def timed124 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed124 xs k (mixQuick acc (Digest.quick (op124 xs[k]!)))
def full124 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full124 xs k (Digest.full (op124 xs[k]!) (mixFull h k.toUInt64))
def run124 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/floatToInt64[nearest]" xs d timed124 full124 trials reps

/-! ### `bfloat16/floatToInt64[towardZero]` -/
@[inline] def op125 (x : Brain) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .towardZero
def timed125 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed125 xs k (mixQuick acc (Digest.quick (op125 xs[k]!)))
def full125 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full125 xs k (Digest.full (op125 xs[k]!) (mixFull h k.toUInt64))
def run125 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/floatToInt64[towardZero]" xs d timed125 full125 trials reps

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
@[inline] def op136 (x y : Brain) := ExecFloat.Binary.compareQuietLess x y
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
@[inline] def op137 (x y : Brain) := ExecFloat.Binary.compareQuietEqual x y
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
@[inline] def op138 (x y : Brain) := ExecFloat.Binary.compareSignalingLessEqual x y
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
@[inline] def op143 (x y : Brain) := ExecFloat.Binary.maxNum x y
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
@[inline] def op144 (x y : Brain) := ExecFloat.Binary.minNum x y
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
@[inline] def op145 (x y : Brain) := (ExecFloat.Binary.ofModel (Model.maximumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Brain)
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
@[inline] def op146 (x y : Brain) := (ExecFloat.Binary.ofModel (Model.minimumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Brain)
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

/-! ### `bfloat16/binaryExponent` -/
@[inline] def op150 (x : Brain) := ExecFloat.Binary.binaryExponent x
def timed150 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed150 xs k (mixQuick acc (Digest.quick (op150 xs[k]!)))
def full150 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full150 xs k (Digest.full (op150 xs[k]!) (mixFull h k.toUInt64))
def run150 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/binaryExponent" xs d timed150 full150 trials reps

/-! ### `bfloat16/binaryExponentInt` -/
@[inline] def op151 (x : Brain) := ExecFloat.Binary.binaryExponentInt x
def timed151 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed151 xs k (mixQuick acc (Digest.quick (op151 xs[k]!)))
def full151 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full151 xs k (Digest.full (op151 xs[k]!) (mixFull h k.toUInt64))
def run151 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/binaryExponentInt" xs d timed151 full151 trials reps

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
@[inline] def op161 (x : Brain) := ExecFloat.Binary.isSignalingNaN x
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

/-! ### `bfloat16/powInt` -/
@[inline] def op197 (x : Brain) (n : Int) := ExecFloat.Binary.powInt x n
def timed197 (xs : Array Brain) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed197 xs ns k (mixQuick acc (Digest.quick (op197 xs[k]! ns[k]!)))
def full197 (xs : Array Brain) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full197 xs ns k (Digest.full (op197 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run197 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ns, dn) := inPow count
  runXI "bfloat16/powInt" xs ns (mixFull dx dn) timed197 full197 trials reps

/-! ### `bfloat16/rsqrt` -/
@[inline] def op198 (x : Brain) := ExecFloat.Binary.rsqrt x
def timed198 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed198 xs k (mixQuick acc (Digest.quick (op198 xs[k]!)))
def full198 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full198 xs k (Digest.full (op198 xs[k]!) (mixFull h k.toUInt64))
def run198 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/rsqrt" xs d timed198 full198 trials reps

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

/-! ### `bfloat16/rootN3` -/
@[inline] def op200 (x : Brain) := ExecFloat.Binary.rootN x 3
def timed200 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed200 xs k (mixQuick acc (Digest.quick (op200 xs[k]!)))
def full200 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full200 xs k (Digest.full (op200 xs[k]!) (mixFull h k.toUInt64))
def run200 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/rootN3" xs d timed200 full200 trials reps

/-! ### `bfloat16/exp[certify]` -/
@[inline] def op201 (x : Brain) := (ExecFloat.Binary.exp x (certify := true)).toOption
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
@[inline] def op202 (x : Brain) := (ExecFloat.Binary.log x (certify := true)).toOption
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

/-! ### `bfloat16/expMinus1` -/
@[inline] def op205 (x : Brain) := (ExecFloat.Binary.expMinus1 x).toOption
def timed205 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed205 xs k (mixQuick acc (Digest.quick (op205 xs[k]!)))
def full205 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full205 xs k (Digest.full (op205 xs[k]!) (mixFull h k.toUInt64))
def run205 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/expMinus1" xs d timed205 full205 trials reps

/-! ### `bfloat16/logPlus1` -/
@[inline] def op206 (x : Brain) := (ExecFloat.Binary.logPlus1 x).toOption
def timed206 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed206 xs k (mixQuick acc (Digest.quick (op206 xs[k]!)))
def full206 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full206 xs k (Digest.full (op206 xs[k]!) (mixFull h k.toUInt64))
def run206 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/logPlus1" xs d timed206 full206 trials reps

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

/-! ### `binary32/convertFromInt64` -/
@[inline] def op209 (n : Int) := (ExecFloat.convert (target := Single) (SourceExact := Int) (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed209 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed209 ns k (mixQuick acc (Digest.quick (op209 ns[k]!)))
def full209 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full209 ns k (Digest.full (op209 ns[k]!) (mixFull h k.toUInt64))
def run209 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary32/convertFromInt64" ns d timed209 full209 trials reps

/-! ### `binary32/intToFloat64` -/
@[inline] def op210 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.intToFloat _ (FixedInt.ofInt n : FixedInt 64) .nearest) : Single)
def timed210 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed210 ns k (mixQuick acc (Digest.quick (op210 ns[k]!)))
def full210 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full210 ns k (Digest.full (op210 ns[k]!) (mixFull h k.toUInt64))
def run210 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary32/intToFloat64" ns d timed210 full210 trials reps

/-! ### `binary32/floatToInt64[nearest]` -/
@[inline] def op211 (x : Single) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .nearest
def timed211 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed211 xs k (mixQuick acc (Digest.quick (op211 xs[k]!)))
def full211 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full211 xs k (Digest.full (op211 xs[k]!) (mixFull h k.toUInt64))
def run211 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/floatToInt64[nearest]" xs d timed211 full211 trials reps

/-! ### `binary32/floatToInt64[towardZero]` -/
@[inline] def op212 (x : Single) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .towardZero
def timed212 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed212 xs k (mixQuick acc (Digest.quick (op212 xs[k]!)))
def full212 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full212 xs k (Digest.full (op212 xs[k]!) (mixFull h k.toUInt64))
def run212 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/floatToInt64[towardZero]" xs d timed212 full212 trials reps

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
@[inline] def op223 (x y : Single) := ExecFloat.Binary.compareQuietLess x y
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
@[inline] def op224 (x y : Single) := ExecFloat.Binary.compareQuietEqual x y
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
@[inline] def op225 (x y : Single) := ExecFloat.Binary.compareSignalingLessEqual x y
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
@[inline] def op230 (x y : Single) := ExecFloat.Binary.maxNum x y
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
@[inline] def op231 (x y : Single) := ExecFloat.Binary.minNum x y
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
@[inline] def op232 (x y : Single) := (ExecFloat.Binary.ofModel (Model.maximumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Single)
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
@[inline] def op233 (x y : Single) := (ExecFloat.Binary.ofModel (Model.minimumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Single)
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

/-! ### `binary32/binaryExponent` -/
@[inline] def op237 (x : Single) := ExecFloat.Binary.binaryExponent x
def timed237 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed237 xs k (mixQuick acc (Digest.quick (op237 xs[k]!)))
def full237 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full237 xs k (Digest.full (op237 xs[k]!) (mixFull h k.toUInt64))
def run237 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/binaryExponent" xs d timed237 full237 trials reps

/-! ### `binary32/binaryExponentInt` -/
@[inline] def op238 (x : Single) := ExecFloat.Binary.binaryExponentInt x
def timed238 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed238 xs k (mixQuick acc (Digest.quick (op238 xs[k]!)))
def full238 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full238 xs k (Digest.full (op238 xs[k]!) (mixFull h k.toUInt64))
def run238 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/binaryExponentInt" xs d timed238 full238 trials reps

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
@[inline] def op248 (x : Single) := ExecFloat.Binary.isSignalingNaN x
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

/-! ### `binary32/powInt` -/
@[inline] def op284 (x : Single) (n : Int) := ExecFloat.Binary.powInt x n
def timed284 (xs : Array Single) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed284 xs ns k (mixQuick acc (Digest.quick (op284 xs[k]! ns[k]!)))
def full284 (xs : Array Single) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full284 xs ns k (Digest.full (op284 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run284 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ns, dn) := inPow count
  runXI "binary32/powInt" xs ns (mixFull dx dn) timed284 full284 trials reps

/-! ### `binary32/rsqrt` -/
@[inline] def op285 (x : Single) := ExecFloat.Binary.rsqrt x
def timed285 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed285 xs k (mixQuick acc (Digest.quick (op285 xs[k]!)))
def full285 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full285 xs k (Digest.full (op285 xs[k]!) (mixFull h k.toUInt64))
def run285 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/rsqrt" xs d timed285 full285 trials reps

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

/-! ### `binary32/rootN3` -/
@[inline] def op287 (x : Single) := ExecFloat.Binary.rootN x 3
def timed287 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed287 xs k (mixQuick acc (Digest.quick (op287 xs[k]!)))
def full287 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full287 xs k (Digest.full (op287 xs[k]!) (mixFull h k.toUInt64))
def run287 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/rootN3" xs d timed287 full287 trials reps

/-! ### `binary32/exp[certify]` -/
@[inline] def op288 (x : Single) := (ExecFloat.Binary.exp x (certify := true)).toOption
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
@[inline] def op289 (x : Single) := (ExecFloat.Binary.log x (certify := true)).toOption
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

/-! ### `binary32/expMinus1` -/
@[inline] def op292 (x : Single) := (ExecFloat.Binary.expMinus1 x).toOption
def timed292 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed292 xs k (mixQuick acc (Digest.quick (op292 xs[k]!)))
def full292 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full292 xs k (Digest.full (op292 xs[k]!) (mixFull h k.toUInt64))
def run292 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/expMinus1" xs d timed292 full292 trials reps

/-! ### `binary32/logPlus1` -/
@[inline] def op293 (x : Single) := (ExecFloat.Binary.logPlus1 x).toOption
def timed293 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed293 xs k (mixQuick acc (Digest.quick (op293 xs[k]!)))
def full293 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full293 xs k (Digest.full (op293 xs[k]!) (mixFull h k.toUInt64))
def run293 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/logPlus1" xs d timed293 full293 trials reps

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

/-! ### `binary64/convertFromInt64` -/
@[inline] def op296 (n : Int) := (ExecFloat.convert (target := Double) (SourceExact := Int) (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed296 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed296 ns k (mixQuick acc (Digest.quick (op296 ns[k]!)))
def full296 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full296 ns k (Digest.full (op296 ns[k]!) (mixFull h k.toUInt64))
def run296 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary64/convertFromInt64" ns d timed296 full296 trials reps

/-! ### `binary64/intToFloat64` -/
@[inline] def op297 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.intToFloat _ (FixedInt.ofInt n : FixedInt 64) .nearest) : Double)
def timed297 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed297 ns k (mixQuick acc (Digest.quick (op297 ns[k]!)))
def full297 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full297 ns k (Digest.full (op297 ns[k]!) (mixFull h k.toUInt64))
def run297 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary64/intToFloat64" ns d timed297 full297 trials reps

/-! ### `binary64/floatToInt64[nearest]` -/
@[inline] def op298 (x : Double) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .nearest
def timed298 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed298 xs k (mixQuick acc (Digest.quick (op298 xs[k]!)))
def full298 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full298 xs k (Digest.full (op298 xs[k]!) (mixFull h k.toUInt64))
def run298 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/floatToInt64[nearest]" xs d timed298 full298 trials reps

/-! ### `binary64/floatToInt64[towardZero]` -/
@[inline] def op299 (x : Double) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .towardZero
def timed299 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed299 xs k (mixQuick acc (Digest.quick (op299 xs[k]!)))
def full299 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full299 xs k (Digest.full (op299 xs[k]!) (mixFull h k.toUInt64))
def run299 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/floatToInt64[towardZero]" xs d timed299 full299 trials reps

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
@[inline] def op310 (x y : Double) := ExecFloat.Binary.compareQuietLess x y
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
@[inline] def op311 (x y : Double) := ExecFloat.Binary.compareQuietEqual x y
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
@[inline] def op312 (x y : Double) := ExecFloat.Binary.compareSignalingLessEqual x y
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
@[inline] def op317 (x y : Double) := ExecFloat.Binary.maxNum x y
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
@[inline] def op318 (x y : Double) := ExecFloat.Binary.minNum x y
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
@[inline] def op319 (x y : Double) := (ExecFloat.Binary.ofModel (Model.maximumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Double)
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
@[inline] def op320 (x y : Double) := (ExecFloat.Binary.ofModel (Model.minimumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Double)
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

/-! ### `binary64/binaryExponent` -/
@[inline] def op324 (x : Double) := ExecFloat.Binary.binaryExponent x
def timed324 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed324 xs k (mixQuick acc (Digest.quick (op324 xs[k]!)))
def full324 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full324 xs k (Digest.full (op324 xs[k]!) (mixFull h k.toUInt64))
def run324 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/binaryExponent" xs d timed324 full324 trials reps

/-! ### `binary64/binaryExponentInt` -/
@[inline] def op325 (x : Double) := ExecFloat.Binary.binaryExponentInt x
def timed325 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed325 xs k (mixQuick acc (Digest.quick (op325 xs[k]!)))
def full325 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full325 xs k (Digest.full (op325 xs[k]!) (mixFull h k.toUInt64))
def run325 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/binaryExponentInt" xs d timed325 full325 trials reps

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
@[inline] def op335 (x : Double) := ExecFloat.Binary.isSignalingNaN x
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

/-! ### `binary64/powInt` -/
@[inline] def op371 (x : Double) (n : Int) := ExecFloat.Binary.powInt x n
def timed371 (xs : Array Double) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed371 xs ns k (mixQuick acc (Digest.quick (op371 xs[k]! ns[k]!)))
def full371 (xs : Array Double) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full371 xs ns k (Digest.full (op371 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run371 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ns, dn) := inPow count
  runXI "binary64/powInt" xs ns (mixFull dx dn) timed371 full371 trials reps

/-! ### `binary64/rsqrt` -/
@[inline] def op372 (x : Double) := ExecFloat.Binary.rsqrt x
def timed372 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed372 xs k (mixQuick acc (Digest.quick (op372 xs[k]!)))
def full372 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full372 xs k (Digest.full (op372 xs[k]!) (mixFull h k.toUInt64))
def run372 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/rsqrt" xs d timed372 full372 trials reps

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

/-! ### `binary64/rootN3` -/
@[inline] def op374 (x : Double) := ExecFloat.Binary.rootN x 3
def timed374 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed374 xs k (mixQuick acc (Digest.quick (op374 xs[k]!)))
def full374 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full374 xs k (Digest.full (op374 xs[k]!) (mixFull h k.toUInt64))
def run374 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/rootN3" xs d timed374 full374 trials reps

/-! ### `binary64/exp[certify]` -/
@[inline] def op375 (x : Double) := (ExecFloat.Binary.exp x (certify := true)).toOption
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
@[inline] def op376 (x : Double) := (ExecFloat.Binary.log x (certify := true)).toOption
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

/-! ### `binary64/expMinus1` -/
@[inline] def op379 (x : Double) := (ExecFloat.Binary.expMinus1 x).toOption
def timed379 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed379 xs k (mixQuick acc (Digest.quick (op379 xs[k]!)))
def full379 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full379 xs k (Digest.full (op379 xs[k]!) (mixFull h k.toUInt64))
def run379 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/expMinus1" xs d timed379 full379 trials reps

/-! ### `binary64/logPlus1` -/
@[inline] def op380 (x : Double) := (ExecFloat.Binary.logPlus1 x).toOption
def timed380 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed380 xs k (mixQuick acc (Digest.quick (op380 xs[k]!)))
def full380 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full380 xs k (Digest.full (op380 xs[k]!) (mixFull h k.toUInt64))
def run380 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/logPlus1" xs d timed380 full380 trials reps

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

/-! ### `binary128/convertFromInt64` -/
@[inline] def op383 (n : Int) := (ExecFloat.convert (target := Quad) (SourceExact := Int) (TargetExact := FloatLib.Numerics.SignedRat) n)
def timed383 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed383 ns k (mixQuick acc (Digest.quick (op383 ns[k]!)))
def full383 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full383 ns k (Digest.full (op383 ns[k]!) (mixFull h k.toUInt64))
def run383 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary128/convertFromInt64" ns d timed383 full383 trials reps

/-! ### `binary128/intToFloat64` -/
@[inline] def op384 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.intToFloat _ (FixedInt.ofInt n : FixedInt 64) .nearest) : Quad)
def timed384 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed384 ns k (mixQuick acc (Digest.quick (op384 ns[k]!)))
def full384 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full384 ns k (Digest.full (op384 ns[k]!) (mixFull h k.toUInt64))
def run384 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary128/intToFloat64" ns d timed384 full384 trials reps

/-! ### `binary128/floatToInt64[nearest]` -/
@[inline] def op385 (x : Quad) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .nearest
def timed385 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed385 xs k (mixQuick acc (Digest.quick (op385 xs[k]!)))
def full385 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full385 xs k (Digest.full (op385 xs[k]!) (mixFull h k.toUInt64))
def run385 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/floatToInt64[nearest]" xs d timed385 full385 trials reps

/-! ### `binary128/floatToInt64[towardZero]` -/
@[inline] def op386 (x : Quad) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .towardZero
def timed386 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed386 xs k (mixQuick acc (Digest.quick (op386 xs[k]!)))
def full386 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full386 xs k (Digest.full (op386 xs[k]!) (mixFull h k.toUInt64))
def run386 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/floatToInt64[towardZero]" xs d timed386 full386 trials reps

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
@[inline] def op397 (x y : Quad) := ExecFloat.Binary.compareQuietLess x y
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
@[inline] def op398 (x y : Quad) := ExecFloat.Binary.compareQuietEqual x y
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
@[inline] def op399 (x y : Quad) := ExecFloat.Binary.compareSignalingLessEqual x y
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
@[inline] def op404 (x y : Quad) := ExecFloat.Binary.maxNum x y
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
@[inline] def op405 (x y : Quad) := ExecFloat.Binary.minNum x y
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
@[inline] def op406 (x y : Quad) := (ExecFloat.Binary.ofModel (Model.maximumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Quad)
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
@[inline] def op407 (x y : Quad) := (ExecFloat.Binary.ofModel (Model.minimumNumber (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) : Quad)
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

/-! ### `binary128/binaryExponent` -/
@[inline] def op411 (x : Quad) := ExecFloat.Binary.binaryExponent x
def timed411 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed411 xs k (mixQuick acc (Digest.quick (op411 xs[k]!)))
def full411 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full411 xs k (Digest.full (op411 xs[k]!) (mixFull h k.toUInt64))
def run411 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/binaryExponent" xs d timed411 full411 trials reps

/-! ### `binary128/binaryExponentInt` -/
@[inline] def op412 (x : Quad) := ExecFloat.Binary.binaryExponentInt x
def timed412 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed412 xs k (mixQuick acc (Digest.quick (op412 xs[k]!)))
def full412 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full412 xs k (Digest.full (op412 xs[k]!) (mixFull h k.toUInt64))
def run412 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/binaryExponentInt" xs d timed412 full412 trials reps

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
@[inline] def op422 (x : Quad) := ExecFloat.Binary.isSignalingNaN x
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
  runT "binary128/fma[towardZero]" xs ys zs (mixFull (mixFull dx dy) dz) timed446 full446 trials reps

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

/-! ### `binary128/powInt` -/
@[inline] def op458 (x : Quad) (n : Int) := ExecFloat.Binary.powInt x n
def timed458 (xs : Array Quad) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed458 xs ns k (mixQuick acc (Digest.quick (op458 xs[k]! ns[k]!)))
def full458 (xs : Array Quad) (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full458 xs ns k (Digest.full (op458 xs[k]! ns[k]!) (mixFull h k.toUInt64))
def run458 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ns, dn) := inPow count
  runXI "binary128/powInt" xs ns (mixFull dx dn) timed458 full458 trials reps

/-! ### `binary128/rsqrt` -/
@[inline] def op459 (x : Quad) := ExecFloat.Binary.rsqrt x
def timed459 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed459 xs k (mixQuick acc (Digest.quick (op459 xs[k]!)))
def full459 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full459 xs k (Digest.full (op459 xs[k]!) (mixFull h k.toUInt64))
def run459 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/rsqrt" xs d timed459 full459 trials reps

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

/-! ### `binary128/rootN3` -/
@[inline] def op461 (x : Quad) := ExecFloat.Binary.rootN x 3
def timed461 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed461 xs k (mixQuick acc (Digest.quick (op461 xs[k]!)))
def full461 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full461 xs k (Digest.full (op461 xs[k]!) (mixFull h k.toUInt64))
def run461 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/rootN3" xs d timed461 full461 trials reps

/-! ### `binary128/exp[certify]` -/
@[inline] def op462 (x : Quad) := (ExecFloat.Binary.exp x (certify := true)).toOption
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
@[inline] def op463 (x : Quad) := (ExecFloat.Binary.log x (certify := true)).toOption
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

/-! ### `binary128/expMinus1` -/
@[inline] def op466 (x : Quad) := (ExecFloat.Binary.expMinus1 x).toOption
def timed466 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed466 xs k (mixQuick acc (Digest.quick (op466 xs[k]!)))
def full466 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full466 xs k (Digest.full (op466 xs[k]!) (mixFull h k.toUInt64))
def run466 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/expMinus1" xs d timed466 full466 trials reps

/-! ### `binary128/logPlus1` -/
@[inline] def op467 (x : Quad) := (ExecFloat.Binary.logPlus1 x).toOption
def timed467 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed467 xs k (mixQuick acc (Digest.quick (op467 xs[k]!)))
def full467 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full467 xs k (Digest.full (op467 xs[k]!) (mixFull h k.toUInt64))
def run467 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/logPlus1" xs d timed467 full467 trials reps

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

/-! ### `binary256/intToFloat64` -/
@[inline] def op470 (n : Int) := (ExecFloat.Binary.ofModel (ExecDType.intToFloat _ (FixedInt.ofInt n : FixedInt 64) .nearest) : Oct)
def timed470 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed470 ns k (mixQuick acc (Digest.quick (op470 ns[k]!)))
def full470 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full470 ns k (Digest.full (op470 ns[k]!) (mixFull h k.toUInt64))
def run470 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "binary256/intToFloat64" ns d timed470 full470 trials reps

/-! ### `binary256/floatToInt64[nearest]` -/
@[inline] def op471 (x : Oct) := ExecDType.floatToInt (width := 64) (ExecFloat.Binary.toModel x) .nearest
def timed471 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed471 xs k (mixQuick acc (Digest.quick (op471 xs[k]!)))
def full471 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full471 xs k (Digest.full (op471 xs[k]!) (mixFull h k.toUInt64))
def run471 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/floatToInt64[nearest]" xs d timed471 full471 trials reps

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

/-! ### `binary256/binaryExponent` -/
@[inline] def op481 (x : Oct) := ExecFloat.Binary.binaryExponent x
def timed481 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed481 xs k (mixQuick acc (Digest.quick (op481 xs[k]!)))
def full481 (xs : Array Oct) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full481 xs k (Digest.full (op481 xs[k]!) (mixFull h k.toUInt64))
def run481 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inOct seedX count
  runU "binary256/binaryExponent" xs d timed481 full481 trials reps

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
@[inline] def op498 (n : Int) := (ExecFloat.convert (target := P32) (SourceExact := Int) (TargetExact := Rat) n)
def timed498 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed498 ns k (mixQuick acc (Digest.quick (op498 ns[k]!)))
def full498 (ns : Array Int) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full498 ns k (Digest.full (op498 ns[k]!) (mixFull h k.toUInt64))
def run498 (count trials reps : Nat) : IO Unit := do
  let (ns, d) := inInt64 count
  runI "posit32/convertFromInt64" ns d timed498 full498 trials reps

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
@[inline] def op514 (s : String) := (ExecFloat.Posit.parse s : Except Formats.Posit.Model.ParseError P32)
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

/-! ### `posit32/powInt` -/
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
  runXI "posit32/powInt" xs ns (mixFull dx dn) timed521 full521 trials reps

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

/-! ### `posit32/expMinus1` -/
@[inline] def op525 (x : P32) := ExecFloat.Posit.expMinus1 x
def timed525 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed525 xs k (mixQuick acc (Digest.quick (op525 xs[k]!)))
def full525 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full525 xs k (Digest.full (op525 xs[k]!) (mixFull h k.toUInt64))
def run525 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/expMinus1" xs d timed525 full525 trials reps

/-! ### `posit32/logPlus1` -/
@[inline] def op526 (x : P32) := ExecFloat.Posit.logPlus1 x
def timed526 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed526 xs k (mixQuick acc (Digest.quick (op526 xs[k]!)))
def full526 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full526 xs k (Digest.full (op526 xs[k]!) (mixFull h k.toUInt64))
def run526 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/logPlus1" xs d timed526 full526 trials reps

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

/-! ### `posit32/rootN3` -/
@[inline] def op529 (x : P32) := ExecFloat.Posit.rootN x 3
def timed529 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed529 xs k (mixQuick acc (Digest.quick (op529 xs[k]!)))
def full529 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full529 xs k (Digest.full (op529 xs[k]!) (mixFull h k.toUInt64))
def run529 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/rootN3" xs d timed529 full529 trials reps

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

/-! ### `posit32/quireDot8` -/
@[inline] def op532 (a b : Array P32) := (ExecFloat.Posit.Quire.qToP ((a.zip b).foldl (fun q p => ExecFloat.Posit.Quire.qMulAdd q p.1 p.2) (ExecFloat.Posit.Quire.pToQ (0 : P32))) : P32)
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

/-! ### `binary16/ref.add[mixed]` -/
@[inline] def op533 (x y : Half) := ExecFloat.add x y
def timed533 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed533 xs ys k (mixQuick acc (Digest.quick (op533 xs[k]! ys[k]!)))
def full533 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full533 xs ys k (Digest.full (op533 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run533 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.add[mixed]" xs ys (mixFull dx dy) timed533 full533 trials reps

/-! ### `binary16/ref.sub[mixed]` -/
@[inline] def op534 (x y : Half) := ExecFloat.sub x y
def timed534 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed534 xs ys k (mixQuick acc (Digest.quick (op534 xs[k]! ys[k]!)))
def full534 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full534 xs ys k (Digest.full (op534 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run534 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.sub[mixed]" xs ys (mixFull dx dy) timed534 full534 trials reps

/-! ### `binary16/ref.mul[mixed]` -/
@[inline] def op535 (x y : Half) := ExecFloat.mul x y
def timed535 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed535 xs ys k (mixQuick acc (Digest.quick (op535 xs[k]! ys[k]!)))
def full535 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full535 xs ys k (Digest.full (op535 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run535 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.mul[mixed]" xs ys (mixFull dx dy) timed535 full535 trials reps

/-! ### `binary16/ref.div[mixed]` -/
@[inline] def op536 (x y : Half) := ExecFloat.div x y
def timed536 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed536 xs ys k (mixQuick acc (Digest.quick (op536 xs[k]! ys[k]!)))
def full536 (xs ys : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full536 xs ys k (Digest.full (op536 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run536 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  runB "binary16/ref.div[mixed]" xs ys (mixFull dx dy) timed536 full536 trials reps

/-! ### `binary16/ref.sqrt[mixed]` -/
@[inline] def op537 (x : Half) := ExecFloat.sqrt x
def timed537 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed537 xs k (mixQuick acc (Digest.quick (op537 xs[k]!)))
def full537 (xs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full537 xs k (Digest.full (op537 xs[k]!) (mixFull h k.toUInt64))
def run537 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inHalf seedX count
  runU "binary16/ref.sqrt[mixed]" xs d timed537 full537 trials reps

/-! ### `binary16/ref.fma[mixed]` -/
@[inline] def op538 (x y z : Half) := ExecFloat.fma x y z
def timed538 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed538 xs ys zs k (mixQuick acc (Digest.quick (op538 xs[k]! ys[k]! zs[k]!)))
def full538 (xs ys zs : Array Half) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full538 xs ys zs k (Digest.full (op538 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run538 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inHalf seedX count
  let (ys, dy) := inHalf seedY count
  let (zs, dz) := inHalf seedZ count
  runT "binary16/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed538 full538 trials reps

/-! ### `bfloat16/ref.add[mixed]` -/
@[inline] def op539 (x y : Brain) := ExecFloat.add x y
def timed539 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed539 xs ys k (mixQuick acc (Digest.quick (op539 xs[k]! ys[k]!)))
def full539 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full539 xs ys k (Digest.full (op539 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run539 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.add[mixed]" xs ys (mixFull dx dy) timed539 full539 trials reps

/-! ### `bfloat16/ref.sub[mixed]` -/
@[inline] def op540 (x y : Brain) := ExecFloat.sub x y
def timed540 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed540 xs ys k (mixQuick acc (Digest.quick (op540 xs[k]! ys[k]!)))
def full540 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full540 xs ys k (Digest.full (op540 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run540 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.sub[mixed]" xs ys (mixFull dx dy) timed540 full540 trials reps

/-! ### `bfloat16/ref.mul[mixed]` -/
@[inline] def op541 (x y : Brain) := ExecFloat.mul x y
def timed541 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed541 xs ys k (mixQuick acc (Digest.quick (op541 xs[k]! ys[k]!)))
def full541 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full541 xs ys k (Digest.full (op541 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run541 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.mul[mixed]" xs ys (mixFull dx dy) timed541 full541 trials reps

/-! ### `bfloat16/ref.div[mixed]` -/
@[inline] def op542 (x y : Brain) := ExecFloat.div x y
def timed542 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed542 xs ys k (mixQuick acc (Digest.quick (op542 xs[k]! ys[k]!)))
def full542 (xs ys : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full542 xs ys k (Digest.full (op542 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run542 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  runB "bfloat16/ref.div[mixed]" xs ys (mixFull dx dy) timed542 full542 trials reps

/-! ### `bfloat16/ref.sqrt[mixed]` -/
@[inline] def op543 (x : Brain) := ExecFloat.sqrt x
def timed543 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed543 xs k (mixQuick acc (Digest.quick (op543 xs[k]!)))
def full543 (xs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full543 xs k (Digest.full (op543 xs[k]!) (mixFull h k.toUInt64))
def run543 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inBrain seedX count
  runU "bfloat16/ref.sqrt[mixed]" xs d timed543 full543 trials reps

/-! ### `bfloat16/ref.fma[mixed]` -/
@[inline] def op544 (x y z : Brain) := ExecFloat.fma x y z
def timed544 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed544 xs ys zs k (mixQuick acc (Digest.quick (op544 xs[k]! ys[k]! zs[k]!)))
def full544 (xs ys zs : Array Brain) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full544 xs ys zs k (Digest.full (op544 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run544 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inBrain seedX count
  let (ys, dy) := inBrain seedY count
  let (zs, dz) := inBrain seedZ count
  runT "bfloat16/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed544 full544 trials reps

/-! ### `binary32/ref.add[mixed]` -/
@[inline] def op545 (x y : Single) := ExecFloat.add x y
def timed545 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed545 xs ys k (mixQuick acc (Digest.quick (op545 xs[k]! ys[k]!)))
def full545 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full545 xs ys k (Digest.full (op545 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run545 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.add[mixed]" xs ys (mixFull dx dy) timed545 full545 trials reps

/-! ### `binary32/ref.sub[mixed]` -/
@[inline] def op546 (x y : Single) := ExecFloat.sub x y
def timed546 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed546 xs ys k (mixQuick acc (Digest.quick (op546 xs[k]! ys[k]!)))
def full546 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full546 xs ys k (Digest.full (op546 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run546 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.sub[mixed]" xs ys (mixFull dx dy) timed546 full546 trials reps

/-! ### `binary32/ref.mul[mixed]` -/
@[inline] def op547 (x y : Single) := ExecFloat.mul x y
def timed547 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed547 xs ys k (mixQuick acc (Digest.quick (op547 xs[k]! ys[k]!)))
def full547 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full547 xs ys k (Digest.full (op547 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run547 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.mul[mixed]" xs ys (mixFull dx dy) timed547 full547 trials reps

/-! ### `binary32/ref.div[mixed]` -/
@[inline] def op548 (x y : Single) := ExecFloat.div x y
def timed548 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed548 xs ys k (mixQuick acc (Digest.quick (op548 xs[k]! ys[k]!)))
def full548 (xs ys : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full548 xs ys k (Digest.full (op548 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run548 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  runB "binary32/ref.div[mixed]" xs ys (mixFull dx dy) timed548 full548 trials reps

/-! ### `binary32/ref.sqrt[mixed]` -/
@[inline] def op549 (x : Single) := ExecFloat.sqrt x
def timed549 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed549 xs k (mixQuick acc (Digest.quick (op549 xs[k]!)))
def full549 (xs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full549 xs k (Digest.full (op549 xs[k]!) (mixFull h k.toUInt64))
def run549 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inSingle seedX count
  runU "binary32/ref.sqrt[mixed]" xs d timed549 full549 trials reps

/-! ### `binary32/ref.fma[mixed]` -/
@[inline] def op550 (x y z : Single) := ExecFloat.fma x y z
def timed550 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed550 xs ys zs k (mixQuick acc (Digest.quick (op550 xs[k]! ys[k]! zs[k]!)))
def full550 (xs ys zs : Array Single) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full550 xs ys zs k (Digest.full (op550 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run550 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inSingle seedX count
  let (ys, dy) := inSingle seedY count
  let (zs, dz) := inSingle seedZ count
  runT "binary32/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed550 full550 trials reps

/-! ### `binary64/ref.add[mixed]` -/
@[inline] def op551 (x y : Double) := ExecFloat.add x y
def timed551 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed551 xs ys k (mixQuick acc (Digest.quick (op551 xs[k]! ys[k]!)))
def full551 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full551 xs ys k (Digest.full (op551 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run551 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.add[mixed]" xs ys (mixFull dx dy) timed551 full551 trials reps

/-! ### `binary64/ref.add[ordinary]` -/
@[inline] def op552 (x y : Double) := ExecFloat.add x y
def timed552 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed552 xs ys k (mixQuick acc (Digest.quick (op552 xs[k]! ys[k]!)))
def full552 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full552 xs ys k (Digest.full (op552 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run552 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.add[ordinary]" xs ys (mixFull dx dy) timed552 full552 trials reps

/-! ### `binary64/ref.add[tiny]` -/
@[inline] def op553 (x y : Double) := ExecFloat.add x y
def timed553 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed553 xs ys k (mixQuick acc (Digest.quick (op553 xs[k]! ys[k]!)))
def full553 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full553 xs ys k (Digest.full (op553 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run553 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.add[tiny]" xs ys (mixFull dx dy) timed553 full553 trials reps

/-! ### `binary64/ref.add[huge]` -/
@[inline] def op554 (x y : Double) := ExecFloat.add x y
def timed554 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed554 xs ys k (mixQuick acc (Digest.quick (op554 xs[k]! ys[k]!)))
def full554 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full554 xs ys k (Digest.full (op554 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run554 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.add[huge]" xs ys (mixFull dx dy) timed554 full554 trials reps

/-! ### `binary64/ref.add[subnormal]` -/
@[inline] def op555 (x y : Double) := ExecFloat.add x y
def timed555 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed555 xs ys k (mixQuick acc (Digest.quick (op555 xs[k]! ys[k]!)))
def full555 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full555 xs ys k (Digest.full (op555 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run555 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.add[subnormal]" xs ys (mixFull dx dy) timed555 full555 trials reps

/-! ### `binary64/ref.add[special]` -/
@[inline] def op556 (x y : Double) := ExecFloat.add x y
def timed556 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed556 xs ys k (mixQuick acc (Digest.quick (op556 xs[k]! ys[k]!)))
def full556 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full556 xs ys k (Digest.full (op556 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run556 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.add[special]" xs ys (mixFull dx dy) timed556 full556 trials reps

/-! ### `binary64/ref.sub[mixed]` -/
@[inline] def op557 (x y : Double) := ExecFloat.sub x y
def timed557 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed557 xs ys k (mixQuick acc (Digest.quick (op557 xs[k]! ys[k]!)))
def full557 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full557 xs ys k (Digest.full (op557 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run557 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.sub[mixed]" xs ys (mixFull dx dy) timed557 full557 trials reps

/-! ### `binary64/ref.sub[ordinary]` -/
@[inline] def op558 (x y : Double) := ExecFloat.sub x y
def timed558 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed558 xs ys k (mixQuick acc (Digest.quick (op558 xs[k]! ys[k]!)))
def full558 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full558 xs ys k (Digest.full (op558 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run558 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.sub[ordinary]" xs ys (mixFull dx dy) timed558 full558 trials reps

/-! ### `binary64/ref.sub[tiny]` -/
@[inline] def op559 (x y : Double) := ExecFloat.sub x y
def timed559 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed559 xs ys k (mixQuick acc (Digest.quick (op559 xs[k]! ys[k]!)))
def full559 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full559 xs ys k (Digest.full (op559 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run559 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.sub[tiny]" xs ys (mixFull dx dy) timed559 full559 trials reps

/-! ### `binary64/ref.sub[huge]` -/
@[inline] def op560 (x y : Double) := ExecFloat.sub x y
def timed560 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed560 xs ys k (mixQuick acc (Digest.quick (op560 xs[k]! ys[k]!)))
def full560 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full560 xs ys k (Digest.full (op560 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run560 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.sub[huge]" xs ys (mixFull dx dy) timed560 full560 trials reps

/-! ### `binary64/ref.sub[subnormal]` -/
@[inline] def op561 (x y : Double) := ExecFloat.sub x y
def timed561 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed561 xs ys k (mixQuick acc (Digest.quick (op561 xs[k]! ys[k]!)))
def full561 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full561 xs ys k (Digest.full (op561 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run561 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.sub[subnormal]" xs ys (mixFull dx dy) timed561 full561 trials reps

/-! ### `binary64/ref.sub[special]` -/
@[inline] def op562 (x y : Double) := ExecFloat.sub x y
def timed562 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed562 xs ys k (mixQuick acc (Digest.quick (op562 xs[k]! ys[k]!)))
def full562 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full562 xs ys k (Digest.full (op562 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run562 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.sub[special]" xs ys (mixFull dx dy) timed562 full562 trials reps

/-! ### `binary64/ref.mul[mixed]` -/
@[inline] def op563 (x y : Double) := ExecFloat.mul x y
def timed563 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed563 xs ys k (mixQuick acc (Digest.quick (op563 xs[k]! ys[k]!)))
def full563 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full563 xs ys k (Digest.full (op563 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run563 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.mul[mixed]" xs ys (mixFull dx dy) timed563 full563 trials reps

/-! ### `binary64/ref.mul[ordinary]` -/
@[inline] def op564 (x y : Double) := ExecFloat.mul x y
def timed564 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed564 xs ys k (mixQuick acc (Digest.quick (op564 xs[k]! ys[k]!)))
def full564 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full564 xs ys k (Digest.full (op564 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run564 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.mul[ordinary]" xs ys (mixFull dx dy) timed564 full564 trials reps

/-! ### `binary64/ref.mul[tiny]` -/
@[inline] def op565 (x y : Double) := ExecFloat.mul x y
def timed565 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed565 xs ys k (mixQuick acc (Digest.quick (op565 xs[k]! ys[k]!)))
def full565 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full565 xs ys k (Digest.full (op565 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run565 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.mul[tiny]" xs ys (mixFull dx dy) timed565 full565 trials reps

/-! ### `binary64/ref.mul[huge]` -/
@[inline] def op566 (x y : Double) := ExecFloat.mul x y
def timed566 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed566 xs ys k (mixQuick acc (Digest.quick (op566 xs[k]! ys[k]!)))
def full566 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full566 xs ys k (Digest.full (op566 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run566 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.mul[huge]" xs ys (mixFull dx dy) timed566 full566 trials reps

/-! ### `binary64/ref.mul[subnormal]` -/
@[inline] def op567 (x y : Double) := ExecFloat.mul x y
def timed567 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed567 xs ys k (mixQuick acc (Digest.quick (op567 xs[k]! ys[k]!)))
def full567 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full567 xs ys k (Digest.full (op567 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run567 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.mul[subnormal]" xs ys (mixFull dx dy) timed567 full567 trials reps

/-! ### `binary64/ref.mul[special]` -/
@[inline] def op568 (x y : Double) := ExecFloat.mul x y
def timed568 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed568 xs ys k (mixQuick acc (Digest.quick (op568 xs[k]! ys[k]!)))
def full568 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full568 xs ys k (Digest.full (op568 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run568 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.mul[special]" xs ys (mixFull dx dy) timed568 full568 trials reps

/-! ### `binary64/ref.div[mixed]` -/
@[inline] def op569 (x y : Double) := ExecFloat.div x y
def timed569 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed569 xs ys k (mixQuick acc (Digest.quick (op569 xs[k]! ys[k]!)))
def full569 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full569 xs ys k (Digest.full (op569 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run569 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  runB "binary64/ref.div[mixed]" xs ys (mixFull dx dy) timed569 full569 trials reps

/-! ### `binary64/ref.div[ordinary]` -/
@[inline] def op570 (x y : Double) := ExecFloat.div x y
def timed570 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed570 xs ys k (mixQuick acc (Digest.quick (op570 xs[k]! ys[k]!)))
def full570 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full570 xs ys k (Digest.full (op570 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run570 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  runB "binary64/ref.div[ordinary]" xs ys (mixFull dx dy) timed570 full570 trials reps

/-! ### `binary64/ref.div[tiny]` -/
@[inline] def op571 (x y : Double) := ExecFloat.div x y
def timed571 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed571 xs ys k (mixQuick acc (Digest.quick (op571 xs[k]! ys[k]!)))
def full571 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full571 xs ys k (Digest.full (op571 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run571 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  runB "binary64/ref.div[tiny]" xs ys (mixFull dx dy) timed571 full571 trials reps

/-! ### `binary64/ref.div[huge]` -/
@[inline] def op572 (x y : Double) := ExecFloat.div x y
def timed572 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed572 xs ys k (mixQuick acc (Digest.quick (op572 xs[k]! ys[k]!)))
def full572 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full572 xs ys k (Digest.full (op572 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run572 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  runB "binary64/ref.div[huge]" xs ys (mixFull dx dy) timed572 full572 trials reps

/-! ### `binary64/ref.div[subnormal]` -/
@[inline] def op573 (x y : Double) := ExecFloat.div x y
def timed573 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed573 xs ys k (mixQuick acc (Digest.quick (op573 xs[k]! ys[k]!)))
def full573 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full573 xs ys k (Digest.full (op573 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run573 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  runB "binary64/ref.div[subnormal]" xs ys (mixFull dx dy) timed573 full573 trials reps

/-! ### `binary64/ref.div[special]` -/
@[inline] def op574 (x y : Double) := ExecFloat.div x y
def timed574 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed574 xs ys k (mixQuick acc (Digest.quick (op574 xs[k]! ys[k]!)))
def full574 (xs ys : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full574 xs ys k (Digest.full (op574 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run574 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  runB "binary64/ref.div[special]" xs ys (mixFull dx dy) timed574 full574 trials reps

/-! ### `binary64/ref.sqrt[mixed]` -/
@[inline] def op575 (x : Double) := ExecFloat.sqrt x
def timed575 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed575 xs k (mixQuick acc (Digest.quick (op575 xs[k]!)))
def full575 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full575 xs k (Digest.full (op575 xs[k]!) (mixFull h k.toUInt64))
def run575 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count
  runU "binary64/ref.sqrt[mixed]" xs d timed575 full575 trials reps

/-! ### `binary64/ref.sqrt[ordinary]` -/
@[inline] def op576 (x : Double) := ExecFloat.sqrt x
def timed576 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed576 xs k (mixQuick acc (Digest.quick (op576 xs[k]!)))
def full576 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full576 xs k (Digest.full (op576 xs[k]!) (mixFull h k.toUInt64))
def run576 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 0)
  runU "binary64/ref.sqrt[ordinary]" xs d timed576 full576 trials reps

/-! ### `binary64/ref.sqrt[tiny]` -/
@[inline] def op577 (x : Double) := ExecFloat.sqrt x
def timed577 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed577 xs k (mixQuick acc (Digest.quick (op577 xs[k]!)))
def full577 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full577 xs k (Digest.full (op577 xs[k]!) (mixFull h k.toUInt64))
def run577 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 45)
  runU "binary64/ref.sqrt[tiny]" xs d timed577 full577 trials reps

/-! ### `binary64/ref.sqrt[huge]` -/
@[inline] def op578 (x : Double) := ExecFloat.sqrt x
def timed578 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed578 xs k (mixQuick acc (Digest.quick (op578 xs[k]!)))
def full578 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full578 xs k (Digest.full (op578 xs[k]!) (mixFull h k.toUInt64))
def run578 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 55)
  runU "binary64/ref.sqrt[huge]" xs d timed578 full578 trials reps

/-! ### `binary64/ref.sqrt[subnormal]` -/
@[inline] def op579 (x : Double) := ExecFloat.sqrt x
def timed579 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed579 xs k (mixQuick acc (Digest.quick (op579 xs[k]!)))
def full579 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full579 xs k (Digest.full (op579 xs[k]!) (mixFull h k.toUInt64))
def run579 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 65)
  runU "binary64/ref.sqrt[subnormal]" xs d timed579 full579 trials reps

/-! ### `binary64/ref.sqrt[special]` -/
@[inline] def op580 (x : Double) := ExecFloat.sqrt x
def timed580 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed580 xs k (mixQuick acc (Digest.quick (op580 xs[k]!)))
def full580 (xs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full580 xs k (Digest.full (op580 xs[k]!) (mixFull h k.toUInt64))
def run580 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inDouble seedX count (some 85)
  runU "binary64/ref.sqrt[special]" xs d timed580 full580 trials reps

/-! ### `binary64/ref.fma[mixed]` -/
@[inline] def op581 (x y z : Double) := ExecFloat.fma x y z
def timed581 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed581 xs ys zs k (mixQuick acc (Digest.quick (op581 xs[k]! ys[k]! zs[k]!)))
def full581 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full581 xs ys zs k (Digest.full (op581 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run581 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count
  let (ys, dy) := inDouble seedY count
  let (zs, dz) := inDouble seedZ count
  runT "binary64/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed581 full581 trials reps

/-! ### `binary64/ref.fma[ordinary]` -/
@[inline] def op582 (x y z : Double) := ExecFloat.fma x y z
def timed582 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed582 xs ys zs k (mixQuick acc (Digest.quick (op582 xs[k]! ys[k]! zs[k]!)))
def full582 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full582 xs ys zs k (Digest.full (op582 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run582 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 0)
  let (ys, dy) := inDouble seedY count (some 0)
  let (zs, dz) := inDouble seedZ count (some 0)
  runT "binary64/ref.fma[ordinary]" xs ys zs (mixFull (mixFull dx dy) dz) timed582 full582 trials reps

/-! ### `binary64/ref.fma[tiny]` -/
@[inline] def op583 (x y z : Double) := ExecFloat.fma x y z
def timed583 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed583 xs ys zs k (mixQuick acc (Digest.quick (op583 xs[k]! ys[k]! zs[k]!)))
def full583 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full583 xs ys zs k (Digest.full (op583 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run583 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 45)
  let (ys, dy) := inDouble seedY count (some 45)
  let (zs, dz) := inDouble seedZ count (some 45)
  runT "binary64/ref.fma[tiny]" xs ys zs (mixFull (mixFull dx dy) dz) timed583 full583 trials reps

/-! ### `binary64/ref.fma[huge]` -/
@[inline] def op584 (x y z : Double) := ExecFloat.fma x y z
def timed584 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed584 xs ys zs k (mixQuick acc (Digest.quick (op584 xs[k]! ys[k]! zs[k]!)))
def full584 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full584 xs ys zs k (Digest.full (op584 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run584 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 55)
  let (ys, dy) := inDouble seedY count (some 55)
  let (zs, dz) := inDouble seedZ count (some 55)
  runT "binary64/ref.fma[huge]" xs ys zs (mixFull (mixFull dx dy) dz) timed584 full584 trials reps

/-! ### `binary64/ref.fma[subnormal]` -/
@[inline] def op585 (x y z : Double) := ExecFloat.fma x y z
def timed585 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed585 xs ys zs k (mixQuick acc (Digest.quick (op585 xs[k]! ys[k]! zs[k]!)))
def full585 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full585 xs ys zs k (Digest.full (op585 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run585 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 65)
  let (ys, dy) := inDouble seedY count (some 65)
  let (zs, dz) := inDouble seedZ count (some 65)
  runT "binary64/ref.fma[subnormal]" xs ys zs (mixFull (mixFull dx dy) dz) timed585 full585 trials reps

/-! ### `binary64/ref.fma[special]` -/
@[inline] def op586 (x y z : Double) := ExecFloat.fma x y z
def timed586 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed586 xs ys zs k (mixQuick acc (Digest.quick (op586 xs[k]! ys[k]! zs[k]!)))
def full586 (xs ys zs : Array Double) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full586 xs ys zs k (Digest.full (op586 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run586 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inDouble seedX count (some 85)
  let (ys, dy) := inDouble seedY count (some 85)
  let (zs, dz) := inDouble seedZ count (some 85)
  runT "binary64/ref.fma[special]" xs ys zs (mixFull (mixFull dx dy) dz) timed586 full586 trials reps

/-! ### `binary128/ref.add[mixed]` -/
@[inline] def op587 (x y : Quad) := ExecFloat.add x y
def timed587 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed587 xs ys k (mixQuick acc (Digest.quick (op587 xs[k]! ys[k]!)))
def full587 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full587 xs ys k (Digest.full (op587 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run587 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.add[mixed]" xs ys (mixFull dx dy) timed587 full587 trials reps

/-! ### `binary128/ref.add[ordinary]` -/
@[inline] def op588 (x y : Quad) := ExecFloat.add x y
def timed588 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed588 xs ys k (mixQuick acc (Digest.quick (op588 xs[k]! ys[k]!)))
def full588 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full588 xs ys k (Digest.full (op588 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run588 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.add[ordinary]" xs ys (mixFull dx dy) timed588 full588 trials reps

/-! ### `binary128/ref.add[tiny]` -/
@[inline] def op589 (x y : Quad) := ExecFloat.add x y
def timed589 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed589 xs ys k (mixQuick acc (Digest.quick (op589 xs[k]! ys[k]!)))
def full589 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full589 xs ys k (Digest.full (op589 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run589 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.add[tiny]" xs ys (mixFull dx dy) timed589 full589 trials reps

/-! ### `binary128/ref.add[huge]` -/
@[inline] def op590 (x y : Quad) := ExecFloat.add x y
def timed590 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed590 xs ys k (mixQuick acc (Digest.quick (op590 xs[k]! ys[k]!)))
def full590 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full590 xs ys k (Digest.full (op590 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run590 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.add[huge]" xs ys (mixFull dx dy) timed590 full590 trials reps

/-! ### `binary128/ref.add[subnormal]` -/
@[inline] def op591 (x y : Quad) := ExecFloat.add x y
def timed591 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed591 xs ys k (mixQuick acc (Digest.quick (op591 xs[k]! ys[k]!)))
def full591 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full591 xs ys k (Digest.full (op591 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run591 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.add[subnormal]" xs ys (mixFull dx dy) timed591 full591 trials reps

/-! ### `binary128/ref.add[special]` -/
@[inline] def op592 (x y : Quad) := ExecFloat.add x y
def timed592 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed592 xs ys k (mixQuick acc (Digest.quick (op592 xs[k]! ys[k]!)))
def full592 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full592 xs ys k (Digest.full (op592 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run592 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.add[special]" xs ys (mixFull dx dy) timed592 full592 trials reps

/-! ### `binary128/ref.sub[mixed]` -/
@[inline] def op593 (x y : Quad) := ExecFloat.sub x y
def timed593 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed593 xs ys k (mixQuick acc (Digest.quick (op593 xs[k]! ys[k]!)))
def full593 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full593 xs ys k (Digest.full (op593 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run593 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.sub[mixed]" xs ys (mixFull dx dy) timed593 full593 trials reps

/-! ### `binary128/ref.sub[ordinary]` -/
@[inline] def op594 (x y : Quad) := ExecFloat.sub x y
def timed594 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed594 xs ys k (mixQuick acc (Digest.quick (op594 xs[k]! ys[k]!)))
def full594 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full594 xs ys k (Digest.full (op594 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run594 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.sub[ordinary]" xs ys (mixFull dx dy) timed594 full594 trials reps

/-! ### `binary128/ref.sub[tiny]` -/
@[inline] def op595 (x y : Quad) := ExecFloat.sub x y
def timed595 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed595 xs ys k (mixQuick acc (Digest.quick (op595 xs[k]! ys[k]!)))
def full595 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full595 xs ys k (Digest.full (op595 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run595 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.sub[tiny]" xs ys (mixFull dx dy) timed595 full595 trials reps

/-! ### `binary128/ref.sub[huge]` -/
@[inline] def op596 (x y : Quad) := ExecFloat.sub x y
def timed596 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed596 xs ys k (mixQuick acc (Digest.quick (op596 xs[k]! ys[k]!)))
def full596 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full596 xs ys k (Digest.full (op596 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run596 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.sub[huge]" xs ys (mixFull dx dy) timed596 full596 trials reps

/-! ### `binary128/ref.sub[subnormal]` -/
@[inline] def op597 (x y : Quad) := ExecFloat.sub x y
def timed597 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed597 xs ys k (mixQuick acc (Digest.quick (op597 xs[k]! ys[k]!)))
def full597 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full597 xs ys k (Digest.full (op597 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run597 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.sub[subnormal]" xs ys (mixFull dx dy) timed597 full597 trials reps

/-! ### `binary128/ref.sub[special]` -/
@[inline] def op598 (x y : Quad) := ExecFloat.sub x y
def timed598 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed598 xs ys k (mixQuick acc (Digest.quick (op598 xs[k]! ys[k]!)))
def full598 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full598 xs ys k (Digest.full (op598 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run598 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.sub[special]" xs ys (mixFull dx dy) timed598 full598 trials reps

/-! ### `binary128/ref.mul[mixed]` -/
@[inline] def op599 (x y : Quad) := ExecFloat.mul x y
def timed599 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed599 xs ys k (mixQuick acc (Digest.quick (op599 xs[k]! ys[k]!)))
def full599 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full599 xs ys k (Digest.full (op599 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run599 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.mul[mixed]" xs ys (mixFull dx dy) timed599 full599 trials reps

/-! ### `binary128/ref.mul[ordinary]` -/
@[inline] def op600 (x y : Quad) := ExecFloat.mul x y
def timed600 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed600 xs ys k (mixQuick acc (Digest.quick (op600 xs[k]! ys[k]!)))
def full600 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full600 xs ys k (Digest.full (op600 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run600 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.mul[ordinary]" xs ys (mixFull dx dy) timed600 full600 trials reps

/-! ### `binary128/ref.mul[tiny]` -/
@[inline] def op601 (x y : Quad) := ExecFloat.mul x y
def timed601 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed601 xs ys k (mixQuick acc (Digest.quick (op601 xs[k]! ys[k]!)))
def full601 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full601 xs ys k (Digest.full (op601 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run601 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.mul[tiny]" xs ys (mixFull dx dy) timed601 full601 trials reps

/-! ### `binary128/ref.mul[huge]` -/
@[inline] def op602 (x y : Quad) := ExecFloat.mul x y
def timed602 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed602 xs ys k (mixQuick acc (Digest.quick (op602 xs[k]! ys[k]!)))
def full602 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full602 xs ys k (Digest.full (op602 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run602 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.mul[huge]" xs ys (mixFull dx dy) timed602 full602 trials reps

/-! ### `binary128/ref.mul[subnormal]` -/
@[inline] def op603 (x y : Quad) := ExecFloat.mul x y
def timed603 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed603 xs ys k (mixQuick acc (Digest.quick (op603 xs[k]! ys[k]!)))
def full603 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full603 xs ys k (Digest.full (op603 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run603 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.mul[subnormal]" xs ys (mixFull dx dy) timed603 full603 trials reps

/-! ### `binary128/ref.mul[special]` -/
@[inline] def op604 (x y : Quad) := ExecFloat.mul x y
def timed604 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed604 xs ys k (mixQuick acc (Digest.quick (op604 xs[k]! ys[k]!)))
def full604 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full604 xs ys k (Digest.full (op604 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run604 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.mul[special]" xs ys (mixFull dx dy) timed604 full604 trials reps

/-! ### `binary128/ref.div[mixed]` -/
@[inline] def op605 (x y : Quad) := ExecFloat.div x y
def timed605 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed605 xs ys k (mixQuick acc (Digest.quick (op605 xs[k]! ys[k]!)))
def full605 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full605 xs ys k (Digest.full (op605 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run605 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  runB "binary128/ref.div[mixed]" xs ys (mixFull dx dy) timed605 full605 trials reps

/-! ### `binary128/ref.div[ordinary]` -/
@[inline] def op606 (x y : Quad) := ExecFloat.div x y
def timed606 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed606 xs ys k (mixQuick acc (Digest.quick (op606 xs[k]! ys[k]!)))
def full606 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full606 xs ys k (Digest.full (op606 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run606 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  runB "binary128/ref.div[ordinary]" xs ys (mixFull dx dy) timed606 full606 trials reps

/-! ### `binary128/ref.div[tiny]` -/
@[inline] def op607 (x y : Quad) := ExecFloat.div x y
def timed607 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed607 xs ys k (mixQuick acc (Digest.quick (op607 xs[k]! ys[k]!)))
def full607 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full607 xs ys k (Digest.full (op607 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run607 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  runB "binary128/ref.div[tiny]" xs ys (mixFull dx dy) timed607 full607 trials reps

/-! ### `binary128/ref.div[huge]` -/
@[inline] def op608 (x y : Quad) := ExecFloat.div x y
def timed608 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed608 xs ys k (mixQuick acc (Digest.quick (op608 xs[k]! ys[k]!)))
def full608 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full608 xs ys k (Digest.full (op608 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run608 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  runB "binary128/ref.div[huge]" xs ys (mixFull dx dy) timed608 full608 trials reps

/-! ### `binary128/ref.div[subnormal]` -/
@[inline] def op609 (x y : Quad) := ExecFloat.div x y
def timed609 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed609 xs ys k (mixQuick acc (Digest.quick (op609 xs[k]! ys[k]!)))
def full609 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full609 xs ys k (Digest.full (op609 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run609 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  runB "binary128/ref.div[subnormal]" xs ys (mixFull dx dy) timed609 full609 trials reps

/-! ### `binary128/ref.div[special]` -/
@[inline] def op610 (x y : Quad) := ExecFloat.div x y
def timed610 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed610 xs ys k (mixQuick acc (Digest.quick (op610 xs[k]! ys[k]!)))
def full610 (xs ys : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full610 xs ys k (Digest.full (op610 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run610 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  runB "binary128/ref.div[special]" xs ys (mixFull dx dy) timed610 full610 trials reps

/-! ### `binary128/ref.sqrt[mixed]` -/
@[inline] def op611 (x : Quad) := ExecFloat.sqrt x
def timed611 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed611 xs k (mixQuick acc (Digest.quick (op611 xs[k]!)))
def full611 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full611 xs k (Digest.full (op611 xs[k]!) (mixFull h k.toUInt64))
def run611 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count
  runU "binary128/ref.sqrt[mixed]" xs d timed611 full611 trials reps

/-! ### `binary128/ref.sqrt[ordinary]` -/
@[inline] def op612 (x : Quad) := ExecFloat.sqrt x
def timed612 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed612 xs k (mixQuick acc (Digest.quick (op612 xs[k]!)))
def full612 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full612 xs k (Digest.full (op612 xs[k]!) (mixFull h k.toUInt64))
def run612 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 0)
  runU "binary128/ref.sqrt[ordinary]" xs d timed612 full612 trials reps

/-! ### `binary128/ref.sqrt[tiny]` -/
@[inline] def op613 (x : Quad) := ExecFloat.sqrt x
def timed613 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed613 xs k (mixQuick acc (Digest.quick (op613 xs[k]!)))
def full613 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full613 xs k (Digest.full (op613 xs[k]!) (mixFull h k.toUInt64))
def run613 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 45)
  runU "binary128/ref.sqrt[tiny]" xs d timed613 full613 trials reps

/-! ### `binary128/ref.sqrt[huge]` -/
@[inline] def op614 (x : Quad) := ExecFloat.sqrt x
def timed614 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed614 xs k (mixQuick acc (Digest.quick (op614 xs[k]!)))
def full614 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full614 xs k (Digest.full (op614 xs[k]!) (mixFull h k.toUInt64))
def run614 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 55)
  runU "binary128/ref.sqrt[huge]" xs d timed614 full614 trials reps

/-! ### `binary128/ref.sqrt[subnormal]` -/
@[inline] def op615 (x : Quad) := ExecFloat.sqrt x
def timed615 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed615 xs k (mixQuick acc (Digest.quick (op615 xs[k]!)))
def full615 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full615 xs k (Digest.full (op615 xs[k]!) (mixFull h k.toUInt64))
def run615 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 65)
  runU "binary128/ref.sqrt[subnormal]" xs d timed615 full615 trials reps

/-! ### `binary128/ref.sqrt[special]` -/
@[inline] def op616 (x : Quad) := ExecFloat.sqrt x
def timed616 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed616 xs k (mixQuick acc (Digest.quick (op616 xs[k]!)))
def full616 (xs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full616 xs k (Digest.full (op616 xs[k]!) (mixFull h k.toUInt64))
def run616 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inQuad seedX count (some 85)
  runU "binary128/ref.sqrt[special]" xs d timed616 full616 trials reps

/-! ### `binary128/ref.fma[mixed]` -/
@[inline] def op617 (x y z : Quad) := ExecFloat.fma x y z
def timed617 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed617 xs ys zs k (mixQuick acc (Digest.quick (op617 xs[k]! ys[k]! zs[k]!)))
def full617 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full617 xs ys zs k (Digest.full (op617 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run617 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count
  let (ys, dy) := inQuad seedY count
  let (zs, dz) := inQuad seedZ count
  runT "binary128/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed617 full617 trials reps

/-! ### `binary128/ref.fma[ordinary]` -/
@[inline] def op618 (x y z : Quad) := ExecFloat.fma x y z
def timed618 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed618 xs ys zs k (mixQuick acc (Digest.quick (op618 xs[k]! ys[k]! zs[k]!)))
def full618 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full618 xs ys zs k (Digest.full (op618 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run618 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 0)
  let (ys, dy) := inQuad seedY count (some 0)
  let (zs, dz) := inQuad seedZ count (some 0)
  runT "binary128/ref.fma[ordinary]" xs ys zs (mixFull (mixFull dx dy) dz) timed618 full618 trials reps

/-! ### `binary128/ref.fma[tiny]` -/
@[inline] def op619 (x y z : Quad) := ExecFloat.fma x y z
def timed619 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed619 xs ys zs k (mixQuick acc (Digest.quick (op619 xs[k]! ys[k]! zs[k]!)))
def full619 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full619 xs ys zs k (Digest.full (op619 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run619 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 45)
  let (ys, dy) := inQuad seedY count (some 45)
  let (zs, dz) := inQuad seedZ count (some 45)
  runT "binary128/ref.fma[tiny]" xs ys zs (mixFull (mixFull dx dy) dz) timed619 full619 trials reps

/-! ### `binary128/ref.fma[huge]` -/
@[inline] def op620 (x y z : Quad) := ExecFloat.fma x y z
def timed620 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed620 xs ys zs k (mixQuick acc (Digest.quick (op620 xs[k]! ys[k]! zs[k]!)))
def full620 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full620 xs ys zs k (Digest.full (op620 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run620 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 55)
  let (ys, dy) := inQuad seedY count (some 55)
  let (zs, dz) := inQuad seedZ count (some 55)
  runT "binary128/ref.fma[huge]" xs ys zs (mixFull (mixFull dx dy) dz) timed620 full620 trials reps

/-! ### `binary128/ref.fma[subnormal]` -/
@[inline] def op621 (x y z : Quad) := ExecFloat.fma x y z
def timed621 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed621 xs ys zs k (mixQuick acc (Digest.quick (op621 xs[k]! ys[k]! zs[k]!)))
def full621 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full621 xs ys zs k (Digest.full (op621 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run621 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 65)
  let (ys, dy) := inQuad seedY count (some 65)
  let (zs, dz) := inQuad seedZ count (some 65)
  runT "binary128/ref.fma[subnormal]" xs ys zs (mixFull (mixFull dx dy) dz) timed621 full621 trials reps

/-! ### `binary128/ref.fma[special]` -/
@[inline] def op622 (x y z : Quad) := ExecFloat.fma x y z
def timed622 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed622 xs ys zs k (mixQuick acc (Digest.quick (op622 xs[k]! ys[k]! zs[k]!)))
def full622 (xs ys zs : Array Quad) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full622 xs ys zs k (Digest.full (op622 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run622 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inQuad seedX count (some 85)
  let (ys, dy) := inQuad seedY count (some 85)
  let (zs, dz) := inQuad seedZ count (some 85)
  runT "binary128/ref.fma[special]" xs ys zs (mixFull (mixFull dx dy) dz) timed622 full622 trials reps

/-! ### `posit32/ref.add[mixed]` -/
@[inline] def op623 (x y : P32) := ExecFloat.add x y
def timed623 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed623 xs ys k (mixQuick acc (Digest.quick (op623 xs[k]! ys[k]!)))
def full623 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full623 xs ys k (Digest.full (op623 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run623 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.add[mixed]" xs ys (mixFull dx dy) timed623 full623 trials reps

/-! ### `posit32/ref.sub[mixed]` -/
@[inline] def op624 (x y : P32) := ExecFloat.sub x y
def timed624 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed624 xs ys k (mixQuick acc (Digest.quick (op624 xs[k]! ys[k]!)))
def full624 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full624 xs ys k (Digest.full (op624 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run624 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.sub[mixed]" xs ys (mixFull dx dy) timed624 full624 trials reps

/-! ### `posit32/ref.mul[mixed]` -/
@[inline] def op625 (x y : P32) := ExecFloat.mul x y
def timed625 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed625 xs ys k (mixQuick acc (Digest.quick (op625 xs[k]! ys[k]!)))
def full625 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full625 xs ys k (Digest.full (op625 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run625 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.mul[mixed]" xs ys (mixFull dx dy) timed625 full625 trials reps

/-! ### `posit32/ref.div[mixed]` -/
@[inline] def op626 (x y : P32) := ExecFloat.div x y
def timed626 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed626 xs ys k (mixQuick acc (Digest.quick (op626 xs[k]! ys[k]!)))
def full626 (xs ys : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full626 xs ys k (Digest.full (op626 xs[k]! ys[k]!) (mixFull h k.toUInt64))
def run626 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  runB "posit32/ref.div[mixed]" xs ys (mixFull dx dy) timed626 full626 trials reps

/-! ### `posit32/ref.sqrt[mixed]` -/
@[inline] def op627 (x : P32) := ExecFloat.sqrt x
def timed627 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed627 xs k (mixQuick acc (Digest.quick (op627 xs[k]!)))
def full627 (xs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full627 xs k (Digest.full (op627 xs[k]!) (mixFull h k.toUInt64))
def run627 (count trials reps : Nat) : IO Unit := do
  let (xs, d) := inP32 seedX count
  runU "posit32/ref.sqrt[mixed]" xs d timed627 full627 trials reps

/-! ### `posit32/ref.fma[mixed]` -/
@[inline] def op628 (x y z : P32) := ExecFloat.fma x y z
def timed628 (xs ys zs : Array P32) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | k + 1, acc => timed628 xs ys zs k (mixQuick acc (Digest.quick (op628 xs[k]! ys[k]! zs[k]!)))
def full628 (xs ys zs : Array P32) : Nat → UInt64 → UInt64
  | 0, h => h
  | k + 1, h => full628 xs ys zs k (Digest.full (op628 xs[k]! ys[k]! zs[k]!) (mixFull h k.toUInt64))
def run628 (count trials reps : Nat) : IO Unit := do
  let (xs, dx) := inP32 seedX count
  let (ys, dy) := inP32 seedY count
  let (zs, dz) := inP32 seedZ count
  runT "posit32/ref.fma[mixed]" xs ys zs (mixFull (mixFull dx dy) dz) timed628 full628 trials reps

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

/-- Every timed cell, by name. -/
def cells : Array (String × (Nat → Nat → Nat → IO Unit)) := #[
  ("binary64->binary32/cast", run0),
  ("binary64->binary32/Model.cast", run1),
  ("binary32->binary64/cast", run2),
  ("binary32->binary64/Model.cast", run3),
  ("binary64->binary16/cast", run4),
  ("binary64->binary16/Model.cast", run5),
  ("binary16->binary64/cast", run6),
  ("binary16->binary64/Model.cast", run7),
  ("binary64->binary128/cast", run8),
  ("binary64->binary128/Model.cast", run9),
  ("binary128->binary64/cast", run10),
  ("binary128->binary64/Model.cast", run11),
  ("binary64->bfloat16/cast", run12),
  ("binary64->bfloat16/Model.cast", run13),
  ("bfloat16->binary32/cast", run14),
  ("bfloat16->binary32/Model.cast", run15),
  ("binary32->binary16/cast", run16),
  ("binary32->binary16/Model.cast", run17),
  ("binary16->binary32/cast", run18),
  ("binary16->binary32/Model.cast", run19),
  ("binary32->bfloat16/cast", run20),
  ("binary32->bfloat16/Model.cast", run21),
  ("binary128->binary32/cast", run22),
  ("binary128->binary32/Model.cast", run23),
  ("binary256->binary64/cast", run24),
  ("binary256->binary64/Model.cast", run25),
  ("binary64->binary256/cast", run26),
  ("binary64->binary256/Model.cast", run27),
  ("binary128->binary256/cast", run28),
  ("binary128->binary256/Model.cast", run29),
  ("binary256->binary128/cast", run30),
  ("binary256->binary128/Model.cast", run31),
  ("posit32->binary64/cast", run32),
  ("binary64->posit32/cast", run33),
  ("posit32->binary32/cast", run34),
  ("binary16/convertFromInt64", run35),
  ("binary16/intToFloat64", run36),
  ("binary16/floatToInt64[nearest]", run37),
  ("binary16/floatToInt64[towardZero]", run38),
  ("binary16/roundToIntegral[nearest]", run39),
  ("binary16/roundToIntegral[towardZero]", run40),
  ("binary16/roundToIntegral[up]", run41),
  ("binary16/roundToIntegral[down]", run42),
  ("binary16/roundToIntegral[status]", run43),
  ("binary16/remainder", run44),
  ("binary16/compareLess", run45),
  ("binary16/compareLessEqual", run46),
  ("binary16/beq", run47),
  ("binary16/compare", run48),
  ("binary16/compareQuietLess", run49),
  ("binary16/compareQuietEqual", run50),
  ("binary16/compareSignalingLessEqual", run51),
  ("binary16/totalOrder", run52),
  ("binary16/totalOrderMag", run53),
  ("binary16/maximum", run54),
  ("binary16/minimum", run55),
  ("binary16/maxNum", run56),
  ("binary16/minNum", run57),
  ("binary16/maximumNumber", run58),
  ("binary16/minimumNumber", run59),
  ("binary16/nextUp", run60),
  ("binary16/nextDown", run61),
  ("binary16/scale", run62),
  ("binary16/binaryExponent", run63),
  ("binary16/binaryExponentInt", run64),
  ("binary16/negate", run65),
  ("binary16/abs", run66),
  ("binary16/copySign", run67),
  ("binary16/isNaN", run68),
  ("binary16/isNormal", run69),
  ("binary16/isSubnormal", run70),
  ("binary16/isZero", run71),
  ("binary16/isFinite", run72),
  ("binary16/isInfinite", run73),
  ("binary16/isSignalingNaN", run74),
  ("binary16/signBit", run75),
  ("binary16/classify", run76),
  ("binary16/isCanonical", run77),
  ("binary16/format[scientific]", run78),
  ("binary16/format[exact]", run79),
  ("binary16/format[hex]", run80),
  ("binary16/toString", run81),
  ("binary16/parse", run82),
  ("binary16/parse[status]", run83),
  ("binary16/add[up]", run84),
  ("binary16/mul[up]", run85),
  ("binary16/div[up]", run86),
  ("binary16/sqrt[up]", run87),
  ("binary16/fma[up]", run88),
  ("binary16/add[down]", run89),
  ("binary16/mul[down]", run90),
  ("binary16/div[down]", run91),
  ("binary16/sqrt[down]", run92),
  ("binary16/fma[down]", run93),
  ("binary16/add[towardZero]", run94),
  ("binary16/mul[towardZero]", run95),
  ("binary16/div[towardZero]", run96),
  ("binary16/sqrt[towardZero]", run97),
  ("binary16/fma[towardZero]", run98),
  ("binary16/add[status]", run99),
  ("binary16/sub[status]", run100),
  ("binary16/mul[status]", run101),
  ("binary16/div[status]", run102),
  ("binary16/sqrt[status]", run103),
  ("binary16/fma[status]", run104),
  ("binary16/square", run105),
  ("binary16/exp", run106),
  ("binary16/log", run107),
  ("binary16/sin", run108),
  ("binary16/pow", run109),
  ("binary16/powInt", run110),
  ("binary16/rsqrt", run111),
  ("binary16/hypot", run112),
  ("binary16/rootN3", run113),
  ("binary16/exp[certify]", run114),
  ("binary16/log[certify]", run115),
  ("binary16/cos", run116),
  ("binary16/tanh", run117),
  ("binary16/expMinus1", run118),
  ("binary16/logPlus1", run119),
  ("binary16/sum8", run120),
  ("binary16/dot8", run121),
  ("bfloat16/convertFromInt64", run122),
  ("bfloat16/intToFloat64", run123),
  ("bfloat16/floatToInt64[nearest]", run124),
  ("bfloat16/floatToInt64[towardZero]", run125),
  ("bfloat16/roundToIntegral[nearest]", run126),
  ("bfloat16/roundToIntegral[towardZero]", run127),
  ("bfloat16/roundToIntegral[up]", run128),
  ("bfloat16/roundToIntegral[down]", run129),
  ("bfloat16/roundToIntegral[status]", run130),
  ("bfloat16/remainder", run131),
  ("bfloat16/compareLess", run132),
  ("bfloat16/compareLessEqual", run133),
  ("bfloat16/beq", run134),
  ("bfloat16/compare", run135),
  ("bfloat16/compareQuietLess", run136),
  ("bfloat16/compareQuietEqual", run137),
  ("bfloat16/compareSignalingLessEqual", run138),
  ("bfloat16/totalOrder", run139),
  ("bfloat16/totalOrderMag", run140),
  ("bfloat16/maximum", run141),
  ("bfloat16/minimum", run142),
  ("bfloat16/maxNum", run143),
  ("bfloat16/minNum", run144),
  ("bfloat16/maximumNumber", run145),
  ("bfloat16/minimumNumber", run146),
  ("bfloat16/nextUp", run147),
  ("bfloat16/nextDown", run148),
  ("bfloat16/scale", run149),
  ("bfloat16/binaryExponent", run150),
  ("bfloat16/binaryExponentInt", run151),
  ("bfloat16/negate", run152),
  ("bfloat16/abs", run153),
  ("bfloat16/copySign", run154),
  ("bfloat16/isNaN", run155),
  ("bfloat16/isNormal", run156),
  ("bfloat16/isSubnormal", run157),
  ("bfloat16/isZero", run158),
  ("bfloat16/isFinite", run159),
  ("bfloat16/isInfinite", run160),
  ("bfloat16/isSignalingNaN", run161),
  ("bfloat16/signBit", run162),
  ("bfloat16/classify", run163),
  ("bfloat16/isCanonical", run164),
  ("bfloat16/format[scientific]", run165),
  ("bfloat16/format[exact]", run166),
  ("bfloat16/format[hex]", run167),
  ("bfloat16/toString", run168),
  ("bfloat16/parse", run169),
  ("bfloat16/parse[status]", run170),
  ("bfloat16/add[up]", run171),
  ("bfloat16/mul[up]", run172),
  ("bfloat16/div[up]", run173),
  ("bfloat16/sqrt[up]", run174),
  ("bfloat16/fma[up]", run175),
  ("bfloat16/add[down]", run176),
  ("bfloat16/mul[down]", run177),
  ("bfloat16/div[down]", run178),
  ("bfloat16/sqrt[down]", run179),
  ("bfloat16/fma[down]", run180),
  ("bfloat16/add[towardZero]", run181),
  ("bfloat16/mul[towardZero]", run182),
  ("bfloat16/div[towardZero]", run183),
  ("bfloat16/sqrt[towardZero]", run184),
  ("bfloat16/fma[towardZero]", run185),
  ("bfloat16/add[status]", run186),
  ("bfloat16/sub[status]", run187),
  ("bfloat16/mul[status]", run188),
  ("bfloat16/div[status]", run189),
  ("bfloat16/sqrt[status]", run190),
  ("bfloat16/fma[status]", run191),
  ("bfloat16/square", run192),
  ("bfloat16/exp", run193),
  ("bfloat16/log", run194),
  ("bfloat16/sin", run195),
  ("bfloat16/pow", run196),
  ("bfloat16/powInt", run197),
  ("bfloat16/rsqrt", run198),
  ("bfloat16/hypot", run199),
  ("bfloat16/rootN3", run200),
  ("bfloat16/exp[certify]", run201),
  ("bfloat16/log[certify]", run202),
  ("bfloat16/cos", run203),
  ("bfloat16/tanh", run204),
  ("bfloat16/expMinus1", run205),
  ("bfloat16/logPlus1", run206),
  ("bfloat16/sum8", run207),
  ("bfloat16/dot8", run208),
  ("binary32/convertFromInt64", run209),
  ("binary32/intToFloat64", run210),
  ("binary32/floatToInt64[nearest]", run211),
  ("binary32/floatToInt64[towardZero]", run212),
  ("binary32/roundToIntegral[nearest]", run213),
  ("binary32/roundToIntegral[towardZero]", run214),
  ("binary32/roundToIntegral[up]", run215),
  ("binary32/roundToIntegral[down]", run216),
  ("binary32/roundToIntegral[status]", run217),
  ("binary32/remainder", run218),
  ("binary32/compareLess", run219),
  ("binary32/compareLessEqual", run220),
  ("binary32/beq", run221),
  ("binary32/compare", run222),
  ("binary32/compareQuietLess", run223),
  ("binary32/compareQuietEqual", run224),
  ("binary32/compareSignalingLessEqual", run225),
  ("binary32/totalOrder", run226),
  ("binary32/totalOrderMag", run227),
  ("binary32/maximum", run228),
  ("binary32/minimum", run229),
  ("binary32/maxNum", run230),
  ("binary32/minNum", run231),
  ("binary32/maximumNumber", run232),
  ("binary32/minimumNumber", run233),
  ("binary32/nextUp", run234),
  ("binary32/nextDown", run235),
  ("binary32/scale", run236),
  ("binary32/binaryExponent", run237),
  ("binary32/binaryExponentInt", run238),
  ("binary32/negate", run239),
  ("binary32/abs", run240),
  ("binary32/copySign", run241),
  ("binary32/isNaN", run242),
  ("binary32/isNormal", run243),
  ("binary32/isSubnormal", run244),
  ("binary32/isZero", run245),
  ("binary32/isFinite", run246),
  ("binary32/isInfinite", run247),
  ("binary32/isSignalingNaN", run248),
  ("binary32/signBit", run249),
  ("binary32/classify", run250),
  ("binary32/isCanonical", run251),
  ("binary32/format[scientific]", run252),
  ("binary32/format[exact]", run253),
  ("binary32/format[hex]", run254),
  ("binary32/toString", run255),
  ("binary32/parse", run256),
  ("binary32/parse[status]", run257),
  ("binary32/add[up]", run258),
  ("binary32/mul[up]", run259),
  ("binary32/div[up]", run260),
  ("binary32/sqrt[up]", run261),
  ("binary32/fma[up]", run262),
  ("binary32/add[down]", run263),
  ("binary32/mul[down]", run264),
  ("binary32/div[down]", run265),
  ("binary32/sqrt[down]", run266),
  ("binary32/fma[down]", run267),
  ("binary32/add[towardZero]", run268),
  ("binary32/mul[towardZero]", run269),
  ("binary32/div[towardZero]", run270),
  ("binary32/sqrt[towardZero]", run271),
  ("binary32/fma[towardZero]", run272),
  ("binary32/add[status]", run273),
  ("binary32/sub[status]", run274),
  ("binary32/mul[status]", run275),
  ("binary32/div[status]", run276),
  ("binary32/sqrt[status]", run277),
  ("binary32/fma[status]", run278),
  ("binary32/square", run279),
  ("binary32/exp", run280),
  ("binary32/log", run281),
  ("binary32/sin", run282),
  ("binary32/pow", run283),
  ("binary32/powInt", run284),
  ("binary32/rsqrt", run285),
  ("binary32/hypot", run286),
  ("binary32/rootN3", run287),
  ("binary32/exp[certify]", run288),
  ("binary32/log[certify]", run289),
  ("binary32/cos", run290),
  ("binary32/tanh", run291),
  ("binary32/expMinus1", run292),
  ("binary32/logPlus1", run293),
  ("binary32/sum8", run294),
  ("binary32/dot8", run295),
  ("binary64/convertFromInt64", run296),
  ("binary64/intToFloat64", run297),
  ("binary64/floatToInt64[nearest]", run298),
  ("binary64/floatToInt64[towardZero]", run299),
  ("binary64/roundToIntegral[nearest]", run300),
  ("binary64/roundToIntegral[towardZero]", run301),
  ("binary64/roundToIntegral[up]", run302),
  ("binary64/roundToIntegral[down]", run303),
  ("binary64/roundToIntegral[status]", run304),
  ("binary64/remainder", run305),
  ("binary64/compareLess", run306),
  ("binary64/compareLessEqual", run307),
  ("binary64/beq", run308),
  ("binary64/compare", run309),
  ("binary64/compareQuietLess", run310),
  ("binary64/compareQuietEqual", run311),
  ("binary64/compareSignalingLessEqual", run312),
  ("binary64/totalOrder", run313),
  ("binary64/totalOrderMag", run314),
  ("binary64/maximum", run315),
  ("binary64/minimum", run316),
  ("binary64/maxNum", run317),
  ("binary64/minNum", run318),
  ("binary64/maximumNumber", run319),
  ("binary64/minimumNumber", run320),
  ("binary64/nextUp", run321),
  ("binary64/nextDown", run322),
  ("binary64/scale", run323),
  ("binary64/binaryExponent", run324),
  ("binary64/binaryExponentInt", run325),
  ("binary64/negate", run326),
  ("binary64/abs", run327),
  ("binary64/copySign", run328),
  ("binary64/isNaN", run329),
  ("binary64/isNormal", run330),
  ("binary64/isSubnormal", run331),
  ("binary64/isZero", run332),
  ("binary64/isFinite", run333),
  ("binary64/isInfinite", run334),
  ("binary64/isSignalingNaN", run335),
  ("binary64/signBit", run336),
  ("binary64/classify", run337),
  ("binary64/isCanonical", run338),
  ("binary64/format[scientific]", run339),
  ("binary64/format[exact]", run340),
  ("binary64/format[hex]", run341),
  ("binary64/toString", run342),
  ("binary64/parse", run343),
  ("binary64/parse[status]", run344),
  ("binary64/add[up]", run345),
  ("binary64/mul[up]", run346),
  ("binary64/div[up]", run347),
  ("binary64/sqrt[up]", run348),
  ("binary64/fma[up]", run349),
  ("binary64/add[down]", run350),
  ("binary64/mul[down]", run351),
  ("binary64/div[down]", run352),
  ("binary64/sqrt[down]", run353),
  ("binary64/fma[down]", run354),
  ("binary64/add[towardZero]", run355),
  ("binary64/mul[towardZero]", run356),
  ("binary64/div[towardZero]", run357),
  ("binary64/sqrt[towardZero]", run358),
  ("binary64/fma[towardZero]", run359),
  ("binary64/add[status]", run360),
  ("binary64/sub[status]", run361),
  ("binary64/mul[status]", run362),
  ("binary64/div[status]", run363),
  ("binary64/sqrt[status]", run364),
  ("binary64/fma[status]", run365),
  ("binary64/square", run366),
  ("binary64/exp", run367),
  ("binary64/log", run368),
  ("binary64/sin", run369),
  ("binary64/pow", run370),
  ("binary64/powInt", run371),
  ("binary64/rsqrt", run372),
  ("binary64/hypot", run373),
  ("binary64/rootN3", run374),
  ("binary64/exp[certify]", run375),
  ("binary64/log[certify]", run376),
  ("binary64/cos", run377),
  ("binary64/tanh", run378),
  ("binary64/expMinus1", run379),
  ("binary64/logPlus1", run380),
  ("binary64/sum8", run381),
  ("binary64/dot8", run382),
  ("binary128/convertFromInt64", run383),
  ("binary128/intToFloat64", run384),
  ("binary128/floatToInt64[nearest]", run385),
  ("binary128/floatToInt64[towardZero]", run386),
  ("binary128/roundToIntegral[nearest]", run387),
  ("binary128/roundToIntegral[towardZero]", run388),
  ("binary128/roundToIntegral[up]", run389),
  ("binary128/roundToIntegral[down]", run390),
  ("binary128/roundToIntegral[status]", run391),
  ("binary128/remainder", run392),
  ("binary128/compareLess", run393),
  ("binary128/compareLessEqual", run394),
  ("binary128/beq", run395),
  ("binary128/compare", run396),
  ("binary128/compareQuietLess", run397),
  ("binary128/compareQuietEqual", run398),
  ("binary128/compareSignalingLessEqual", run399),
  ("binary128/totalOrder", run400),
  ("binary128/totalOrderMag", run401),
  ("binary128/maximum", run402),
  ("binary128/minimum", run403),
  ("binary128/maxNum", run404),
  ("binary128/minNum", run405),
  ("binary128/maximumNumber", run406),
  ("binary128/minimumNumber", run407),
  ("binary128/nextUp", run408),
  ("binary128/nextDown", run409),
  ("binary128/scale", run410),
  ("binary128/binaryExponent", run411),
  ("binary128/binaryExponentInt", run412),
  ("binary128/negate", run413),
  ("binary128/abs", run414),
  ("binary128/copySign", run415),
  ("binary128/isNaN", run416),
  ("binary128/isNormal", run417),
  ("binary128/isSubnormal", run418),
  ("binary128/isZero", run419),
  ("binary128/isFinite", run420),
  ("binary128/isInfinite", run421),
  ("binary128/isSignalingNaN", run422),
  ("binary128/signBit", run423),
  ("binary128/classify", run424),
  ("binary128/isCanonical", run425),
  ("binary128/format[scientific]", run426),
  ("binary128/format[exact]", run427),
  ("binary128/format[hex]", run428),
  ("binary128/toString", run429),
  ("binary128/parse", run430),
  ("binary128/parse[status]", run431),
  ("binary128/add[up]", run432),
  ("binary128/mul[up]", run433),
  ("binary128/div[up]", run434),
  ("binary128/sqrt[up]", run435),
  ("binary128/fma[up]", run436),
  ("binary128/add[down]", run437),
  ("binary128/mul[down]", run438),
  ("binary128/div[down]", run439),
  ("binary128/sqrt[down]", run440),
  ("binary128/fma[down]", run441),
  ("binary128/add[towardZero]", run442),
  ("binary128/mul[towardZero]", run443),
  ("binary128/div[towardZero]", run444),
  ("binary128/sqrt[towardZero]", run445),
  ("binary128/fma[towardZero]", run446),
  ("binary128/add[status]", run447),
  ("binary128/sub[status]", run448),
  ("binary128/mul[status]", run449),
  ("binary128/div[status]", run450),
  ("binary128/sqrt[status]", run451),
  ("binary128/fma[status]", run452),
  ("binary128/square", run453),
  ("binary128/exp", run454),
  ("binary128/log", run455),
  ("binary128/sin", run456),
  ("binary128/pow", run457),
  ("binary128/powInt", run458),
  ("binary128/rsqrt", run459),
  ("binary128/hypot", run460),
  ("binary128/rootN3", run461),
  ("binary128/exp[certify]", run462),
  ("binary128/log[certify]", run463),
  ("binary128/cos", run464),
  ("binary128/tanh", run465),
  ("binary128/expMinus1", run466),
  ("binary128/logPlus1", run467),
  ("binary128/sum8", run468),
  ("binary128/dot8", run469),
  ("binary256/intToFloat64", run470),
  ("binary256/floatToInt64[nearest]", run471),
  ("binary256/roundToIntegral[nearest]", run472),
  ("binary256/roundToIntegral[towardZero]", run473),
  ("binary256/remainder", run474),
  ("binary256/compareLess", run475),
  ("binary256/compare", run476),
  ("binary256/totalOrder", run477),
  ("binary256/maximum", run478),
  ("binary256/nextUp", run479),
  ("binary256/scale", run480),
  ("binary256/binaryExponent", run481),
  ("binary256/negate", run482),
  ("binary256/abs", run483),
  ("binary256/isNaN", run484),
  ("binary256/classify", run485),
  ("binary256/format[scientific]", run486),
  ("binary256/parse", run487),
  ("binary256/add[up]", run488),
  ("binary256/mul[up]", run489),
  ("binary256/div[up]", run490),
  ("binary256/sqrt[up]", run491),
  ("binary256/fma[up]", run492),
  ("binary256/add[status]", run493),
  ("binary256/square", run494),
  ("binary256/exp", run495),
  ("posit32/ofFixedInt64", run496),
  ("posit32/toFixedInt64", run497),
  ("posit32/convertFromInt64", run498),
  ("posit32/compareLess", run499),
  ("posit32/compareLessEqual", run500),
  ("posit32/beq", run501),
  ("posit32/compare", run502),
  ("posit32/next", run503),
  ("posit32/prior", run504),
  ("posit32/negate", run505),
  ("posit32/abs", run506),
  ("posit32/sign", run507),
  ("posit32/nearestInt", run508),
  ("posit32/ceil", run509),
  ("posit32/floor", run510),
  ("posit32/isNaR", run511),
  ("posit32/isZero", run512),
  ("posit32/display", run513),
  ("posit32/parse", run514),
  ("posit32/exp", run515),
  ("posit32/log", run516),
  ("posit32/sin", run517),
  ("posit32/log2", run518),
  ("posit32/rSqrt", run519),
  ("posit32/hypot", run520),
  ("posit32/powInt", run521),
  ("posit32/cos", run522),
  ("posit32/tan", run523),
  ("posit32/arcTan", run524),
  ("posit32/expMinus1", run525),
  ("posit32/logPlus1", run526),
  ("posit32/log10", run527),
  ("posit32/tanH", run528),
  ("posit32/rootN3", run529),
  ("posit32/compound", run530),
  ("posit32/fMM", run531),
  ("posit32/quireDot8", run532),
  ("binary16/ref.add[mixed]", run533),
  ("binary16/ref.sub[mixed]", run534),
  ("binary16/ref.mul[mixed]", run535),
  ("binary16/ref.div[mixed]", run536),
  ("binary16/ref.sqrt[mixed]", run537),
  ("binary16/ref.fma[mixed]", run538),
  ("bfloat16/ref.add[mixed]", run539),
  ("bfloat16/ref.sub[mixed]", run540),
  ("bfloat16/ref.mul[mixed]", run541),
  ("bfloat16/ref.div[mixed]", run542),
  ("bfloat16/ref.sqrt[mixed]", run543),
  ("bfloat16/ref.fma[mixed]", run544),
  ("binary32/ref.add[mixed]", run545),
  ("binary32/ref.sub[mixed]", run546),
  ("binary32/ref.mul[mixed]", run547),
  ("binary32/ref.div[mixed]", run548),
  ("binary32/ref.sqrt[mixed]", run549),
  ("binary32/ref.fma[mixed]", run550),
  ("binary64/ref.add[mixed]", run551),
  ("binary64/ref.add[ordinary]", run552),
  ("binary64/ref.add[tiny]", run553),
  ("binary64/ref.add[huge]", run554),
  ("binary64/ref.add[subnormal]", run555),
  ("binary64/ref.add[special]", run556),
  ("binary64/ref.sub[mixed]", run557),
  ("binary64/ref.sub[ordinary]", run558),
  ("binary64/ref.sub[tiny]", run559),
  ("binary64/ref.sub[huge]", run560),
  ("binary64/ref.sub[subnormal]", run561),
  ("binary64/ref.sub[special]", run562),
  ("binary64/ref.mul[mixed]", run563),
  ("binary64/ref.mul[ordinary]", run564),
  ("binary64/ref.mul[tiny]", run565),
  ("binary64/ref.mul[huge]", run566),
  ("binary64/ref.mul[subnormal]", run567),
  ("binary64/ref.mul[special]", run568),
  ("binary64/ref.div[mixed]", run569),
  ("binary64/ref.div[ordinary]", run570),
  ("binary64/ref.div[tiny]", run571),
  ("binary64/ref.div[huge]", run572),
  ("binary64/ref.div[subnormal]", run573),
  ("binary64/ref.div[special]", run574),
  ("binary64/ref.sqrt[mixed]", run575),
  ("binary64/ref.sqrt[ordinary]", run576),
  ("binary64/ref.sqrt[tiny]", run577),
  ("binary64/ref.sqrt[huge]", run578),
  ("binary64/ref.sqrt[subnormal]", run579),
  ("binary64/ref.sqrt[special]", run580),
  ("binary64/ref.fma[mixed]", run581),
  ("binary64/ref.fma[ordinary]", run582),
  ("binary64/ref.fma[tiny]", run583),
  ("binary64/ref.fma[huge]", run584),
  ("binary64/ref.fma[subnormal]", run585),
  ("binary64/ref.fma[special]", run586),
  ("binary128/ref.add[mixed]", run587),
  ("binary128/ref.add[ordinary]", run588),
  ("binary128/ref.add[tiny]", run589),
  ("binary128/ref.add[huge]", run590),
  ("binary128/ref.add[subnormal]", run591),
  ("binary128/ref.add[special]", run592),
  ("binary128/ref.sub[mixed]", run593),
  ("binary128/ref.sub[ordinary]", run594),
  ("binary128/ref.sub[tiny]", run595),
  ("binary128/ref.sub[huge]", run596),
  ("binary128/ref.sub[subnormal]", run597),
  ("binary128/ref.sub[special]", run598),
  ("binary128/ref.mul[mixed]", run599),
  ("binary128/ref.mul[ordinary]", run600),
  ("binary128/ref.mul[tiny]", run601),
  ("binary128/ref.mul[huge]", run602),
  ("binary128/ref.mul[subnormal]", run603),
  ("binary128/ref.mul[special]", run604),
  ("binary128/ref.div[mixed]", run605),
  ("binary128/ref.div[ordinary]", run606),
  ("binary128/ref.div[tiny]", run607),
  ("binary128/ref.div[huge]", run608),
  ("binary128/ref.div[subnormal]", run609),
  ("binary128/ref.div[special]", run610),
  ("binary128/ref.sqrt[mixed]", run611),
  ("binary128/ref.sqrt[ordinary]", run612),
  ("binary128/ref.sqrt[tiny]", run613),
  ("binary128/ref.sqrt[huge]", run614),
  ("binary128/ref.sqrt[subnormal]", run615),
  ("binary128/ref.sqrt[special]", run616),
  ("binary128/ref.fma[mixed]", run617),
  ("binary128/ref.fma[ordinary]", run618),
  ("binary128/ref.fma[tiny]", run619),
  ("binary128/ref.fma[huge]", run620),
  ("binary128/ref.fma[subnormal]", run621),
  ("binary128/ref.fma[special]", run622),
  ("posit32/ref.add[mixed]", run623),
  ("posit32/ref.sub[mixed]", run624),
  ("posit32/ref.mul[mixed]", run625),
  ("posit32/ref.div[mixed]", run626),
  ("posit32/ref.sqrt[mixed]", run627),
  ("posit32/ref.fma[mixed]", run628),
  ("binary16/sqrt[status,runtime]",
    runSqrtRuntime "binary16/sqrt[status,runtime]" FloatFormat.binary16 5 10),
  ("bfloat16/sqrt[status,runtime]",
    runSqrtRuntime "bfloat16/sqrt[status,runtime]" FloatFormat.bfloat16 8 7),
  ("binary32/sqrt[status,runtime]",
    runSqrtRuntime "binary32/sqrt[status,runtime]" FloatFormat.binary32 8 23),
  ("binary64/sqrt[status,runtime]",
    runSqrtRuntime "binary64/sqrt[status,runtime]" FloatFormat.binary64 11 52),
  ("binary128/sqrt[status,runtime]",
    runSqrtRuntime "binary128/sqrt[status,runtime]" FloatFormat.binary128 15 112)]

end FloatLibBenchmarks.Public.TimeOps

open FloatLibBenchmarks.Public.TimeOps in
public def main (args : List String) : IO UInt32 := do
  let usage := "usage: execFloatTimeOps list | run CELL COUNT TRIALS REPS\n" ++
    "COUNT, TRIALS, and REPS must be positive integers"
  match args with
  | ["list"] =>
      for (name, _) in cells do
        IO.println name
      return 0
  | ["run", name, countText, trialsText, repsText] =>
      let (some count, some trials, some reps) :=
          (countText.toNat?, trialsText.toNat?, repsText.toNat?)
        | IO.eprintln usage; return 1
      if count == 0 || trials == 0 || reps == 0 then
        IO.eprintln usage
        return 1
      match cells.find? (·.1 == name) with
      | some (_, action) =>
          action count trials reps
          return 0
      | none =>
          IO.eprintln s!"unknown cell {name}"
          return 1
  | _ =>
      IO.eprintln usage
      return 1
