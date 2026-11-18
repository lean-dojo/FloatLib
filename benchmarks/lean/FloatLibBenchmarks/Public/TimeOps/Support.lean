/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.Sweep
public import FloatLibBenchmarks.Support.Posit
public import FloatLib
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast

/-!
# Operands, digests and timing driver

Deterministic operands, complete result digests, and the shared trial driver for public-operation
timings.
-/

@[expose] public section

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
    mixFull h ((0x200 : UInt64) ||| (if r.value then (1 : UInt64) else 0) ||| (statusBits
      r.status <<< 1))

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

def feedPosition (h : UInt64) : ExecFloat.InputPosition → UInt64
  | .source => mixFull h 0xB1
  | .left => mixFull h 0xB2
  | .right => mixFull h 0xB3
  | .addend => mixFull h 0xB4
  | .operand index => feedNatAll (mixFull h 0xB5) index

def feedPayload (h : UInt64) : Option Nat → UInt64
  | none => mixFull h 0xC0
  | some payload => feedNatAll (mixFull h 0xC1) payload

def feedExceptional (h : UInt64) : FloatLib.Numerics.ExceptionalValue → UInt64
  | .nan payload negative signaling =>
      mixFull (feedPayload (mixFull h 0xD0) payload)
        ((if negative then 1 else 0) ||| (if signaling then 2 else 0))
  | .notAReal => mixFull h 0xD1
  | .reserved payload => feedPayload (mixFull h 0xD2) payload
  | .undefined => mixFull h 0xD3

/-- Every field of a failure, read from its constructors rather than from how it prints. -/
def feedFailure (h : UInt64) (f : ExecFloat.ConversionFailure) : UInt64 :=
  let h := mixFull h (failureCode f)
  match f with
  | .infinity position _ => feedPosition h position
  | .exceptional position value => feedExceptional (feedPosition h position) value
  | .divisionByZero | .outOfRange | .unsupportedPolicy => h

instance {α : Type} [Digest α] : Digest (ExecFloat.ConversionOutcome α) where
  quick o := match o with
    | .success v s => Digest.quick v ^^^ (conversionStatusBits s <<< 57)
    | .failure f => failureCode f
  full o h := match o with
    | .success v s => mixFull (Digest.full v (mixFull h 0xA00)) (conversionStatusBits s)
    | .failure f => feedFailure (mixFull h 0xA01) f

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

end FloatLibBenchmarks.Public.TimeOps
