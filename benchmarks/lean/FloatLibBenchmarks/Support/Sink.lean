/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Observable benchmark sinks

Benchmark loops mix each result into an observable word so the compiler cannot discard the
measured calculation. Keeping the mixer in this dependency-free module gives every benchmark
runner the same operation without coupling low-level diagnostics to the full public sweep.
-/

@[expose] public section

namespace FloatLibBenchmarks.Support.Sink

/--
The fixed initial state for latency-oriented benchmark loops.

It is deliberately nonzero so the first fixture is not a special case.  The value has no numerical
meaning: it only makes each result observable and selects the next precomputed fixture.
-/
def initial : UInt64 :=
  14695981039346656037

/-- Mix one observed result word into a benchmark sink. -/
@[inline] def mix (sink value : UInt64) : UInt64 :=
  (sink ^^^ value) * 1099511628211

/-- Mix one natural-valued observation into a benchmark sink. -/
@[inline] def mixNat (sink : UInt64) (value : Nat) : UInt64 :=
  mix sink (UInt64.ofNat value)

/--
Select one of sixteen precomputed inputs from the previous observable result.

This creates a loop-carried dependency without feeding an arithmetic result back as an operand.
The latter would rapidly turn multiplication, division, and square root into an overflow,
underflow, or fixed-point benchmark instead of measuring ordinary finite inputs.
-/
@[inline] def dependentIndex (sink : UInt64) : Nat :=
  let folded := (sink ^^^ (sink >>> 32)) ^^^ ((sink ^^^ (sink >>> 32)) >>> 16)
  (folded &&& 15).toNat

end FloatLibBenchmarks.Support.Sink
