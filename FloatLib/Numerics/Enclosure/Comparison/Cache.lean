/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Comparison.Runtime

/-!
# Sharing enclosures between rounding comparisons

A rounding search compares one mathematical value with many boundaries. Its enclosures depend
on the requested accuracy, not on the boundary, so recomputing the same Taylor polynomial at
every bisection step is unnecessary.

`cacheIntervals` delays a finite prefix with Lean's pure `Thunk` type. A requested entry is
computed once and shared by subsequent comparisons. Entries beyond the prefix are computed
normally; the cache size never limits the mathematical search. The cache is explicit data:
returning a curried function here would let eta expansion move allocation into each lookup.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Comparison

/-- A shared finite prefix, followed by an unrestricted interval generator. -/
structure IntervalCache where
  /-- Lazily evaluated intervals at the most frequently requested degrees. -/
  values : Array (Thunk RationalInterval)
  /-- The original generator remains available beyond the cached prefix. -/
  fallback : Nat → RationalInterval

/-- Retrieve an interval, computing and sharing its cached entry when present. -/
def IntervalCache.get (cache : IntervalCache) (n : Nat) : RationalInterval :=
  if h : n < cache.values.size then cache.values[n].get else cache.fallback n

/-- Lazily cache the first `count` intervals without changing the sequence. -/
def cacheIntervals (intervals : Nat → RationalInterval) (count : Nat) : IntervalCache :=
  ⟨Array.ofFn (fun n : Fin count => Thunk.mk (fun _ => intervals n)), intervals⟩

/-- Caching changes evaluation cost but leaves every rational endpoint unchanged. -/
@[simp] theorem cacheIntervals_apply (intervals : Nat → RationalInterval) (count n : Nat) :
    (cacheIntervals intervals count).get n = intervals n := by
  simp [cacheIntervals, IntervalCache.get, Thunk.get]

/--
A comparison prepared once for many boundaries.

The data constructor keeps the shared interval array outside the boundary function. Direct
comparisons cover exact rational values and algorithms whose enclosures depend on the boundary.
-/
inductive Prepared where
  /-- A comparison that does not share a target's interval sequence. -/
  | direct (run : ℚ → Ordering)
  /-- A total adaptive comparison with a shared target enclosure sequence. -/
  | enclosed (cache : IntervalCache)
      (terminates : ∀ boundary : ℚ, ∃ n, Separates (cache.get n) boundary)

/-- Compare a prepared target with one rational boundary. -/
def Prepared.compare (prepared : Prepared) (boundary : ℚ) : Ordering :=
  match prepared with
  | .direct run => run boundary
  | .enclosed cache terminates => Comparison.compare cache.get boundary (terminates boundary)

end FloatLib.Numerics.Enclosure.Comparison
