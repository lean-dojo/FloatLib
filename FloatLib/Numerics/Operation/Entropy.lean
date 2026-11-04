/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Explicit entropy for numerical operations

Stochastic rounding and randomized numerical algorithms have to show their entropy state in the
function type, and `EntropyResult` and `EntropyKernel` make that state transition visible without a
global random source or a runtime operation dictionary.

An optimized kernel stays an ordinary monomorphic function, and its proof contract records how the
input entropy, the result, and the output entropy are related.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

universe u v w x

/-- A numerical result paired with the entropy state available to the next operation. -/
structure EntropyResult (Entropy : Type u) (Result : Type v) where
  /-- The operation's ordinary result. -/
  result : Result
  /-- The updated entropy state, returned as data. -/
  entropy : Entropy
  deriving DecidableEq, Repr

/-- Direct function type for a context-dependent operation that consumes and returns entropy. -/
abbrev EntropyKernel (Context : Type u) (Entropy : Type v)
    (Exact : Type w) (Result : Type x) :=
  Context → Entropy → Exact → EntropyResult Entropy Result

namespace EntropyResult

/-- Transform only the ordinary result while preserving the updated entropy state. -/
@[inline] def map {Entropy : Type u} {A : Type v} {B : Type w}
    (f : A → B) (outcome : EntropyResult Entropy A) : EntropyResult Entropy B :=
  ⟨f outcome.result, outcome.entropy⟩

/-- Mapping an entropy result applies the supplied function to its ordinary result. -/
@[simp, grind =] theorem map_result {Entropy : Type u} {A : Type v} {B : Type w}
    (f : A → B) (outcome : EntropyResult Entropy A) :
    (outcome.map f).result = f outcome.result :=
  rfl

/-- Mapping an entropy result leaves its updated entropy state unchanged. -/
@[simp, grind =] theorem map_entropy {Entropy : Type u} {A : Type v} {B : Type w}
    (f : A → B) (outcome : EntropyResult Entropy A) :
    (outcome.map f).entropy = outcome.entropy :=
  rfl

end EntropyResult

/--
Relational correctness of an entropy-threading executable operation.

The relation may express deterministic state evolution, a probabilistic interpretation of the
consumed bits, or merely that the selected result belongs to a permitted stochastic support.
-/
def RefinesEntropy {Context : Type u} {Entropy : Type v}
    {Exact : Type w} {Result : Type x}
    (run : EntropyKernel Context Entropy Exact Result)
    (post : Context → Entropy → Exact → Result → Entropy → Prop) : Prop :=
  ∀ context entropy input,
    let outcome := run context entropy input
    post context entropy input outcome.result outcome.entropy

end FloatLib.Numerics.Operation
