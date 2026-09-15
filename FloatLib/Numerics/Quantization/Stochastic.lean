/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Entropy
public import FloatLib.Numerics.Quantization.Spec

/-!
# Explicit-entropy stochastic quantization

A stochastic quantizer is represented as an ordinary relational specification whose context
contains the incoming entropy and whose result contains the updated entropy. No hidden random
source is available to the kernel, so executions can be replayed and proofs can state exactly
which entropy transition was used.

Probability laws remain family-specific: some kernels consume a random bit, others a fixed-width
word or a splittable generator. Those distributional guarantees are separate from the shared
state-transition interface defined here.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

universe u v w x y

/-- Lift an explicit entropy-transition relation into the common quantization interface. -/
def ofRelation {Context : Type u} {Entropy : Type v}
    {Exact : Type w} {Result : Type x}
    (relation : Context → Entropy → Exact → Result → Entropy → Prop) :
    Spec (Context × Entropy) Exact (Operation.EntropyResult Entropy Result) :=
  fun state input outcome =>
    relation state.1 state.2 input outcome.result outcome.entropy

/-- View a concrete entropy-threading kernel as a singleton stochastic specification. -/
def ofKernel {Context : Type u} {Entropy : Type v}
    {Exact : Type w} {Result : Type x}
    (run : Operation.EntropyKernel Context Entropy Exact Result) :
    Spec (Context × Entropy) Exact (Operation.EntropyResult Entropy Result) :=
  Spec.ofFunction fun state input => run state.1 state.2 input

/-- A concrete entropy kernel implements the singleton specification generated from itself. -/
theorem implements_ofKernel {Context : Type u} {Entropy : Type v}
    {Exact : Type w} {Result : Type x}
    (run : Operation.EntropyKernel Context Entropy Exact Result) :
    (ofKernel run).Implements (fun state input => run state.1 state.2 input) :=
  Spec.implements_ofFunction _

/-- Conformance to an entropy relation is exactly the pointwise transition property. -/
theorem implements_ofRelation_iff {Context : Type u} {Entropy : Type v}
    {Exact : Type w} {Result : Type x}
    (relation : Context → Entropy → Exact → Result → Entropy → Prop)
    (run : Operation.EntropyKernel Context Entropy Exact Result) :
    (ofRelation relation).Implements
        (fun state input => run state.1 state.2 input) ↔
      Operation.RefinesEntropy run relation := by
  constructor
  · intro implements context entropy input
    exact implements (context, entropy) input
  · intro refines state input
    exact refines state.1 state.2 input

end FloatLib.Numerics.Quantization.Stochastic
