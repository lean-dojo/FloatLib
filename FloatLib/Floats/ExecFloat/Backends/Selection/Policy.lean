/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module


/-!
# Backend-selection policy

A policy says how much one-time setup may be amortized, how allocations and memory are charged,
and which resource ceilings are absolute. The built-in latency, balanced, and throughput profiles
are format-independent starting points rather than claims about a particular machine.

`PolicyFor` makes the choice static at the format carrier. Users can select another profile with a
scoped instance, while the encoded value type and arithmetic semantics remain unchanged. This
also keeps execution and `#float_info` on the same plan.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

universe u

/-- Workload and memory policy used by the deterministic selector. -/
structure Policy where
  /-- Expected calls over which one-time setup is amortized. -/
  expectedCalls : Nat
  /-- Relative cost charged for one allocation on every call. -/
  allocationPenalty : Nat
  /-- Number of bytes represented by one memory-cost block. -/
  memoryBlockBytes : Nat
  /-- Relative warm-call cost charged for one temporary-memory block. -/
  temporaryBlockPenalty : Nat
  /-- Relative cold cost charged for one persistent-memory block. -/
  residentBlockPenalty : Nat
  /-- Hard peak-temporary-memory limit for every optional candidate. -/
  maxTemporaryBytes : Nat
  /-- Hard resident-memory limit for every optional candidate. -/
  maxResidentBytes : Nat
  deriving DecidableEq, Repr

namespace Policy

/--
First-call-oriented policy.

This profile is appropriate when an operation may be used only a handful of times and a large
one-time setup cost would dominate. Resource ceilings remain identical to `Policy.default`.
-/
def latency : Policy where
  expectedCalls := 1
  allocationPenalty := 32
  memoryBlockBytes := 64
  temporaryBlockPenalty := 1
  residentBlockPenalty := 1
  maxTemporaryBytes := 64 * 1024 * 1024
  maxResidentBytes := 1024 * 1024

/--
Default balanced policy.

The one-megabyte resident-memory ceiling admits all unary and binary byte-result tables through
eight encoded bits and ternary tables through six bits, while rejecting an eight-bit FMA table
(sixteen megabytes). The cost model may still reject an admissible table when its construction
cannot amortize over the expected workload. Families and applications may publish a different
static policy when their workload warrants it.
-/
def default : Policy where
  expectedCalls := 100000
  allocationPenalty := 32
  memoryBlockBytes := 64
  temporaryBlockPenalty := 1
  residentBlockPenalty := 1
  maxTemporaryBytes := 64 * 1024 * 1024
  maxResidentBytes := 1024 * 1024

/--
Sustained-throughput policy.

The five-million-call horizon admits a larger one-time setup cost when the selected kernel has a
materially faster steady state. The resident-memory ceiling admits every exhaustive table over a
byte-sized carrier; the cost model still rejects a large table when its setup cannot amortize at
this horizon. Wider carriers remain governed by the same fixed resource bound.
-/
def throughput : Policy where
  expectedCalls := 5000000
  allocationPenalty := 32
  memoryBlockBytes := 64
  temporaryBlockPenalty := 1
  residentBlockPenalty := 1
  maxTemporaryBytes := 64 * 1024 * 1024
  maxResidentBytes := 16 * 1024 * 1024

/-- Stable user-facing name for a built-in policy, or `custom` for an application policy. -/
def profileName (policy : Policy) : String :=
  if policy = latency then
    "latency"
  else if policy = default then
    "balanced"
  else if policy = throughput then
    "throughput"
  else
    "custom"

end Policy

/--
A statically recognizable planning profile.

The built-in constructors expose fixed policies for specialization. `custom` carries an
application-defined policy, which may be fixed or computed at runtime. Execution and inspection
recover the complete policy from the same profile.
-/
inductive PolicyProfile where
  | latency
  | balanced
  | throughput
  | custom (policy : Policy)

/-- Recover the complete cost policy represented by a static profile. -/
@[always_inline] def PolicyProfile.policy : PolicyProfile → Policy
  | .latency => Policy.latency
  | .balanced => Policy.default
  | .throughput => Policy.throughput
  | .custom policy => policy

/--
Static planning policy associated with a format carrier.

This class changes backend choice, not numerical semantics or the `ExecFloat` value type. Concrete
format families may depend on it when constructing operation capabilities. A local or scoped
instance can therefore request a latency or throughput plan without wrapping values or changing
user arithmetic.
-/
class PolicyFor (F : Type u) where
  /-- Static or application-defined profile used to choose kernels for `F`. -/
  profile : PolicyProfile

/-- The complete cost policy carried by a format's static planning profile. -/
@[always_inline] def PolicyFor.policy {F : Type u} (planning : PolicyFor F) : Policy :=
  (PolicyFor.profile F (self := planning)).policy

/-- Construct a planning instance for an application-defined cost policy. -/
@[instance_reducible] def PolicyFor.custom {F : Type u} (policy : Policy) : PolicyFor F where
  profile := .custom policy

/-- Balanced planning is the format-independent default. -/
instance (priority := 100) defaultPolicyFor (F : Type u) : PolicyFor F where
  profile := .balanced

namespace PlanningLatency

/--
Select first-call-oriented plans for every capability that consumes `PolicyFor`.

Opening this scope changes execution planning, not the numerical type or its semantics.
-/
scoped instance policy (F : Type u) : PolicyFor F where
  profile := .latency

end PlanningLatency

namespace PlanningThroughput

/--
Select sustained-throughput plans for every capability that consumes `PolicyFor`.

The scope is carrier- and format-independent: descriptor families, direct standard formats, and
user-defined formats all use the same policy mechanism.
-/
scoped instance policy (F : Type u) : PolicyFor F where
  profile := .throughput

end PlanningThroughput

end FloatLib.Floats.ExecFloat.Backend
