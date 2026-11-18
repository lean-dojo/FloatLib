/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Tactic.DeclareCapability

/-!
# Uniform operation-specific capability API

The public `Add`, `Sub`, `Mul`, `Div`, `Sqrt`, and `Fma` namespaces all derive their interfaces from
the one indexed `Capability` contract. So each namespace has the same planning and certification
surface, and each keeps the operation's natural arity.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

variable {F : Type u} [EncodedFormat F]
    [planning : Backend.PolicyFor F]

namespace Add

declare_execfloat_capability spec for .add on F using planning.policy
declare_execfloat_capability candidates for .add on F using planning.policy
declare_execfloat_capability policy for .add on F using planning.policy
declare_execfloat_capability selected for .add on F using planning.policy
declare_execfloat_capability selectedEqPlanner for .add on F using planning.policy
declare_execfloat_capability selectedCandidate for .add on F using planning.policy
declare_execfloat_capability binaryRun for .add on F using planning.policy
declare_execfloat_capability binaryRefinement for .add on F using planning.policy

end Add

namespace Sub

declare_execfloat_capability spec for .sub on F using planning.policy
declare_execfloat_capability candidates for .sub on F using planning.policy
declare_execfloat_capability policy for .sub on F using planning.policy
declare_execfloat_capability selected for .sub on F using planning.policy
declare_execfloat_capability selectedEqPlanner for .sub on F using planning.policy
declare_execfloat_capability selectedCandidate for .sub on F using planning.policy
declare_execfloat_capability binaryRun for .sub on F using planning.policy
declare_execfloat_capability binaryRefinement for .sub on F using planning.policy

end Sub

namespace Mul

declare_execfloat_capability spec for .mul on F using planning.policy
declare_execfloat_capability candidates for .mul on F using planning.policy
declare_execfloat_capability policy for .mul on F using planning.policy
declare_execfloat_capability selected for .mul on F using planning.policy
declare_execfloat_capability selectedEqPlanner for .mul on F using planning.policy
declare_execfloat_capability selectedCandidate for .mul on F using planning.policy
declare_execfloat_capability binaryRun for .mul on F using planning.policy
declare_execfloat_capability binaryRefinement for .mul on F using planning.policy

end Mul

namespace Div

declare_execfloat_capability spec for .div on F using planning.policy
declare_execfloat_capability candidates for .div on F using planning.policy
declare_execfloat_capability policy for .div on F using planning.policy
declare_execfloat_capability selected for .div on F using planning.policy
declare_execfloat_capability selectedEqPlanner for .div on F using planning.policy
declare_execfloat_capability selectedCandidate for .div on F using planning.policy
declare_execfloat_capability binaryRun for .div on F using planning.policy
declare_execfloat_capability binaryRefinement for .div on F using planning.policy

end Div

namespace Sqrt

declare_execfloat_capability spec for .sqrt on F using planning.policy
declare_execfloat_capability candidates for .sqrt on F using planning.policy
declare_execfloat_capability policy for .sqrt on F using planning.policy
declare_execfloat_capability selected for .sqrt on F using planning.policy
declare_execfloat_capability selectedEqPlanner for .sqrt on F using planning.policy
declare_execfloat_capability selectedCandidate for .sqrt on F using planning.policy
declare_execfloat_capability unaryRun for .sqrt on F using planning.policy
declare_execfloat_capability unaryRefinement for .sqrt on F using planning.policy

end Sqrt

namespace Fma

declare_execfloat_capability spec for .fma on F using planning.policy
declare_execfloat_capability candidates for .fma on F using planning.policy
declare_execfloat_capability policy for .fma on F using planning.policy
declare_execfloat_capability selected for .fma on F using planning.policy
declare_execfloat_capability selectedEqPlanner for .fma on F using planning.policy
declare_execfloat_capability selectedCandidate for .fma on F using planning.policy
declare_execfloat_capability ternaryRun for .fma on F using planning.policy
declare_execfloat_capability ternaryRefinement for .fma on F using planning.policy

end Fma

end ExecFloat
end FloatLib.Floats
