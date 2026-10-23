/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat
public import FloatLib.Floats.Formats.FiniteOnly
public import FloatLib.Floats.Formats.OCP

/-!
# Monomorphic low-bit code-generation probes

These exported entry points let `benchmarks/scripts/checks/static-lowbit-codegen.sh` inspect the compiler
output of the public universal API. The OCP E2M1 probes cover six direct exhaustive tables. The
E2M3, E3M2, E4M3FN, E5M2, E4M3FNUZ and E5M2FNUZ probes cover five tables each and an FMA on the
generic single-rounding kernel, and two throughput probes cover the E2M3 and E3M2 FMA tables.
The FNUZ probes also guard the finite-only formats' own exceptional-value policy.

The required result is a native `uint8_t` boundary with the nominal format and capability
dictionaries specialized away. This follows Lean's documented erased-subtype representation and
runtime code-generation model:

* <https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Prelude.lean#L697-L699>
* <https://lean-lang.org/doc/reference/latest/Run-Time-Code-Generation/>.
-/

@[expose] public section

namespace FloatLibBenchmarks.Codegen.StaticLowBit

open FloatLib.Floats
open FloatLib.Floats.Formats.OCP.MX

/-- Retained public OCP E2M1 addition boundary. -/
@[noinline] def e2m1Add
    (left right : E2M1) : E2M1 :=
  ExecFloat.add left right

/-- Retained public OCP E2M1 subtraction boundary. -/
@[noinline] def e2m1Sub
    (left right : E2M1) : E2M1 :=
  ExecFloat.sub left right

/-- Retained public OCP E2M1 multiplication boundary. -/
@[noinline] def e2m1Mul
    (left right : E2M1) : E2M1 :=
  ExecFloat.mul left right

/-- Retained public OCP E2M1 division boundary. -/
@[noinline] def e2m1Div
    (left right : E2M1) : E2M1 :=
  ExecFloat.div left right

/-- Retained public OCP E2M1 square-root boundary. -/
@[noinline] def e2m1Sqrt
    (value : E2M1) : E2M1 :=
  ExecFloat.sqrt value

/-- Retained public OCP E2M1 fused multiply-add boundary. -/
@[noinline] def e2m1Fma
    (left right addend : E2M1) : E2M1 :=
  ExecFloat.fma left right addend

/-- Retained public OCP E2M3 addition boundary. -/
@[noinline] def e2m3Add
    (left right : E2M3) : E2M3 :=
  ExecFloat.add left right

/-- Retained public OCP E2M3 subtraction boundary. -/
@[noinline] def e2m3Sub
    (left right : E2M3) : E2M3 :=
  ExecFloat.sub left right

/-- Retained public OCP E2M3 multiplication boundary. -/
@[noinline] def e2m3Mul
    (left right : E2M3) : E2M3 :=
  ExecFloat.mul left right

/-- Retained public OCP E2M3 division boundary. -/
@[noinline] def e2m3Div
    (left right : E2M3) : E2M3 :=
  ExecFloat.div left right

/-- Retained public OCP E2M3 square-root boundary. -/
@[noinline] def e2m3Sqrt
    (value : E2M3) : E2M3 :=
  ExecFloat.sqrt value

/-- Retained public OCP E2M3 fused multiply-add boundary. -/
@[noinline] def e2m3Fma
    (left right addend : E2M3) : E2M3 :=
  ExecFloat.fma left right addend

/-- Retained public OCP E3M2 addition boundary. -/
@[noinline] def e3m2Add
    (left right : E3M2) : E3M2 :=
  ExecFloat.add left right

/-- Retained public OCP E3M2 subtraction boundary. -/
@[noinline] def e3m2Sub
    (left right : E3M2) : E3M2 :=
  ExecFloat.sub left right

/-- Retained public OCP E3M2 multiplication boundary. -/
@[noinline] def e3m2Mul
    (left right : E3M2) : E3M2 :=
  ExecFloat.mul left right

/-- Retained public OCP E3M2 division boundary. -/
@[noinline] def e3m2Div
    (left right : E3M2) : E3M2 :=
  ExecFloat.div left right

/-- Retained public OCP E3M2 square-root boundary. -/
@[noinline] def e3m2Sqrt
    (value : E3M2) : E3M2 :=
  ExecFloat.sqrt value

/-- Retained public OCP E3M2 fused multiply-add boundary. -/
@[noinline] def e3m2Fma
    (left right addend : E3M2) : E3M2 :=
  ExecFloat.fma left right addend

namespace ThroughputPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

/--
Retained throughput-policy E2M3 FMA boundary.

Balanced planning avoids this 256 KiB exhaustive table. The throughput policy amortizes its
one-time construction and must compile to the direct lookup.
-/
@[noinline] def e2m3Fma
    (left right addend : E2M3) : E2M3 :=
  ExecFloat.fma left right addend

/-- Retained throughput-policy E3M2 FMA boundary with the same table-size tradeoff. -/
@[noinline] def e3m2Fma
    (left right addend : E3M2) : E3M2 :=
  ExecFloat.fma left right addend

end ThroughputPlan

/-- Retained public OCP E4M3FN addition boundary. -/
@[noinline] def e4m3fnAdd
    (left right : E4M3FN) : E4M3FN :=
  ExecFloat.add left right

/-- Retained public OCP E4M3FN subtraction boundary. -/
@[noinline] def e4m3fnSub
    (left right : E4M3FN) : E4M3FN :=
  ExecFloat.sub left right

/-- Retained public OCP E4M3FN multiplication boundary. -/
@[noinline] def e4m3fnMul
    (left right : E4M3FN) : E4M3FN :=
  ExecFloat.mul left right

/-- Retained public OCP E4M3FN division boundary. -/
@[noinline] def e4m3fnDiv
    (left right : E4M3FN) : E4M3FN :=
  ExecFloat.div left right

/-- Retained public OCP E4M3FN square-root boundary. -/
@[noinline] def e4m3fnSqrt
    (value : E4M3FN) : E4M3FN :=
  ExecFloat.sqrt value

/-- Retained public OCP E4M3FN fused multiply-add boundary. -/
@[noinline] def e4m3fnFma
    (left right addend : E4M3FN) : E4M3FN :=
  ExecFloat.fma left right addend

/-- Retained public OCP E5M2 addition boundary. -/
@[noinline] def e5m2Add
    (left right : E5M2) : E5M2 :=
  ExecFloat.add left right

/-- Retained public OCP E5M2 subtraction boundary. -/
@[noinline] def e5m2Sub
    (left right : E5M2) : E5M2 :=
  ExecFloat.sub left right

/-- Retained public OCP E5M2 multiplication boundary. -/
@[noinline] def e5m2Mul
    (left right : E5M2) : E5M2 :=
  ExecFloat.mul left right

/-- Retained public OCP E5M2 division boundary. -/
@[noinline] def e5m2Div
    (left right : E5M2) : E5M2 :=
  ExecFloat.div left right

/-- Retained public OCP E5M2 square-root boundary. -/
@[noinline] def e5m2Sqrt
    (value : E5M2) : E5M2 :=
  ExecFloat.sqrt value

/-- Retained public OCP E5M2 fused multiply-add boundary. -/
@[noinline] def e5m2Fma
    (left right addend : E5M2) : E5M2 :=
  ExecFloat.fma left right addend

/-- Retained public finite-only E4M3FNUZ addition boundary. -/
@[noinline] def e4m3fnuzAdd
    (left right : E4M3FNUZ) : E4M3FNUZ :=
  ExecFloat.add left right

/-- Retained public finite-only E4M3FNUZ subtraction boundary. -/
@[noinline] def e4m3fnuzSub
    (left right : E4M3FNUZ) : E4M3FNUZ :=
  ExecFloat.sub left right

/-- Retained public finite-only E4M3FNUZ multiplication boundary. -/
@[noinline] def e4m3fnuzMul
    (left right : E4M3FNUZ) : E4M3FNUZ :=
  ExecFloat.mul left right

/-- Retained public finite-only E4M3FNUZ division boundary. -/
@[noinline] def e4m3fnuzDiv
    (left right : E4M3FNUZ) : E4M3FNUZ :=
  ExecFloat.div left right

/-- Retained public finite-only E4M3FNUZ square-root boundary. -/
@[noinline] def e4m3fnuzSqrt
    (value : E4M3FNUZ) : E4M3FNUZ :=
  ExecFloat.sqrt value

/-- Retained public finite-only E4M3FNUZ fused multiply-add boundary. -/
@[noinline] def e4m3fnuzFma
    (left right addend : E4M3FNUZ) : E4M3FNUZ :=
  ExecFloat.fma left right addend

/-- Retained public finite-only E5M2FNUZ addition boundary. -/
@[noinline] def e5m2fnuzAdd
    (left right : E5M2FNUZ) : E5M2FNUZ :=
  ExecFloat.add left right

/-- Retained public finite-only E5M2FNUZ subtraction boundary. -/
@[noinline] def e5m2fnuzSub
    (left right : E5M2FNUZ) : E5M2FNUZ :=
  ExecFloat.sub left right

/-- Retained public finite-only E5M2FNUZ multiplication boundary. -/
@[noinline] def e5m2fnuzMul
    (left right : E5M2FNUZ) : E5M2FNUZ :=
  ExecFloat.mul left right

/-- Retained public finite-only E5M2FNUZ division boundary. -/
@[noinline] def e5m2fnuzDiv
    (left right : E5M2FNUZ) : E5M2FNUZ :=
  ExecFloat.div left right

/-- Retained public finite-only E5M2FNUZ square-root boundary. -/
@[noinline] def e5m2fnuzSqrt
    (value : E5M2FNUZ) : E5M2FNUZ :=
  ExecFloat.sqrt value

/-- Retained public finite-only E5M2FNUZ fused multiply-add boundary. -/
@[noinline] def e5m2fnuzFma
    (left right addend : E5M2FNUZ) : E5M2FNUZ :=
  ExecFloat.fma left right addend

end FloatLibBenchmarks.Codegen.StaticLowBit
