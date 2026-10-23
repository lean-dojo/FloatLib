/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked
public import FloatLib.Floats.ExecFloat
public import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# Configured binary32 and binary64 code-generation probes

These monomorphic boundaries exercise the user-facing parameterized spelling:

```lean
ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
```

They call neither a nominal IEEE wrapper nor a backend. Generated-code checks require the
configured types to retain native `UInt32` and `UInt64` calling conventions and require each
public operation to resolve to its first-order certified kernel without a runtime capability
closure. These checks show that a project-local `Float32` or `Float64` abbreviation does not pay
for the general descriptor interface.

The configured selector probes spell the same operations through `ExecFloat.Binary.add` and its
siblings. Qualified calls, an explicit nearest-even mode, field notation and operators must compile
to the generic operation's kernel, and directed and status forms must reach the descriptor-model
kernels.

Ten more boundaries call `NativeFPU.Unchecked`. They are checked on their own, so host primitives
can never be mistaken for evidence about certified dispatch.
-/

@[expose] public section

namespace FloatLibBenchmarks.Codegen.ConfiguredBinary

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

@[noinline] def binary32Add (left right : Binary32) : Binary32 :=
  ExecFloat.add left right

@[noinline] def binary32Sub (left right : Binary32) : Binary32 :=
  ExecFloat.sub left right

@[noinline] def binary32Mul (left right : Binary32) : Binary32 :=
  ExecFloat.mul left right

@[noinline] def binary32Div (left right : Binary32) : Binary32 :=
  ExecFloat.div left right

@[noinline] def binary32Sqrt (value : Binary32) : Binary32 :=
  ExecFloat.sqrt value

@[noinline] def binary32Fma
    (left right addend : Binary32) : Binary32 :=
  ExecFloat.fma left right addend

@[noinline] def binary64Add (left right : Binary64) : Binary64 :=
  ExecFloat.add left right

@[noinline] def binary64Sub (left right : Binary64) : Binary64 :=
  ExecFloat.sub left right

@[noinline] def binary64Mul (left right : Binary64) : Binary64 :=
  ExecFloat.mul left right

@[noinline] def binary64Div (left right : Binary64) : Binary64 :=
  ExecFloat.div left right

@[noinline] def binary64Sqrt (value : Binary64) : Binary64 :=
  ExecFloat.sqrt value

@[noinline] def binary64Fma
    (left right addend : Binary64) : Binary64 :=
  ExecFloat.fma left right addend

/-!
## Configured selectors

`ExecFloat.Binary.add` and its siblings are the one-name configured operations. Their default
call, nearest-even without status, must compile to the same selected kernel as the generic
operation above, whether it is spelled `ExecFloat.Binary.add x y`, with an explicit
`(mode := .nearest)`, by field notation `x.add y`, or, for the four operators, `x + y`. The
directed and status forms take the descriptor-model kernels instead.
-/

@[noinline] def binary32AddBinary (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.add left right

@[noinline] def binary32AddNearest (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.add left right (mode := .nearest)

@[noinline] def binary32AddField (left right : Binary32) : Binary32 :=
  left.add right

@[noinline] def binary32AddOperator (left right : Binary32) : Binary32 :=
  left + right

@[noinline] def binary32AddUp (left right : Binary32) : Binary32 :=
  left.add right (mode := .up)

@[noinline] def binary32AddStatus (left right : Binary32) :=
  left.add right (status := true)

@[noinline] def binary32SubBinary (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.sub left right

@[noinline] def binary32SubNearest (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.sub left right (mode := .nearest)

@[noinline] def binary32SubField (left right : Binary32) : Binary32 :=
  left.sub right

@[noinline] def binary32SubOperator (left right : Binary32) : Binary32 :=
  left - right

@[noinline] def binary32SubUp (left right : Binary32) : Binary32 :=
  left.sub right (mode := .up)

@[noinline] def binary32SubStatus (left right : Binary32) :=
  left.sub right (status := true)

@[noinline] def binary32MulBinary (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.mul left right

@[noinline] def binary32MulNearest (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.mul left right (mode := .nearest)

@[noinline] def binary32MulField (left right : Binary32) : Binary32 :=
  left.mul right

@[noinline] def binary32MulOperator (left right : Binary32) : Binary32 :=
  left * right

@[noinline] def binary32MulUp (left right : Binary32) : Binary32 :=
  left.mul right (mode := .up)

@[noinline] def binary32MulStatus (left right : Binary32) :=
  left.mul right (status := true)

@[noinline] def binary32DivBinary (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.div left right

@[noinline] def binary32DivNearest (left right : Binary32) : Binary32 :=
  ExecFloat.Binary.div left right (mode := .nearest)

@[noinline] def binary32DivField (left right : Binary32) : Binary32 :=
  left.div right

@[noinline] def binary32DivOperator (left right : Binary32) : Binary32 :=
  left / right

@[noinline] def binary32DivUp (left right : Binary32) : Binary32 :=
  left.div right (mode := .up)

@[noinline] def binary32DivStatus (left right : Binary32) :=
  left.div right (status := true)

@[noinline] def binary32SqrtBinary (value : Binary32) : Binary32 :=
  ExecFloat.Binary.sqrt value

@[noinline] def binary32SqrtNearest (value : Binary32) : Binary32 :=
  ExecFloat.Binary.sqrt value (mode := .nearest)

@[noinline] def binary32SqrtField (value : Binary32) : Binary32 :=
  value.sqrt

@[noinline] def binary32SqrtNearestAway (value : Binary32) : Binary32 :=
  value.sqrt (mode := .nearestAway)

@[noinline] def binary32SqrtUp (value : Binary32) : Binary32 :=
  value.sqrt (mode := .up)

@[noinline] def binary32SqrtStatus (value : Binary32) :=
  value.sqrt (status := true)

@[noinline] def binary32FmaBinary (left right addend : Binary32) : Binary32 :=
  ExecFloat.Binary.fma left right addend

@[noinline] def binary32FmaNearest (left right addend : Binary32) : Binary32 :=
  ExecFloat.Binary.fma left right addend (mode := .nearest)

@[noinline] def binary32FmaField (left right addend : Binary32) : Binary32 :=
  left.fma right addend

@[noinline] def binary32FmaUp (left right addend : Binary32) : Binary32 :=
  left.fma right addend (mode := .up)

@[noinline] def binary32FmaStatus (left right addend : Binary32) :=
  left.fma right addend (status := true)

@[noinline] def binary64AddBinary (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.add left right

@[noinline] def binary64AddNearest (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.add left right (mode := .nearest)

@[noinline] def binary64AddField (left right : Binary64) : Binary64 :=
  left.add right

@[noinline] def binary64AddOperator (left right : Binary64) : Binary64 :=
  left + right

@[noinline] def binary64AddUp (left right : Binary64) : Binary64 :=
  left.add right (mode := .up)

@[noinline] def binary64AddStatus (left right : Binary64) :=
  left.add right (status := true)

@[noinline] def binary64SubBinary (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.sub left right

@[noinline] def binary64SubNearest (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.sub left right (mode := .nearest)

@[noinline] def binary64SubField (left right : Binary64) : Binary64 :=
  left.sub right

@[noinline] def binary64SubOperator (left right : Binary64) : Binary64 :=
  left - right

@[noinline] def binary64SubUp (left right : Binary64) : Binary64 :=
  left.sub right (mode := .up)

@[noinline] def binary64SubStatus (left right : Binary64) :=
  left.sub right (status := true)

@[noinline] def binary64MulBinary (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.mul left right

@[noinline] def binary64MulNearest (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.mul left right (mode := .nearest)

@[noinline] def binary64MulField (left right : Binary64) : Binary64 :=
  left.mul right

@[noinline] def binary64MulOperator (left right : Binary64) : Binary64 :=
  left * right

@[noinline] def binary64MulUp (left right : Binary64) : Binary64 :=
  left.mul right (mode := .up)

@[noinline] def binary64MulStatus (left right : Binary64) :=
  left.mul right (status := true)

@[noinline] def binary64DivBinary (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.div left right

@[noinline] def binary64DivNearest (left right : Binary64) : Binary64 :=
  ExecFloat.Binary.div left right (mode := .nearest)

@[noinline] def binary64DivField (left right : Binary64) : Binary64 :=
  left.div right

@[noinline] def binary64DivOperator (left right : Binary64) : Binary64 :=
  left / right

@[noinline] def binary64DivUp (left right : Binary64) : Binary64 :=
  left.div right (mode := .up)

@[noinline] def binary64DivStatus (left right : Binary64) :=
  left.div right (status := true)

@[noinline] def binary64SqrtBinary (value : Binary64) : Binary64 :=
  ExecFloat.Binary.sqrt value

@[noinline] def binary64SqrtNearest (value : Binary64) : Binary64 :=
  ExecFloat.Binary.sqrt value (mode := .nearest)

@[noinline] def binary64SqrtField (value : Binary64) : Binary64 :=
  value.sqrt

@[noinline] def binary64SqrtNearestAway (value : Binary64) : Binary64 :=
  value.sqrt (mode := .nearestAway)

@[noinline] def binary64SqrtUp (value : Binary64) : Binary64 :=
  value.sqrt (mode := .up)

@[noinline] def binary64SqrtStatus (value : Binary64) :=
  value.sqrt (status := true)

@[noinline] def binary64FmaBinary (left right addend : Binary64) : Binary64 :=
  ExecFloat.Binary.fma left right addend

@[noinline] def binary64FmaNearest (left right addend : Binary64) : Binary64 :=
  ExecFloat.Binary.fma left right addend (mode := .nearest)

@[noinline] def binary64FmaField (left right addend : Binary64) : Binary64 :=
  left.fma right addend

@[noinline] def binary64FmaUp (left right addend : Binary64) : Binary64 :=
  left.fma right addend (mode := .up)

@[noinline] def binary64FmaStatus (left right addend : Binary64) :=
  left.fma right addend (status := true)

/-! ## Explicit unchecked host probes -/

@[noinline] def unchecked32Add (left right : Binary32) : Binary32 :=
  Configured.NativeFPU.Unchecked.add32 left right

@[noinline] def unchecked32Sub (left right : Binary32) : Binary32 :=
  Configured.NativeFPU.Unchecked.sub32 left right

@[noinline] def unchecked32Mul (left right : Binary32) : Binary32 :=
  Configured.NativeFPU.Unchecked.mul32 left right

@[noinline] def unchecked32Div (left right : Binary32) : Binary32 :=
  Configured.NativeFPU.Unchecked.div32 left right

@[noinline] def unchecked32Sqrt (value : Binary32) : Binary32 :=
  Configured.NativeFPU.Unchecked.sqrt32 value

@[noinline] def unchecked64Add (left right : Binary64) : Binary64 :=
  Configured.NativeFPU.Unchecked.add64 left right

@[noinline] def unchecked64Sub (left right : Binary64) : Binary64 :=
  Configured.NativeFPU.Unchecked.sub64 left right

@[noinline] def unchecked64Mul (left right : Binary64) : Binary64 :=
  Configured.NativeFPU.Unchecked.mul64 left right

@[noinline] def unchecked64Div (left right : Binary64) : Binary64 :=
  Configured.NativeFPU.Unchecked.div64 left right

@[noinline] def unchecked64Sqrt (value : Binary64) : Binary64 :=
  Configured.NativeFPU.Unchecked.sqrt64 value

end FloatLibBenchmarks.Codegen.ConfiguredBinary
