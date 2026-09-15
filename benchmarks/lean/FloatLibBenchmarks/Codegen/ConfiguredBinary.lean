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

They do not call a nominal IEEE wrapper or a backend directly. Generated-code checks require the
configured types to retain native `UInt32` and `UInt64` calling conventions and require each
public operation to resolve to its first-order certified kernel without a runtime capability
closure. This is the executable evidence that a project-local `Float32` or `Float64` abbreviation
does not pay for the general descriptor interface.

Ten additional boundaries call `NativeFPU.Unchecked` explicitly. They are checked separately so
the presence of host primitives can never be mistaken for evidence about certified dispatch.
-/

@[expose] public section

namespace FloatLibBenchmarks.Codegen.ConfiguredBinary

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- User-facing IEEE binary32 configuration. -/
abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/-- User-facing IEEE binary64 configuration. -/
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

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
