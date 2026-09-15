/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured

/-!
# Monomorphic Posit Standard code-generation probes

These exported entry points expose the generated representation of all six public `ExecFloat`
operations at representative widths. They call only the universal arithmetic API; none names a
storage carrier, certified candidate, or Posit kernel.

The selected widths cover both sides of every static storage boundary, not merely familiar
powers of two. Widths 2 and 8 also distinguish the smallest exhaustive-table plan from the byte
carrier's direct binary kernels. Widths 36 through 38 are internal regression probes in the
middle of the `UInt64` storage tier; they ensure that no accidental format-width crossover enters
the unified packed-word operations. They are not named public formats. The generated-code audit
uses these probes to distinguish specialization of an ordinary public call from properties of a
particular recursive benchmark loop.
-/

@[expose] public section

namespace FloatLibBenchmarks.Codegen.Posit

open FloatLib.Floats

syntax "posit_codegen_probes "
  ident ident ident ident ident ident " : " term : command

macro_rules
  | `(posit_codegen_probes
        $addName:ident $subName:ident $mulName:ident $divName:ident
        $sqrtName:ident $fmaName:ident : $type:term) =>
      `(
        /-- Retained monomorphic observation boundary for public posit addition. -/
        @[noinline] def $addName (left right : $type) : $type :=
          ExecFloat.add left right

        /-- Retained monomorphic observation boundary for public posit subtraction. -/
        @[noinline] def $subName (left right : $type) : $type :=
          ExecFloat.sub left right

        /-- Retained monomorphic observation boundary for public posit multiplication. -/
        @[noinline] def $mulName (left right : $type) : $type :=
          ExecFloat.mul left right

        /-- Retained monomorphic observation boundary for public posit division. -/
        @[noinline] def $divName (left right : $type) : $type :=
          ExecFloat.div left right

        /-- Retained monomorphic observation boundary for public posit square root. -/
        @[noinline] def $sqrtName (value : $type) : $type :=
          ExecFloat.sqrt value

        /-- Retained monomorphic observation boundary for public posit fused multiply-add. -/
        @[noinline] def $fmaName (left right addend : $type) : $type :=
          ExecFloat.fma left right addend)

posit_codegen_probes
  p2Add p2Sub p2Mul p2Div p2Sqrt p2Fma : ExecFloat.Posit 2
posit_codegen_probes
  p8Add p8Sub p8Mul p8Div p8Sqrt p8Fma : ExecFloat.Posit 8
posit_codegen_probes
  p9Add p9Sub p9Mul p9Div p9Sqrt p9Fma : ExecFloat.Posit 9
posit_codegen_probes
  p16Add p16Sub p16Mul p16Div p16Sqrt p16Fma : ExecFloat.Posit 16
posit_codegen_probes
  p17Add p17Sub p17Mul p17Div p17Sqrt p17Fma : ExecFloat.Posit 17
posit_codegen_probes
  p32Add p32Sub p32Mul p32Div p32Sqrt p32Fma : ExecFloat.Posit 32
posit_codegen_probes
  p33Add p33Sub p33Mul p33Div p33Sqrt p33Fma : ExecFloat.Posit 33
posit_codegen_probes
  p36Add p36Sub p36Mul p36Div p36Sqrt p36Fma : ExecFloat.Posit 36
posit_codegen_probes
  p37Add p37Sub p37Mul p37Div p37Sqrt p37Fma : ExecFloat.Posit 37
posit_codegen_probes
  p38Add p38Sub p38Mul p38Div p38Sqrt p38Fma : ExecFloat.Posit 38
posit_codegen_probes
  p64Add p64Sub p64Mul p64Div p64Sqrt p64Fma : ExecFloat.Posit 64
posit_codegen_probes
  p65Add p65Sub p65Mul p65Div p65Sqrt p65Fma : ExecFloat.Posit 65
posit_codegen_probes
  p128Add p128Sub p128Mul p128Div p128Sqrt p128Fma : ExecFloat.Posit 128
posit_codegen_probes
  p129Add p129Sub p129Mul p129Div p129Sqrt p129Fma : ExecFloat.Posit 129
posit_codegen_probes
  p256Add p256Sub p256Mul p256Div p256Sqrt p256Fma : ExecFloat.Posit 256
posit_codegen_probes
  p4096Add p4096Sub p4096Mul p4096Div p4096Sqrt p4096Fma : ExecFloat.Posit 4096

end FloatLibBenchmarks.Codegen.Posit
