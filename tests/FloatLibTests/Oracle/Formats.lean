/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.OCP.MX.E8M0.Core
import FloatLib.Floats.Formats.P3109.Runtime

/-!
# Exact vectors for public format references

This executable exposes one normalized, family-independent stream of decoded values. Repository
scripts compare that stream with independent ONNX decoders and the IEEE P3109 working
group's published value tables.

The output is deliberately exact: finite values retain an integer significand and power-of-two
exponent instead of passing through a host floating-point type.
-/

namespace FloatLibTests.Oracle.Formats

open FloatLib.Numerics
open FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

private def emitFinite
    (family format : String)
    (bits : Nat)
    (value : FloatLib.Numerics.Dyadic)
    (subnormal : Bool) :
    IO Unit :=
  IO.println <|
    s!"{family},{format},{bits},finite,{value.negative},{value.significand}," ++
      s!"{value.exponent},{subnormal}"

private def emitInfinity
    (family format : String) (bits : Nat) (negative : Bool) : IO Unit :=
  IO.println s!"{family},{format},{bits},infinity,{negative},0,0,false"

private def emitNaN (family format : String) (bits : Nat) : IO Unit :=
  IO.println s!"{family},{format},{bits},nan,false,0,0,false"

private def emitBinaryFormat (name : String) (format : FloatFormat) : IO Unit := do
  for bits in List.range (2 ^ format.bitWidth) do
    let value := Model.ofNatBits (fmt := format) bits
    match Model.exactValue value with
    | .finite exact =>
        emitFinite "onnx" name bits exact (Model.isSubnormal value)
    | .infinity negative =>
        emitInfinity "onnx" name bits negative
    | .nan _ _ _ =>
        emitNaN "onnx" name bits

private def emitE8M0 : IO Unit := do
  for bits in List.range 256 do
    let value := OCP.MX.E8M0.ofNatBits bits
    match OCP.MX.E8M0.toDyadic? value with
    | some exact => emitFinite "onnx" "e8m0" bits exact false
    | none => emitNaN "onnx" "e8m0" bits

private def emitONNX : IO Unit := do
  emitBinaryFormat "e2m1" FloatFormat.e2m1
  emitBinaryFormat "e4m3fn" FloatFormat.e4m3fn
  emitBinaryFormat "e4m3fnuz" FloatFormat.e4m3fnuz
  emitBinaryFormat "e5m2" FloatFormat.e5m2
  emitBinaryFormat "e5m2fnuz" FloatFormat.e5m2fnuz
  emitE8M0

private def p3109Name (format : P3109.Format) : String :=
  let signedness :=
    match format.signedness with
    | .signed => "s"
    | .unsigned => "u"
  let domain :=
    match format.domain with
    | .finite => "f"
    | .extended => "e"
  s!"Binary{format.bitWidth}p{format.precision}{signedness}{domain}"

private def p3109Subnormal (format : P3109.Format) (bits : Nat) : Bool :=
  let magnitude :=
    match format.signedness with
    | .signed =>
        if format.signBoundary < bits then bits - format.signBoundary else bits
    | .unsigned => bits
  magnitude != 0 && magnitude / (2 ^ format.trailingBits) == 0

private def emitP3109Format (format : P3109.Format) : IO Unit := do
  let name := p3109Name format
  for bits in List.range format.modulus do
    match format.decodeNat bits with
    | .finite exact =>
        emitFinite "p3109" name bits exact (p3109Subnormal format bits)
    | .infinity negative =>
        emitInfinity "p3109" name bits negative
    | .exceptional _ =>
        emitNaN "p3109" name bits

private def emitP3109 (minimumWidth maximumWidth : Nat) : IO Unit := do
  for bitWidth in List.range (maximumWidth + 1) do
    if minimumWidth ≤ bitWidth then
      for precisionOffset in List.range bitWidth do
        let precision := precisionOffset + 1
        for signedness in [P3109.Signedness.signed, .unsigned] do
          for domain in [P3109.Domain.finite, .extended] do
            match P3109.Format.ofParameters? bitWidth precision signedness domain with
            | some format => emitP3109Format format
            | none => pure ()

private def parseNat (name text : String) : IO Nat :=
  match text.toNat? with
  | some value => pure value
  | none => throw <| IO.userError s!"{name} must be a natural number: {text}"

private def usage : String :=
  "usage: oracle formats onnx | p3109 MIN_WIDTH MAX_WIDTH"

/-- Emit exact ONNX or P3109 decoding vectors. -/
public def run (args : List String) : IO UInt32 := do
  let header := "family,format,code,kind,negative,significand,exponent,subnormal"
  match args with
  | ["onnx"] =>
      IO.println header
      emitONNX
      pure 0
  | ["p3109", minimumText, maximumText] =>
      let minimumWidth ← parseNat "MIN_WIDTH" minimumText
      let maximumWidth ← parseNat "MAX_WIDTH" maximumText
      if minimumWidth < 3 || maximumWidth < minimumWidth then
        throw <| IO.userError s!"invalid P3109 width range\n{usage}"
      IO.println header
      emitP3109 minimumWidth maximumWidth
      pure 0
  | _ =>
      throw <| IO.userError usage

end FloatLibTests.Oracle.Formats
