/-
Copyright (c) 2026 Robert Weller
Released under MIT license as described in the file LICENSE.
Authors: Robert Weller
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Construction
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Construction
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Plan.Construction
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Plan.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Plan.Runtime

/-!
# Proved static-byte binary-interchange formats

This is the public entry point for static-byte formats: the representation and table
certificates, exact conversion capabilities, the default proved `ExecFloat` backends, and optional
policy-driven planning.

## Backend

Family-selected operations come with their refinement theorems and the default `ExecFloat`
capability instances. Runtime-only consumers should import `StaticByte.Backend.Runtime`.

## Core

Here are the compact static-byte runtime, lazy verified table construction, and the proof bridges
that nominal binary formats use. For the runtime alone, import `StaticByte.Core.Runtime`.

## Conversion

Exact-rational decoding and quantization under a caller-supplied policy, with the installed
conversion instances and their reduction theorems. Code that only runs conversions can import
`StaticByte.Conversion.Runtime`.

## Plan

Static-byte cost estimates and first-order dispatch, with its correctness theorems and verified
`ExecFloat` capability constructors. Runtime-only consumers should import
`StaticByte.Plan.Runtime`.
-/

@[expose] public section
