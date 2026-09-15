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

This is the public entry point for the static-byte representation and table certificates, exact
conversion capabilities, default proved `ExecFloat` backends, and optional policy-driven planning
infrastructure.

## Backend

This module exposes family-selected operations, their refinement theorems, and the
default `ExecFloat` capability instances. Runtime-only consumers should import
`StaticByte.Backend.Runtime`.

## Core

This module exposes the compact static-byte runtime, lazy verified table construction, and the
proof bridges used by nominal binary formats. Runtime-only consumers should import
`StaticByte.Core.Runtime`.

## Conversion

This module exposes exact-rational decoding, explicit-policy quantization, installed conversion
instances, and their reduction theorems. Runtime-only consumers should import
`StaticByte.Conversion.Runtime`.

## Plan

This module exposes static-byte cost estimates, first-order dispatch, its correctness theorems,
and verified `ExecFloat` capability constructors. Runtime-only consumers should import
`StaticByte.Plan.Runtime`.
-/

@[expose] public section
