/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

meta import FloatLib
meta import Lean.Elab.Command

/-!
# Root import boundary

Inspect the complete imported module set of `FloatLib` in isolation from other conformance
modules. Host-FPU operations and the configured and model elementary-function barrels must stay
opt-in, even when an intermediate production module changes its imports. Individual contract and
kernel modules may remain available through the root.

The meta import loads implementation dependencies as well as public imports, so a private import
in an intermediate module cannot hide an opt-in dependency from this audit.
-/

open Lean

run_cmd do
  let moduleNames := (← getEnv).header.moduleNames
  unless moduleNames.contains `FloatLib do
    throwError "the root import audit must import FloatLib"
  for forbidden in #[
      `FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked,
      `FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals,
      `FloatLib.Floats.Formats.BinaryInterchange.Transcendentals] do
    if moduleNames.contains forbidden then
      throwError "FloatLib imports the opt-in module {forbidden}"
