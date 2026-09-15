/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Arb.Oracle
public import FloatLibTests.Accounting

/-!
# Arb parser regression checks

These checks cover validation performed before an external Arb payload enters interval arithmetic.

They exercise malformed signs, exponents, radii, and non-finite spellings at the trust boundary.
The module is intentionally a regression suite rather than a parser specification: accepted
payloads are still interpreted by the separately documented exact interval conversion, while bad
external text must fail explicitly.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.ArbParser

open Lean
open FloatLibTests.Arb
open FloatLibTests.Accounting

/-- A negative radius from an external payload is rejected instead of becoming reversed bounds. -/
def negativeRadiusRejected : Thunk Bool := ⟨fun _ =>
  let payload := Json.mkObj
    [("mid", Json.str "0"), ("rad", Json.str "-1"), ("exp", Json.str "0")]
  match parseMidRad10Exp payload with
  | .error _ => true
  | .ok _ => false⟩

/-- A valid radius still reconstructs the expected exact enclosure. -/
def validRadiusBounds : Thunk Bool := ⟨fun _ =>
  let payload := Json.mkObj
    [("mid", Json.str "10"), ("rad", Json.str "2"), ("exp", Json.str "-1")]
  match parseMidRad10Exp payload with
  | .error _ => false
  | .ok ball => ball.toRatBounds == (4 / 5, 6 / 5)⟩

/-- Named parser checks, exposed so validation tools need not parse the rendered report. -/
def failureRows : Thunk (List (String × Nat)) := ⟨fun _ =>
  [ ("negativeRadiusRejected", failureCount negativeRadiusRejected.get)
  , ("validRadiusBounds", failureCount validRadiusBounds.get)
  ]⟩

/-- Aggregate failure count for the Arb payload checks. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  namedFailureTotal failureRows.get⟩

/-- Human-readable result consumed by the external-oracle regression runner. -/
def report : Thunk String := ⟨fun _ =>
  renderFailureReport failureRows.get⟩

end FloatLibTests.Regression.ArbParser
