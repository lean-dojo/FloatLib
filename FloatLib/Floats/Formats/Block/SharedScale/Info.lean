/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.SharedScale.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.ExecFloat.Info

/-!
# Inspection for exact shared-scale blocks

On a shared-scale block, `#float_info` reports the lane count, the unbounded mathematical carrier,
and the exact `quantizeAt` theorem, which rounds each lane on the integer grid of the caller's one
exponent. It doesn't pretend that a particular OCP MX encoding or scale-selection policy has been
chosen. The printed nonclaims say so, and we keep them in the public output because they are what
separates this reusable core from a concrete hardware format.

The module is meta-only, so vector runtime code never imports command elaboration.
-/

public meta section

namespace FloatLib.Floats.Formats.Block.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

/--
Build the shared-scale description used by both the raw block code and its configured
`ExecFloat` wrapper. Lane semantics and contextual rounding live here, and each carrier adds
only its own execution and wrapper-theorem entries.
-/
meta def profile (lanes : Nat) : FormatProfile where
  family := "contextual shared-scale block"
  standard :=
    "policy-neutral mathematical core inspired by OCP MX; no concrete MX element encoding claimed"
  representation :=
    [ ⟨"storage", "one Int exponent and a fixed-length vector of Int significands"⟩
    , ⟨"lanes", toString lanes⟩
    , ⟨"shared radix", "2"⟩
    , ⟨"lane value", "significand × 2^sharedExponent"⟩
    , ⟨"field widths", "unbounded in this mathematical core"⟩
    ]
  values :=
    [ ⟨"finite block", s!"exact vector of {lanes} rational values"⟩
    , ⟨"signed zero", "no; integer lane significands have one zero"⟩
    , ⟨"infinity", "no"⟩
    , ⟨"NaN", "no"⟩
    ]
  rounding :=
    [ ⟨"quantization", "nearest-even integer rounding at a caller-supplied shared exponent"⟩
    , ⟨"scale selection", "contextual and explicit; no hidden maximum-magnitude policy"⟩
    , ⟨"overflow", "none; exponent and lane significands are unbounded"⟩
    ]
  execution :=
    [ ⟨"carrier", "SharedScaleCode with Int exponent and Vector Int lanes"⟩
    , ⟨"dispatch", "direct vector kernel using exact rational nearest-even rounding"⟩
    , ⟨"backend proof", "quantizeAt implements the relational contextual specification"⟩
    ]
  specializedOperations :=
    [ ⟨"quantizeAt",
        "nearest-even lane quantization at the caller-supplied shared exponent"⟩ ]
  theoremSurfaces :=
    [ { topic := "exact block representation"
        declarations :=
          [ ``FloatLib.Floats.Formats.Block.represents_iff
          , ``FloatLib.Floats.Formats.Block.blockScaled_sharedScale
          ]
        applicability := .verifiedForType
        scope := "every shared exponent, stored lane, and represented rational vector" }
    , { topic := "contextual nearest-even quantization"
        declarations :=
          [ ``FloatLib.Floats.Formats.Block.quantizesAt_quantizeAt
          , ``FloatLib.Floats.Formats.Block.quantizeAt_refines
          , ``FloatLib.Floats.Formats.Block.decode_quantizeAt_get
          ]
        applicability := .verifiedForType
        scope := "the shared exponent is supplied explicitly by the caller"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each lane is nearest-even rounded to the exact integer grid selected by the caller's shared exponent." } }
    ]
  nonclaims :=
    [ "a standardized bounded MX lane code, reserved scale encoding, or scale-selection algorithm is implemented"
    , "the scalar six-operation `ExecFloat` API applies to vector-valued blocks"
    , "NaN, infinity, saturation, or per-lane status flags are represented"
    ]

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs?
              ``FloatLib.Floats.Formats.Block.SharedScaleCode 1 typeExpr
          | throwUnsupportedSyntax
        let lanes ← Inspection.readNat "shared-scale lane count" arguments[0]!
        logInfoAt tk <| ← Inspection.renderProfile (profile lanes) typeExpr .none

end FloatLib.Floats.Formats.Block.FloatInfo.Command
