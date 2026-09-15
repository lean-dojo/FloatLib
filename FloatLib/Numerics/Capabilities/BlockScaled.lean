/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System

/-!
# Block-scaled representation capability

Block-scaled codes store one scale shared by several significands. This proof-only capability
relates that concrete decomposition to a system's finite block denotation while leaving the
index, scale, stored significand, lane value, and scaling operation fully generic.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u v w x

/--
A numerical system's finite denotation is lane-wise reconstruction from one shared scale.

All executable projections are explicit parameters. The proposition certifies them but does not
force numerical kernels to access a typeclass dictionary in their inner loops.
-/
def BlockScaled (system : NumericalSystem)
    (Index : Type u) (Scale : Type v) (Stored : Type w) (Lane : Type x)
    (laneAt : system.Scalar → Index → Lane)
    (scaleOf : system.Code → Scale)
    (storedAt : system.Code → Index → Stored)
    (applyScale : Scale → Stored → Lane) : Prop :=
  ∀ code block,
    system.Represents code block →
      ∀ lane,
        laneAt block lane = applyScale (scaleOf code) (storedAt code lane)

end FloatLib.Numerics
