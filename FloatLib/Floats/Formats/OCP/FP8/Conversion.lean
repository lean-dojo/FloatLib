/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Rational
public import FloatLib.Tactic.CompilerOptimize
public import FloatLib.Tactic.KernelOptimize

/-!
# OFP8 conversion

OCP OFP8 revision 1.0 (2023-12-01), §5.2.1, requires nearest-even conversion
with both SAT and NONSAT overflow. `policy` selects these rules for any
configured or static-byte destination. `convert` exposes the same quantizer
at the descriptor level, for every exactly decodable source.

The outcome specification and exceptional-input equations are proved below.
Every finite result has the independent nearest-even real-grid value, clipped
for SAT and for fully finite destination encodings. This value theorem assumes
that the delivered result is finite; it does not classify the overflow boundary.
The extra status fields are FloatLib diagnostics; OFP8 requires no exception flags.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.FP8

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.BinaryInterchange

universe u

/--
OFP8 revision 1.0, §5.2.1: `.saturate` selects SAT and `.native` selects NONSAT.
Use with `ExecFloat.convert` and nearest-even rounding. Gradual underflow and
propagated NaNs are retained, and infinity follows the selected overflow rule.
-/
@[inline] def policy (overflow : OverflowMode) : ExecFloat.Binary.Conversion.Policy :=
  { overflow
    infinity := match overflow with
      | .native => .native
      | .saturate => .saturate }

/--
OFP8 revision 1.0, §5.2.1: nearest-even SAT/NONSAT conversion into `destination`.
The source is decoded exactly once. Binary32, binary16 and bfloat16 are the
standard source formats; other exact decoders and destinations are extensions.
-/
@[inline] def convert {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (overflow : OverflowMode) (value : Source) :
    ConversionOutcome (Model destination) :=
  ExecFloat.Binary.Conversion.runWith id ((policy overflow).withRounding .nearest)
    (ExactDecoder.run value)

/--
OFP8 revision 1.0, §5.2.1: every conversion satisfies the shared binary
quantizer's complete outcome specification, for all descriptors and decoders.
-/
theorem convert_spec {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (overflow : OverflowMode) (value : Source) :
    ExecFloat.Binary.Conversion.specWith id ((policy overflow).withRounding .nearest)
      (ExactDecoder.run value) (convert destination overflow value) :=
  ExecFloat.Binary.Conversion.implements_runWith id _ _

/--
OFP8 revision 1.0, §5.2.1: a finite source uses the existing exact rational
rounder, with the selected overflow rule and gradual underflow.
-/
theorem convert_finite {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (overflow : OverflowMode) (value : Source)
    (exact : SignedRat) (h : ExactDecoder.run value = .finite exact) :
    convert destination overflow value =
      ExecFloat.Binary.Conversion.quantizeFiniteWith id
        ((policy overflow).withRounding .nearest) exact := by
  simp only [convert, h, ExecFloat.Binary.Conversion.runWith]

/--
OFP8 revision 1.0, §5.2.1: a finite delivered result is nearest-even real-grid
rounding of the exact source, with endpoint clipping for SAT. Fully finite
destination encodings also clip under NONSAT; those encodings are an extension.
This theorem assumes a finite result and does not classify exceptional overflow.
-/
theorem toReal_convert_finite {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (overflow : OverflowMode) (value : Source)
    (exact : SignedRat) (rounded : Model destination) (status : ConversionStatus)
    (hsource : ExactDecoder.run value = .finite exact)
    (hout : convert destination overflow value = .success rounded status)
    (hfinite : Model.isFinite rounded = true) :
    Model.toReal rounded =
      if overflow = .saturate ∨ destination.encoding = .finite then
        Model.clampAt destination (Model.roundAt destination (exact.value : ℝ))
      else Model.roundAt destination (exact.value : ℝ) := by
  rw [convert_finite destination overflow value exact hsource] at hout
  simp only [ExecFloat.Binary.Conversion.quantizeFiniteWith] at hout
  split at hout
  next result hround =>
    cases hout
    have h := Model.Policy.toReal_roundRat_nearest destination overflow 0 exact.negative
      exact.value.num.natAbs exact.value.den result exact.value.den_nz
      (by simpa only [policy, ExecFloat.Binary.Conversion.Policy.withRounding] using hround)
      hfinite
    simpa only [id_eq, ExecFloat.Binary.Conversion.signedRat_toReal,
      Model.Policy.isFinite_overflowResult_nearest_eq, decide_eq_true_eq] using h
  next => cases hout

/-- OFP8 revision 1.0, §5.2.1 Table 3: SAT infinity becomes signed maximum finite. -/
theorem convert_infinity_sat {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (negative : Bool)
    (h : ExactDecoder.run value = .infinity negative) :
    convert destination .saturate value =
      .success (Model.maxFinite destination negative)
        { inexact := true, overflow := true, saturated := true, mappedSpecial := true } := by
  simp [convert, h, policy, ExecFloat.Binary.Conversion.Policy.withRounding,
    ExecFloat.Binary.Conversion.runWith, ExecFloat.Binary.Conversion.quantizeInfinityWith]

/--
OFP8 revision 1.0, §5.2.1 Table 3: NONSAT infinity uses native overflow,
which is NaN for E4M3 and signed infinity for E5M2.
-/
theorem convert_infinity_nonsat {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (negative : Bool)
    (h : ExactDecoder.run value = .infinity negative) :
    convert destination .native value =
      let rounded := Model.nativeOverflow destination negative
      let mapped := !Model.isInfinite rounded
      .success rounded { inexact := mapped, overflow := mapped, mappedSpecial := mapped } := by
  simp [convert, h, policy, ExecFloat.Binary.Conversion.Policy.withRounding,
    ExecFloat.Binary.Conversion.runWith, ExecFloat.Binary.Conversion.quantizeInfinityWith]

/--
OFP8 revision 1.0, §5.2.1 Table 3: a source NaN is propagated to a destination
NaN when the descriptor supports one. The standard leaves its sign and payload free.
-/
theorem convert_nan {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (overflow : OverflowMode) (value : Source)
    (payload : Option Nat) (negative signaling : Bool) (nan : Model destination)
    (hnan : Model.canonicalNaN? destination = some nan)
    (h : ExactDecoder.run value = .exceptional (.nan payload negative signaling)) :
    convert destination overflow value =
      .success (Model.propagatedNaN destination negative (payload.getD 0))
        { invalid := signaling } := by
  simp [convert, h, policy, ExecFloat.Binary.Conversion.Policy.withRounding,
    ExecFloat.Binary.Conversion.runWith, ExecFloat.Binary.Conversion.quantizeExceptionalWith,
    hnan]

namespace Reference

/-- OFP8 revision 1.0, §5.2.1: the complete reference conversion at every descriptor. -/
@[compiler_optimize baseline]
def conversion : ExecFloat.Backend.Certified (@convert) :=
  .reference { name := "OFP8 exact conversion", kind := .generic, steadyCost := 1 } (@convert)

end Reference

attribute [kernel_optimize unfold] convert policy

end FloatLib.Floats.Formats.OCP.FP8
