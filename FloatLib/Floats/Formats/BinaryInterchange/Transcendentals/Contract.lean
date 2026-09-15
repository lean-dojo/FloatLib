/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Floats.Interval.Quantized
public import FloatLib.Numerics.Enclosure.Elementary.Proof

/-!
# Proof contracts for transcendental approximations

These contracts state and prove accuracy claims about an approximation:

1. a real function value lies in a proved enclosure;
2. an executable result satisfies a proved absolute-error budget; and
3. an enclosure is narrow enough that both endpoints round to the same destination value.

When both endpoints round alike, monotonicity forces the enclosed function value to round there
too. `StableEnclosure.roundAt_eq_roundAt_lower` proves this fact. Constructing an enclosure
requires Lean proofs of both bounds; external numerical output alone does not supply them.

IEEE exceptional-value behavior and the sign of an exact zero remain separate bit-level
obligations. `roundAt` is the finite real grid semantics.

`ApproximationCertificateOn` and `CorrectlyRoundedCertificateOn` restrict the finite-real
guarantees to an explicit predicate on encoded inputs. For example, a logarithm certificate can
use `fun input ↦ 0 < toReal input`; an exponential certificate can use a proved input range on
which the result remains finite. Membership never replaces the obligation to prove output
finiteness. Outside the domain these certificates make no claim, so exceptional-value and overflow
behavior need separate specifications. The certificates without `On` apply to every finite input
and are equivalent to the domain-restricted certificates with domain `fun _ ↦ True`.

## References

* IEEE 754-2019, Section 9.2, recommended correctly rounded operations.
* F. de Dinechin, C. Lauter, and J.-M. Muller, “Fast and correctly rounded logarithms in
  double-precision,” RAIRO-Theoretical Informatics and Applications 41(1), 2007.
* S. Boldo and G. Melquiond, “Flocq: A Unified Library for Proving Floating-Point Algorithms in
  Coq,” IEEE ARITH 2011.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.Transcendentals.Contract

open FloatLib.Floats.Interval

/-- A checked closed real enclosure of `f x`. -/
structure RealEnclosure (f : ℝ → ℝ) (x : ℝ) where
  /-- Proved lower endpoint. -/
  lower : ℝ
  /-- Proved upper endpoint. -/
  upper : ℝ
  /-- The lower endpoint does not exceed the exact value. -/
  lower_le : lower ≤ f x
  /-- The exact value does not exceed the upper endpoint. -/
  le_upper : f x ≤ upper

namespace RealEnclosure

/-- Use proved executable rational endpoints in a real-valued approximation contract. -/
def ofRational {f : ℝ → ℝ} {x : ℝ}
    (interval : FloatLib.Numerics.RationalInterval) (hx : interval.Contains (f x)) :
    RealEnclosure f x where
  lower := interval.lo
  upper := interval.hi
  lower_le := hx.1
  le_upper := hx.2

/-- A Taylor enclosure whose rational endpoints are computed inside FloatLib. -/
noncomputable def expRational (x : ℚ) (degree : Nat) : RealEnclosure Real.exp (x : ℝ) :=
  ofRational (FloatLib.Numerics.Enclosure.exp x degree)
    (FloatLib.Numerics.Enclosure.contains_exp x degree)

/-- A proved rational logarithm enclosure for a positive input. -/
noncomputable def logRational (x : ℚ) (degree : Nat) (hx : 0 < x) :
    RealEnclosure Real.log (x : ℝ) :=
  ofRational (FloatLib.Numerics.Enclosure.log x degree)
    (FloatLib.Numerics.Enclosure.contains_log x degree hx)

/-- The exact function value belongs to its enclosure. -/
theorem mem_Icc {f : ℝ → ℝ} {x : ℝ} (enclosure : RealEnclosure f x) :
    f x ∈ Set.Icc enclosure.lower enclosure.upper :=
  ⟨enclosure.lower_le, enclosure.le_upper⟩

/-- Every proved enclosure has ordered endpoints. -/
theorem lower_le_upper {f : ℝ → ℝ} {x : ℝ} (enclosure : RealEnclosure f x) :
    enclosure.lower ≤ enclosure.upper :=
  enclosure.lower_le.trans enclosure.le_upper

/--
Any candidate lying in the same enclosure has absolute error at most its width.

This conservative bound is often sufficient for a first verified implementation. A sharper
algorithm-specific proof can populate `ApproximationCertificate` directly.
-/
theorem abs_sub_le_width {f : ℝ → ℝ} {x candidate : ℝ}
    (enclosure : RealEnclosure f x)
    (hcandidate : enclosure.lower ≤ candidate ∧ candidate ≤ enclosure.upper) :
    |candidate - f x| ≤ enclosure.upper - enclosure.lower := by
  apply (abs_le).2
  constructor <;> linarith [enclosure.lower_le, enclosure.le_upper]

/-- Build an enclosure by monotonicity from a real input interval. -/
def ofMonotone {f : ℝ → ℝ} (hf : Monotone f) (input : RInterval)
    {x : ℝ} (hx : x ∈ input) : RealEnclosure f x where
  lower := f input.lo
  upper := f input.hi
  lower_le := hf hx.1
  le_upper := hf hx.2

/-- Round a proved real enclosure outward with any sound endpoint rounder. -/
noncomputable def outward {f : ℝ → ℝ} {x : ℝ}
    (rounder : Rounder) (enclosure : RealEnclosure f x) : RealEnclosure f x where
  lower := rounder.down enclosure.lower
  upper := rounder.up enclosure.upper
  lower_le := (rounder.down_le enclosure.lower).trans enclosure.lower_le
  le_upper := enclosure.le_upper.trans (rounder.le_up enclosure.upper)

/-- Sound exponential enclosure on an input interval. -/
noncomputable def exp (input : RInterval) {x : ℝ} (hx : x ∈ input) :
    RealEnclosure Real.exp x :=
  ofMonotone Real.exp_monotone input hx

/-- Sound hyperbolic-sine enclosure on an input interval. -/
noncomputable def sinh (input : RInterval) {x : ℝ} (hx : x ∈ input) :
    RealEnclosure Real.sinh x :=
  ofMonotone Real.sinh_strictMono.monotone input hx

/-- Enclose sine in `[-1, 1]` for every real argument. -/
def sin (x : ℝ) : RealEnclosure Real.sin x where
  lower := -1
  upper := 1
  lower_le := Real.neg_one_le_sin x
  le_upper := Real.sin_le_one x

/-- Enclose cosine in `[-1, 1]` for every real argument. -/
def cos (x : ℝ) : RealEnclosure Real.cos x where
  lower := -1
  upper := 1
  lower_le := Real.neg_one_le_cos x
  le_upper := Real.cos_le_one x

/-- Enclose hyperbolic tangent in `[-1, 1]` for every real argument. -/
def tanh (x : ℝ) : RealEnclosure Real.tanh x where
  lower := -1
  upper := 1
  lower_le := (Real.neg_one_lt_tanh x).le
  le_upper := (Real.tanh_lt_one x).le

/--
Sound hyperbolic-cosine enclosure on an input interval.

The upper endpoint uses the largest absolute endpoint because `cosh` is even and increases with
absolute value.
-/
noncomputable def cosh (input : RInterval) {x : ℝ} (hx : x ∈ input) :
    RealEnclosure Real.cosh x where
  lower := 1
  upper := Real.cosh (RInterval.absMax input)
  lower_le := Real.one_le_cosh x
  le_upper := by
    apply (Real.cosh_le_cosh).2
    have hmaxNonnegative : 0 ≤ RInterval.absMax input :=
      (abs_nonneg input.lo).trans (le_max_left |input.lo| |input.hi|)
    simpa only [abs_of_nonneg hmaxNonnegative] using
      (RInterval.abs_le_absMax (I := input) hx)

/-- Convert the existing proved logarithm interval into the common enclosure contract. -/
noncomputable def log (rounder : Rounder) (input : RInterval)
    {x : ℝ} (hpositive : 0 < input.lo) (hx : x ∈ input) :
    RealEnclosure Real.log x :=
  let output := RInterval.log rounder input
  let sound := RInterval.mem_log (R := rounder) hpositive hx
  { lower := output.lo
    upper := output.hi
    lower_le := sound.1
    le_upper := sound.2 }

/--
Convert the existing proved square-root interval into the common enclosure contract.

No sign hypothesis is needed: `Real.sqrt` is zero on negative arguments and monotone on all of `ℝ`.
-/
noncomputable def sqrt (rounder : Rounder) (input : RInterval)
    {x : ℝ} (hx : x ∈ input) :
    RealEnclosure Real.sqrt x :=
  let output := RInterval.sqrt rounder input
  let sound := RInterval.mem_sqrt (R := rounder) hx
  { lower := output.lo
    upper := output.hi
    lower_le := sound.1
    le_upper := sound.2 }

end RealEnclosure

/--
A proved enclosure whose endpoints select one nearest-even destination-grid value.

The inherited enclosure bounds and the endpoint-rounding equality are all proof obligations.
-/
structure StableEnclosure (fmt : FloatFormat) (f : ℝ → ℝ) (x : ℝ)
    extends RealEnclosure f x where
  /-- Both enclosure endpoints round to the same finite-grid real value. -/
  endpoints_round_same : roundAt fmt lower = roundAt fmt upper

namespace StableEnclosure

/-- A stable enclosure determines the correctly rounded real value of the exact function. -/
theorem roundAt_eq_roundAt_lower {fmt : FloatFormat} {f : ℝ → ℝ} {x : ℝ}
    (enclosure : StableEnclosure fmt f x) :
    roundAt fmt (f x) = roundAt fmt enclosure.lower := by
  apply le_antisymm
  · calc
      roundAt fmt (f x) ≤ roundAt fmt enclosure.upper :=
        roundAt_mono fmt enclosure.le_upper
      _ = roundAt fmt enclosure.lower := enclosure.endpoints_round_same.symm
  · exact roundAt_mono fmt enclosure.lower_le

end StableEnclosure

/--
A finite encoded result backed by a stable real enclosure.

The final equality connects the stored result to the lower endpoint's rounded value. Together with
stability, this proves correct nearest-even rounding of the exact function in finite real
semantics.
-/
structure CertifiedRoundedResult
    (fmt : FloatFormat) (f : ℝ → ℝ) (x : ℝ)
    extends StableEnclosure fmt f x where
  /-- Encoded result returned by an implementation. -/
  value : Model fmt
  /-- The encoded result is finite, so `toReal` is its complete numerical magnitude. -/
  value_finite : isFinite value = true
  /-- The implementation selected the endpoint-certified rounded real value. -/
  value_eq_lower_round : toReal value = roundAt fmt lower

namespace CertifiedRoundedResult

/-- The certified encoded result has the correctly rounded real value of `f x`. -/
theorem toReal_value_eq_roundAt {fmt : FloatFormat} {f : ℝ → ℝ} {x : ℝ}
    (result : CertifiedRoundedResult fmt f x) :
    toReal result.value = roundAt fmt (f x) := by
  rw [result.value_eq_lower_round, result.toStableEnclosure.roundAt_eq_roundAt_lower]

end CertifiedRoundedResult

/--
Whole-algorithm absolute-error contract for an executable unary approximation.

The fields require output finiteness and an error bound for every finite input.
-/
structure ApproximationCertificate
    (fmt : FloatFormat)
    (f : ℝ → ℝ)
    (approximation : Model fmt → Model fmt)
    (errorBudget : Model fmt → ℝ) : Prop where
  /-- Every advertised error budget is nonnegative. -/
  budget_nonnegative : ∀ input, 0 ≤ errorBudget input
  /-- Finite inputs in scope produce finite outputs. -/
  output_finite :
    ∀ input, isFinite input = true → isFinite (approximation input) = true
  /-- The decoded result satisfies the advertised real absolute-error budget. -/
  error_le :
    ∀ input, isFinite input = true →
      |toReal (approximation input) - f (toReal input)| ≤ errorBudget input

/--
Whole-algorithm correctly-rounded finite-real contract.

Both components are propositions, so the certificate adds no runtime data.
-/
def CorrectlyRoundedCertificate
    (fmt : FloatFormat)
    (f : ℝ → ℝ)
    (implementation : Model fmt → Model fmt) : Prop :=
  (∀ input, isFinite input = true → isFinite (implementation input) = true) ∧
  (∀ input, isFinite input = true →
    toReal (implementation input) = roundAt fmt (f (toReal input)))

namespace CorrectlyRoundedCertificate

/-- Finite inputs in scope produce finite outputs. -/
theorem output_finite {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt}
    (certificate : CorrectlyRoundedCertificate fmt f implementation) :
    ∀ input, isFinite input = true → isFinite (implementation input) = true :=
  certificate.1

/-- At every finite input, the result equals nearest-even rounding of the exact real function. -/
theorem toReal_eq_roundAt {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt}
    (certificate : CorrectlyRoundedCertificate fmt f implementation) :
    ∀ input, isFinite input = true →
      toReal (implementation input) = roundAt fmt (f (toReal input)) :=
  certificate.2

end CorrectlyRoundedCertificate

/--
Absolute-error contract on an explicit domain of encoded inputs.

The domain can express mathematical restrictions, such as positivity for logarithms, and the
range on which finite output is promised. Budgets must be nonnegative on the domain; output
finiteness and accuracy are required for every finite input in that domain. In particular, merely
restricting the mathematical domain does not discharge the output-finiteness obligation.
-/
structure ApproximationCertificateOn
    (fmt : FloatFormat)
    (f : ℝ → ℝ)
    (approximation : Model fmt → Model fmt)
    (errorBudget : Model fmt → ℝ)
    (domain : Model fmt → Prop) : Prop where
  /-- Every budget advertised on the domain is nonnegative. -/
  budget_nonnegative : ∀ input, domain input → 0 ≤ errorBudget input
  /-- Finite inputs in the domain produce finite outputs. -/
  output_finite :
    ∀ input, isFinite input = true → domain input → isFinite (approximation input) = true
  /-- The decoded result satisfies the budget at every finite input in the domain. -/
  error_le :
    ∀ input, isFinite input = true → domain input →
      |toReal (approximation input) - f (toReal input)| ≤ errorBudget input

namespace ApproximationCertificateOn

/-- Restrict an absolute-error certificate to a smaller domain. -/
theorem mono {fmt : FloatFormat} {f : ℝ → ℝ}
    {approximation : Model fmt → Model fmt} {errorBudget : Model fmt → ℝ}
    {domain smallerDomain : Model fmt → Prop}
    (certificate : ApproximationCertificateOn fmt f approximation errorBudget domain)
    (hsub : ∀ input, smallerDomain input → domain input) :
    ApproximationCertificateOn fmt f approximation errorBudget smallerDomain where
  budget_nonnegative input hdomain := certificate.budget_nonnegative input (hsub input hdomain)
  output_finite input hfinite hdomain :=
    certificate.output_finite input hfinite (hsub input hdomain)
  error_le input hfinite hdomain :=
    certificate.error_le input hfinite (hsub input hdomain)

end ApproximationCertificateOn

namespace ApproximationCertificate

/-- A whole-algorithm absolute-error certificate applies on any chosen domain. -/
theorem on_domain {fmt : FloatFormat} {f : ℝ → ℝ}
    {approximation : Model fmt → Model fmt} {errorBudget : Model fmt → ℝ}
    (certificate : ApproximationCertificate fmt f approximation errorBudget)
    (domain : Model fmt → Prop) :
    ApproximationCertificateOn fmt f approximation errorBudget domain where
  budget_nonnegative input _ := certificate.budget_nonnegative input
  output_finite input hfinite _ := certificate.output_finite input hfinite
  error_le input hfinite _ := certificate.error_le input hfinite

end ApproximationCertificate

namespace ApproximationCertificateOn

/-- The unrestricted domain gives the absolute-error contract for all finite inputs. -/
@[simp] theorem true_iff {fmt : FloatFormat} {f : ℝ → ℝ}
    {approximation : Model fmt → Model fmt} {errorBudget : Model fmt → ℝ} :
    ApproximationCertificateOn fmt f approximation errorBudget (fun _ ↦ True) ↔
      ApproximationCertificate fmt f approximation errorBudget := by
  constructor
  · intro certificate
    exact {
      budget_nonnegative := fun input ↦ certificate.budget_nonnegative input trivial
      output_finite := fun input hfinite ↦ certificate.output_finite input hfinite trivial
      error_le := fun input hfinite ↦ certificate.error_le input hfinite trivial }
  · intro certificate
    exact certificate.on_domain (fun _ ↦ True)

end ApproximationCertificateOn

/--
Correct nearest-even finite-real rounding on an explicit domain of encoded inputs.

Every finite input in the domain must produce a finite result with the stated rounded real
value. This does not certify overflow, exceptional values, or the sign of zero: `roundAt` has no
upper exponent bound, and those behaviors need separate bit-level specifications.
-/
def CorrectlyRoundedCertificateOn
    (fmt : FloatFormat)
    (f : ℝ → ℝ)
    (implementation : Model fmt → Model fmt)
    (domain : Model fmt → Prop) : Prop :=
  (∀ input, isFinite input = true → domain input → isFinite (implementation input) = true) ∧
  (∀ input, isFinite input = true → domain input →
    toReal (implementation input) = roundAt fmt (f (toReal input)))

namespace CorrectlyRoundedCertificateOn

/-- Finite inputs in the certified domain produce finite outputs. -/
theorem output_finite {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt} {domain : Model fmt → Prop}
    (certificate : CorrectlyRoundedCertificateOn fmt f implementation domain) :
    ∀ input, isFinite input = true → domain input → isFinite (implementation input) = true :=
  certificate.1

/-- At finite inputs in the domain, the result equals rounding of the exact real function. -/
theorem toReal_eq_roundAt {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt} {domain : Model fmt → Prop}
    (certificate : CorrectlyRoundedCertificateOn fmt f implementation domain) :
    ∀ input, isFinite input = true → domain input →
      toReal (implementation input) = roundAt fmt (f (toReal input)) :=
  certificate.2

/-- Restrict a correctly-rounded certificate to a smaller domain. -/
theorem mono {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt} {domain smallerDomain : Model fmt → Prop}
    (certificate : CorrectlyRoundedCertificateOn fmt f implementation domain)
    (hsub : ∀ input, smallerDomain input → domain input) :
    CorrectlyRoundedCertificateOn fmt f implementation smallerDomain :=
  ⟨fun input hfinite hdomain ↦ certificate.output_finite input hfinite (hsub input hdomain),
    fun input hfinite hdomain ↦ certificate.toReal_eq_roundAt input hfinite (hsub input hdomain)⟩

/-- Assemble a domain certificate from stable enclosures certifying the implementation's results. -/
theorem of_certified_results {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt} {domain : Model fmt → Prop}
    (results : ∀ input, isFinite input = true → domain input →
      CertifiedRoundedResult fmt f (toReal input))
    (hvalue : ∀ input hfinite hdomain,
      (results input hfinite hdomain).value = implementation input) :
    CorrectlyRoundedCertificateOn fmt f implementation domain := by
  constructor
  · intro input hfinite hdomain
    rw [← hvalue input hfinite hdomain]
    exact (results input hfinite hdomain).value_finite
  · intro input hfinite hdomain
    rw [← hvalue input hfinite hdomain]
    exact (results input hfinite hdomain).toReal_value_eq_roundAt

end CorrectlyRoundedCertificateOn

namespace CorrectlyRoundedCertificate

/-- A whole-algorithm correctly-rounded certificate applies on any chosen domain. -/
theorem on_domain {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt}
    (certificate : CorrectlyRoundedCertificate fmt f implementation)
    (domain : Model fmt → Prop) :
    CorrectlyRoundedCertificateOn fmt f implementation domain :=
  ⟨fun input hfinite _ ↦ certificate.output_finite input hfinite,
    fun input hfinite _ ↦ certificate.toReal_eq_roundAt input hfinite⟩

end CorrectlyRoundedCertificate

namespace CorrectlyRoundedCertificateOn

/-- The unrestricted domain gives the correct-rounding contract for all finite inputs. -/
@[simp] theorem true_iff {fmt : FloatFormat} {f : ℝ → ℝ}
    {implementation : Model fmt → Model fmt} :
    CorrectlyRoundedCertificateOn fmt f implementation (fun _ ↦ True) ↔
      CorrectlyRoundedCertificate fmt f implementation := by
  constructor
  · intro certificate
    exact ⟨fun input hfinite ↦ certificate.output_finite input hfinite trivial,
      fun input hfinite ↦ certificate.toReal_eq_roundAt input hfinite trivial⟩
  · intro certificate
    exact certificate.on_domain (fun _ ↦ True)

end CorrectlyRoundedCertificateOn

end Model.Transcendentals.Contract
end FloatLib.Floats.Formats.BinaryInterchange
