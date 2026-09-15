/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sign.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Runtime
public import FloatLib.Numerics.IEEEClass

/-!
# Decimal classification and quantum queries

The predicates of IEEE 754-2019 §§5.7.2–5.7.3 are non-signaling, including on
signaling NaNs. Normality depends on numerical magnitude, not coefficient length:
different members of one cohort have the same classification.
`quantumExponent` is an additional finite-datum query, not an IEEE operation name.
Canonicality belongs to the stored word because decoding accepts redundant words.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Decimal classification uses the shared ten IEEE floating-point classes. -/
abbrev Class := Numerics.IEEEClass

namespace Datum

/-- Finiteness includes either sign of zero. -/
def isFinite : Datum → Bool
  | .finite _ _ _ => true
  | _ => false

/-- Test numerical zero, independently of its sign and quantum. -/
def isZero : Datum → Bool
  | .finite _ c _ => c == 0
  | _ => false

/-- Test either signed infinity. -/
def isInfinite : Datum → Bool
  | .infinity _ => true
  | _ => false

/-- Test either signaling or quiet NaN. -/
def isNaN : Datum → Bool
  | .nan _ _ _ => true
  | _ => false

/-- A finite value is normal when its magnitude reaches the format's normal threshold. -/
def isNormal (f : Format) : Datum → Bool
  | .finite _ c q => decide (f.minNormal ≤ (c : ℚ) * (10 : ℚ) ^ q)
  | _ => false

/-- A subnormal is nonzero and smaller in magnitude than the normal threshold. -/
def isSubnormal (f : Format) : Datum → Bool
  | .finite _ c q => decide (c ≠ 0 ∧ (c : ℚ) * (10 : ℚ) ^ q < f.minNormal)
  | _ => false

/-- Classify a datum without changing it or raising invalid on a signaling NaN. -/
def classify (f : Format) : Datum → Class
  | .nan _ t _ => if t then .signalingNaN else .quietNaN
  | .infinity s => if s then .negativeInfinity else .positiveInfinity
  | .finite s c q =>
      if c = 0 then
        if s then .negativeZero else .positiveZero
      else if (c : ℚ) * (10 : ℚ) ^ q < f.minNormal then
        if s then .negativeSubnormal else .positiveSubnormal
      else
        if s then .negativeNormal else .positiveNormal

/-- Return a finite datum's stored quantum exponent; special values return `none`. -/
def quantumExponent : Datum → Option Int
  | .finite _ _ q => some q
  | _ => none

/-- Equal finite quanta, or two infinities, or two NaNs, as specified by §5.7.3.
Signs, coefficients and NaN signaling bits are immaterial. -/
def sameQuantum : Datum → Datum → Bool
  | .finite _ _ q, .finite _ _ r => q == r
  | .infinity _, .infinity _ | .nan _ _ _, .nan _ _ _ => true
  | _, _ => false

/-- The decimal radix, including for a special operand. -/
def radix (_ : Datum) : Nat := 10

end Datum

/-- Test canonical storage, including redundant DPD declets, oversized BID coefficients
and ignored infinity/NaN bits. Decoding alone cannot distinguish these representations. -/
def Encoding.isCanonical (encoding : Encoding) (f : Format) (w : BitVec f.bitWidth) :
    Bool :=
  decide (encoding.canonicalize f w = w)

end FloatLib.Floats.Formats.DecimalInterchange
