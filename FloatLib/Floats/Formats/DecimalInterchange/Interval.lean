/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Runtime
public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Decimal interchange interval endpoints

`intervalRounding` equips actual BID or DPD words with rational outward rounding. The descriptor
may be decimal32, decimal64, decimal128, or a custom decimal layout. Directed decimal projection
produces each endpoint, which is encoded with the selected codec and checked against the exact
input after decoding. A successful enclosure therefore bounds the input using the actual stored
words, not only the decimal datums before encoding.

NaNs and infinities have no rational interpretation. Overflow that needs an infinite endpoint
returns `none`; it is not replaced by a finite bound that would exclude the input. The shared
`Numerics.Interval` operations provide addition, subtraction, multiplication, and division away
from zero using these endpoints.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- An interval whose endpoints are complete decimal interchange words in one layout. -/
abbrev Interval (format : Format) := Numerics.Interval (BitVec format.bitWidth)

/-- Interpret a decimal endpoint as an exact rational, rejecting NaNs and infinities. -/
def decodeIntervalEndpoint (format : Format) (encoding : Encoding)
    (word : BitVec format.bitWidth) : Option ℚ :=
  (encoding.decode format word).toRat?

/-- Directed decimal projections encoded in the selected interchange representation. -/
def intervalCandidates (format : Format) (encoding : Encoding) (x : ℚ) : Interval format :=
  ⟨encoding.codec.encode format (project format .towardNegative x 0).value,
    encoding.codec.encode format (project format .towardPositive x 0).value⟩

/--
Checked outward rounding for decimal words, valid for every descriptor and either codec.

The exact endpoint check also covers exceptional outputs and catches any candidate that fails
to bracket the target; the result never silently treats a saturated finite value as infinity.
-/
def intervalRounding (format : Format) (encoding : Encoding) :
    Numerics.OutwardRounding (BitVec format.bitWidth) ℚ :=
  Numerics.OutwardRounding.ofCandidates
    (decodeIntervalEndpoint format encoding) (intervalCandidates format encoding)

end FloatLib.Floats.Formats.DecimalInterchange
