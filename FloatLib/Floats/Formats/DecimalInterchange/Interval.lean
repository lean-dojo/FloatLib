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

`intervalRounding` gives BID or DPD words a rational outward rounding, for decimal32, decimal64,
decimal128, or a custom decimal layout. Each endpoint comes from a directed decimal projection. It
is encoded with the selected codec, decoded again, and compared with the exact input, so a
successful enclosure bounds the input with the words that are really stored, and not just with the
datums before encoding.

NaNs and infinities have no rational value. When overflow would need an infinite endpoint, the
result is `none`, because a finite bound in its place would leave the input outside. With these
endpoints, the shared `Numerics.Interval` operations give you addition, subtraction,
multiplication, and division away from zero.
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
  ⟨encoding.codec.encode format (project format .down x 0).value,
    encoding.codec.encode format (project format .up x 0).value⟩

/--
Checked outward rounding for decimal words, valid for every descriptor and either codec.

The exact endpoint check also covers exceptional outputs and catches any candidate that fails
to bracket the target. A saturated finite value is never silently treated as infinity.
-/
def intervalRounding (format : Format) (encoding : Encoding) :
    Numerics.OutwardRounding (BitVec format.bitWidth) ℚ :=
  Numerics.OutwardRounding.ofCandidates
    (decodeIntervalEndpoint format encoding) (intervalCandidates format encoding)

end FloatLib.Floats.Formats.DecimalInterchange
