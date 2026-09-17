/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval.Runtime
public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Binary adapter for format-independent interval arithmetic

The generic finite interval API uses exact rational decoding and directed binary rounding.
It returns `none` if an endpoint is exceptional or no finite enclosure is produced. The richer
`Binary.Interval` operations remain available when an IEEE whole-range infinity fallback is
desired instead.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Checked finite outward rounding for the configured binary carrier, including finite encodings.

Directed model rounding supplies candidates; exact rational comparisons certify the accepted
enclosure and reject inappropriate saturation at the range boundary.
-/
def intervalRounding :
    Numerics.OutwardRounding
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) ℚ :=
  Numerics.OutwardRounding.ofCandidates Binary.toRat? fun x =>
    ⟨Binary.ofModel (Model.roundRatDown format (decide (x.num < 0)) x.num.natAbs x.den),
      Binary.ofModel (Model.roundRatUp format (decide (x.num < 0)) x.num.natAbs x.den)⟩

end FloatLib.Floats.ExecFloat.Binary
