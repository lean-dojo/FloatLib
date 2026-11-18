/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.OCP.FP8.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
public import FloatLibBenchmarks.Standards.Protocol

/-!
# OFP8 conversion timing inputs

OFP8 revision 1.0, §5.2.1: both overflow modes are measured for E4M3 and
E5M2, with binary16, bfloat16 and binary32 sources. Reverse and cross-format
conversions exercise the general exact-decoder interface. Native input arrays
contain both signs, signed zeros, a subnormal, the largest finite word, an
all-ones exponent and a NaN. The kernel fixture uses the same first finite word.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards.OFP8

open FloatLib.Numerics FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- Eight stored inputs prepared before timing, including the special-value regimes. -/
def sample (fmt : FloatFormat) (seed : Nat) : Model fmt :=
  match seed % 8 with
  | 0 => Model.ofFields fmt false fmt.exponentBias (2 ^ fmt.fracWidth / 3 + 1)
  | 1 => Model.ofFields fmt true fmt.exponentBias (2 ^ fmt.fracWidth / 3 + 1)
  | 2 => Model.ofNatBits 1
  | 3 => Model.zero fmt false
  | 4 => Model.zero fmt true
  | 5 => Model.maxFinite fmt false
  | 6 => Model.ofFields fmt false fmt.expAllOnesNat 0
  | _ => Model.canonicalNaN fmt

/-- Force every decoded data field, including signed zero and exceptional metadata. -/
def observeDecoded : NumericalValue SignedRat → Nat
  | .finite value =>
      8 * Nat.pair (observeInt value.value.num) value.value.den + 2 * value.negative.toNat
  | .infinity negative => 8 * negative.toNat + 1
  | .exceptional (.nan payload negative signaling) =>
      32 * (payload.map (· + 1)).getD 0 +
        16 * negative.toNat + 8 * signaling.toNat + 3
  | .exceptional .notAReal => 5
  | .exceptional (.reserved payload) => 8 * (payload.map (· + 1)).getD 0 + 6
  | .exceptional .undefined => 7

attribute [kernel_optimize unfold] sample observeDecoded

end FloatLibBenchmarks.Standards.OFP8
