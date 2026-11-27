/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.StandardProof
public import FloatLib.Tactic.Interval.Registry

/-!
# Registered elementary functions

The standard elementary functions use the same enclosure registration as user-defined operations.
Their containment theorems are proved in `FloatLib.Numerics.Enclosure.Expression.StandardProof`,
which needs no tactic, and get the attribute `interval_extension` here. `acceptedDomain?` says
which argument enclosures the partial ones accept, and `interval` quotes it when the backend
rejects a call.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

attribute [interval_extension] exp_extension_sound log_extension_sound sin_extension_sound
  cos_extension_sound tan_extension_sound arcsin_extension_sound arccos_extension_sound
  arctan_extension_sound sinh_extension_sound cosh_extension_sound tanh_extension_sound
  sqrt_extension_sound arsinh_extension_sound arcosh_extension_sound artanh_extension_sound
  rpow_extension_sound logb_extension_sound

/--
The argument enclosures that a partial registered enclosure accepts, keyed by its registration and
phrased for `interval`'s message when it rejects a call. These are conditions on the enclosures the
backend computes. The real functions themselves are defined by Mathlib at every real argument. The
other registrations here accept every argument enclosure.
-/
meta def acceptedDomain? (registration : Lean.Name) : Option String :=
  [ (``log_extension_sound, "argument enclosures with a positive lower endpoint")
  , (``sqrt_extension_sound, "argument enclosures with a nonnegative lower endpoint")
  , (``tan_extension_sound, "arguments whose cosine enclosure excludes zero")
  , (``arcsin_extension_sound,
      "argument enclosures inside [-1, 1]; an endpoint very close to -1 or 1 can also need a \
        larger precision")
  , (``arccos_extension_sound,
      "argument enclosures inside [-1, 1]; an endpoint very close to -1 or 1 can also need a \
        larger precision")
  , (``arcosh_extension_sound, "argument enclosures with a lower endpoint of at least 1")
  , (``artanh_extension_sound, "argument enclosures strictly inside (-1, 1)")
  , (``rpow_extension_sound, "base enclosures with a positive lower endpoint")
  , (``logb_extension_sound,
      "positive base and argument enclosures whose base logarithm enclosure excludes zero, so \
        the base enclosure must stay away from 1")
  ].lookup registration

end FloatLib.Numerics.Interval
