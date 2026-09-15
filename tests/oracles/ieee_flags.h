/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 * IEEE 754 exception flags read from MPFR's global flag state.
 */

#ifndef FLOATLIB_IEEE_FLAGS_H
#define FLOATLIB_IEEE_FLAGS_H

#include <mpfr.h>

struct ieee_flags {
  int invalid;
  int divide_by_zero;
  int overflow;
  int underflow;
  int inexact;
};

/*
 * Read the five IEEE flags after one rounded operation and mpfr_subnormalize.
 *
 * mpfr_subnormalize marks the precision reduction for an exact subnormal with
 * its underflow flag. IEEE 754 underflow additionally requires loss of
 * accuracy, matching FloatLib's after-rounding tininess rule
 * (dyadicRoundingStatus in Formats/BinaryInterchange/Status/Runtime.lean), so
 * underflow is reported only together with inexact.
 *
 * MPFR's NaN flag is only a first approximation of IEEE invalid: MPFR has one
 * NaN class and cannot see signaling NaNs. Callers that know the operand
 * encodings refine `invalid` themselves.
 */
static inline struct ieee_flags ieee_flags_from_mpfr(void) {
  struct ieee_flags flags;
  flags.invalid = mpfr_nanflag_p() != 0;
  flags.divide_by_zero = mpfr_divby0_p() != 0;
  flags.overflow = mpfr_overflow_p() != 0;
  flags.inexact = mpfr_inexflag_p() != 0;
  flags.underflow = (mpfr_underflow_p() != 0) && flags.inexact;
  return flags;
}

#endif
