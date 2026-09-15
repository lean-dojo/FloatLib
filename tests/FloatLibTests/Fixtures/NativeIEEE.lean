/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Native IEEE validation fixtures

Named binary32 and binary64 encodings used at the compiled native-FPU boundary. Keeping these
fixtures here prevents validation runners from repeating unexplained hexadecimal words.

The three corpora have distinct roles: arithmetic pairs exercise interactions between classes,
rounding ties, cancellation, and gradual underflow; square-root inputs exercise unary domain
boundaries; and interop inputs exercise conversion and canonicalization. They intentionally
include noncanonical NaNs so the runtime checks Lean's documented NaN-canonicalization behavior.
-/

@[expose] public section

namespace FloatLibTests.Fixtures.NativeIEEE

/-- Named encodings needed by the native-boundary validation corpora. -/
structure EdgeCases (Word : Type) where
  positiveZero : Word
  negativeZero : Word
  smallestSubnormal : Word
  negativeSmallestSubnormal : Word
  nextSubnormal : Word
  largestSubnormal : Word
  smallestNormal : Word
  half : Word
  halfUlpAtOne : Word
  one : Word
  nextAboveOne : Word
  two : Word
  four : Word
  negativeOne : Word
  largestFinite : Word
  positiveInfinity : Word
  negativeInfinity : Word
  quietNaN : Word
  signalingNaN : Word

/-- Named IEEE binary32 encodings used by all native-boundary checks. -/
def binary32Cases : EdgeCases UInt32 where
  positiveZero := 0x00000000
  negativeZero := 0x80000000
  smallestSubnormal := 0x00000001
  negativeSmallestSubnormal := 0x80000001
  nextSubnormal := 0x00000002
  largestSubnormal := 0x007fffff
  smallestNormal := 0x00800000
  half := 0x3f000000
  halfUlpAtOne := 0x33800000
  one := 0x3f800000
  nextAboveOne := 0x3f800001
  two := 0x40000000
  four := 0x40800000
  negativeOne := 0xbf800000
  largestFinite := 0x7f7fffff
  positiveInfinity := 0x7f800000
  negativeInfinity := 0xff800000
  quietNaN := 0x7fc12345
  signalingNaN := 0x7f812345

/-- Named IEEE binary64 encodings used by all native-boundary checks. -/
def binary64Cases : EdgeCases UInt64 where
  positiveZero := 0x0000000000000000
  negativeZero := 0x8000000000000000
  smallestSubnormal := 0x0000000000000001
  negativeSmallestSubnormal := 0x8000000000000001
  nextSubnormal := 0x0000000000000002
  largestSubnormal := 0x000fffffffffffff
  smallestNormal := 0x0010000000000000
  half := 0x3fe0000000000000
  halfUlpAtOne := 0x3ca0000000000000
  one := 0x3ff0000000000000
  nextAboveOne := 0x3ff0000000000001
  two := 0x4000000000000000
  four := 0x4010000000000000
  negativeOne := 0xbff0000000000000
  largestFinite := 0x7fefffffffffffff
  positiveInfinity := 0x7ff0000000000000
  negativeInfinity := 0xfff0000000000000
  quietNaN := 0x7ff8123456789abc
  signalingNaN := 0x7ff0123456789abc

/-- Binary-operation samples spanning ordinary values and every IEEE value class. -/
def arithmeticPairs {Word : Type} (cases : EdgeCases Word) : List (Word × Word) :=
  [ (cases.one, cases.two)
  , (cases.one, cases.halfUlpAtOne)
  , (cases.nextAboveOne, cases.negativeOne)
  , (cases.negativeOne, cases.one)
  , (cases.smallestSubnormal, cases.nextSubnormal)
  , (cases.negativeSmallestSubnormal, cases.smallestSubnormal)
  , (cases.smallestNormal, cases.half)
  , (cases.largestSubnormal, cases.smallestSubnormal)
  , (cases.largestSubnormal, cases.smallestNormal)
  , (cases.largestFinite, cases.largestFinite)
  , (cases.positiveZero, cases.negativeZero)
  , (cases.positiveInfinity, cases.one)
  , (cases.quietNaN, cases.one)
  , (cases.signalingNaN, cases.negativeInfinity)
  ]

/-- Square-root samples spanning its finite-domain boundaries and exceptional values. -/
def squareRootInputs {Word : Type} (cases : EdgeCases Word) : List Word :=
  [ cases.positiveZero
  , cases.negativeZero
  , cases.smallestSubnormal
  , cases.largestSubnormal
  , cases.smallestNormal
  , cases.one
  , cases.four
  , cases.negativeOne
  , cases.positiveInfinity
  , cases.quietNaN
  ]

/-- Representative encodings for testing native conversion and NaN canonicalization. -/
def interopInputs {Word : Type} (cases : EdgeCases Word) : List Word :=
  [ cases.positiveZero
  , cases.negativeZero
  , cases.smallestSubnormal
  , cases.negativeSmallestSubnormal
  , cases.largestSubnormal
  , cases.smallestNormal
  , cases.one
  , cases.nextAboveOne
  , cases.positiveInfinity
  , cases.negativeInfinity
  , cases.quietNaN
  , cases.signalingNaN
  ]

end FloatLibTests.Fixtures.NativeIEEE
