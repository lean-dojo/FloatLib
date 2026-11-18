/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard

/-!
# The N1169 spellings at the example layout

N1169, ISO/IEC TR 18037:2006(E), C 7.18a.2, 7.18a.3 and 7.18a.6, and §4.1.6. Every generated
spelling of `Embedded.Standard` is evaluated here at `Layout.example` (8, 16 and 32-bit `fract`
types and `accum` types with eight integral bits), by Lean's kernel: the limit macros, the
associated integer types, the `abs`, `round`, `countls`, `bits`, `*bits`, mixed integer and
`strtofx` functions of each type, and the operators on `short fract` values.

Each theorem is one evaluation at this layout. The statements for every layout are the theorems
of `Embedded.Proof`, `Embedded.Limits` and `Embedded.Text` about the operations that the spellings
specialize.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

namespace Examples

/-- Nearest rounding with ties to even, as a conversion rounding. -/
abbrev even : Rounding := NearestRounding.even.toRounding

/-- The type `short fract`. -/
abbrev shortFract : CType := ⟨.fract, .short, true, false⟩

/-- The greatest `short fract` value of the example layout. -/
abbrev top : (Layout.example.format shortFract).Code := SFRACT_MAX Layout.example

/-- The least positive `short fract` value of the example layout. -/
abbrev unit : (Layout.example.format shortFract).Code :=
  SFRACT_EPSILON Layout.example Layout.example_valid

/-- The environment that rounds every conversion to nearest with ties to even, with the default
overflow modes and exact arithmetic. -/
abbrev environment : Environment := { rounding := fun _ => even }

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the fractional bit counts `*_FBIT` of
    the twelve types, at the example layout.
-/
theorem fbit :
    [SFRACT_FBIT Layout.example, FRACT_FBIT Layout.example, LFRACT_FBIT Layout.example,
      USFRACT_FBIT Layout.example, UFRACT_FBIT Layout.example, ULFRACT_FBIT Layout.example,
      SACCUM_FBIT Layout.example, ACCUM_FBIT Layout.example, LACCUM_FBIT Layout.example,
      USACCUM_FBIT Layout.example, UACCUM_FBIT Layout.example, ULACCUM_FBIT Layout.example] =
      [7, 15, 31, 8, 16, 32, 7, 15, 31, 8, 16, 32] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the integral bit counts `*_IBIT` of the
    six accum types, at the example layout.
-/
theorem ibit :
    [SACCUM_IBIT Layout.example, ACCUM_IBIT Layout.example, LACCUM_IBIT Layout.example,
      USACCUM_IBIT Layout.example, UACCUM_IBIT Layout.example, ULACCUM_IBIT Layout.example] =
      [8, 8, 8, 8, 8, 8] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the values of the greatest codes `*_MAX`
    of the twelve types, at the example
layout. -/
theorem max :
    [Format.decode (SFRACT_MAX Layout.example), Format.decode (FRACT_MAX Layout.example),
      Format.decode (LFRACT_MAX Layout.example), Format.decode (USFRACT_MAX Layout.example),
      Format.decode (UFRACT_MAX Layout.example), Format.decode (ULFRACT_MAX Layout.example),
      Format.decode (SACCUM_MAX Layout.example), Format.decode (ACCUM_MAX Layout.example),
      Format.decode (LACCUM_MAX Layout.example), Format.decode (USACCUM_MAX Layout.example),
      Format.decode (UACCUM_MAX Layout.example), Format.decode (ULACCUM_MAX Layout.example)] =
      [127 / 128, 32767 / 32768, 2147483647 / 2147483648, 255 / 256, 65535 / 65536,
        4294967295 / 4294967296, 32767 / 128, 8388607 / 32768, 549755813887 / 2147483648,
        65535 / 256, 16777215 / 65536, 1099511627775 / 4294967296] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the values of the least codes `*_MIN` of
    the six signed types, at the example
layout. -/
theorem min :
    [Format.decode (SFRACT_MIN Layout.example), Format.decode (FRACT_MIN Layout.example),
      Format.decode (LFRACT_MIN Layout.example), Format.decode (SACCUM_MIN Layout.example),
      Format.decode (ACCUM_MIN Layout.example), Format.decode (LACCUM_MIN Layout.example)] =
      [-1, -1, -1, -256, -256, -256] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the values of the least positive codes
    `*_EPSILON` of the twelve types, at the
example layout. -/
theorem epsilon :
    [Format.decode (SFRACT_EPSILON Layout.example Layout.example_valid),
      Format.decode (FRACT_EPSILON Layout.example Layout.example_valid),
      Format.decode (LFRACT_EPSILON Layout.example Layout.example_valid),
      Format.decode (USFRACT_EPSILON Layout.example Layout.example_valid),
      Format.decode (UFRACT_EPSILON Layout.example Layout.example_valid),
      Format.decode (ULFRACT_EPSILON Layout.example Layout.example_valid),
      Format.decode (SACCUM_EPSILON Layout.example Layout.example_valid),
      Format.decode (ACCUM_EPSILON Layout.example Layout.example_valid),
      Format.decode (LACCUM_EPSILON Layout.example Layout.example_valid),
      Format.decode (USACCUM_EPSILON Layout.example Layout.example_valid),
      Format.decode (UACCUM_EPSILON Layout.example Layout.example_valid),
      Format.decode (ULACCUM_EPSILON Layout.example Layout.example_valid)] =
      [1 / 128, 1 / 32768, 1 / 2147483648, 1 / 256, 1 / 65536, 1 / 4294967296, 1 / 128, 1 / 32768,
        1 / 2147483648, 1 / 256, 1 / 65536, 1 / 4294967296] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.2: the associated integer types `int_*_t`
    and `uint_*_t` with no excess width, at
the example layout. -/
theorem integer :
    [int_hr_t Layout.example 0, int_r_t Layout.example 0, int_lr_t Layout.example 0,
      uint_uhr_t Layout.example 0, uint_ur_t Layout.example 0, uint_ulr_t Layout.example 0,
      int_hk_t Layout.example 0, int_k_t Layout.example 0, int_lk_t Layout.example 0,
      uint_uhk_t Layout.example 0, uint_uk_t Layout.example 0, uint_ulk_t Layout.example 0] =
      [.signed 8, .signed 16, .signed 32, .unsigned 8, .unsigned 16, .unsigned 32, .signed 16,
        .signed 24, .signed 40, .unsigned 16, .unsigned 24, .unsigned 40] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.2: each `abs` spelling saturates the
    least value to the greatest, at the example
layout. -/
theorem abs :
    [Format.decode (abshr Layout.example (SFRACT_MIN Layout.example)),
      Format.decode (absr Layout.example (FRACT_MIN Layout.example)),
      Format.decode (abslr Layout.example (LFRACT_MIN Layout.example)),
      Format.decode (abshk Layout.example (SACCUM_MIN Layout.example)),
      Format.decode (absk Layout.example (ACCUM_MIN Layout.example)),
      Format.decode (abslk Layout.example (LACCUM_MIN Layout.example))] =
      [127 / 128, 32767 / 32768, 2147483647 / 2147483648, 32767 / 128, 8388607 / 32768,
        549755813887 / 2147483648] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.5: each `bits` spelling returns the
    coefficient of the greatest code, at the
example layout. -/
theorem bits :
    [bitshr Layout.example (SFRACT_MAX Layout.example),
      bitsr Layout.example (FRACT_MAX Layout.example),
      bitslr Layout.example (LFRACT_MAX Layout.example),
      bitsuhr Layout.example (USFRACT_MAX Layout.example),
      bitsur Layout.example (UFRACT_MAX Layout.example),
      bitsulr Layout.example (ULFRACT_MAX Layout.example),
      bitshk Layout.example (SACCUM_MAX Layout.example),
      bitsk Layout.example (ACCUM_MAX Layout.example),
      bitslk Layout.example (LACCUM_MAX Layout.example),
      bitsuhk Layout.example (USACCUM_MAX Layout.example),
      bitsuk Layout.example (UACCUM_MAX Layout.example),
      bitsulk Layout.example (ULACCUM_MAX Layout.example)] =
      [127, 32767, 2147483647, 255, 65535, 4294967295, 32767, 8388607, 549755813887, 65535,
        16777215, 1099511627775] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.6: each `*bits` spelling maps the
    coefficient one to the least positive value,
at the example layout. -/
theorem ofBits :
    [(hrbits Layout.example 1).map Format.decode, (rbits Layout.example 1).map Format.decode,
      (lrbits Layout.example 1).map Format.decode, (uhrbits Layout.example 1).map Format.decode,
      (urbits Layout.example 1).map Format.decode, (ulrbits Layout.example 1).map Format.decode,
      (hkbits Layout.example 1).map Format.decode, (kbits Layout.example 1).map Format.decode,
      (lkbits Layout.example 1).map Format.decode, (uhkbits Layout.example 1).map Format.decode,
      (ukbits Layout.example 1).map Format.decode, (ulkbits Layout.example 1).map Format.decode] =
      [some (1 / 128), some (1 / 32768), some (1 / 2147483648), some (1 / 256), some (1 / 65536),
        some (1 / 4294967296), some (1 / 128), some (1 / 32768), some (1 / 2147483648),
        some (1 / 256), some (1 / 65536), some (1 / 4294967296)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.4: each `countls` spelling at the least
    positive value, at the example layout.
-/
theorem countls :
    [countlshr Layout.example (SFRACT_EPSILON Layout.example Layout.example_valid),
      countlsr Layout.example (FRACT_EPSILON Layout.example Layout.example_valid),
      countlslr Layout.example (LFRACT_EPSILON Layout.example Layout.example_valid),
      countlsuhr Layout.example (USFRACT_EPSILON Layout.example Layout.example_valid),
      countlsur Layout.example (UFRACT_EPSILON Layout.example Layout.example_valid),
      countlsulr Layout.example (ULFRACT_EPSILON Layout.example Layout.example_valid),
      countlshk Layout.example (SACCUM_EPSILON Layout.example Layout.example_valid),
      countlsk Layout.example (ACCUM_EPSILON Layout.example Layout.example_valid),
      countlslk Layout.example (LACCUM_EPSILON Layout.example Layout.example_valid),
      countlsuhk Layout.example (USACCUM_EPSILON Layout.example Layout.example_valid),
      countlsuk Layout.example (UACCUM_EPSILON Layout.example Layout.example_valid),
      countlsulk Layout.example (ULACCUM_EPSILON Layout.example Layout.example_valid)] =
      [6, 14, 30, 7, 15, 31, 14, 22, 38, 15, 23, 39] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: each `round` spelling to one
    fractional bit, ties to even, at the greatest
value of the example layout: the rounded value saturates. -/
theorem round :
    [(roundhr Layout.example .even (SFRACT_MAX Layout.example) 1).map Format.decode,
      (roundr Layout.example .even (FRACT_MAX Layout.example) 1).map Format.decode,
      (roundlr Layout.example .even (LFRACT_MAX Layout.example) 1).map Format.decode,
      (rounduhr Layout.example .even (USFRACT_MAX Layout.example) 1).map Format.decode,
      (roundur Layout.example .even (UFRACT_MAX Layout.example) 1).map Format.decode,
      (roundulr Layout.example .even (ULFRACT_MAX Layout.example) 1).map Format.decode,
      (roundhk Layout.example .even (SACCUM_MAX Layout.example) 1).map Format.decode,
      (roundk Layout.example .even (ACCUM_MAX Layout.example) 1).map Format.decode,
      (roundlk Layout.example .even (LACCUM_MAX Layout.example) 1).map Format.decode,
      (rounduhk Layout.example .even (USACCUM_MAX Layout.example) 1).map Format.decode,
      (rounduk Layout.example .even (UACCUM_MAX Layout.example) 1).map Format.decode,
      (roundulk Layout.example .even (ULACCUM_MAX Layout.example) 1).map Format.decode] =
      [some (127 / 128), some (32767 / 32768), some (2147483647 / 2147483648), some (255 / 256),
        some (65535 / 65536), some (4294967295 / 4294967296), some (32767 / 128),
        some (8388607 / 32768), some (549755813887 / 2147483648), some (65535 / 256),
        some (16777215 / 65536), some (1099511627775 / 4294967296)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: each `muli` spelling multiplies three
    by the greatest value, truncated toward
zero, at the example layout. -/
theorem muli :
    [mulir Layout.example (.signed 16) 3 (FRACT_MAX Layout.example),
      mulilr Layout.example (.signed 16) 3 (LFRACT_MAX Layout.example),
      muliur Layout.example (.signed 16) 3 (UFRACT_MAX Layout.example),
      muliulr Layout.example (.signed 16) 3 (ULFRACT_MAX Layout.example),
      mulik Layout.example (.signed 16) 3 (ACCUM_MAX Layout.example),
      mulilk Layout.example (.signed 16) 3 (LACCUM_MAX Layout.example),
      muliuk Layout.example (.signed 16) 3 (UACCUM_MAX Layout.example),
      muliulk Layout.example (.signed 16) 3 (ULACCUM_MAX Layout.example)] =
      [some 2, some 2, some 2, some 2, some 767, some 767, some 767, some 767] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: each `divi` spelling divides three by
    the greatest value, truncated toward
zero, at the example layout. -/
theorem divi :
    [divir Layout.example (.signed 16) 3 (FRACT_MAX Layout.example),
      divilr Layout.example (.signed 16) 3 (LFRACT_MAX Layout.example),
      diviur Layout.example (.signed 16) 3 (UFRACT_MAX Layout.example),
      diviulr Layout.example (.signed 16) 3 (ULFRACT_MAX Layout.example),
      divik Layout.example (.signed 16) 3 (ACCUM_MAX Layout.example),
      divilk Layout.example (.signed 16) 3 (LACCUM_MAX Layout.example),
      diviuk Layout.example (.signed 16) 3 (UACCUM_MAX Layout.example),
      diviulk Layout.example (.signed 16) 3 (ULACCUM_MAX Layout.example)] =
      [some 3, some 3, some 3, some 3, some 0, some 0, some 0, some 0] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: each `*divi` spelling rounds one third
    to the named type, ties to even, at
the example layout. -/
theorem fxdivi :
    [(rdivi Layout.example even 1 3).map Format.decode,
      (lrdivi Layout.example even 1 3).map Format.decode,
      (urdivi Layout.example even 1 3).map Format.decode,
      (ulrdivi Layout.example even 1 3).map Format.decode,
      (kdivi Layout.example even 1 3).map Format.decode,
      (lkdivi Layout.example even 1 3).map Format.decode,
      (ukdivi Layout.example even 1 3).map Format.decode,
      (ulkdivi Layout.example even 1 3).map Format.decode] =
      [some (10923 / 32768), some (715827883 / 2147483648), some (21845 / 65536),
        some (1431655765 / 4294967296), some (10923 / 32768), some (715827883 / 2147483648),
        some (21845 / 65536), some (1431655765 / 4294967296)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: each `idiv` spelling divides the
    greatest value by the least positive one
into a signed 16-bit integer, at the example layout: only `fract` has a quotient in range. -/
theorem idiv :
    [
      idivr Layout.example (.signed 16) (FRACT_MAX Layout.example) (FRACT_EPSILON Layout.example
        Layout.example_valid),
      idivlr Layout.example (.signed 16) (LFRACT_MAX Layout.example) (LFRACT_EPSILON Layout.example
        Layout.example_valid),
      idivur Layout.example (.signed 16) (UFRACT_MAX Layout.example) (UFRACT_EPSILON Layout.example
        Layout.example_valid),
      idivulr Layout.example (.signed 16) (ULFRACT_MAX Layout.example) (ULFRACT_EPSILON
        Layout.example Layout.example_valid),
      idivk Layout.example (.signed 16) (ACCUM_MAX Layout.example) (ACCUM_EPSILON Layout.example
        Layout.example_valid),
      idivlk Layout.example (.signed 16) (LACCUM_MAX Layout.example) (LACCUM_EPSILON Layout.example
        Layout.example_valid),
      idivuk Layout.example (.signed 16) (UACCUM_MAX Layout.example) (UACCUM_EPSILON Layout.example
        Layout.example_valid),
      idivulk Layout.example (.signed 16) (ULACCUM_MAX Layout.example) (ULACCUM_EPSILON
        Layout.example Layout.example_valid)] =
      [some 32767, none, none, none, none, none, none, none] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.8: each `strtofx` spelling converts the
    text `0.5` to one half, at the example
layout. -/
theorem strtofx :
    [Format.decode (strtofxhr Layout.example even "0.5").value,
      Format.decode (strtofxr Layout.example even "0.5").value,
      Format.decode (strtofxlr Layout.example even "0.5").value,
      Format.decode (strtofxuhr Layout.example even "0.5").value,
      Format.decode (strtofxur Layout.example even "0.5").value,
      Format.decode (strtofxulr Layout.example even "0.5").value,
      Format.decode (strtofxhk Layout.example even "0.5").value,
      Format.decode (strtofxk Layout.example even "0.5").value,
      Format.decode (strtofxlk Layout.example even "0.5").value,
      Format.decode (strtofxuhk Layout.example even "0.5").value,
      Format.decode (strtofxuk Layout.example even "0.5").value,
      Format.decode (strtofxulk Layout.example even "0.5").value] =
      [1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.8: each `strtofx` spelling consumes the
    three characters of `0.5`, at the
example layout. -/
theorem strtofx_end :
    [(strtofxhr Layout.example even "0.5").endptr, (strtofxr Layout.example even "0.5").endptr,
      (strtofxlr Layout.example even "0.5").endptr, (strtofxuhr Layout.example even "0.5").endptr,
      (strtofxur Layout.example even "0.5").endptr, (strtofxulr Layout.example even "0.5").endptr,
      (strtofxhk Layout.example even "0.5").endptr, (strtofxk Layout.example even "0.5").endptr,
      (strtofxlk Layout.example even "0.5").endptr, (strtofxuhk Layout.example even "0.5").endptr,
      (strtofxuk Layout.example even "0.5").endptr, (strtofxulk Layout.example even "0.5").endptr] =
      [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.3: the six comparisons of the greatest with the
    least positive `short fract`
value of the example layout. -/
theorem compare :
    [Compare.«==» top unit, Compare.«!=» top unit, Compare.«<» top unit, Compare.«<=» top unit,
      Compare.«>» top unit, Compare.«>=» top unit] =
      [false, true, false, false, true, true] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.3: the six comparisons of the integer zero with
    the greatest `short fract` value
of the example layout. -/
theorem compare_integerLeft :
    [IntegerLeft.«==» 0 top, IntegerLeft.«!=» 0 top, IntegerLeft.«<» 0 top, IntegerLeft.«<=» 0 top,
      IntegerLeft.«>» 0 top, IntegerLeft.«>=» 0 top] =
      [false, true, true, true, false, false] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.3: the six comparisons of the greatest `short
    fract` value of the example layout
with the integer zero. -/
theorem compare_integerRight :
    [IntegerRight.«==» top 0, IntegerRight.«!=» top 0, IntegerRight.«<» top 0,
      IntegerRight.«<=» top 0, IntegerRight.«>» top 0, IntegerRight.«>=» top 0] =
      [false, true, false, false, true, true] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: the integer one combined with the least
    positive `short fract` value of the
example layout, saturating, ties to even. -/
theorem integerLeft :
    [(IntegerLeft.«+» even .SAT 1 unit).map Format.decode,
      (IntegerLeft.«-» even .SAT 1 unit).map Format.decode,
      (IntegerLeft.«*» even .SAT 1 unit).map Format.decode,
      (IntegerLeft.«/» even .SAT 1 unit).map Format.decode] =
      [some (127 / 128), some (127 / 128), some (1 / 128), some (127 / 128)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: the least positive `short fract` value
    of the example layout combined with the
integer one, saturating, ties to even. -/
theorem integerRight :
    [(IntegerRight.«+» even .SAT unit 1).map Format.decode,
      (IntegerRight.«-» even .SAT unit 1).map Format.decode,
      (IntegerRight.«*» even .SAT unit 1).map Format.decode,
      (IntegerRight.«/» even .SAT unit 1).map Format.decode] =
      [some (127 / 128), some (-127 / 128), some (1 / 128), some (1 / 128)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: compound assignment to a signed 8-bit integer
    through the saturated `short
fract` intermediate of the example layout. -/
theorem assign_integerLeft :
    [Assignment.IntegerLeft.«+=» (.signed 8) even .SAT 1 unit,
      Assignment.IntegerLeft.«-=» (.signed 8) even .SAT 1 unit,
      Assignment.IntegerLeft.«*=» (.signed 8) even .SAT 1 unit,
      Assignment.IntegerLeft.«/=» (.signed 8) even .SAT 1 unit] =
      [some 0, some 0, some 0, some 0] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: compound assignment to a `short fract` value of
    the example layout with the
integer one on the right. -/
theorem assign_integerRight :
    [(Assignment.IntegerRight.«+=» even .SAT unit 1).map Format.decode,
      (Assignment.IntegerRight.«-=» even .SAT unit 1).map Format.decode,
      (Assignment.IntegerRight.«*=» even .SAT unit 1).map Format.decode,
      (Assignment.IntegerRight.«/=» even .SAT unit 1).map Format.decode] =
      [some (127 / 128), some (-127 / 128), some (1 / 128), some (1 / 128)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1: the prefix increment and decrement of the
    least positive `short fract` value
of the example layout, saturating. -/
theorem prefixUpdate :
    [(Prefix.«++» even .SAT unit).map Format.decode,
      (Prefix.«--» even .SAT unit).map Format.decode] =
      [some (127 / 128), some (-127 / 128)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1: the postfix increment and decrement return the
    old value and the saturated new
one. -/
theorem postfixUpdate :
    [(Postfix.«++» even .SAT unit).map fun p => (Format.decode p.1, Format.decode p.2),
      (Postfix.«--» even .SAT unit).map fun p => (Format.decode p.1, Format.decode p.2)] =
      [some (1 / 128, 127 / 128), some (1 / 128, -127 / 128)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.2: the shifts and the shift assignments by two
    bits on `short fract` values of
the example layout. -/
theorem shift :
    [(Binary.«<<» even .SAT unit 2).map Format.decode,
      (Binary.«>>» even .SAT top 2).map Format.decode,
      (Assignment.«<<=» even .SAT unit 2).map Format.decode,
      (Assignment.«>>=» even .SAT top 2).map Format.decode] =
      [some (1 / 32), some (1 / 4), some (1 / 32), some (1 / 4)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: assigning one third to a `short fract` object of
    the example layout, ties to
even. -/
theorem assign :
    [(Assignment.«=» (Layout.example.format shortFract) even .SAT (1 / 3)).map Format.decode] =
      [some (43 / 128)] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: the four arithmetic operators on the greatest
    and the least positive `short
fract` value of the example layout under the default overflow mode: the sum and the quotient
overflow. -/
theorem binary :
    [(Binary.«+» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Binary.«-» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Binary.«*» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Binary.«/» Layout.example environment shortFract shortFract top unit).map Format.decode] =
      [none, some (63 / 64), some (1 / 128), none] := by
  decide +kernel

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: the four compound assignments on the greatest
    and the least positive `short
fract` value of the example layout under the default overflow mode. -/
theorem compound :
    [(Assignment.«+=» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Assignment.«-=» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Assignment.«*=» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Assignment.«/=» Layout.example environment shortFract shortFract top unit).map
        Format.decode] =
      [none, some (63 / 64), some (1 / 128), none] := by
  decide +kernel

end Examples

end FloatLib.Floats.Formats.FixedPoint.Embedded
