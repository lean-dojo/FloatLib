/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.PackedRow

/-!
# Packed row command rejection tests

Signed and unsigned literals must fit the requested lane width.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Packed

open FloatLib.Numerics.Packed

/-- error: entry 1 is 128, which does not fit a signed lane of width 8 -/
#guard_msgs (error) in
packed_row tooWide (width := 8) := [1, 128]

/-- error: entry 0 is -1, which does not fit an unsigned lane of width 8 -/
#guard_msgs (error) in
packed_row negative (width := 8) (signed := false) := [-1]

/-- error: entry 0 is 256, which does not fit an unsigned lane of width 8 -/
#guard_msgs (error) in
packed_row tooWideUnsigned (width := 8) (signed := false) := [256]

/-! Rows files hold plain decimal integers. Digit separators, signs other than a leading `-`, and
other characters are errors, also in tokens long enough to be read in blocks. -/

#guard (parseEntries "12, -3  # comment\n7").toOption == some #[12, -3, 7]
#guard (parseEntries "123456789012345678901234567890 -42").toOption ==
  some #[123456789012345678901234567890, -42]
#guard (parseEntries "1_000").toOption == none
#guard (parseEntries "10000000000000_0000000000").toOption == none
#guard (parseEntries "+5").toOption == none
#guard (parseEntries "éééééééééé").toOption == none

end FloatLibTests.Conformance.Numerics.Packed
