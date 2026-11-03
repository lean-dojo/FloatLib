/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# `#float_info` without a family report

This module imports the generic inspection commands and the configured binary types, but not the
binary family's report. `#float_info` must then name the module to import, for an `ExecFloat` type
and for the proof model alike, and must say what it reports on for a type that is neither.
-/

open FloatLib.Floats

/--
error: no `#float_info` report is imported for Binary32; add `import FloatLib.Floats.Formats.BinaryInterchange` or `import FloatLib`
-/
#guard_msgs in
#float_info Binary32

/--
error: no `#float_info` report is imported for Formats.BinaryInterchange.Model Formats.BinaryInterchange.FloatFormat.binary32; add `import FloatLib.Floats.Formats.BinaryInterchange` or `import FloatLib`
-/
#guard_msgs in
#float_info Formats.BinaryInterchange.Model Formats.BinaryInterchange.FloatFormat.binary32

/--
error: `#float_info` has no report for Nat. It reports FloatLib's numerical types
-/
#guard_msgs (substring := true) in
#float_info Nat
