/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# CSV output helpers

Small, stable renderers shared by benchmark executables. These functions deliberately avoid
locale-dependent or implementation-specific formatting so generated result files remain easy to
compare across runs.
-/

@[expose] public section

namespace FloatLibBenchmarks.Support.CSV

/-- Render a Boolean as the conventional lowercase CSV field. -/
def bool (value : Bool) : String :=
  if value then "true" else "false"

end FloatLibBenchmarks.Support.CSV
