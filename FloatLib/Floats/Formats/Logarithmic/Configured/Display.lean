/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Core
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# Value display of logarithmic formats

A value `±β^e` prints as its exact decimal when that expansion terminates and `|e| ≤ 32`, such
as `8` or `-0.5`, and as the power, such as `2^-80` or `-3^-2`, otherwise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Logarithmic.Code

open FloatLib.Numerics

/-- Text of a logarithmic code: `0`, an exact decimal for `|e| ≤ 32`, or the signed power. -/
def display {radix : Radix} : Code radix → String
  | .zero => "0"
  | .value negative exponent =>
      let power := s!"{radix.base}^{exponent}"
      match (if exponent.natAbs ≤ 32 then DecimalText.ofRat? (Code.value negative exponent :
          Code radix).toRat else none) with
      | some exact => String.ofList exact.trimTrailingZeros.fixedCharacters
      | none => if negative then "-" ++ power else power

end FloatLib.Floats.Formats.Logarithmic.Code

namespace FloatLib.Floats.ExecFloat.Logarithmic

/-- Logarithmic values print their exact value. -/
instance (radix : FloatLib.Numerics.Radix) : FormatDisplay (Family radix) where
  format code := Formats.Logarithmic.Code.display code

end FloatLib.Floats.ExecFloat.Logarithmic
