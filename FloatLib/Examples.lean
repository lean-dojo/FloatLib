/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Examples.BasicOperations
public import FloatLib.Examples.CustomFormats
public import FloatLib.Examples.FormatComparison
public import FloatLib.Examples.PositQuire
public import FloatLib.Examples.SpecializedFormats
public import FloatLib.Examples.Transcendentals

/-!
# FloatLib examples

Each example starts from a concrete question, shows the code, and records selected `#eval` results
in comments. Start with `BasicOperations`, which asks what `0.1 + 0.2` gives
in binary32 and how to prove something about it. The other modules can be read independently:

* `CustomFormats` builds a custom 16-bit binary layout, a 12-bit posit, a decimal fixed-point
  grid, and a P3109 type, and checks which calculations are exact in each.
* `FormatComparison` evaluates one expression as native `Float`, `Float32`, FloatLib binary64
  and binary32, and Posit32, then rounds one third in all four IEEE directions.
* `PositQuire` computes a dot product in a quire, with no rounding until the end, and proves when
  that accumulation is exact.
* `SpecializedFormats` multiplies logarithmic numbers, looks up a codebook product, and quantizes
  shared-scale and OCP MX blocks.
* `Transcendentals` computes `sin`, `cos`, and a composition of `exp`, `log`, and `tanh`.
  The example file imports `Configured.Transcendentals`; those functions are not installed by
  `import FloatLib`. It states what is and is not promised about accuracy.

To try a sample in the editor, start a scratch file with `import FloatLib`. For the
`Transcendentals` example, also import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`. Copy the namespace
openings, type aliases, and definitions you need, then add `#eval` followed by the value's name.
Binary values and posits print their exact stored value;
`toString`, string interpolation, and `IO.println` use the same display API.

From the repository root, build all examples with `lake build FloatLib.Examples`, or run the
comparison with `lake -d tests exe check example`. Copy the examples into an application and
change the inputs or format parameters to explore their behavior. Sample values are private;
the reusable functions, including `PositQuire.dotProduct`, are public.
-/
