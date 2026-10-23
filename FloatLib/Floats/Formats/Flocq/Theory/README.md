# Rounded-real theory (`Flocq/Theory`)

This is where we develop rounded arithmetic over `ℝ`: radix powers, FIX/FLX/FLT and
abrupt-underflow formats, rounding modes, ULPs, error bounds, and Sterbenz's lemma for exact
subtraction. None of it depends on a bit encoding or an executable kernel.

We develop the theory in Lean following Flocq's organization, but leave out its specialized
algorithm proofs and Coq application modules. Finite-result bridge theorems in
`Formats/BinaryInterchange/` connect it to executable binary arithmetic, and
`Flocq/Calculation/` builds brackets and truncation on top of it.

Its main definitions are `bpow`, `genericFormat`, `ulp`, and `round`. Import individual modules
to keep dependencies small, or `FloatLib.Floats.Formats.Flocq.Theory` for the full theory.

| Mathematical role | Definitions |
| --- | --- |
| Parametric rounding model on `ℝ` | `FloatRep` / `NF` |
| Executable bits + special values | `ExecFloat.Binary` |
| Finite real meaning of those bits | `Model.toReal`, `Model.roundAt fmt` |
| Host / accelerator result | separately stated conformance, not this layer |

The raw `NF` constructor accepts off-grid comparison values, and `NF.ofReal` rounds onto the
grid. When a theorem needs its input on the grid, it says so with an `NF.IsRepresentable`
hypothesis. Affine quantization over exact rationals lives elsewhere, in
`FloatLib.Numerics.Quantization`. Here, `FloatRep` supplies the real-valued rounding model.
