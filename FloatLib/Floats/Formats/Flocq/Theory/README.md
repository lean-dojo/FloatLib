# Rounded-real theory (`Flocq/Theory`)

Here we develop rounded arithmetic over `ℝ`: radix powers, FIX/FLX/FLT and abrupt-underflow
formats, rounding modes, ULPs, error bounds, and Sterbenz's lemma for exact subtraction.
The theory is independent of any bit encoding or executable kernel.

We follow Flocq's organization while developing the theory in Lean. The scope here excludes
its specialized algorithm proofs and Coq application modules. We connect the theory to
executable binary arithmetic in `Formats/BinaryInterchange/` through finite-result bridge theorems.
`Flocq/Calculation/` builds on this theory with brackets and truncation.

The main definitions are `bpow`, `genericFormat`, `ulp`, and `round`. Individual module imports
keep dependencies small; `FloatLib.Floats.Formats.Flocq.Theory` brings in the full theory.

| Mathematical role | Definitions |
| --- | --- |
| Parametric rounding model on `ℝ` | `FloatRep` / `NF` |
| Executable bits + special values | `ExecFloat.Binary` |
| Finite real meaning of those bits | `Model.toReal`, `Model.roundAt fmt` |
| Host / accelerator result | separately stated conformance, not this layer |

The raw `NF` constructor admits off-grid comparison values, while `NF.ofReal` rounds onto the
grid. We state `NF.IsRepresentable` explicitly when a theorem needs an input on that grid.
Affine quantization over exact rationals lives separately in `FloatLib.Numerics.Quantization`;
`FloatRep` supplies the real-valued rounding model.
