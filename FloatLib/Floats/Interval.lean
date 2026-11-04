/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Interval
public import FloatLib.Floats.Interval.Quantized
public import FloatLib.Floats.Interval.RealBounds
public import FloatLib.Floats.Interval.Rounders

/-!
# Interval arithmetic

FloatLib has several executable interval interfaces, and they share outward rounding and real
containment proofs:

- `Numerics.Interval α` pairs endpoints in any representation. Its operations use a supplied
  `Numerics.OutwardRounding`, and the binary, decimal, and posit adapters provide rational decoders
  and checked endpoint rounding. Successful results enclose arbitrary real values between the
  inputs, through the theorems in `Numerics.Enclosure.Interval.Real`.
- `BinaryInterchange.Model.Interval fmt` and `ExecFloat.Binary.Interval` provide directed binary
  arithmetic. Their IEEE arithmetic theorems accept finite input bounds and allow infinite output
  bounds after overflow. Finite-only formats come with range premises.
- `Numerics.RationalInterval` holds the exact rational bounds used by the elementary function
  kernels.

If you are proving things over `ℝ` and don't need to execute them, `Floats.Interval.Quantized`
supplies noncomputable intervals whose endpoints lie on a Flocq-style rounding grid. Concrete
endpoint adapters are in each format's `Interval` module, and the optional Arb comparison adapter is
in `FloatLibTests.Arb.ModelTranscendentals`.

## References

- S. M. Rump, [Verification methods: Rigorous results using floating-point
  arithmetic](https://doi.org/10.1017/S096249291000005X), *Acta Numerica* 19 (2010), §§5.1-5.5:
  endpoint arithmetic, outward rounding, and containment under composition.
- S. Boldo and G. Melquiond, [Flocq: A Unified Library for Proving Floating-Point Algorithms in
  Coq](https://doi.org/10.1109/ARITH.2011.40), ARITH 2011: the rounded-real grids used by the
  proof-side interval interface.
-/

@[expose] public section
