/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.Block
public import FloatLib.Floats.Formats.Block.Configured
public import FloatLib.Floats.Formats.Block.Catalog
public import FloatLib.Floats.Formats.Block.CodedDot
public import FloatLib.Kernels.Block.Maximum
public import FloatLib.Floats.Formats.Block.Stored
public import FloatLib.Floats.Formats.Block.Working
public import FloatLib.Floats.Formats.Block.Working.KernelPath

/-!
# Block-scaled numerical formats

In a block-scaled format a group of narrow elements shares a scale, and groups of blocks may share
outer scales. One theory covers every such format:

* `Block.Rounding`, `Block.Format`, `Block.Policy`, `Block.Bounds`, `Block.Transpose`, `Block.Dot`:
  the value theory over any ordered field, with error budgets, flush to zero, scale selection,
  transposition, exact block dot products and ordered accumulation;
* `Block.Binary`: every binary descriptor and fixed-point grid as a rounding map over the reals;
* `Block.Catalog`: OCP MX, NVFP4, Four Over Six and the fixed-point combine format as instances;
* `Block.Coded`, `Block.Codecs`, `Block.CodedDot`, `Block.Configured`: stored tensors over the
  rationals for any element and scale codec, their exact decoding and dot products, and the
  common executable carrier;
* `Block.Stored`: the stored formats and policies of OCP MX variants, NVFP4 and Four Over Six;
* `Block.Working`: quantizers that compute the scaled input in a working arithmetic (binary32
  for the reference implementations): their error budget and their agreement with the exact
  quantizer, for every block-scaled format, with NVFP4 as the instance;
* `Block.Working.Binary`, `Block.Working.KernelPath`: the quantizer on the encodings of a binary
  working format in the order of torchao's `nvfp4_quantize`, what it stores when an operation
  overflows and when none does, and its kernel rules. `Block.nvfp4Working` is NVFP4 in binary32.

Kernel-checked instances on explicit data are in the test module
`FloatLibTests.Conformance.Formats.BlockExamples`.

`Block.Roundoff` registers the error budgets with the `roundoff` commands. It is a named import,
as `FloatLib.Tactic.Roundoff` is.

## References

* Open Compute Project, *OCP Microscaling Formats (MX) Specification, Version 1.0*,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
* NVIDIA, *Pretraining Large Language Models with NVFP4*, arXiv:2509.25149.
* J. Cook et al., *Four Over Six: More Accurate NVFP4 Quantization with Adaptive Block Scaling*,
  arXiv:2512.02010.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.1–5.4 and 6.1–6.3.
-/

@[expose] public section
