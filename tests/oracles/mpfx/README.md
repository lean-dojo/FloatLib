# FloatLib against MPFX

MPFX is the C++ library from Saiki, Zorn, Richey, and Tatlock's "When Double Rounding is Correct"
(arXiv:2610.09005). It computes a round-to-odd result in a `double` or `float` container, using
either hardware arithmetic (`hw`) or error-free transformations (`eft`), and then rounds that
result again to the target format. The scripts in this directory compare it with FloatLib, which
gives the exact result and all five IEEE flags.

- `run.sh` checks one format, operation, and operand set in the four rounding directions required
  for binary formats.
- `operands.py` writes the operand sets, `mpfx_list.cpp` compares MPFX with FloatLib's results,
  and `classify.py` groups sign and flag differences. It keeps unexplained EFT differences apart
  from any claim about their cause.
- `repro.cpp` reproduces each bug against MPFR, SoftFloat, and the host FPU alone.

You need a C++20 compiler that accepts `static_assert(false)` in discarded template branches (CWG
2518), because we include MPFX as is, with its compile-time assertions intact.

Give `tests/oracles/exhaustive16.sh` the `--mpfx-dir` option and the exhaustive binary16 and
bfloat16 campaign compares MPFX on every operand pair as well.

```bash
work=$(mktemp -d)
bash tests/oracles/mpfx/run.sh --mpfx-dir /path/to/mpfx --work "$work" 11 50 sqrt tiny 200000
python3 -I tests/oracles/mpfx/classify.py "$work"
```

At MPFX commit `b2d27a2`, standalone examples reproduce four problems, which we reported upstream
as [bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36):

1. An exact zero sum, difference, or FMA result under roundTowardNegative comes out as `+0`, where
   IEEE 754 §6.3 requires `-0`.
2. `sqrt(-inf)` raises no invalid flag.
3. When the container's own result overflows, as for bfloat16 in `float`, the overflow flag is
   lost.
4. The `eft` engine reads the sign of the rounding error from an FMA remainder. Where that
   remainder underflows the container, the result is treated as exact, so it's misrounded in the
   directed modes and at nearest-even ties and loses its inexact and underflow flags. This covers
   square root and the `float` container, bfloat16 included.

You'll find the counts in `tests/results/differential/`.
