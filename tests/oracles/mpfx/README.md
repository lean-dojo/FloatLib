# FloatLib against MPFX

MPFX is the C++ library of Saiki, Zorn, Richey, and Tatlock, "When Double Rounding is Correct"
(arXiv:2610.09005). It computes a round-to-odd result in a `double` or `float` container, with
hardware arithmetic (`hw`) or error-free transformations (`eft`), and rounds that result again to
the target format. These tools compare it with FloatLib, which supplies the exact result and all
five IEEE flags.

- `run.sh` checks one format, operation, and operand set in the four IEEE directions.
- `operands.py` writes the operand sets, `mpfx_list.cpp` compares MPFX with FloatLib's results,
  and `classify.py` groups sign and flag differences while keeping unexplained EFT differences
  separate from claims about their cause.
- `repro.cpp` reproduces each bug against MPFR, SoftFloat, and the host FPU alone.

Use a C++20 compiler that supports `static_assert(false)` in discarded template branches
(CWG 2518). MPFX is included directly with its compile-time assertions intact.

The exhaustive binary16 and bfloat16 campaign also compares MPFX on every operand pair when
`tests/oracles/exhaustive16.sh` is given `--mpfx-dir`.

```bash
work=$(mktemp -d)
bash tests/oracles/mpfx/run.sh --mpfx-dir /path/to/mpfx --work "$work" 11 50 sqrt tiny 200000
python3 -I tests/oracles/mpfx/classify.py "$work"
```

At MPFX commit `b2d27a2`, standalone examples reproduce four problems, reported upstream as
[bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36):

1. An exact zero sum, difference, or FMA result under roundTowardNegative is `+0`; IEEE 754 §6.3
   requires `-0`.
2. `sqrt(-inf)` raises no invalid flag.
3. When the container's own result overflows, as for bfloat16 in `float`, the overflow flag is
   lost.
4. The `eft` engine reads the sign of the rounding error from an FMA remainder; where that
   remainder underflows the container, the result is treated as exact, misrounded in the directed
   modes and at nearest-even ties, and its inexact and underflow flags are dropped. This covers
   square root and the `float` container, including bfloat16.

The counts are in `tests/results/differential/`.
