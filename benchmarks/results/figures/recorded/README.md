# Recorded numbers of the figures

The timing mode of `benchmarks/plots/figures.py` measures the checkout it runs in. These files
hold what it does not measure. Each row names the toolchain and the day it was measured. All of
it was measured on the machine of the other results (Intel Xeon Platinum 8275CL, 96 threads,
shared with other jobs).

| file | what it holds | where it comes from |
| --- | --- | --- |
| `coq-flocq.csv` | Five loops per binary format in Coq 8.20.1 with Flocq 4.2.2 (`BinarySingleNaN`, `mode_NE`), under `vm_compute` and under `lazy`, microseconds per operation; an empty cell is no result within 300 seconds and 8 GB. | `benchmarks/suite/run.sh matched flocq` on 2026-11-15, image `leanfloat-flocq-bench:4.2.2`, one container at a time with 8 GB and two CPUs. Coq printed the value Lean computed in every row (`values`). |
| `coq-loops.csv` | Three theorems about loops of 1,000 steps in Coq: kernel conversion at `Qed`, and `vm_compute`. | `benchmarks/kernel/FlocqConversion.v`, the `Time Qed` lines, 2026-11-15, same container. |
| `complex-times.csv` | Compiled time per call of the 18 complex functions at seven formats, milliseconds. | The complex functions' result table of 2026-11-16 (Lean 4.35.0): the average over each run of `tests/oracles/complex_mpc.py`, whose arguments differ from run to run, timed in Python around the compiled oracle. |
| `interval-corpora.csv` | One row per goal and engine: 169 goals from the tests of FloatLib's `interval`, Mathlib's `dyadic_interval`, SymLean's `cega` and the IEANTN floors; whether one tactic call closed the goal with the three standard axioms only, and the wall seconds of its file, imports included. | The comparison of 2026-11-16, Lean 4.35.0. The goal files are other projects' tests and are not in this repository. |

The Coq files of the exact-arithmetic suite are `../../exact/coq.log` and `coq.md`
(`benchmarks/exact/run.sh coq`, 2026-11-15).
