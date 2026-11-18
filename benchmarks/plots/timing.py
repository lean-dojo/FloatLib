"""The timing mode of `figures.py`: every time measurement of the figures, on this checkout.

`measure(raw, jobs, threads, only)` runs the benchmark runners that already live under
`benchmarks/` (they do the measuring: `Lean.Kernel.whnf`, Lean's profiler, `IO.monoNanosNow`,
`/usr/bin/time`), at most `jobs` at a time, and writes their logs under `raw`, outside the
checkout. Nothing is measured in Python. `figures.py` then turns the logs into the CSV files of
the figures.

The runners call Lake through `tests/lib/lake.sh`, which holds one build lock per build
directory for as long as a command runs, so two measurements would wait for each other. The
timing mode therefore builds what the measurements need once, with the real Lake, reads the
environment of `lake env` once, and then hands the runners a stand-in for `lake` that only
starts the command in that environment (`LAKE`, a documented knob of `lake.sh`), each runner
with its own name for the build directory (`FLOATLIB_BUILD_DIR`, a symbolic link), hence with
its own lock. Nothing is built while a measurement runs.
"""
from __future__ import annotations

import os
import shlex
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# The executables that the compiled measurements start. Lake links them before the first
# measurement; a missing one fails its own section only.
EXECUTABLES = ["execFloatSweep", "execFloatFP8Bench", "execFloatPositBench",
               "execFloatFormatComparison", "execFloatPositVectors", "execFloatSelectionMatrix",
               "execFloatIEEE2019", "exactCompiled"]

SHIM = r'''#!/usr/bin/env bash
# Stand-in for `lake` while the figures are measured (written by benchmarks/plots/timing.py).
# The environment of `lake env` was read once and everything was built before, so `env` and
# `exe` only start their command and `build` only checks that its target exists.
while [[ "${1:-}" == -R || "${1:-}" == -K* ]]; do shift; done
command="${1:?lake command}"; shift
# shellcheck disable=SC1090
source "$FIGURES_LAKE_ENV"
case "$command" in
  env) exec "$@" ;;
  exe) name="$1"; shift; exec "$FIGURES_BUILD/bin/$name" "$@" ;;
  build)
    for target in "$@"; do
      [[ -e "$FIGURES_BUILD/bin/$target" ]] ||
        { echo "lake stand-in: $target was not built before the measurement" >&2; exit 1; }
    done ;;
  *) echo "lake stand-in: no command $command" >&2; exit 2 ;;
esac
'''

FUNCTIONS = r"""
source tests/lib/lake.sh
exe="$(floatlib_build_path bin/execFloatIEEE2019)"
: > @LOG@
for format in e4f3 binary16 binary32 binary64 binary128; do
  timeout 600 "$exe" functions "$format" 8 >> @LOG@ 2>&1 || echo "FAILED $format" >> @LOG@
done
timeout 900 "$exe" functions binary256 2 >> @LOG@ 2>&1 || echo "FAILED binary256" >> @LOG@
names="$(grep '^binary,binary16,' @LOG@ | cut -d, -f4)"
for format in binary1024 binary4096; do
  printf '%s\n' $names | xargs -P 4 -I{} bash -c \
    'timeout "${FIGURES_FUNCTION_TIMEOUT:-120}" "$1" functions "$2" 1 "$3" 2>&1 || echo "NORESULT $2 $3"' \
    _ "$exe" "$format" {} >> @LOG@
done
grep -c '^binary,' @LOG@
"""

# The order in which sections start. The short kernel sections go first, while the machine is
# still quiet: their cells are differences of a few microseconds. The long sections queue
# behind them, the longest first, so that a run takes about as long as its longest section.
START_ORDER = ["kernel-binary", "kernel-public", "kernel-spec", "kernel-public-64", "kernel-spec-64",
               "kernel-64", "matched", "families", "blocks", "extras", "loops", "exhaustive",
               "exact-native", "compiled-comparison", "ieee2019-wide", "ieee2019", "functions",
               "compiled", "ieee2019-compiled", "exact", "exact-compiled"]
BINARY_FORMATS = ("e4m3 e5m2 binary16 bfloat16 e8f15 binary32 binary64 e15f64 binary128 binary256 "
                  "binary512 binary1024 binary4096")
IEEE_FORMATS = "e4f3 binary16 binary32 binary64 binary128 binary256 decimal32 decimal64 decimal128"


def sections(raw: Path) -> list:
    """(name, seconds allowed, shell command run from the repository root)."""
    q = shlex.quote
    suite, kernel, exact = q(str(raw / "suite")), q(str(raw / "kernel")), q(str(raw / "exact"))
    ieee, wide = q(str(raw / "ieee2019")), q(str(raw / "ieee2019-wide"))
    return [
        # Kernel time per operation, binary formats of 8 to 4,096 bits, as `float_decide`
        # rewrites the operation.
        ("kernel-binary", 2400,
         f"SUITE_FORMATS='{BINARY_FORMATS}' benchmarks/suite/run.sh {suite} kernel-binary"),
        # The same cells as written: the public operations (and the reference operations of the
        # two one-byte formats, whose public operations are table lookups).
        ("kernel-public", 2400,
         f"KERNEL_BENCH_OUT={kernel} benchmarks/kernel/run.sh public 8 3 "
         "binary16 bfloat16 binary32 binary64 binary128"),
        ("kernel-spec", 1200, f"KERNEL_BENCH_OUT={kernel} benchmarks/kernel/run.sh spec 8 3 e4m3 e5m2"),
        # The same three runs with 64 triples per cell and the kernel's conversions on both sides,
        # so that a cell is the operation alone (the second table of results/kernel/README.md).
        ("kernel-public-64", 2400,
         f"KERNEL_BENCH_CONVERSIONS=kernel KERNEL_BENCH_OUT={kernel}/triples64 benchmarks/kernel/run.sh "
         "public 64 2 binary16 bfloat16 binary32 binary64 binary128"),
        ("kernel-spec-64", 1200,
         f"KERNEL_BENCH_CONVERSIONS=kernel KERNEL_BENCH_OUT={kernel}/triples64 benchmarks/kernel/run.sh "
         "spec 64 2 e4m3 e5m2"),
        ("kernel-64", 1200, f"KERNEL_BENCH_OUT={kernel}/triples64 benchmarks/kernel/run.sh kernel 64 5"),
        # IEEE 754-2019 clauses 5 and 9 under the standard's names, binary and decimal.
        ("ieee2019", 3000, f"KERNEL_BENCH_OUT={ieee} benchmarks/kernel/ieee2019.sh 4 3 {IEEE_FORMATS}"),
        # At 1,024 and 4,096 bits every row runs in its own Lean process with a limit of 60
        # seconds, eight at a time: a row that needs longer has no value (`n/a`).
        ("ieee2019-wide", 3000,
         f"KERNEL_BENCH_OUT={wide} KERNEL_BENCH_ROW_TIMEOUT=${{FIGURES_ROW_TIMEOUT:-60}} "
         "KERNEL_BENCH_JOBS=${FIGURES_ROW_JOBS:-8} benchmarks/kernel/ieee2019.sh 4 3 binary1024 binary4096"),
        # Status flags, comparisons, conversions, casts and literals in binary32 and binary64.
        ("extras", 2400, f"KERNEL_BENCH_OUT={kernel} benchmarks/kernel/extras.sh 64 5"),
        # Three theorems about loops of 1,000 steps, both ways.
        ("loops", 1800, f"mkdir -p {kernel} && benchmarks/kernel/loops.sh 3 > {kernel}/loops.log 2>&1"),
        # The loops that Coq with Flocq also runs, the other families, all pairs.
        ("matched", 1800, f"benchmarks/suite/run.sh {suite} matched"),
        ("families", 1800, f"benchmarks/suite/run.sh {suite} families"),
        ("exhaustive", 2400, f"benchmarks/suite/run.sh {suite} exhaustive"),
        ("blocks", 1800,
         f"mkdir -p {kernel} && source tests/lib/lake.sh && "
         f"floatlib_lake env timeout --kill-after=10 1500 lean benchmarks/kernel/MX.lean > {kernel}/mx.log 2>&1; "
         f"floatlib_lake env timeout --kill-after=10 1500 lean benchmarks/kernel/NVFP4.lean > {kernel}/nvfp4.log 2>&1; true"),
        # Exact kernel arithmetic: operations, other projects' checks, FloatLib's own exact layer
        # and `interval` at this checkout; `decide +kernel` against `native_decide` (its last
        # statement is one that `native_decide` refuses, so Lean exits with an error and the
        # log is what counts); compiled code and load time.
        ("exact", 2400,
         f"EXACT_BENCH_OUT={exact} EXACT_BENCH_RUNS=3 benchmarks/exact/run.sh "
         "operations workloads baseline tactic"),
        ("exact-native", 1800,
         f"EXACT_BENCH_OUT={exact} EXACT_BENCH_RUNS=3 benchmarks/exact/run.sh native > {exact}-native.out 2>&1; "
         f"test -s {exact}/native.log"),
        ("exact-compiled", 1800, f"EXACT_BENCH_OUT={exact} benchmarks/exact/run.sh compiled load"),
        # Compiled code: the precision sweep, FP8 and posits; and, as a section of its own
        # because it takes the longest, FloatLib next to MPFR, Berkeley SoftFloat and the host FPU
        # (one development trial, as `benchmarks/suite/run.sh compiled` starts it).
        ("compiled", 3000, f"SUITE_COMPARISON=0 benchmarks/suite/run.sh {suite} compiled"),
        ("compiled-comparison", 3300,
         f"mkdir -p {suite}/compiled && rm -rf {suite}/compiled/comparison && "
         "FORMAT_COMPARE_DEVELOPMENT_ONLY=1 FORMAT_COMPARE_INCLUDE_UNIVERSAL=0 FORMAT_COMPARE_INCLUDE_PYTHON=0 "
         f"benchmarks/scripts/format-comparison.sh 1 {suite}/compiled/comparison "
         f"> {suite}/compiled/comparison.log 2>&1"),
        # Compiled time of the IEEE 754-2019 operations, and of the recommended functions of
        # clause 9.2 format by format: eight operands up to 128 bits, two at 256 bits, and one
        # at 1,024 and 4,096 bits, where each function runs alone with a limit of 120 seconds.
        ("ieee2019-compiled", 2400,
         f"mkdir -p {ieee} && source tests/lib/lake.sh && "
         f"floatlib_benchmark_lake exe execFloatIEEE2019 > {ieee}/compiled.log 2>&1"),
        ("functions", 3000, f"mkdir -p {ieee} && " + FUNCTIONS.replace("@LOG@", f"{ieee}/functions.log")),
    ]


def shell(command: str, *, env: dict, log: Path, seconds: int, cwd: Path = ROOT) -> tuple:
    """Exit code and wall seconds of one command; its own process group is killed on timeout."""
    start = time.monotonic()
    with log.open("w") as stream:
        process = subprocess.Popen(["bash", "-c", command], cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, 15)
            try:
                process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, 9)
                process.wait()
            code = 124
    return code, time.monotonic() - start


def build_directory() -> Path:
    """The build directory of this checkout: `FLOATLIB_BUILD_DIR`, or `.lake/build` here."""
    chosen = os.environ.get("FLOATLIB_BUILD_DIR") or str(ROOT / ".lake/build")
    path = Path(chosen).resolve()
    if not (path / "lib").is_dir():
        raise SystemExit(f"no built library under {path}: build FloatLib first "
                         "(the timing mode builds only its own executables, incrementally)")
    return path


PREPARE = r"""
# One hold of the build lock for the build and for reading the environment of `lake env`.
source tests/lib/lake.sh
floatlib_acquire_build_lock
trap floatlib_release_build_lock EXIT
cd benchmarks
lake() { command "${LAKE:-lake}" -R -KbuildDir="$FLOATLIB_BUILD_DIR" "$@"; }
status=0
if ! lake build $FIGURES_EXECUTABLES > "$FIGURES_TOOLS/build.log" 2>&1; then
  # One target that fails stops Lake, so the others are built one by one.
  for target in $FIGURES_EXECUTABLES; do
    lake build "$target" > "$FIGURES_TOOLS/build-$target.log" 2>&1 || { echo "not built: $target"; status=1; }
  done
fi
lake env env -0 > "$FIGURES_TOOLS/lake-env.bin"
exit "$status"
"""


def prepare(raw: Path, build: Path, reuse: bool, log) -> dict:
    """Link the executables and read the environment of `lake env`, with the real Lake.

    With `reuse`, an earlier run in `raw` did both and nothing is built or read again.
    """
    tools = raw / "tools"
    tools.mkdir(parents=True, exist_ok=True)
    (raw / "tmp").mkdir(exist_ok=True)
    base = {**os.environ, "FLOATLIB_BUILD_DIR": str(build), "TMPDIR": str(raw / "tmp")}
    base.pop("FLOATLIB_LAKE_CONFIGURED_FOR", None)
    base.pop("LAKE", None)
    if reuse and (tools / "lake-env.sh").exists():
        log("reusing the executables and the Lake environment of an earlier run (tools/lake-env.sh)")
    else:
        code, seconds = shell(PREPARE, log=tools / "prepare.log", seconds=3600,
                              env={**base, "FIGURES_TOOLS": str(tools),
                                   "FIGURES_EXECUTABLES": " ".join(EXECUTABLES)})
        log(f"build of {len(EXECUTABLES)} executables and `lake env`: exit {code}, {seconds:.0f} s "
            "(tools/build.log)")
        lines = []
        for entry in (tools / "lake-env.bin").read_bytes().decode().split("\0"):
            name, _, value = entry.partition("=")
            if name and name not in ("LAKE", "_", "SHLVL", "PWD", "OLDPWD") and base.get(name) != value:
                lines.append(f"export {name}={shlex.quote(value)}")
        (tools / "lake-env.sh").write_text("\n".join(lines) + "\n")
    shim = tools / "lake"
    shim.write_text(SHIM)
    shim.chmod(0o755)
    return base


def measure(raw: Path, jobs: int, threads: int, only: list, log, reuse: bool = False) -> list:
    """Run the sections; returns (name, exit code, seconds) for each."""
    build = build_directory()
    base = prepare(raw, build, reuse, log)
    tools = raw / "tools"
    chosen = [s for s in sections(raw) if not only or s[0] in only]
    unknown = set(only or []) - {s[0] for s in chosen}
    if unknown:
        raise SystemExit(f"no timing section named {', '.join(sorted(unknown))}")
    chosen.sort(key=lambda s: START_ORDER.index(s[0]) if s[0] in START_ORDER else len(START_ORDER))

    def run(section) -> tuple:
        name, seconds, command = section
        alias = tools / f"build-{name}"       # a name of its own for the build directory
        if alias.is_symlink():
            alias.unlink()
        alias.symlink_to(build)
        env = {**base, "LAKE": str(tools / "lake"), "FIGURES_LAKE_ENV": str(tools / "lake-env.sh"),
               "FIGURES_BUILD": str(build), "FLOATLIB_BUILD_DIR": str(alias),
               "LEAN_NUM_THREADS": str(max(1, threads // max(1, jobs)))}
        code, spent = shell(command, env=env, log=raw / f"{name}.out", seconds=seconds)
        log(f"{name}: exit {code}, {spent:.0f} s")
        return name, code, spent

    (raw / "suite").mkdir(exist_ok=True)
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        done = list(pool.map(run, chosen))
    if any(name in ("kernel-binary", "matched", "families", "exhaustive", "compiled", "compiled-comparison")
           for name, _, _ in done):
        code, spent = shell(f"python3 -I benchmarks/suite/tables.py {shlex.quote(str(raw / 'suite'))}",
                            env=base, log=raw / "suite-tables.out", seconds=600)
        log(f"suite tables: exit {code}, {spent:.0f} s")
    return done
