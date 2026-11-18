#!/usr/bin/env python3
"""Turn the logs of benchmarks/exact/run.sh into Markdown tables.

usage: tables.py RESULTS_DIR

Reads the `*.log` files that `run.sh` wrote into RESULTS_DIR and writes one `*.md` next to each:

  operations.log            -> operations.md   one table per type, a column per operand size
  baseline.log              -> baseline.md     FloatLib's own exact layer
  tactic.log                -> tactic.md       the `interval` tactic
  workloads.log             -> workloads.md    the kernel checks of other projects
  native.log                -> native.md       kernel against `native_decide`
  compiled.log              -> compiled.md     kernel against compiled code
  coq.log                   -> coq.md          Coq 8.20.1 under `vm_compute`
  load.log                  -> load.md         time to load a check module

The Lean release named in the tables is read from `toolchain.log`, the copy of `lean-toolchain`
that `run.sh` leaves in RESULTS_DIR when it measures.

Every number in the tables is a time that Lean, Coq or `/usr/bin/time` printed; this script only
divides totals by counts, formats and aligns. A missing log is skipped.
"""
import re
import sys
from collections import OrderedDict
from pathlib import Path

out = Path(sys.argv[1])
KOP = re.compile(r"^KOP (.*) bits=(\d+) ns=(\d+) warm=(\d+) value=")
KTERM = re.compile(r"^KTERM (.*) ns=(\d+) value=(.*)$")
KCMD = re.compile(r"^KCMD (.*) ns=(\d+) errors=(\w+)")


def fmt(ns):
    """A time in nanoseconds with three significant digits and its unit."""
    if ns is None:
        return "n/a"
    for unit, scale in (("s", 1e9), ("ms", 1e6), ("µs", 1e3)):
        if ns >= scale:
            return f"{ns / scale:.3g} {unit}"
    return f"{ns:.3g} ns"


def ratio(first, second):
    if not first or not second:
        return "n/a"
    return f"{first / second:.1f}x"


def lines(name):
    path = out / name
    return path.read_text().splitlines() if path.exists() else None


def lean_release():
    """The Lean release that produced the logs, for example `Lean 4.36.0`."""
    recorded = lines("toolchain.log")
    if not recorded or ":v" not in recorded[0]:
        raise SystemExit(f"{out / 'toolchain.log'} does not name the toolchain of the logs; "
                         "`run.sh` writes it when it measures")
    return "Lean " + recorded[0].strip().rsplit(":v", 1)[1]


def table(header, rows):
    text = ["| " + " | ".join(header) + " |", "| " + " | ".join("---" for _ in header) + " |"]
    text += ["| " + " | ".join(row) + " |" for row in rows]
    return "\n".join(text) + "\n"


def parse(log):
    """Rows of a log in order of first appearance: (kind, tag, bits or None, cold ns, warm ns or
    None). A row that a log has several times (EXACT_BENCH_RUNS) keeps its fastest times."""
    rows = OrderedDict()

    def keep(kind, tag, bits, cold, warm):
        old = rows.get((kind, tag, bits))
        if old:
            cold = min(cold, old[3])
            warm = warm if old[4] is None else min(warm, old[4])
        rows[(kind, tag, bits)] = (kind, tag, bits, cold, warm)

    for line in log:
        m = KOP.match(line)
        if m:
            keep("op", m[1], int(m[2]), int(m[3]), int(m[4]))
            continue
        m = KTERM.match(line)
        if m:
            keep("term", m[1], None, int(m[2]), None)
            continue
        m = KCMD.match(line)
        if m:
            keep("cmd", m[1], None, int(m[2]), None)
    return list(rows.values())


def groups(rows):
    """Tags grouped by their prefix before the first slash, in order of appearance."""
    result = OrderedDict()
    for row in rows:
        group, _, name = row[1].partition("/")
        result.setdefault(group, []).append((name,) + row[2:])
    return result


def operations():
    log = lines("operations.log")
    if log is None:
        return
    text = ["# Kernel cost of one exact operation\n",
            f"{lean_release()}, `Lean.Kernel.whnf`. Each cell is `cold / warm`: one operation in a fresh "
            "kernel state, and one more operation in a state that has already done one. The column "
            "is the size of the operands in bits. Written by `benchmarks/exact/run.sh operations`.\n"]
    for group, rows in groups(parse(log)).items():
        sizes = sorted({r[1] for r in rows if r[1] is not None})
        names = list(OrderedDict.fromkeys(r[0] for r in rows))
        cells = {(r[0], r[1]): r for r in rows}
        body = []
        for name in names:
            line = [f"`{name}`"]
            for size in sizes:
                r = cells.get((name, size))
                line.append("" if r is None else f"{fmt(r[2])} / {fmt(r[3])}")
            body.append(line)
        text.append(f"\n## {group}\n")
        text.append(table(["operation"] + [f"{s:,} bits" for s in sizes], body))
    (out / "operations.md").write_text("\n".join(text))


def single(stem, title, intro):
    log = lines(f"{stem}.log")
    if log is None:
        return
    text = [f"# {title}\n", intro + "\n"]
    for group, rows in groups(parse(log)).items():
        body = [[f"`{name}`" + ("" if bits is None else f", {bits:,} bits"), fmt(cold)]
                for name, bits, cold, warm in rows]
        text.append(f"\n## {group}\n")
        text.append(table(["row", "time"], body))
    (out / f"{stem}.md").write_text("\n".join(text))


def coq():
    log = lines("coq.log")
    if log is None:
        return
    rows, pending = [], None
    for line in log:
        m = re.match(r"^ROW (.*) (\d+) (\d+)$", line)
        if m:
            pending = (m[1], int(m[2]), int(m[3]))
            continue
        m = re.match(r"^Finished transaction in ([0-9.]+) secs", line)
        if m and pending:
            rows.append(pending + (float(m[1]),))
            pending = None
    names = list(OrderedDict.fromkeys(r[0] for r in rows))
    sizes = sorted({r[1] for r in rows})
    cells = {(r[0], r[1]): r for r in rows}
    body = []
    for name in names:
        line = [f"`{name}`"]
        for size in sizes:
            r = cells.get((name, size))
            if r is None:
                line.append("")
            elif r[3] == 0:
                # Coq prints times to the millisecond.
                line.append("< " + fmt(1e6 / r[2]))
            else:
                line.append(fmt(r[3] * 1e9 / r[2]))
        body.append(line)
    text = ["# Coq 8.20.1 on the same operand sizes\n",
            "`vm_compute` in the image `leanfloat-flocq-bench:4.2.2`, one container with 8 GB and "
            "two cores. Each cell is the time Coq printed for a loop divided by its number of "
            "iterations. `Z` and `Q` are Coq's binary integers and rationals, `BigZ` is the "
            "`bignums` library on 63-bit machine words. An empty cell was not run. Written by "
            "`benchmarks/exact/run.sh coq`.\n",
            table(["operation"] + [f"{s:,} bits" for s in sizes], body)]
    (out / "coq.md").write_text("\n".join(text))


def native():
    log = lines("native.log")
    if log is None:
        return
    cells = OrderedDict()
    for line in log:
        m = KCMD.match(line)
        if m and m[1].startswith("native/"):
            name, _, kind = m[1][len("native/"):].rpartition("|")
            best = cells.setdefault(name, {})
            if m[3] == "true":
                best[kind] = None
            elif best.get(kind, int(m[2])) is not None:
                best[kind] = min(int(m[2]), best.get(kind, int(m[2])))
    body = [[name] + ["failed" if c.get(kind, 0) is None else fmt(c.get(kind))
                      for kind in ("kernel", "native")] for name, c in cells.items()]
    text = ["# The kernel against `native_decide`\n",
            "Each row times the same closed statement with `decide +kernel` and `native_decide`. "
            "Both columns include elaboration. The native column also includes compilation. "
            "`native_decide` trusts the compiler and introduces an axiom for its result. "
            "A `failed` cell means the statement did not compile with `native_decide`. "
            "Run `benchmarks/exact/run.sh native` to generate the statements and repeat the comparison.\n",
            table(["statement", "`decide +kernel`", "`native_decide`"], body)]
    (out / "native.md").write_text("\n".join(text))


def compiled():
    log = lines("compiled.log")
    if log is None:
        return
    kernel = {}
    for name in ("operations.log", "baseline.log"):
        for row in parse(lines(name) or []):
            kernel[(row[1], row[2])] = row[3]
    body = []
    for line in log:
        m = re.match(r"^COMPILED (.*) bits=(\d+) ns=(\d+)", line)
        if not m:
            continue
        tag, bits, ns = m[1], int(m[2]), int(m[3])
        k = kernel.get((tag, bits))
        body.append([f"`{tag}`", f"{bits:,}", fmt(k), fmt(ns), ratio(k, ns)])
    text = ["# The kernel against compiled code\n",
            "One call of the same definition in Lean's kernel (`Lean.Kernel.whnf`, fresh state) "
            "and in the compiled program `exactCompiled` (`benchmarks/lean/FloatLibBenchmarks/"
            "Exact/Compiled.lean`, Lean's C backend and GMP). The compiled time includes about "
            "0.35 µs of loop around each call. `IntegerRoot.Seeded.newton` is what compiled code "
            "runs for `IntegerRoot.newton`. Written by `benchmarks/exact/run.sh compiled`.\n",
            table(["operation", "bits", "kernel", "compiled", "kernel / compiled"], body)]
    (out / "compiled.md").write_text("\n".join(text))


def plain(stem, title, intro, header):
    log = lines(f"{stem}.log")
    if log is None:
        return
    body = [line.split("\t") for line in log if line.startswith("ROW\t")]
    text = [f"# {title}\n", intro + "\n", table(header, [row[1:] for row in body])]
    (out / f"{stem}.md").write_text("\n".join(text))


operations()
single("baseline", "FloatLib's own exact layer in the kernel",
       f"{lean_release()}, `Lean.Kernel.whnf`, one operation in a fresh kernel state. The benchmark "
       "file `benchmarks/exact/Baseline.lean` uses the library's exact layer as the library's own "
       "proofs do. Written by `benchmarks/exact/run.sh baseline`.")
single("tactic", "The `interval` tactic",
       "Time to elaborate one `example` closed by `interval`: reification, the kernel check and "
       f"the addition to the environment ({lean_release()}, `benchmarks/exact/Tactic.lean`). "
       "Written by `benchmarks/exact/run.sh tactic`.")
single("workloads", "Kernel checks of other projects",
       f"{lean_release()}, `Lean.Kernel.whnf`, one check in a fresh kernel state. Each project's check "
       "is copied as its authors wrote it and timed next to the same check on "
       "`FloatLib.Numerics.Kernel`. The section `packed` times FloatLib's packed rows against the same "
       "norm computed entry by entry. Written by `benchmarks/exact/run.sh workloads`.")
coq()
native()
compiled()
plain("load", "Time to load a check module",
      "`lean` on a file that imports the named modules and proves one statement by "
      "`decide +kernel`: wall time and peak memory from `/usr/bin/time`, fastest of three runs. "
      "Written by `benchmarks/exact/run.sh load`.",
      ["imports", "modules loaded", "wall", "peak memory"])
