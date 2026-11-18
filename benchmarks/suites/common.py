"""Lean checks in separate processes, provenance, and unambiguous CSV result records."""

from __future__ import annotations

import csv
import hashlib
import json
import os
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from process import run as monitored


ROOT = Path(__file__).resolve().parents[2]
PROOF_RUNNER = ROOT / "benchmarks/suites/Proofs.lean"
csv.field_size_limit(64 * 1024 * 1024)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def write_csv(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({
                key: json.dumps(value, ensure_ascii=False) if isinstance(value, (dict, list))
                else value for key, value in row.items()
            })


def provenance() -> dict:
    return {
        "floatlib_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "tracked_diff_sha256": hashlib.sha256(subprocess.check_output(
            ["git", "diff", "--binary", "HEAD"], cwd=ROOT
        )).hexdigest(),
        "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "proof_runner_sha256": digest(PROOF_RUNNER),
        "time_definition": (
            "Lean monotonic time for command elaboration, diagnostics, transitive axiom "
            "checking and statement printing inside each restored environment"
        ),
        "thread_limit": os.environ.get("LEAN_NUM_THREADS", ""),
        "workers": workers(),
        "cgroup": Path("/proc/self/cgroup").read_text(),
    }


def workers() -> int:
    """Processes measured at the same time (`FLOATLIB_SUITE_WORKERS`, default one)."""
    return max(1, int(os.environ.get("FLOATLIB_SUITE_WORKERS", "1")))


def selected(cases: list) -> list:
    """The range `FLOATLIB_SUITE_OFFSET`/`LIMIT` of the plan, in plan order."""
    offset = int(os.environ.get("FLOATLIB_SUITE_OFFSET", "0"))
    limit = int(os.environ.get("FLOATLIB_SUITE_LIMIT", str(len(cases))))
    return cases[offset:offset + limit]


def in_order(function, items):
    """Results of `function` over `items` in order, from at most `workers()` threads.

    Each call starts and waits for its own child process, so the threads only wait.
    """
    with ThreadPoolExecutor(max_workers=workers()) as pool:
        yield from pool.map(function, items)


def runner(output: Path, imports: tuple) -> Path:
    """The proof runner, with the modules a route adds placed before its own imports."""
    if not imports:
        return PROOF_RUNNER
    head, mark, tail = PROOF_RUNNER.read_text().partition("\nimport ")
    text = head + "".join(f"\nimport {name}" for name in imports) + mark + tail
    path = output / f"Proofs-{hashlib.sha256(text.encode()).hexdigest()[:12]}.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)
    return path


def prove(cases: list[dict], output: Path, *, batch_size=8, timeout=180,
          imports: tuple = ()) -> list[dict]:
    """Retain completed rows on timeouts; never turn a missing row into proof success.

    `imports` names modules that this route needs beyond those of `Proofs.lean`.
    """
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    changes = hashlib.sha256(subprocess.check_output(
        ["git", "diff", "--binary", "HEAD"], cwd=ROOT)).hexdigest()
    proofs = runner(output, tuple(imports))

    def measure(batch_index: int) -> tuple[list[dict], int]:
        batch = cases[batch_index:batch_index + batch_size]
        identity = hashlib.sha256("\n".join(case["id"] for case in batch).encode()).hexdigest()[:20]
        name = "batch-" + identity
        plan = output / (name + ".json")
        raw = output / (name + ".jsonl")
        log = output / (name + ".log")
        stamp = output / (name + ".stamp")
        active = output / (name + ".active")
        usage = output / (name + ".usage.json")
        write_json(plan, batch)
        signature = ":".join([digest(plan), digest(proofs), digest(Path(__file__)),
                              digest(Path(__file__).with_name("process.py")),
                              tree, changes, str(timeout), str(batch_size)])
        cached = []
        if raw.exists() and stamp.exists() and stamp.read_text() == signature:
            cached = [json.loads(line) for line in raw.read_text().splitlines() if line]
            if {r["id"] for r in cached} != {r["id"] for r in batch}:
                cached = []
        status = 0
        stopped = ""
        if not cached:
            raw.unlink(missing_ok=True)
            active.unlink(missing_ok=True)
            env = {**os.environ, "FLOATLIB_SUITE_PLAN": str(plan.resolve()),
                   "FLOATLIB_SUITE_OUTPUT": str(raw.resolve()),
                   "FLOATLIB_SUITE_ACTIVE": str(active.resolve())}
            measurement = monitored(
                ["lean", "-M", "4096", str(proofs)], cwd=ROOT, env=env,
                log=log, timeout=timeout)
            status, stopped = measurement["exit_code"], measurement["termination"]
            write_json(usage, measurement)
            if raw.exists():
                for line in raw.read_text().splitlines():
                    try:
                        cached.append(json.loads(line))
                    except json.JSONDecodeError:
                        # A killed writer may leave its final record incomplete.
                        pass
            if status == 0:
                stamp.write_text(signature)
        by_id = {r["id"]: r for r in cached}
        active_id = active.read_text().strip() if active.exists() else ""
        resources = json.loads(usage.read_text()) if usage.exists() else {}
        measured = []
        for case in batch:
            row = by_id.get(case["id"], {
                "id": case["id"],
                "status": (stopped or "runner_error") if case["id"] == active_id or not active_id
                          else "not_run_after_process_failure",
                "reason": f"Lean process exit {status}; see {log.name}",
                "elapsed_ns": "", "statement": "", "axioms": [],
            })
            row.update({
                "plan_sha256": digest(plan), "log": str(log.relative_to(output.parent)),
                "plan": str(plan.relative_to(output.parent)),
                "floatlib_commit": tree, "tracked_diff_sha256": changes,
                "proof_runner_sha256": digest(proofs),
                "harness_sha256": digest(Path(__file__)),
                "measurement_utc": resources.get("measurement_utc", ""),
                "process_elapsed_seconds": resources.get("elapsed_seconds", ""),
                "process_sampled_peak_rss_kib": resources.get("sampled_peak_rss_kib", ""),
            })
            measured.append(row)
        return measured, status

    partial = output.parent / (output.name + ".partial.csv")
    for measured, status in in_order(measure, range(0, len(cases), batch_size)):
        rows.extend(measured)
        write_csv(partial, rows)
        print(f"{output.parent.name}/{output.name}: {len(rows)}"
              f"/{len(cases)} cases, Lean exit {status}", flush=True)
    return rows


def merge_csv(path: Path, rows: list[dict]) -> None:
    """Keep measured rows from earlier ranges; a new attempt for an id supersedes the old one."""
    measured = {}
    if path.exists():
        with path.open() as stream:
            measured = {row["id"]: row for row in csv.DictReader(stream)}
    for row in rows:
        if row.get("status") != "not_run" or row["id"] not in measured:
            measured[row["id"]] = row
    write_csv(path, [measured[row["id"]] for row in rows])
