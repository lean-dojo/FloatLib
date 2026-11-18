"""Finite conformance checks against MPFR, CORE-MATH and, for the complex rows, GNU MPC."""
from __future__ import annotations
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import ROOT, digest, merge_csv, provenance, selected, write_csv, write_json
from fetch import fetch
from process import run as monitored
from corpus import OPERATIONS, calibration_cases, core_cases
from lefevre import cases as lefevre_cases
from screen import cases as screen_cases
from capabilities import evidence, probe
import complex_reference


def same_bits(left, right, width):
    fraction = 23 if width == 32 else 52
    exponent = 8 if width == 32 else 11
    mask = ((1 << exponent) - 1) << fraction
    def nan(bits):
        return bits & mask == mask and bits & ((1 << fraction) - 1) != 0
    return nan(left) and nan(right) or left == right


def build_reference(output):
    source = fetch(HERE / "core-math-source.json")
    build = output / "reference"
    build.mkdir(parents=True, exist_ok=True)
    files = [HERE / "reference.c"]
    for width in (32, 64):
        for operation in OPERATIONS:
            suffix = "f" if width == 32 else ""
            files.append(source / f"src/binary{width}/{operation}/{operation}{suffix}.c")
    executable = build / "reference"
    command = ["gcc", "-O3", "-std=gnu11", "-frounding-math", "-fno-fast-math",
               "-DCORE_REFERENCE", *(str(path) for path in files),
               "-lmpfr", "-lgmp", "-lm", "-o", str(executable)]
    signature = hashlib.sha256(
        ("\n".join(command) + digest(HERE / "core-math-source.json")
         + digest(HERE / "reference.c")).encode()).hexdigest()
    stamp = build / "stamp"
    if not executable.exists() or not stamp.exists() or stamp.read_text() != signature:
        result = monitored(command, cwd=ROOT, log=build / "compile.log", timeout=180)
        write_json(build / "compile.json", {"command": command, **result})
        if result["exit_code"]:
            raise RuntimeError(f"Reference compilation failed; see {build / 'compile.log'}")
        stamp.write_text(signature)
    version = subprocess.check_output([str(executable), "--version"], text=True).strip()
    write_json(build / "provenance.json", {
        "version": version, "core_math_revision": json.loads(
            (HERE / "core-math-source.json").read_text())["revision"],
        "gcc_version": subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0],
        "command": command, "binary_sha256": digest(executable),
        "rounding": "nearest, ties to even",
        "mpfr_method": "target precision, IEEE exponent range, ternary-aware subnormal rounding",
        "time_definition": "one C call plus bit conversion; no process startup",
    })
    return executable


def references(cases, executable, output):
    plan = output / "reference-input.txt"
    plan.write_text("".join(
        f"{r['id']} {r['width']} {r['operation']} {r['bits']:x}\n" for r in cases))
    log = output / "reference-output.txt"
    with plan.open() as stream:
        usage = monitored([str(executable)], cwd=ROOT, log=log, timeout=120, stdin=stream)
    write_json(output / "reference-usage.json", usage)
    if usage["exit_code"]:
        raise RuntimeError("Reference execution failed; see reference-output.txt")
    rows = {}
    for line in log.read_text().splitlines():
        ident, expected, nanos, core, core_nanos = line.split()
        if ident in rows:
            raise ValueError("Duplicate reference row: " + ident)
        rows[ident] = {"expected": int(expected, 16), "mpfr_elapsed_ns": int(nanos),
                       "core_math_bits": int(core, 16), "core_math_elapsed_ns": int(core_nanos)}
    if set(rows) != {row["id"] for row in cases}:
        raise ValueError("Reference output does not cover the exact input plan")
    for case in cases:
        row = rows[case["id"]]
        row["reference_agreement"] = same_bits(
            row["expected"], row["core_math_bits"], case["width"])
        if "known_exact" in case and case["known_exact"] != row["expected"]:
            raise ValueError("MPFR calibration failed: " + case["id"])
        if "published_expected" in case:
            row["published_reference_agreement"] = same_bits(
                case["published_expected"], row["expected"], case["width"])
            row["reference_agreement"] &= row["published_reference_agreement"]
    return rows


def execute(cases, output, batch_size, timeout):
    runtime = HERE / "Runtime.lean"
    directory = output / "runtime"
    directory.mkdir(exist_ok=True)
    rows = []
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    native = Path(os.environ.get("FLOATLIB_BUILD_DIR", ROOT / ".lake/build")) / "bin/suiteCorrectRounding"
    if native.is_file():
        command_prefix = [str(native)]
        runner_digest = digest(native)
    else:
        command_prefix = ["lean", "-M", "4096", "--run", str(runtime)]
        runner_digest = digest(runtime)
    tracked_diff = hashlib.sha256(subprocess.check_output(
        ["git", "diff", "HEAD"], cwd=ROOT)).hexdigest()
    for offset in range(0, len(cases), batch_size):
        batch = cases[offset:offset+batch_size]
        batch_key = hashlib.sha256("\n".join(row["id"] for row in batch).encode()).hexdigest()[:20]
        stem = directory / ("batch-" + batch_key)
        plan, raw, log, active, stamp = [
            stem.with_suffix(ext) for ext in (".json", ".jsonl", ".log", ".active", ".stamp")]
        write_json(plan, [{key: row[key] for key in
                          ("id", "width", "operation", "bits", "expected")} for row in batch])
        signature = ":".join([digest(plan), digest(runtime), runner_digest, commit, tracked_diff,
                              digest(HERE.parent / "suites/process.py"), str(timeout)])
        cached = []
        if stamp.exists() and stamp.read_text() == signature and raw.exists():
            cached = [json.loads(line) for line in raw.read_text().splitlines() if line]
        if not cached or {r["id"] for r in cached} != {r["id"] for r in batch}:
            raw.unlink(missing_ok=True)
            active.unlink(missing_ok=True)
            usage = monitored(
                [*command_prefix, str(plan), str(raw)],
                cwd=ROOT, log=log, timeout=timeout,
                env={**os.environ, "FLOATLIB_SUITE_ACTIVE": str(active)},
            )
            write_json(stem.with_suffix(".usage.json"), usage)
            cached = []
            if raw.exists():
                for line in raw.read_text().splitlines():
                    try:
                        cached.append(json.loads(line))
                    except json.JSONDecodeError:
                        pass
            if usage["exit_code"] == 0:
                stamp.write_text(signature)
        else:
            usage = json.loads(stem.with_suffix(".usage.json").read_text())
        by_id = {row["id"]: row for row in cached}
        active_id = active.read_text().strip() if active.exists() else ""
        for case in batch:
            failure = usage["termination"] or "runner_error"
            row = by_id.get(case["id"], {
                "id": case["id"],
                "status": failure if case["id"] == active_id or not active_id
                          else "not_run_after_process_failure",
                "reason": f"Lean exit {usage['exit_code']}; see {log.name}",
                "elapsed_ns": "",
            })
            rows.append({**row, "runtime_log": str(log.relative_to(output)),
                         "runtime_plan_sha256": digest(plan),
                         "floatlib_commit": commit, "tracked_diff_sha256": tracked_diff,
                         "measurement_utc": usage.get("measurement_utc", "")})
        write_csv(output / "runtime.partial.csv", rows)
        print(f"correct-rounding: {min(offset+batch_size, len(cases))}/{len(cases)}", flush=True)
    return rows


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    complex_ids = {op: "complex-" + ("exponential" if op == "exp" else op) + "-api"
                   for op in OPERATIONS}
    complex_probes = probe(output / "capabilities", list(complex_ids.values()))
    executable = build_reference(output)
    samples = int(os.environ.get("FLOATLIB_CR_SAMPLES", "16"))
    inventory, cases = core_cases(samples)
    other_inventory, other_cases = lefevre_cases(samples)
    inventory.extend(other_inventory)
    cases.extend(other_cases)
    if screen_directory := os.environ.get("FLOATLIB_CR_SCREEN"):
        screen_inventory, candidates = screen_cases(Path(screen_directory))
        inventory.extend(screen_inventory)
        cases.extend(candidates)
    else:
        inventory.append({
            "source": "CORE-MATH binary32 exhaustive input screen", "width": 32,
            "status": "not_run", "reason": "FLOATLIB_CR_SCREEN directory not supplied",
            "selected_cases": 0,
        })
    context = provenance()
    write_json(output / "provenance.json", {
        **context, "evidence_kind": "runtime finite-vector checks, not kernel proofs",
        "time_definition": "Lean monotonic time around one forced native function call",
        "runtime_sha256": digest(HERE / "Runtime.lean"),
        "input_policy": "Exact source values only; no binary64-to-binary32 relabeling",
        "comparison_policy": "NaN classification; all other bits, including zero sign, must agree",
    })
    write_csv(output / "coverage.csv", inventory)
    chosen = selected(cases)
    runnable = [row for row in chosen
                if "bits" in row and row.get("status") != "translation_refusal"]
    refs = references([*calibration_cases(), *runnable], executable, output)
    write_json(output / "calibration.json", {
        row["id"]: refs[row["id"]] for row in calibration_cases()})
    calibration = [{**row, **refs[row["id"]]} for row in calibration_cases()]
    write_csv(output / "calibration-lean.csv",
              execute(calibration, output, batch_size=1, timeout=20))
    for row in runnable:
        row.update(refs[row["id"]])
        if not row["reference_agreement"]:
            row.update(status="reference_disagreement",
                       reason="MPFR, CORE-MATH, or the published reference disagree; no verdict")
    checked = execute(
        [row for row in runnable if row["reference_agreement"]], output,
        int(os.environ.get("FLOATLIB_SUITE_BATCH", "1")),
        int(os.environ.get("FLOATLIB_SUITE_TIMEOUT", "20")),
    )
    by_id = {row["id"]: row for row in checked}
    available = all(complex_probes[name]["status"] == "proved" for name in complex_ids.values())
    complex_parts = complex_reference.rows(
        runnable, output, int(os.environ.get("FLOATLIB_CR_COMPLEX_BATCH", "2048")),
        int(os.environ.get("FLOATLIB_CR_COMPLEX_TIMEOUT", "600"))) if available else {}
    results = []
    for row in cases:
        row.update(by_id.get(row["id"], {}))
        row.setdefault("status", "not_run")
        row.setdefault("reason", "" if row["status"] in ("matched", "mismatch")
                       else "Outside the selected runtime range")
        results.append({**row, "domain": "real"})
        capability = complex_probes[complex_ids[row["operation"]]]
        if capability["status"] != "proved":
            status = ("capability_refusal" if capability["status"] == "refused"
                      else "capability_probe_failure")
            parts = [(status, "The tested ExecComplex entry point did not pass its compiler "
                      "probe; see capability_probe_reason", "", "", "")] * 2
        elif row["id"] in complex_parts:
            parts = complex_parts[row["id"]]
        else:
            parts = [("translation_refusal" if row["status"] == "translation_refusal"
                      else "not_run", row["reason"] or "Outside the selected runtime range",
                      "", "", "")] * 2
        for component, (status, reason, actual, expected, elapsed) in zip(
                ("real", "imaginary"), parts):
            results.append({
                **row, "id": row["id"] + ":complex:" + component, "domain": "complex",
                **evidence(capability),
                "component": component, "same_source_argument_bits": row.get("bits", ""),
                "status": status, "actual": actual, "elapsed_ns": elapsed,
                "expected": expected, "mpfr_elapsed_ns": "", "core_math_bits": "",
                "core_math_elapsed_ns": "",
                "reference_agreement": "", "published_expected": "",
                "published_reference_agreement": "", "runtime_log": "",
                "runtime_plan_sha256": "",
                "reason": reason,
                "input_policy": complex_reference.POLICY,
            })
    write_json(output / "selected-inputs.json", chosen)
    merge_csv(output / "results.csv", results)
    return results


if __name__ == "__main__":
    run(Path(sys.argv[1]).resolve())
