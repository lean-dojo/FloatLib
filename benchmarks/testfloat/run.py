"""Berkeley TestFloat campaigns with generated vectors and exact provenance."""
from __future__ import annotations
import hashlib
import json
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import ROOT, digest, in_order, merge_csv, provenance, selected, workers, write_csv, write_json
from fetch import fetch
from process import run as monitored

FORMATS = ("f16", "f32", "f64", "f128")
MODES = ("near_even", "minMag", "min", "max", "near_maxMag")
COMPARISONS = ("eq", "le", "lt", "eq_signaling", "le_quiet", "lt_quiet")
UPSTREAM = "a9c849f1b0eb0264b626d9686ffae167d996e3be"


def matrix():
    """The maintained matrix, extended by one mode; exact widenings need only one mode."""
    rows = []
    def add(fmt, operation, modes=MODES):
        for mode in modes:
            rows.append({"id": f"{fmt}_{operation}_{mode}", "format": fmt,
                         "operation": operation, "rounding": mode})
    for fmt in FORMATS:
        for operation in ("sqrt", "roundToInt", "add", "sub", "mul", "div"):
            add(fmt, operation)
        for operation in ("rem", *COMPARISONS):
            add(fmt, operation, ("near_even",))
    for source, destination, exact in [
        ("f16", "f32", True), ("f16", "f64", True), ("f16", "f128", True),
        ("bf16", "f32", True), ("f32", "bf16", False), ("f32", "f16", False),
        ("f32", "f64", True), ("f32", "f128", True), ("f64", "f16", False),
        ("f64", "f32", False), ("f64", "f128", True), ("f128", "f16", False),
        ("f128", "f32", False), ("f128", "f64", False),
    ]:
        add(source, "to_" + destination, ("near_even",) if exact else MODES)
    # Large FMA vector files are produced one at a time and removed after checking.
    for fmt in FORMATS:
        add(fmt, "mulAdd")
    return rows


def build_generator(output):
    soft = fetch(HERE / "berkeley-softfloat-3-source.json")
    test = fetch(HERE / "berkeley-testfloat-3-source.json")
    directory = output / "build"
    directory.mkdir(exist_ok=True)
    # Generated files stay ignored under upstream/. Source hashes are verified on every run.
    for name, source, target in [("softfloat", soft, None), ("testfloat", test, "testfloat_gen")]:
        command = ["make", "-C", str(source / "build/Linux-x86_64-GCC"), "-j1"]
        if target:
            command.append(target)
        usage = monitored(command, cwd=ROOT, log=directory / (name + ".log"), timeout=180)
        write_json(directory / (name + ".json"), {"command": command, **usage})
        if usage["exit_code"]:
            raise RuntimeError(f"{name} build failed; see {directory}")
    return test / "build/Linux-x86_64-GCC/testfloat_gen"


def execute(case, generator, checker, output, *, level, seed, timeout, context):
    directory = output / "campaigns" / case["id"]
    directory.mkdir(parents=True, exist_ok=True)
    command = [str(generator), "-level", str(level), "-seed", str(seed),
               "-r" + case["rounding"], "-tininessafter"]
    if case["operation"] == "roundToInt":
        command.append("-exact")
    command.append(case["format"] + "_" + case["operation"])
    check_command = [str(checker), case["format"], case["operation"], case["rounding"], "10"]
    signature = hashlib.sha256(json.dumps({
        "generator": digest(generator), "checker": digest(checker),
        "command": command, "check_command": check_command, "timeout": timeout,
        "harness": digest(Path(__file__)),
        "floatlib_commit": context["floatlib_commit"],
        "tracked_diff_sha256": context["tracked_diff_sha256"],
    }, sort_keys=True).encode()).hexdigest()
    result_file = directory / "result.json"
    if result_file.exists() and os.environ.get("FLOATLIB_SUITE_RETRY") != "1":
        old = json.loads(result_file.read_text())
        if old.get("signature") == signature:
            return old
    # One vector file per campaign in flight; generator and checker run one after the other.
    vectors = directory / "vectors.txt"
    try:
        with vectors.open("w") as stream:
            generation = monitored(command, cwd=ROOT, log=directory / "generator.log",
                                   timeout=120, stdout=stream)
        vector_sha256 = digest(vectors)
        vector_bytes = vectors.stat().st_size
        checking = {}
        if generation["exit_code"] == 0:
            with vectors.open() as stream:
                checking = monitored(check_command, cwd=ROOT, log=directory / "checker.log",
                                     timeout=timeout, stdin=stream)
        statistics = {}
        if checking:
            text = (directory / "checker.log").read_text()
            # Only the checker's final summary contains all four fields on one line.
            for line in text.splitlines():
                fields = dict(re.findall(r"([a-z_]+)=(\d+)", line))
                if all(key in fields for key in
                       ("cases", "value_mismatches", "flag_mismatches", "parse_errors")):
                    statistics = {key: int(value) for key, value in fields.items()}
        status, reason = "matched", ""
        if generation["exit_code"]:
            status, reason = "generator_error", "The complete level-1 vector set was not generated"
        elif checking.get("termination"):
            status, reason = checking["termination"], "No complete checker summary; no conformance claim"
        elif not statistics:
            status, reason = "runner_error", "Checker produced no complete summary"
        elif checking["exit_code"] or any(statistics[key] for key in
                ("value_mismatches", "flag_mismatches", "parse_errors")) or not statistics["cases"]:
            status, reason = "mismatch", "See checker.log for first ten counterexamples"
        result = {
            **case, "status": status, "reason": reason, **statistics,
            "level": level, "seed": seed, "source_revision": UPSTREAM,
            "generation_seconds": generation["elapsed_seconds"],
            "lean_check_seconds": checking.get("elapsed_seconds", ""),
            "vector_sha256": vector_sha256, "vector_bytes": vector_bytes,
            "generator_command": command, "checker_command": check_command,
            "generator_usage": generation, "checker_usage": checking,
            "generator_sha256": digest(generator), "checker_sha256": digest(checker),
            "signature": signature,
            "floatlib_commit": context["floatlib_commit"],
            "tracked_diff_sha256": context["tracked_diff_sha256"],
            "measurement_utc": generation["measurement_utc"],
        }
        write_json(result_file, result)
        return result
    finally:
        vectors.unlink(missing_ok=True)


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    metadata = provenance()
    metadata["time_definition"] = "Separate wall times for vector generation and native Lean checking"
    metadata["workers"] = workers()
    metadata["evidence_kind"] = "finite executable differential checks, including five IEEE flags"
    write_json(output / "provenance.json", metadata)
    matrix_rows = matrix()
    chosen = selected(matrix_rows)
    write_json(output / "plan.json", matrix_rows)
    for row in matrix_rows:
        row.update(status="not_run", reason="Outside the selected campaign range")
    merge_csv(output / "results.csv", matrix_rows)
    checker = Path(os.environ.get("FLOATLIB_BUILD_DIR", ROOT / ".lake/build")) / "bin/suiteTestFloat"
    if not checker.is_file():
        raise RuntimeError("Build the suites Lake target suiteTestFloat before running TestFloat")
    generator = build_generator(output)
    level = int(os.environ.get("FLOATLIB_TESTFLOAT_LEVEL", "1"))
    if level != 1:
        raise ValueError("This bounded runner admits the complete level-1 set only")
    seed = int(os.environ.get("FLOATLIB_TESTFLOAT_SEED", "1"))
    done = {}
    timeout = int(os.environ.get("FLOATLIB_SUITE_TIMEOUT", "360"))
    campaigns = in_order(lambda case: execute(case, generator, checker, output, level=level,
                                              seed=seed, timeout=timeout, context=metadata), chosen)
    for case, result in zip(chosen, campaigns):
        done[case["id"]] = result
        merge_csv(output / "results.csv", [done.get(row["id"], row) for row in matrix_rows])
        print(f"testfloat: {case['id']}: {result['status']} {result.get('cases', '')}", flush=True)
    exclusions = [
        {"format": "all", "rounding": mode, "status": "reference_unavailable",
         "reason": reason} for mode, reason in [
            ("awayZero", "Berkeley TestFloat has no away-from-zero mode"),
            ("stochastic", "Berkeley TestFloat does not model stochastic rounding"),
        ]
    ]
    exclusions.extend([
        {"format": "bf16", "rounding": "all", "status": "reference_unavailable",
         "reason": "Pinned Berkeley sources provide bf16/f32 conversions only"},
        {"format": "other FloatFormat descriptors and nonbinary format families",
         "rounding": "all", "status": "reference_unavailable",
         "reason": "The standard generator does not parameterize arbitrary FloatLib formats"},
        {"format": "extF80", "rounding": "all", "status": "adapter_refusal",
         "reason": "No extF80 storage parser in the maintained FloatLib stream checker"},
        {"format": "integer conversions", "rounding": "all", "status": "adapter_refusal",
         "reason": "The maintained checker admits floating-to-floating conversions only"},
        {"format": "exact widenings and rounding-independent comparisons", "rounding": "other modes",
         "status": "mode_independent",
         "reason": "One nearest-even campaign is used, matching the maintained matrix"},
    ])
    write_csv(output / "coverage-exclusions.csv", exclusions)


if __name__ == "__main__":
    run(Path(sys.argv[1]).resolve())
