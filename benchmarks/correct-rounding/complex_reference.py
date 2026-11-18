"""Complex rows of the corpus: FloatLib's compiled complex functions against GNU MPC.

A real case with argument `x` becomes the complex argument `x + i x`, and both parts of the
result are compared. The reference is the one of `tests/oracles/complex_mpc.py`, imported from
there: MPC through gmpy2 at two working precisions, rounded here, undecided when the two differ.
The Lean side is the test workspace's `oracle complex`, one process per batch of requests.
"""
from __future__ import annotations
import importlib.util
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import ROOT, digest, in_order, write_json
from process import run as monitored

DRIVER = ROOT / "tests/oracles/complex_mpc.py"
LAYOUT = {32: (8, 23), 64: (11, 52)}
POLICY = "z = x + i x for the real case's argument x, nearest even"


def oracle() -> Path:
    return Path(os.environ.get("FLOATLIB_BUILD_DIR", ROOT / ".lake/build")) / "bin/oracle"


def reference_module():
    """The MPC reference of the test suite, or the reason it cannot be used here."""
    try:
        spec = importlib.util.spec_from_file_location("complex_mpc", DRIVER)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    except (ImportError, OSError) as error:
        return None, f"The MPC reference needs gmpy2 and mpmath: {error}"
    if not oracle().is_file():
        return None, "Build the test workspace's `oracle` executable before the complex rows"
    return module, ""


def describe(part) -> str:
    kind, payload = part
    return str(payload) if kind == "word" else f"{kind}:{payload}"


def compare(module, case, answer):
    """Statuses of the two parts, the words FloatLib returned and the expected parts."""
    fmt = module.Format(*LAYOUT[case["width"]])
    bits, name = case["bits"], case["operation"]
    fields = answer.split()
    if len(fields) != 2 or fields[0] == "error":
        return [("runner_error", "The oracle answered: " + answer, "", "")] * 2
    words = [int(fields[0]), int(fields[1])]
    expected = module.reference(fmt, name, bits, bits, "nearest",
                                module.exponent_spread(fmt, [bits, bits]))
    if expected is None:
        return [("undecided", "MPC at two precisions does not decide this rounding",
                 words[k], "") for k in (0, 1)]
    parts = []
    for k in (0, 1):
        if module.matches(fmt, name, expected[k], words[k]):
            status, reason = "matched", ""
        elif module.is_tiny(fmt, expected[k]) and module.is_tiny(fmt, ("word", words[k])):
            status = "tiny"
            reason = ("A zero or least subnormal where MPC has the other one or the other sign; "
                      "MPC's sign of a part below its exponent range is not always the exact one")
        else:
            status, reason = "mismatch", "The part differs from the rounded MPC value"
        parts.append((status, reason, words[k], describe(expected[k])))
    return parts


def rows(cases, output: Path, batch_size: int, timeout: int) -> dict:
    """Per case id, the two component results; raises nothing for a failed batch."""
    module, refusal = reference_module()
    if module is None:
        return {case["id"]: [("adapter_refusal", refusal, "", "")] * 2 for case in cases}
    directory = output / "complex"
    directory.mkdir(parents=True, exist_ok=True)
    write_json(directory / "provenance.json", {
        "reference": f"GNU MPC {module.gmpy2.mpc_version()}, MPFR "
                     f"{module.gmpy2.mpfr_version()}, gmpy2 {module.gmpy2.version()}",
        "reference_driver_sha256": digest(DRIVER), "oracle_sha256": digest(oracle()),
        "argument_policy": POLICY,
        "time_definition": "wall time of one oracle process divided by its requests",
    })
    results = {}
    # One function and width per process, so that a batch's time is that function's.
    groups = {}
    for case in cases:
        groups.setdefault((case["operation"], case["width"]), []).append(case)
    batches = [(f"{name}-{width}-{start:07d}", group[start:start + batch_size])
               for (name, width), group in sorted(groups.items())
               for start in range(0, len(group), batch_size)]

    def measure(item):
        label, batch = item
        stem = directory / ("batch-" + label)
        requests, pending = [], []
        fresh = {}
        for case in batch:
            fmt = module.Format(*LAYOUT[case["width"]])
            if module.excluded(fmt, case["operation"], case["bits"], case["bits"]):
                fresh[case["id"]] = [("excluded", "A pole, the origin or a non-finite argument: "
                                      "outside the MPC comparison", "", "")] * 2
                continue
            requests.append(f"{case['operation']} {fmt.exp_width} {fmt.frac_width} nearest "
                            f"{case['bits']} {case['bits']}")
            pending.append(case)
        stem.with_suffix(".in").write_text("".join(line + "\n" for line in requests))
        with stem.with_suffix(".in").open() as stdin, stem.with_suffix(".out").open("w") as stdout:
            usage = monitored([str(oracle()), "complex"], cwd=ROOT, log=stem.with_suffix(".log"),
                              timeout=timeout, stdin=stdin, stdout=stdout)
        write_json(stem.with_suffix(".usage.json"), usage)
        answers = stem.with_suffix(".out").read_text().splitlines()
        if usage["exit_code"] or len(answers) != len(pending):
            failure = usage["termination"] or "runner_error"
            for case in pending:
                fresh[case["id"]] = [(failure, f"oracle exit {usage['exit_code']} with "
                                      f"{len(answers)} of {len(pending)} answers", "", "")] * 2
            return fresh, {}
        per_call = int(1e9 * usage["elapsed_seconds"] / max(1, len(pending)))
        for case, answer in zip(pending, answers):
            fresh[case["id"]] = compare(module, case, answer)
        return fresh, {case["id"]: per_call for case in pending}

    times = {}
    for fresh, elapsed in in_order(measure, batches):
        results.update(fresh)
        times.update(elapsed)
        print(f"correct-rounding complex: {len(results)}/{len(cases)}", flush=True)
    return {ident: [(*part, times.get(ident, "")) for part in parts]
            for ident, parts in results.items()}
