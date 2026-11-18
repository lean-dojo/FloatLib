"""Compile small capability probes and one source-derived roundoff resource case."""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "fpbench"))
from common import prove, provenance, write_csv, write_json


def by_imports(cases):
    """Probes grouped by the modules they add to the proof runner, in file order."""
    groups = {}
    for case in cases:
        groups.setdefault(tuple(case.get("imports", ())), []).append(case)
    return groups


def check(cases, output, timeout):
    """One runner per import set; each probe is its own process."""
    results = []
    for imports, group in by_imports(cases).items():
        results.extend(prove(group, output / "proofs", batch_size=1, timeout=timeout,
                             imports=imports))
    order = {case["id"]: index for index, case in enumerate(cases)}
    return sorted(results, key=lambda row: order[row["id"]])


def probe(output, identifiers):
    """Recheck requested entry points, using the proof cache for this exact checkout."""
    cases = json.loads((HERE / "repro/capabilities.json").read_text())
    selected = [case for case in cases if case["id"] in identifiers]
    if {case["id"] for case in selected} != set(identifiers):
        raise ValueError("Unknown capability probe")
    write_json(output / "plan.json", selected)
    results = check(selected, output, 60)
    write_csv(output / "results.csv", results)
    return {row["id"]: row for row in results}


def evidence(row):
    """Keep the tested interface and its compiler evidence beside each refusal."""
    return {
        "capability_probe_id": row["id"],
        "capability_probe_status": row["status"],
        "capability_probe_reason": row["reason"],
        "capability_probe_commit": row["floatlib_commit"],
        "capability_probe_plan_sha256": row["plan_sha256"],
        "capability_probe_log": str(Path("capabilities") / row["log"]),
    }


def run(output):
    from fetch import fetch
    from translate import cores, translate

    cases = json.loads((HERE / "repro/capabilities.json").read_text())
    source = fetch(HERE.parent / "fpbench/fpbench-source.json")
    for index, name, args, attrs, body in cores(source / "benchmarks/daisy.fpcore"):
        if "determinant" in name.lower():
            cases.append(translate(args, attrs, body, "binary32", "forward",
                                   f"daisy.fpcore:{index}:binary32:forward"))
            break
    write_json(output / "provenance.json", provenance())
    write_json(output / "plan.json", cases)
    write_csv(output / "results.csv", check(cases, output, 45))


if __name__ == "__main__":
    run(Path(sys.argv[1]).resolve())
