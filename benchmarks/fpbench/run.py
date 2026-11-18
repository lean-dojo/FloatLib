"""Inventory every FPCore program and measure all three roundoff routes."""

from __future__ import annotations
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import digest, merge_csv, prove, provenance, selected, write_csv, write_json
from fetch import fetch
from sexpr import Refusal, render
from translate import cores, translate
from numeric import numeric_case
import published
import historical


def run(output: Path):
    manifest = json.loads((HERE / "fpbench-source.json").read_text())
    source = fetch(HERE / "fpbench-source.json") / "benchmarks"
    fetch(HERE / "fptaylor-source.json")
    fetch(HERE / "daisy-source.json")
    references = published.references(HERE)
    write_json(output / "published.json", references)
    metadata, cases, numeric_cases = [], [], {}
    for path in sorted(source.glob("*.fpcore")):
        try:
            programs = list(cores(path))
        except (Refusal, ValueError) as error:
            metadata.append({"id": path.name, "status": "parse_refusal", "reason": str(error)})
            continue
        for index, name, args, attrs, body in programs:
            for precision in ("binary32", "binary64"):
                for method in ("forward", "closed", "backward"):
                    ident = f"{path.name}:{index}:{precision}:{method}"
                    row = {
                        "id": ident, "suite": "fpbench", "source_file": path.name,
                        "source_sha256": digest(path), "source_revision": manifest["revision"],
                        "index": index, "program": name, "default_precision": precision,
                        "method": method, "source_body": render(body),
                        "precondition": render(attrs.get(":pre", "TRUE")),
                        "bound_kind": "conditional Lean theorem; source domain not discharged",
                        "numeric_bound": "", "bound_ratio": "",
                        "numeric_status": "not_run",
                        "numeric_bound_reason": "Source-domain closure has not run",
                    }
                    row.update(published.attach(row, references))
                    try:
                        translated = translate(args, attrs, body, precision, method, ident)
                        row.update({k: v for k, v in translated.items()
                                    if k not in ("commands", "declaration")})
                        cases.append(translated)
                        try:
                            closure = numeric_case(
                                args, attrs, body, precision, method, translated)
                            numeric_cases[ident] = closure
                            row.update({k: v for k, v in closure.items()
                                        if k not in ("id", "commands", "declaration")})
                        except Refusal as error:
                            row.update(numeric_status="translation_refusal",
                                       numeric_bound_reason=str(error))
                    except Refusal as error:
                        row.update(status="translation_refusal", reason=str(error),
                                   numeric_status="translation_refusal",
                                   numeric_bound_reason=str(error))
                    metadata.append(row)
    write_json(output / "provenance.json", provenance())
    write_json(output / "inventory.json", metadata)
    write_json(output / "plan.json", cases)
    write_json(output / "numeric-plan.json", list(numeric_cases.values()))
    # A deterministic selection is explicit in provenance; omitted rows remain "not_run".
    results = prove(selected(cases), output / "proofs",
                    batch_size=int(os.environ.get("FLOATLIB_SUITE_BATCH", "1")),
                    timeout=int(os.environ.get("FLOATLIB_SUITE_TIMEOUT", "45")))
    by_id = {row["id"]: row for row in results}
    enabled = os.environ.get("FLOATLIB_NUMERIC", "1") != "0"
    closures = [numeric_cases[row["id"]] for row in results
                if row["status"] == "proved" and row["id"] in numeric_cases] if enabled else []
    closed = prove(closures, output / "numeric-proofs", batch_size=1,
                   timeout=int(os.environ.get("FLOATLIB_NUMERIC_TIMEOUT", "45")))
    numeric_results = {row["id"].removesuffix(":numeric"): row for row in closed}
    for row in metadata:
        row.update(by_id.get(row["id"], {}))
        row.setdefault("status", "not_run")
        row.setdefault("reason", "" if row["status"] == "proved" else "Outside the selected proof range")
        if row["id"] in numeric_results:
            result = numeric_results[row["id"]]
            row.update(numeric_status=result["status"],
                       numeric_bound_reason=result["reason"],
                       numeric_elapsed_ns=result["elapsed_ns"],
                       numeric_statement=result["statement"],
                       numeric_axioms=result["axioms"],
                       numeric_plan=result["plan"],
                       numeric_plan_sha256=result["plan_sha256"],
                       numeric_log=result["log"],
                       numeric_measurement_utc=result["measurement_utc"],
                       numeric_process_elapsed_seconds=result["process_elapsed_seconds"],
                       numeric_process_sampled_peak_rss_kib=result["process_sampled_peak_rss_kib"])
            if result["status"] == "proved":
                row.update(numeric_bound=row["proposed_bound"],
                           bound_kind="Lean-checked absolute error on finite source-domain inputs")
        elif row["numeric_status"] == "not_run" and row["id"] in by_id:
            row.update(numeric_status="not_attempted",
                       numeric_bound_reason=("Disabled by FLOATLIB_NUMERIC=0" if not enabled else
                                             "Generated theorem did not pass"))
    merge_csv(output / "results.csv", metadata)
    historical.audit(output)
    return metadata


if __name__ == "__main__":
    run(Path(sys.argv[1]).resolve())
