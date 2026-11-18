"""Export the same FPBench inputs with its own exporter and run serial CLI analyses.

Export warnings, byte hashes, commands, resource limits, and independent tool timings
are retained. Sollya receives a byte-preserving copy with a final quit command to
terminate its interpreter. A successful load is not reported as a roundoff bound.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import digest, merge_csv, provenance, write_json
from fetch import fetch
from process import run as measured
from sexpr import render
from translate import cores
from contracts import local_contract


LANGUAGES = {"fptaylor": "fptaylor", "gappa": "gappa", "daisy": "scala",
             "sollya": "sollya", "smtlib": "smt2", "satire": None}


def tool_selection(text):
    selected = set(text.split(",")) if text else set(LANGUAGES)
    unknown = selected - set(LANGUAGES)
    if unknown:
        raise ValueError("Unknown CLI tools: " + ", ".join(sorted(unknown)))
    return selected


def dyadic(text: str) -> Fraction:
    """Read Gappa's exact integer/exponent syntax and OCaml hexadecimal floats."""
    text = text.split("{", 1)[0].strip()
    if "0x" in text.lower():
        return Fraction.from_float(float.fromhex(text))
    match = re.fullmatch(r"(-?\d+)b([+-]?\d+)", text)
    if match:
        return Fraction(int(match[1])) * Fraction(2) ** int(match[2])
    return Fraction(text)


def bound(tool: str, text: str) -> tuple[str, str]:
    if tool == "fptaylor":
        values = []
        for line in text.splitlines():
            if re.match(r"Absolute error \((?:exact|approximate)\):", line):
                value = re.search(r"\(([-+]?0x[0-9a-f.p+-]+)\)", line)
                token = value[1] if value else line.split(":", 1)[1].split()[0]
                try:
                    values.append(dyadic(token))
                except (ValueError, OverflowError):
                    pass
        if values:
            return str(min(values)), "absolute_error"
    elif tool == "gappa":
        # Gappa prints the requested enclosure on a separate interval line.
        matches = re.findall(r"in\s+\[\s*([^,;\]]+)\s*,\s*([^;\]]+)", text)
        values = []
        for lower, upper in matches:
            try:
                values.append(max(abs(dyadic(lower)), abs(dyadic(upper))))
            except (ValueError, OverflowError):
                pass
        if len(values) == 1:
            return str(values[0]), "absolute_error"
    elif tool == "daisy":
        match = re.search(r"Absolute error:\s*([0-9.eE+-]+)", text)
        if match:
            return str(Fraction(match[1])), "absolute_error_displayed_decimal"
    return "", ""


def input_core(args, attrs, body, precision) -> str:
    properties = dict(attrs)
    properties.setdefault(":precision", precision)
    # The original identifier is not semantically significant; names and all
    # properties remain. The input is one complete standard FPCore form.
    return render(["FPCore", args,
                   *(item for pair in properties.items() for item in pair), body]) + "\n"


def run(output: Path):
    output.mkdir(parents=True, exist_ok=True)
    source = fetch(HERE / "fpbench-source.json")
    config_file = os.environ.get("FLOATLIB_TOOL_CONFIG")
    config = json.loads(Path(config_file).read_text()) if config_file else {}
    racket = config.get("racket", {}).get("executable") or shutil.which("racket")
    env = {**os.environ, **config.get("environment", {})}
    context = provenance()
    context.update(exporter_revision=json.loads((HERE / "fpbench-source.json").read_text())["revision"],
                   configuration=config, time_definition="wall clock per CLI invocation; export separate")
    write_json(output / "provenance.json", context)
    timeout = int(os.environ.get("FLOATLIB_TOOL_TIMEOUT", "30"))
    selected_tools = tool_selection(os.environ.get("FLOATLIB_CLI_TOOLS", ""))
    offset = int(os.environ.get("FLOATLIB_SUITE_OFFSET", "0"))
    limit = int(os.environ.get("FLOATLIB_SUITE_LIMIT", "1000000"))
    rows = []
    index = 0
    for path in sorted((source / "benchmarks").glob("*.fpcore")):
        for ordinal, name, args, attrs, body in cores(path):
            for precision in ("binary32", "binary64"):
                core = input_core(args, attrs, body, precision)
                core_hash = hashlib.sha256(core.encode()).hexdigest()
                directory = output / "cases" / core_hash
                selected = offset <= index < offset + limit
                index += 1
                for tool, extension in LANGUAGES.items():
                    row = {
                        "id": f"{path.name}:{ordinal}:{precision}:{tool}",
                        "source_file": path.name, "source_sha256": digest(path),
                        "index": ordinal, "program": name, "default_precision": precision,
                        "effective_precision": attrs.get(":precision", precision),
                        "tool": tool, "input_sha256": core_hash, "status": "not_run",
                        "reason": "Outside selected program range", "numeric_bound": "",
                        "bound_kind": "", "elapsed_seconds": "", "export_seconds": "",
                        "floatlib_commit": context["floatlib_commit"],
                        "tracked_diff_sha256": context["tracked_diff_sha256"],
                        "time_definition": context["time_definition"],
                        "measurement_utc": "",
                    }
                    row.update(local_contract(tool, args, attrs, body, precision))
                    if not selected or tool not in selected_tools:
                        if selected:
                            row["reason"] = "Outside the selected CLI tool set"
                        rows.append(row)
                        continue
                    directory.mkdir(parents=True, exist_ok=True)
                    settings = config.get(tool, {})
                    row["tool_version"] = settings.get("version", "")
                    row["tool_revision"] = settings.get("revision", "")
                    if tool == "satire":
                        row.update(
                            status="tool_unavailable",
                            reason=settings.get("reason", "No audited local Satire CLI adapter"),
                            measurement_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
                        rows.append(row)
                        continue
                    inp = directory / "input.fpcore"
                    inp.write_text(core)
                    exported = directory / ("input." + extension)
                    export_log = directory / (tool + ".export.log")
                    row["measurement_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                    if not racket:
                        row.update(status="exporter_unavailable", reason="Racket is not configured")
                        rows.append(row)
                        continue
                    command = [racket, "-y", str(source / "export.rkt"), str(inp), str(exported)]
                    row["export_command"] = command
                    result = measured(command, cwd=source, log=export_log, env=env, timeout=timeout)
                    row.update(export_seconds=result["elapsed_seconds"],
                               export_exit=result["exit_code"],
                               export_log=str(export_log.relative_to(output)),
                               export_warnings=export_log.read_text(errors="replace")[-8000:])
                    write_json(directory / (tool + ".export.usage.json"), result)
                    if result["exit_code"] != 0 or not exported.exists():
                        row.update(status="export_refusal",
                                   reason=result["termination"] or row["export_warnings"])
                        rows.append(row)
                        continue
                    row["export_sha256"] = digest(exported)
                    if tool == "smtlib":
                        row.update(status="exported", reason="SMT-LIB interchange file; no error-bound analyzer requested")
                        rows.append(row)
                        continue
                    executable = settings.get("executable") or shutil.which(tool)
                    row["tool_version"] = settings.get("version", "")
                    row["tool_revision"] = settings.get("revision", "")
                    if not executable:
                        row.update(status="tool_unavailable",
                                   reason=settings.get("reason", "Plain CLI is not installed"))
                        rows.append(row)
                        continue
                    cwd = Path(settings.get("cwd", directory))
                    local_env = {**env, **settings.get("environment", {})}
                    arguments = settings.get("arguments", [])
                    command = [executable, *arguments, str(exported)]
                    if tool == "fptaylor":
                        tmp = directory / "fptaylor-tmp"
                        tmp.mkdir(exist_ok=True)
                        command[1:1] = ["--tmp-base-dir", str(tmp), "--tmp-date", "false",
                                        "--opt-timeout", str(max(100, (timeout - 5) * 1000)),
                                        "--print-precision", "17", "--print-hex-floats", "true"]
                    if tool == "sollya":
                        # Sollya 8.0 returns 3 at EOF after a valid procedure declaration.
                        # Retain the original export and hash the terminated input separately.
                        terminated = directory / "input.terminated.sollya"
                        terminated.write_bytes(exported.read_bytes() + b"\nquit;\n")
                        command[-1] = str(terminated)
                        row["invocation_input_sha256"] = digest(terminated)
                        row["invocation_adaptation"] = "Append newline and quit; after unchanged export bytes"
                        command[1:1] = ["--nocolor", "--warnonstderr", "--flush"]
                    if tool == "daisy":
                        # FPBench exports operation/argument precisions in this sidecar.
                        precision_map = Path(str(exported) + ".prec.txt")
                        if precision_map.exists():
                            command[1:1] = ["--mixed-precision=" + str(precision_map)]
                            row["precision_map_sha256"] = digest(precision_map)
                        effective = attrs.get(":precision", precision)
                        if effective not in ("binary32", "binary64"):
                            row.update(status="tool_configuration_refusal",
                                       reason=f"Daisy precision mapping is not audited: {effective}")
                            rows.append(row)
                            continue
                        command[1:1] = ["--precision=" + {
                            "binary32": "Float32", "binary64": "Float64"}[effective]]
                    tool_log = directory / (tool + ".log")
                    row["command"] = command
                    result = measured(command, cwd=cwd, env=local_env, log=tool_log, timeout=timeout)
                    write_json(directory / (tool + ".usage.json"), result)
                    text = tool_log.read_text(errors="replace")
                    row.update(elapsed_seconds=result["elapsed_seconds"],
                               exit_code=result["exit_code"],
                               sampled_peak_rss_kib=result["sampled_peak_rss_kib"],
                               log=str(tool_log.relative_to(output)))
                    if result["exit_code"] != 0:
                        row.update(
                            status=result["termination"] or "tool_refusal",
                            reason=text[-8000:] or
                            f"CLI exited with code {result['exit_code']} without diagnostics")
                    elif tool == "sollya":
                        row.update(status="loaded_no_bound",
                                   reason="The FPBench Sollya exporter defines procedures; loading them is not uniform error analysis")
                    else:
                        numeric, kind = bound(tool, text)
                        row.update(status="bounded" if numeric else "no_bound",
                                   numeric_bound=numeric, bound_kind=kind,
                                   reason="" if numeric else text[-8000:])
                    rows.append(row)
                merge_csv(output / "partial.csv", rows)
                if selected:
                    print(f"FPBench tools: {index}: {path.name}:{ordinal}:{precision}", flush=True)
    merge_csv(output / "results.csv", rows)
    return rows


if __name__ == "__main__":
    run(Path(sys.argv[1]).resolve())
