"""Conservatively compare FPBench expressions with native regression exports."""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import digest, provenance, write_csv, write_json
from contracts import local_contract
from numeric import source_box
from published import ALIASES, normalized, references
from sexpr import Refusal, number, properties
from translate import cores


FORMATS = {"binary32": (24, -149, 127), "binary64": (53, -1074, 1023)}


def exact(value: Fraction, precision: str) -> bool:
    """Whether a rational is an exactly representable finite IEEE value."""
    if not value:
        return True
    significand, denominator = abs(value.numerator), value.denominator
    if denominator & (denominator - 1):
        return False
    exponent = -(denominator.bit_length() - 1)
    while significand % 2 == 0:
        significand //= 2
        exponent += 1
    bits, minimum, maximum = FORMATS[precision]
    return (significand.bit_length() <= bits and exponent >= minimum
            and exponent + significand.bit_length() - 1 <= maximum)


def stored_formats(precision):
    return frozenset(("binary32", "binary64") if precision == "binary32" else (precision,))


@dataclass(frozen=True)
class Node:
    tree: tuple
    exact_formats: frozenset


def expression(node, env, precision, rounding):
    if precision not in (*FORMATS, "real"):
        raise Refusal("Unsupported canonical precision: " + precision)
    if rounding not in ("nearestEven", "toPositive", "toNegative", "toZero"):
        raise Refusal("Unsupported canonical rounding: " + rounding)
    if isinstance(node, str):
        if node in env:
            return env[node]
        value = number(node)
        if not value and node.startswith("-"):
            raise Refusal("Negative-zero literals need a separate exporter audit")
        tree = ("literal", str(value))
        exact_formats = frozenset(p for p in FORMATS if exact(value, p))
        if precision == "real" or precision in exact_formats:
            return Node(tree, exact_formats)
        return Node(("round", precision, rounding, tree), stored_formats(precision))
    if not isinstance(node, list) or not node:
        raise Refusal("Malformed expression")
    op, *args = node
    if op == "!":
        attrs, body = properties(args)
        if len(body) != 1 or set(attrs) - {":precision", ":round"}:
            raise Refusal("Unsupported expression annotation")
        return expression(body[0], env, attrs.get(":precision", precision),
                          attrs.get(":round", rounding))
    if op in ("let", "let*"):
        if len(args) != 2:
            raise Refusal("Malformed binding")
        scope = dict(env)
        for name, value in args[0]:
            scope[name] = expression(value, scope if op == "let*" else env,
                                     precision, rounding)
        return expression(args[1], scope, precision, rounding)
    children = [expression(child, env, precision, rounding) for child in args]
    if op == "cast" and len(children) == 1:
        child = children[0]
        if precision == "real" or precision in child.exact_formats:
            return child
        return Node(("round", precision, rounding, child.tree), stored_formats(precision))
    if op == "-" and len(children) == 1:
        child = children[0]
        tree = ("neg", child.tree)
        if precision == "real" or precision in child.exact_formats:
            return Node(tree, child.exact_formats)
        return Node(("round", precision, rounding, tree), stored_formats(precision))
    arities = {"+": 2, "-": 2, "*": 2, "/": 2, "fma": 3, "sqrt": 1, "exp": 1, "log": 1}
    if op not in arities or arities[op] != len(children):
        raise Refusal(f"Unsupported canonical operator: {op}/{len(children)}")
    tree = ("op", precision, rounding, op, tuple(child.tree for child in children))
    return Node(tree, frozenset() if precision == "real" else stored_formats(precision))


def box(pre, names):
    """Require every condition to be a closed variable/constant box relation."""
    if not isinstance(pre, list) or not pre:
        raise Refusal("Not a closed box")
    if pre[0] == "and":
        for part in pre[1:]:
            box(part, names)
    elif pre[0] in ("<=", ">=") and len(pre) >= 3:
        for a, b in zip(pre[1:], pre[2:]):
            if isinstance(a, str) and a in names:
                number(b)
            elif isinstance(b, str) and b in names:
                number(a)
            else:
                raise Refusal("Non-variable box relation")
    else:
        raise Refusal("Not exclusively a closed box")


def canonical(args, attrs, body, default, stored):
    if not all(isinstance(arg, str) for arg in args) or len(args) != len(set(args)):
        raise Refusal("Nonplain or duplicate arguments")
    declared = attrs.get(":precision", default)
    if declared not in ("real", stored):
        raise Refusal("Published input format differs from stored input format")
    pre = attrs.get(":pre", "TRUE")
    box(pre, set(args))
    bounds = source_box(pre, args)
    env = {name: Node(("input", name), stored_formats(stored)) for name in args}
    tree = expression(body, env, declared, attrs.get(":round", "nearestEven")).tree
    return {
        "stored_precision": stored,
        "domain": {name: [str(x) for x in values] for name, values in sorted(bounds.items())},
        "expression": tree,
    }


def signature(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def tests():
    assert exact(Fraction(1, 1 << 149), "binary32")
    assert not exact(Fraction(1, 1 << 150), "binary32")
    assert exact(Fraction((1 << 24) - 1) * (1 << 104), "binary32")
    assert not exact(Fraction(1 << 128), "binary32")
    assert not exact(Fraction(1, 10), "binary64")
    env = {"x": Node(("input", "x"), stored_formats("binary64"))}
    direct = expression(["+", "x", "1"], env, "binary64", "nearestEven")
    assert direct == expression(["+", ["cast", "x"], "1"], env, "binary64", "nearestEven")
    assert direct != expression(["+", "x", "1"], env, "real", "nearestEven")
    assert direct != expression(["+", "x", "1"], env, "binary32", "nearestEven")
    assert direct != expression(["+", "x", "1"], env, "binary64", "toZero")
    assert expression("0.1", env, "real", "nearestEven") != expression(
        "0.1", env, "binary64", "nearestEven")
    left = expression(["+", ["+", "x", "1"], "2"], env, "binary64", "nearestEven")
    right = expression(["+", "x", ["+", "1", "2"]], env, "binary64", "nearestEven")
    assert left != right
    parallel = expression(["let", [["x", "1"], ["y", "x"]], ["+", "x", "y"]],
                          env, "binary64", "nearestEven")
    sequential = expression(["let*", [["x", "1"], ["y", "x"]], ["+", "x", "y"]],
                            env, "binary64", "nearestEven")
    assert parallel != sequential
    narrow = expression(["!", ":precision", "binary32", ["cast", "x"]],
                        env, "binary64", "nearestEven")
    assert narrow.tree != env["x"].tree
    try:
        box(["and", ["<=", "0", "x", "1"], ["<", "x", "1"]], {"x"})
    except Refusal:
        pass
    else:
        raise AssertionError("A strict extra constraint was silently discarded")


def audit(output: Path):
    """Audit native published exports against the pinned FPBench sources."""
    export_root = HERE / "published-fptaylor"
    exports = json.loads((export_root / "manifest.json").read_text())
    exported = {row["input_file"]: row for row in exports["exports"]}
    published = [row for row in references(HERE)
                 if row["provenance_kind"] == "published project regression artifact"
                 and row["tool"] == "fptaylor"]
    rows = []
    source = HERE / "upstream/fpbench/benchmarks"
    for path in sorted(source.glob("*.fpcore")):
        for index, name, args, attrs, body in cores(path):
            key = normalized(name)
            keys = ALIASES.get(key, (key,))
            candidates = [row for row in published if normalized(row["program"]) in keys]
            for default in FORMATS:
                for reference in candidates:
                    record = {
                        "source_file": path.name, "index": index, "program": name,
                        "default_precision": default, "source_sha256": digest(path),
                        "reference_input": reference["input_file"],
                        "reference_input_sha256": reference["input_sha256"],
                        "reference_bound": reference["numeric_bound"],
                        "reference_revision": reference["tool_revision"],
                        "reference_artifact": reference["artifact"],
                        "reference_artifact_sha256": reference["artifact_sha256"],
                        "reference_configuration": reference["configuration"],
                        "reference_configuration_sha256": reference["configuration_sha256"],
                        "reference_elapsed_seconds": reference["elapsed_seconds"],
                        "reference_time_policy": reference["time_policy"],
                        "effective_precision": attrs.get(":precision", default),
                        "auditor_sha256": digest(Path(__file__)),
                        "status": "unmatched", "reason": "",
                    }
                    try:
                        contract = local_contract("fptaylor", args, attrs, body, default)
                        if contract["comparison_contract"] != "compatible_stored_inputs":
                            raise Refusal(contract["comparison_reason"])
                        item = exported[reference["input_file"]]
                        if exports["source_revision"] != reference["tool_revision"]:
                            raise Refusal("Regression source revision mismatch")
                        if item["input_sha256"] != reference["input_sha256"]:
                            raise Refusal("Regression input hash mismatch")
                        input_path = HERE / "upstream/fptaylor" / reference["input_file"]
                        if digest(input_path) != item["input_sha256"]:
                            raise Refusal("Regression source bytes changed")
                        rounding_tokens = set(re.findall(
                            r"\brnd[A-Za-z0-9_]*(?:\[[^\]]*\])?", input_path.read_text()))
                        if rounding_tokens - {"rnd", "rnd64"}:
                            raise Refusal("Nondefault rounding needs a separate exporter audit")
                        exported_path = export_root / item["output_file"]
                        if digest(exported_path) != item["output_sha256"]:
                            raise Refusal("Export bytes changed")
                        programs = list(cores(exported_path))
                        if len(programs) != 1:
                            raise Refusal("Multiple exported expressions")
                        _, _, other_args, other_attrs, other_body = programs[0]
                        if other_attrs.get(":precision") != "real":
                            raise Refusal("Historical input-rounding convention needs a separate audit")
                        stored = attrs.get(":precision", default)
                        original = canonical(args, attrs, body, default, stored)
                        historical = canonical(other_args, other_attrs, other_body, "binary64", stored)
                        record.update(source_contract_sha256=signature(original),
                                      reference_contract_sha256=signature(historical),
                                      reference_export_sha256=item["output_sha256"])
                        if original != historical:
                            differing = [key for key in original if original[key] != historical[key]]
                            raise Refusal("Canonical contracts differ in " + ", ".join(differing))
                        record.update(status="compatible_stored_inputs",
                                      reason="Identical rounded expression and closed box after exact "
                                      "casts, literal normalization and let expansion; historical real "
                                      "inputs contain the finite stored inputs")
                    except (Refusal, ValueError, TypeError, KeyError) as error:
                        record["reason"] = str(error)
                    rows.append(record)
    write_csv(output / "published-contracts.csv", rows)
    write_json(output / "published-contracts-provenance.json", {
        **provenance(),
        "auditor_sha256": digest(Path(__file__)),
        "export_manifest_sha256": digest(export_root / "manifest.json"),
        "rows": len(rows),
        "matched": sum(row["status"] == "compatible_stored_inputs" for row in rows),
        "scope": "Syntactic contract audit; external analyzer soundness is not proved in Lean.",
    })
    print(f"Audited {len(rows)} name candidates; "
          f"{sum(row['status'] == 'compatible_stored_inputs' for row in rows)} match.")
    return rows


if __name__ == "__main__":
    audit(Path(sys.argv[1]).resolve())
