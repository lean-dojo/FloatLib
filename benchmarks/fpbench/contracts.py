"""Conservative source-contract audit for local exporter comparisons.

This audit identifies a syntactic subset whose FPTaylor export rounds each
constant and operation, with unrounded variables and the same closed box.
FPTaylor's continuous input domain contains the representable input values
quantified by the Lean theorem. Its bound therefore applies to those values.
This is an exporter audit, not a proof of the external analyzer's soundness.
"""
from sexpr import Refusal, number
from numeric import source_box
from polynomial import polynomial_guard


def local_contract(tool, args, attrs, body, default_precision):
    if tool not in ("fptaylor", "gappa"):
        return {
            "comparison_contract": "unmatched",
            "comparison_reason": {
                "daisy": (
                    "Rounded literal emission needs a source-contract audit; the CLI "
                    "bound is a displayed decimal converted through binary64"),
                "satire": "Local analyzer unavailable; published contracts require separate audit",
                "sollya": "Exported procedures do not supply a uniform roundoff bound",
                "smtlib": "Interchange export does not supply a roundoff bound",
            }[tool],
        }
    try:
        if not all(isinstance(arg, str) for arg in args):
            raise Refusal("Annotated or tensor arguments are outside the comparison audit")
        if attrs.get(":precision", default_precision) not in ("binary32", "binary64"):
            raise Refusal("Precision is outside the comparison audit")
        if attrs.get(":round", "nearestEven") not in (
                "nearestEven", "toPositive", "toNegative", "toZero"):
            raise Refusal("Rounding mode is outside the comparison audit")
        if ":var-precision" in attrs:
            raise Refusal("Legacy input precision property needs a separate audit")

        def endpoint(node):
            if not isinstance(node, str) or node in args:
                return False
            try:
                number(node)
                return True
            except (ValueError, ZeroDivisionError):
                return False

        def box_condition(node):
            if not isinstance(node, list) or not node:
                return False
            if node[0] == "and":
                return all(box_condition(part) for part in node[1:])
            if node[0] not in ("<=", ">=") or len(node) < 3:
                return False
            return all(
                (isinstance(a, str) and a in args and endpoint(b))
                or (isinstance(b, str) and b in args and endpoint(a))
                for a, b in zip(node[1:], node[2:]))

        precondition = attrs.get(":pre", "TRUE")
        if not box_condition(precondition):
            raise Refusal("Precondition is not exclusively a closed conjunctive variable box")
        source_box(precondition, args)

        def expression(node, names):
            if isinstance(node, str):
                if node not in names:
                    value = number(node)
                    if not value and node.startswith("-"):
                        raise Refusal("Negative-zero literals need a separate exporter audit")
                return
            if not isinstance(node, list) or not node:
                raise Refusal("Malformed expression")
            op, *values = node
            if op in ("let", "let*"):
                scope = set(names)
                for name, value in values[0]:
                    expression(value, scope if op == "let*" else names)
                    scope.add(name)
                expression(values[1], scope)
                return
            arities = {"+": (2,), "-": (1, 2), "*": (2,), "/": (2,),
                       "fma": (3,), "sqrt": (1,), "exp": (1,), "log": (1,)}
            if op not in arities or len(values) not in arities[op]:
                raise Refusal(f"Operator or annotation outside comparison audit: {op}")
            for value in values:
                expression(value, names)

        expression(body, set(args))
        if tool == "gappa":
            magnitude = polynomial_guard(
                args, attrs, body, attrs.get(":precision", default_precision))
            return {
                "comparison_contract": "compatible_stored_inputs",
                "comparison_reason": (
                    "Same integer polynomial and exact closed box; all rounded operations "
                    "pass the finite-magnitude guard. Rounded real inputs include stored inputs"),
                "comparison_maximum_pre_round_magnitude": str(magnitude),
            }
    except (Refusal, ValueError, ZeroDivisionError) as error:
        return {"comparison_contract": "unmatched", "comparison_reason": str(error)}
    return {
        "comparison_contract": "compatible_stored_inputs",
        "comparison_reason": (
            "Same rounded expression and closed box; FPTaylor's continuous unrounded "
            "input domain contains the stored finite inputs of the Lean theorem"),
    }
