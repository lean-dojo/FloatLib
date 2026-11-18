#!/usr/bin/env python3
"""Check that interrupted kernel logs cannot supply truncated benchmark values."""
import importlib.util
from pathlib import Path
import tempfile

spec = importlib.util.spec_from_file_location(
    "collector", Path(__file__).with_name("collect-fixed-point-matrix.py"))
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)

with tempfile.TemporaryDirectory(prefix="fixed-collector-") as directory:
    path = Path(directory) / "kernel.log"
    first = (
        "FIXED_KERNEL first width=4096\n"
        "as written: 1.2 µs\n"
        "with the tagged kernel rules: 0.3 µs\n"
        "value: 123456789\n")
    last = (
        "FIXED_KERNEL last width=4096\n"
        "as written: 2.3 µs\n"
        "with the tagged kernel rules: 0.4 µs\n"
        "value: 987")
    path.write_text(first + last)
    try:
        collector.kernel_rows(path)
    except ValueError as error:
        assert "incomplete kernel normalization" in str(error)
    else:
        raise AssertionError("A truncated integer was accepted")
    rows, omitted = collector.kernel_rows(path, allow_incomplete_tail=True)
    assert set(rows) == {("first", 4096)}
    assert omitted == [dict(operation="last", width=4096)]
    assert rows[("first", 4096)]["kernel_value"] == 123456789

    path.write_text(first + last + "\n")
    rows, omitted = collector.kernel_rows(path)
    assert len(rows) == 2 and not omitted

    # A malformed interior row may not be discarded by the timeout exception.
    path.write_text(last + "\nunfinished\n" + first)
    path.write_text(path.read_text().replace("value: 987\n", "value: \n"))
    try:
        collector.kernel_rows(path, allow_incomplete_tail=True)
    except ValueError as error:
        assert "incomplete kernel normalization" in str(error)
    else:
        raise AssertionError("A malformed interior row was discarded")

    path.write_text(
        "FIXED_KERNEL countlsfx width=1024 tagged_only=true\n"
        "with the tagged kernel rules: 1.0 µs\nvalue: 4\n")
    rows, omitted = collector.kernel_rows(path)
    assert rows[("countlsfx", 1024)]["kernel_written_ns"] is None and not omitted
    path.write_text(path.read_text().replace("countlsfx", "unrelated"))
    try:
        collector.kernel_rows(path)
    except ValueError as error:
        assert "unexpected omitted baseline" in str(error)
    else:
        raise AssertionError("An undocumented missing baseline was accepted")

print("Fixed-point collector interruption checks passed.")
