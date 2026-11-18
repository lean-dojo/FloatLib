#!/usr/bin/env python3
"""Resume a generated fixed-point matrix after its last fully normalized row."""
import argparse
import importlib.util
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("source", type=Path)
parser.add_argument("interrupted_log", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()

spec = importlib.util.spec_from_file_location(
    "collector", Path(__file__).with_name("collect-fixed-point-matrix.py"))
collector = importlib.util.module_from_spec(spec)
spec.loader.exec_module(collector)
complete, omitted = collector.kernel_rows(args.interrupted_log, allow_incomplete_tail=True)
source = args.source.read_text()
markers = list(re.finditer(
    r'^#print "FIXED_KERNEL (.+) width=(\d+)(?: tagged_only=true)?"\n', source, re.M))
keys = [(marker.group(1), int(marker.group(2))) for marker in markers]
if set(keys[:len(complete)]) != complete.keys():
    raise ValueError("The accepted log rows must be an exact prefix of the source")
if len(complete) >= len(markers):
    raise ValueError("The source has no unfinished operations")
start = markers[len(complete)].start()
args.output.write_text(source[:markers[0].start()] + source[start:])
print(f"Accepted {len(complete)} complete rows; "
      f"resuming {len(markers) - len(complete)} rows at {keys[len(complete)]}.")
print(f"Omitted incomplete log tail: {omitted}")
