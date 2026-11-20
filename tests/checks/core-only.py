#!/usr/bin/env python3
"""Print the library modules that load no package.

A module of ``FloatLib.lean`` and ``FloatLib/`` is printed when every module that its imports
reach is one of Lean's own (``Init``, ``Std``, ``Lean``) or another printed module. A certificate
that imports only such modules loads in the time Lean itself takes. These modules do not load
Mathlib's source linters either, so ``tests/checks/linters.sh`` elaborates each of them once more
with ``Mathlib.Init`` imported.

The imports are read from the source text, one module per line of output. Python standard
library only.
"""
import re
from pathlib import Path

root = Path(__file__).resolve().parents[2]
sources = [root / 'FloatLib.lean'] + sorted((root / 'FloatLib').rglob('*.lean'))
imports = {}
for source in sources:
    name = '.'.join(source.relative_to(root).with_suffix('').parts)
    imports[name] = re.findall(
        r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', source.read_text(), re.M)

loads_package = {}


def package(module):
    """Whether `module` or a module it imports belongs to a package other than Lean."""
    if module not in loads_package:
        if module in imports:
            loads_package[module] = False  # A cycle would not compile; this ends the walk.
            loads_package[module] = any(package(name) for name in imports[module])
        else:
            loads_package[module] = module.split('.')[0] not in ('Init', 'Std', 'Lean')
    return loads_package[module]


for module in sorted(imports):
    if not package(module):
        print(module)
