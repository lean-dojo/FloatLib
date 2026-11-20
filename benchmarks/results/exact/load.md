# Time to load a check module

`lean` on a file that imports the named modules and proves one statement by `decide +kernel`: wall time and peak memory from `/usr/bin/time`, fastest of three runs. Written by `benchmarks/exact/run.sh load`.

| imports | modules loaded | wall | peak memory |
| --- | --- | --- | --- |
| core only: `FloatLib.Numerics.Kernel.Frac` | 3360 | 0.27 s | 461 MB |
| the proof module: `FloatLib.Numerics.Kernel.FracProof` | 17840 | 1.83 s | 2286 MB |
| `Frac` and one analysis module of Mathlib (`Mathlib.Analysis.SpecialFunctions.Log.Basic`) | 18255 | 1.83 s | 2453 MB |
| all of FloatLib: `FloatLib` | 36875 | 3.03 s | 4316 MB |
| all of Mathlib: `Mathlib` | 55645 | 4.62 s | 6566 MB |
