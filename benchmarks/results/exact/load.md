# Time to load a check module

`lean` on a file that imports the named modules and proves one statement by `decide +kernel`: wall time and peak memory from `/usr/bin/time`, fastest of three runs. Written by `benchmarks/exact/run.sh load`.

| imports | modules loaded | wall | peak memory |
| --- | --- | --- | --- |
| core only: `FloatLib.Numerics.Kernel.Frac` | 12615 | 1.11 s | 1639 MB |
| the proof module: `FloatLib.Numerics.Kernel.FracProof` | 17840 | 1.63 s | 2274 MB |
| `Frac` and one analysis module of Mathlib (`Mathlib.Analysis.SpecialFunctions.Log.Basic`) | 22060 | 2.01 s | 2841 MB |
| all of FloatLib: `FloatLib` | 36615 | 2.95 s | 4301 MB |
| all of Mathlib: `Mathlib` | 57740 | 4.81 s | 6796 MB |
