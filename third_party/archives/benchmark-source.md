# Benchmark source archive notices

Archive: `benchmarks/results/main/provenance/FloatLib-source-public.tar.gz`

SHA-256: `cb642547e1752b8a38c4d2e3ac096d283159a4a8ee3af61f5494a00ffd7bc0d3`

The [archive member list](../benchmarks-archive-covered-members.txt) identifies
the third-party material under `tests/results/main/` and the archived website reader:

- `ecosystem/raw/fpbench/filter.expected.raw.txt`: FPBench FPCore
  fixture; [MIT license](../licenses/fpbench/LICENSE.txt).
- `ecosystem/raw/verificarlo/upstream-Dockerfile` and
  `upstream-docker-ci.yml`: Verificarlo sources;
  [license terms](../licenses/verificarlo/COPYING).
- `ecosystem/raw/exblas/applied-compatibility.patch`: Agner Fog Vector Class
  excerpts; [GPL-3.0-only notice and full license](../licenses/vectorclass/NOTICE.txt).
- `release/external/09-ibm-fpgen/*.map.tsv` and `*.stream`: original records
  and re-encoded cases; [IBM original notices](../licenses/ibm-fpgen/NOTICE.txt).
- Ecosystem logs contain identified source excerpts covered by the
  CORE-MATH, OpenLibm, RLIBM-ALL, Daisy/Leon, FPTaylor/OCaml interval,
  ReproBLAS, ExBLAS, Verificarlo, TBB and glibc packages in `third_party/`.
- `site/reader/`: [Conway adaptation notice](../licenses/conway/NOTICE.txt)
  and [Apache-2.0 license](../licenses/conway/LICENSE).

The nested test-source archive is covered by its [notice](test-source.md).

Keep this notice and the applicable [license files](../README.md) with copies of
the archive. IBM redistribution permission remains unverified.
