# Building and editing the website

We build the website from the guide's Markdown chapters and declarations exported from Lean.
The build checks examples, links, and figures as part of producing the reader.
Run these commands from the repository root after building the library.
The full build needs Python 3.12, Matplotlib 3.11.0 (the version used for the
checked figures), Node.js, Corepack, and rsync. Install Matplotlib in your Python environment:

```bash
python3 -m pip install matplotlib==3.11.0
```

The reader's JavaScript dependencies are installed from its lockfile during the build.

```bash
source tests/lib/lake.sh
OUT_DIR="${FLOATLIB_BUILD_DIR}-site" bash site/build.sh
python3 site/serve.py --port 10000 --dir "${FLOATLIB_BUILD_DIR}-site"
```

Open `http://localhost:10000/`. The build checks the chapter examples with Lean, compares their
printed results, resolves theorem links and citations, verifies result-derived figures, and
renders the reader. Edit the chapters under `site/content/chapters/`; there is no separate
manual to update.

## Site data pipeline

The exporter writes declarations from the built library to `site/data/nodes.json`.
The [website specification](../SITE_SPEC.md) describes the fields and how the reader uses them.

```bash
site/tooling/export.sh              # Lean export + Python reduce
site/tooling/export.sh --skip-lean  # reuse last raw export while editing the reader's prose
```

The exporter first runs `lake -KbuildDir="$FLOATLIB_BUILD_DIR" build` on the modules in
`site/content/phases.json`: `FloatLib`, the opt-in `NativeFPU.Unchecked`, and
`Configured.Transcendentals`. A default `lake build` does not build those optional modules.
`ExportNodes.lean` then imports them, resolves every listed constant, and writes
each declaration's kind, signature, docstring, module, source range, axioms, and dependencies.
Unresolved or duplicate names stop the export. Python then reduces the graph, attaches
GitHub URLs, validates the data, and writes `nodes.json`.

This data supports links from the book to individual Lean declarations and the **Guide declarations**
view at `#/graph?view=declarations`. That graph contains the guide's selected definitions and theorems.
The **All library modules** view at `#/graph` is generated from every library source import header,
including meta imports.

Build artifacts stay on local disk. `tests/lib/lake.sh` selects `FLOATLIB_BUILD_DIR`;
the site tools append these suffixes to that path:

| Output | Default path | Override |
| --- | --- | --- |
| Raw Lean export | `${FLOATLIB_BUILD_DIR}-site-data/nodes.raw.json` | `export_atlas.py --raw` |
| Extracted Lean files and full-build check report | `${FLOATLIB_BUILD_DIR}-site-check/` | `FLOATLIB_SITE_SCRATCH` or `check_chapters.py --scratch` |
| Reader mirror, dependencies, and intermediate files | `${FLOATLIB_BUILD_DIR}-site-reader/` | `BUILD_DIR` |
| Finished static site | `${FLOATLIB_BUILD_DIR}-site/` | `OUT_DIR` |
| Python cache during the full site build | `${FLOATLIB_BUILD_DIR}-site-pycache/` | `PYTHONPYCACHEPREFIX` |

These defaults also apply when the exporter, checker, or reader build is invoked separately.
Keep any overrides on local storage. If the Lake path helper fails, the Python tools stop;
they do not fall back to `.lake/build` in the checkout. `--skip-lean` reuses the raw export,
so the first export needs to run without that flag.
The reader's declaration data and warnings (`site/data/nodes.json` and
`site/data/reader-warnings.md`) remain in the checkout. Rendered chapters and the overview's HTML
are included in the reader's `public/data/site.json`. The build requires the exported declaration
data, chapters, landing page, and references.

## Nodes

We group declarations into phases in `site/content/phases.json`. Each phase has an `id`,
`title`, and ordered list of `nodes`. A node can give a `name` and optional `title`, or
just a Lean name; in that case its title comes from the first docstring sentence.

The exporter requires unique, resolved names, valid dependencies and source ranges, titles
without em or en dashes, and at least one node per phase. Cross-phase dependencies produce
warnings. Chapter links use `[[Full.Lean.Name]]`; `check_chapters.py` warns if a chapter
names a missing node.

## Chapter checks

`check_chapters.py` compiles each chapter ` ```lean ` block and compares `-- ` result comments
with Lean's output. ` ```lean standalone ` compiles as its own file. `nocheck` skips (warning).
`site/build.sh` enables strict checks and fails on warnings unless `FLOATLIB_SITE_STRICT=0`.

## Source links during editing

URLs point at `HEAD`; excerpts follow the worktree. Dirty nodes drop the `#L..` fragment (or the
URL, if the file is untracked). `site/build.sh --require-clean` refuses a dirty library.
Before the first commit, `source.revision` is `null`, the diff digest is absent, and every
declaration is marked uncommitted with no GitHub URL. Local builds still run all checks;
`--require-clean` also refuses this state.

## Export behavior

- The trust phase shows `@[csimp]` lemmas and the unchecked host API. The full axiom audit
  lives in the test workspace; it is not a graph node. The selected declarations' exported
  axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Source line numbers come from the built `.olean` files, so they can drift after source edits.
  Rebuilding the library before publishing brings them back into agreement.
- `ExportNodes.lean` imports `NativeFPU.Unchecked`; `trust-surface.sh` scans `site/` and
  allowlists that one importer.
- After its imports are built, the Lean export is an environment import and graph walk
  (tens of seconds, several GiB).
