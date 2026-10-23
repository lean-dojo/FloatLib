# Building and editing the website

We build the website from the guide's Markdown chapters and from declarations exported out of
Lean, checking examples, links, and figures along the way. Build the library first, then run these
commands from the repository root. For the full build you'll need Python 3.12 or newer, Matplotlib
3.11.0 (the version the checked figures were made with), Node.js, Corepack, and rsync. Install
Matplotlib in your Python environment:

```bash
python3 -m pip install matplotlib==3.11.0
```

During the build, the reader's JavaScript dependencies are installed from its lockfile.

```bash
source tests/lib/lake.sh
OUT_DIR="${FLOATLIB_BUILD_DIR}-site" bash site/build.sh
python3 site/serve.py --port 10000 --dir "${FLOATLIB_BUILD_DIR}-site"
```

Then open `http://localhost:10000/`. The build checks the chapter examples with Lean, compares
their printed results, resolves theorem links and citations, verifies result-derived figures, and
renders the reader. To change the text, edit the chapters under `site/content/chapters/`. There's
no separate manual to keep in sync.

## Site data pipeline

The exporter writes declarations from the built library to `site/data/nodes.json`, and the
[website specification](../SITE_SPEC.md) describes its fields and how the reader uses them.

```bash
site/tooling/export.sh              # Lean export + Python reduce
site/tooling/export.sh --skip-lean  # reuse last raw export while editing the reader's prose
```

First the exporter runs `lake -KbuildDir="$FLOATLIB_BUILD_DIR" build` on the modules in
`site/content/phases.json`: `FloatLib`, the opt-in `NativeFPU.Unchecked`, and
`Configured.Transcendentals`. (A default `lake build` skips those optional modules.) Next,
`ExportNodes.lean` imports them, resolves every listed constant, and writes out each declaration's
kind, signature, docstring, module, source range, axioms, and dependencies. An unresolved or
duplicate name stops the export. Last, Python reduces the graph, attaches GitHub URLs, validates
the data, and writes `nodes.json`.

With this data, the book can link to individual Lean declarations, and the **Guide declarations**
view at `#/graph?view=declarations` can show the guide's selected definitions and theorems. The
**All library modules** view at `#/graph` comes from somewhere else: every library source import
header, meta imports included.

Build artifacts stay on local disk. `tests/lib/lake.sh` picks `FLOATLIB_BUILD_DIR`, and the site
tools add these suffixes to that path:

| Output | Default path | Override |
| --- | --- | --- |
| Raw Lean export | `${FLOATLIB_BUILD_DIR}-site-data/nodes.raw.json` | `export_atlas.py --raw` |
| Extracted Lean files and full-build check report | `${FLOATLIB_BUILD_DIR}-site-check/` | `FLOATLIB_SITE_SCRATCH` or `check_chapters.py --scratch` |
| Reader mirror, dependencies, and intermediate files | `${FLOATLIB_BUILD_DIR}-site-reader/` | `BUILD_DIR` |
| Finished static site | `${FLOATLIB_BUILD_DIR}-site/` | `OUT_DIR` |
| Python cache during the full site build | `${FLOATLIB_BUILD_DIR}-site-pycache/` | `PYTHONPYCACHEPREFIX` |

The same defaults apply when you run the exporter, checker, or reader build on its own. Keep any
overrides on local storage. If the Lake path helper fails, the Python tools stop, and they never
fall back to `.lake/build` in the checkout. Because `--skip-lean` reuses the raw export, the first
export has to run without that flag. Two files do stay in the checkout: the reader's declaration
data and warnings (`site/data/nodes.json` and `site/data/reader-warnings.md`). Rendered chapters
and the overview's HTML go into the reader's `public/data/site.json`, and the build needs the
exported declaration data, chapters, landing page, and references.

## Nodes

We group declarations into phases in `site/content/phases.json`. Each phase has an `id`, a
`title`, and an ordered list of `nodes`. A node gives either a `name` and an optional `title`, or
just a Lean name, and in that case its title comes from the first sentence of its docstring.

Export fails unless names are unique and resolved, dependencies and source ranges are valid,
titles have no em or en dashes, and every phase has at least one node. Cross-phase dependencies
produce warnings. Chapters link to nodes with `[[Full.Lean.Name]]`, and `check_chapters.py` warns
if a chapter names a missing node.

## Chapter checks

`check_chapters.py` compiles each chapter ` ```lean ` block and compares `-- ` result comments
with Lean's output. ` ```lean standalone ` compiles as its own file, and `nocheck` skips a block
with a warning. `site/build.sh` turns on strict checks and fails on warnings unless
`FLOATLIB_SITE_STRICT=0`.

## Build options

The full build accepts these flags:

| Flag | Effect |
| --- | --- |
| `--skip-lean` | Reuse the raw declaration export; still check chapters and result-derived figures. Use after prose edits, not changes to the selected declarations or library. |
| `--skip-check` | Skip the chapter checker for a quick reader iteration. |
| `--no-compile` | Check chapter structure and links without compiling Lean examples or verifying their printed results. |
| `--allow-missing-results` | Allow a development build when retained result directories are absent. If they are present, their verification still runs and must pass. |
| `--require-clean` | Reject an export from an uncommitted library or an unborn `HEAD`. Cannot be combined with `--allow-missing-results`. |

`FLOATLIB_SITE_REQUIRE_CLEAN=1` does the same as `--require-clean`. During development,
`FLOATLIB_SITE_STRICT=0` lets chapter warnings through, but errors still fail the build. (The
output-directory overrides are in the table above.) Chapters compile with one compiler at a time.
If the machine has the resources for more, set `FLOATLIB_SITE_JOBS` to another worker count.

For a prose-only check that skips Lake and the benchmark results, run the checker against the
existing atlas:

```bash
python3 site/tooling/check_chapters.py --strict --no-compile \
  --scratch /tmp/floatlib-prose-check --json /tmp/floatlib-prose-check/report.json
```

It's no substitute for the full build before publication.

## Source links during editing

URLs point at `HEAD`, but excerpts follow the worktree. When a node is dirty, it keeps its exact
link if the excerpt matches those lines at `HEAD`, falls back to a file-only link if they differ,
and gets no URL if the file isn't in `HEAD` at all. `site/build.sh --require-clean` refuses a
dirty library. Before the first commit, `source.revision` is `null`, there's no diff digest, and
every declaration is marked uncommitted with no GitHub URL. Local builds still run every check in
that state, and `--require-clean` refuses it too.

## Export behavior

- The trust phase shows `@[csimp]` lemmas and the unchecked host API. There's no graph node for
  the full axiom audit, which lives in the test workspace. Exported axioms for the selected
  declarations are `propext`, `Classical.choice`, and `Quot.sound`.
- Source line numbers come from the built `.olean` files, so they can drift after you edit the
  source. Rebuild the library before publishing and they line up again.
- `ExportNodes.lean` imports `NativeFPU.Unchecked`, and `trust-surface.sh` scans `site/` with that
  one importer on its allowlist.
- Once its imports are built, the Lean export is just an environment import and a graph walk (tens
  of seconds, several GiB).
