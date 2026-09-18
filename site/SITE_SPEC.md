# FloatLib website specification

FloatLib's website is a technical book with an introduction, sixteen chapters, and a bibliography.
It explains the numerical representations, executable algorithms, and proofs, and presents the
performance measurements and external comparisons. The public name is FloatLib; the Lean namespace is
`FloatLib` and the Lake package is `floatlib`. The repository URL is
`https://github.com/lean-dojo/FloatLib`.

## Reader and navigation

The reader is a static React application with hash routes:

- `#/`: the FloatLib introduction, highlights, and a chapter index.
- `#/chapter/<slug>`: a chapter, with its title followed directly by the article.
- `#/node/<id>`: a Lean declaration's statement, documentation, source, and proof information.
- `#/references`: the bibliography.
- `#/graph`: every library module and its direct FloatLib imports, including meta imports.
- `#/graph?view=declarations`: the selected declarations from the guide and their dependencies.

The sidebar contains chapter navigation, the dependency graph, and references. Search, theme
selection, keyboard access, and mobile navigation remain available. The graph is a separate page
within this reader. Legacy map URLs open the declaration graph and preserve a selected declaration.
Each declaration page links to its neighborhood in the graph.
Use the supplied FloatLib logo in the navigation header, with “Verified floating point in Lean”
beside it. The same cropped artwork appears in the README.

Label the two graph views accurately: the module graph covers every source module under `FloatLib`
and the root entry point; the declaration graph covers the guide's selected definitions and
theorems. Include search, selection, immediate dependencies and dependents, group filtering, zoom,
and pan. Keep the graph's controls usable on mobile and provide keyboard-accessible connection lists.

Chapter summaries are metadata for search; they are not displayed as agenda paragraphs under chapter
titles. The landing page opens with a concise definition of FloatLib and the author byline,
and an introduction that explains what the library implements and proves. It does not open with a
fictional origin story or instructions about which kind of reader should read which chapter.
The navigation already names FloatLib, so do not repeat it as a visible landing-page heading.
Keep an accessible heading for the overview. Invite readers to build on the library and link to
the contributing guide.

The book starts with using FloatLib and a short code tour in chapter 1. The detailed source tour
belongs beside the relevant explanations, rather than in a second directory-by-directory chapter.
The reading order is: a working program; machine numbers; the history and its
incident case studies; verification; execution, models, and rounding; the format families; kernels and dispatch;
performance and the native-float comparison; external validation. The bibliography is a separate
reference list, not a numbered chapter. Keep old chapter and
section bookmarks working when material moves. Reordering should update chapter labels and links,
without renaming historical result records or duplicating their figures.

## Typography and figures

Keep the existing restrained book typography: readable serif prose, monospace Lean, generous line
height, and a centered measure. Type and article widths scale together on large screens. Navigation
collapses on mobile. Long code and tables can scroll inside their own containers; the page itself
must not overflow. Render math with bundled MathJax assets and highlight Lean code without changing
what is copied.

Figures belong beside the explanation that makes them useful. Performance and validation plots belong
in their respective chapters. Captions identify the measured
quantity and enough scope to prevent misreading. Explain log scales, missing series, and qualified
outcomes where relevant. A large case count is not a percentage of coverage, and the duration of a
test campaign is not library performance. Keep diagrams that explain a representation or algorithm;
do not replace the article with dashboards, decorative cards, or proof inventories.

A Markdown image may use its optional title for the visible caption, with a separate description
in the alt text. Use this on chapter figures so the description and caption do not repeat each
other. Timing plots should say that lower is faster; comparison-count plots should say they count
cases, not time.

The reader numbers figures within each chapter: Figure 2.1, Figure 2.2, and so on.
Refer to each figure from nearby prose and tell the reader what to look for. Link the reference
to `#/chapter/<slug>/figure-<asset-stem>`; for example,
`[Figure 2.1](#/chapter/from-reals-to-machine-numbers/figure-ch01-binary32-layout)`.
The anchor comes from the image filename, so reordering figures changes their displayed numbers
without breaking links. Update the numbers in prose when changing their order.

## Writing

Explain the subject directly and in depth. Develop a concrete example far enough that the reader can
follow the mechanism, then connect it to the mathematics and the implementation. Preserve useful
existing explanations, equations, checked examples, citations, and qualifications. Edit weak framing
without compressing a substantial chapter into a summary.

Follow the `research-storytelling` skill when available. Use the relevant explanatory techniques
from its reference authors: a running example, a diagram developed through several steps, an
experiment interpreted from its evidence, or a derivation that makes the implementation intelligible.
The technique should fit the chapter. Preserve its distinct argument and rhythm.

Use “we” for the authors' voice throughout the guide and interface. Do not invent the authors'
experiences, motives, conversations, or development history. First-person phrasing can guide a
calculation or describe a choice made in the exposition; autobiographical claims
need evidence from the authors' actual work. Avoid canned chapter
agendas, audience-routing paragraphs, repeated promises about what the reader will learn, dramatic
one-line conclusions, and generic recaps. A chapter may open with an example, a definition, or an
observation; it does not need a ritual question or a syllabus sentence. Explain design decisions
through their technical consequences. Do not mandate a uniform paragraph template across chapters.

Claims about proof scope must name the relevant contract. Binary arithmetic, a P3109 projection, a
block-format encoding, and an approximate transcendental function do not have interchangeable
correctness guarantees. Keep numerical assumptions and limitations with the claim they qualify.

Link to source code through descriptive words in the sentence, such as “allocation measurements”
or “the rounding proof”, rather than printing long file paths in the prose. Keep literal paths
in commands and instructions where the reader needs to type them. Check each link against the
actual source location.

## Source layout

- `content/landing.md`: opening definition, author byline, introduction, and highlights.
- `content/chapters/NN-slug.md`: the sixteen chapters.
- `content/references.json`: bibliography entries and primary-source links. Undated web resources
  carry an `accessed` date in `YYYY-MM-DD` form, displayed separately from the publication year.
- `content/assets/`: published images.
- `logo.png`: original logo artwork; `content/assets/floatlib-logo.png` is the cropped version
  used by the reader and README.
- `content/assets/figures/` and `content/assets/data/`: figure generators and shared styles.
- `content/phases.json`: selected declarations, their group IDs/titles, and exporter imports.
- `data/nodes.json`: exported declarations and source provenance.
- `tooling/`: Lean export, metadata assembly, and chapter checks.
- `reader/`: React reader, Markdown rendering, data build, and existing route tests.
- `build.sh`: figure freshness checks, export, chapter verification, and reader build.
- `serve.py`: local preview server with cache revalidation and legacy-path redirects.

Front matter in chapters contains `number`, `slug`, `title`, `summary`, and optional internal `phases`.
Landing front matter contains `lede` and `authors`. Keep the recorded author names and affiliations
unless the authors supply a change. A Markdown image such as `![Caption](assets/figure.png)` becomes
a figure with its caption. The reader copies published assets and excludes plotting code and input
data from the public bundle.

## Declaration data

`data/nodes.json` contains `source`, `phases`, and `nodes`. Source provenance includes the repository,
revision, and working-tree status. An unborn HEAD uses a null revision and no worktree diff digest;
all nodes are uncommitted and have no source URL. Each selected node retains its full Lean name as its
id, kind, title, phase ID, module, file and line range, source URL, statement, documentation, axioms,
selected dependencies, source excerpt, and dirty status. Each phase contains only its `id` and `title`.
The phase list must be nonempty, and each phase must contain a node. Names must resolve and be
unique; dependencies, source ranges, and provenance are validated. Dependencies are computed through
unselected declarations and transitively reduced.
These are supporting details for a declaration, not the organizing interface of the book.
The reader also generates its complete module graph from the source import headers. Ignore comments,
include public and meta imports, and reject missing project imports and cycles. External dependencies
such as Mathlib are outside this graph. Do not infer proof dependencies from module imports.

A link `[[Full.Lean.Name]]` resolves to `#/node/<URL-encoded-name>` when the declaration is exported.
Missing names render as code and are reported by the checker; the strict site build rejects unresolved
links. Source links must honestly represent the exported revision and working-tree status.

## Reader data

The reader build requires `data/nodes.json`, Markdown chapters, `content/landing.md`, and
`content/references.json`. It writes `public/data/site.json` with:

- `generatedAt`, `source`, and `origin`: generation time, declaration provenance, and input paths.
- `phases`: group IDs and titles.
- `nodes`: exported declarations with dependents, chapter mentions, highlighted statement/source
  lines, and rendered documentation.
- `modules`: the complete module graph, with each module's ID, file, group, direct dependencies,
  and meta dependencies.
- `chapters`: chapter number, slug, title, summary, source file, rendered HTML, search text,
  and declaration mentions. The reader derives section navigation from the rendered headings.
  Internal frontmatter phase names are validated while reading the chapters.
- `landing`: rendered `html` with optional `lede` and `authors` from the front matter.
- `references`: bibliography entries with key, authors, title, venue, year, and source URL.

The reader renders the landing HTML as one article followed by the chapter index. Numbered citations
link to bibliography entries; their source URLs remain links to the cited publications.
The data build also writes `data/reader-warnings.md` and the bundled MathJax stylesheet and fonts.

## Evidence and measurement claims

Use the recorded results to check numerical claims:

- `benchmarks/results/main/release/benchmark/`: scalar timings, ratios, metadata, and preflight results.
- `benchmarks/results/flocq-matched/`: matched binary timings, full-value comparisons, and captured sources.
- `tests/results/main/release/external/`: direct external comparisons and their diagnostics.
- `tests/results/main/ecosystem/`: wider upstream and workload results, including qualified outcomes.

Read `benchmarks/docs/Comparison.md`, `tests/EXTERNAL.md`, and the relevant result metadata before
interpreting a series. The main figure is `content/assets/format-comparison-main.png`. Figure
scripts identify their authoritative inputs; do not keep duplicate benchmark CSVs under the site.
Keep the machine, affinity, workload, implementation boundaries, exclusions, and measurement date
available next to the detailed results. Different total widths need not imply equal precision across
formats. Distinguish direct FloatLib comparisons from another project's own tests. Retain and explain
disagreements rather than presenting a universal pass label.

## Verification and build directories

Keep build outputs, dependency caches, and scratch checks outside the source tree.
`tests/lib/lake.sh` defines the shared per-checkout `FLOATLIB_BUILD_DIR`; site scripts derive their
defaults from it. `BUILD_DIR` controls the reader build mirror, `OUT_DIR` the finished site,
and `FLOATLIB_SITE_SCRATCH` the chapter scratch directory. The standard output is
`${FLOATLIB_BUILD_DIR}-site`, not a build directory in the checkout. Source files and maintained
published figures stay in the repository.

Run `bash site/build.sh` for the full site check. The export builds the modules listed in
`content/phases.json`, including the optional binary transcendental and unchecked host APIs.
`--skip-lean` may reuse a current declaration export
after prose-only edits; it still checks chapter examples and figure freshness. The build regenerates
result-derived figures in local scratch and compares their bytes with the maintained assets. It must
not silently skip missing evidence for a release build.
The [build-options table](tooling/README.md#build-options) documents the remaining development
flags, strictness settings, and clean-source requirement.

Every fenced `lean` block in `content/chapters/` is extracted into a per-chapter scratch file,
prefixed with `import FloatLib`, and compiled against the local library build. Claimed evaluation
outputs are checked. An unresolved link, unexpected compiler warning, output mismatch, or failing
example fails the strict build. A new Lean example on the landing page must be checked in local
scratch or copied verbatim from a checked chapter example; the chapter extractor does not check the
landing page itself. Remove temporary test sources after checking them; do not add persistent test
modules for prose or reader edits.

Use `python3 site/serve.py --dir <local-output>` to preview. Inspect the built site in a browser at
desktop and mobile widths, including the introduction, all chapter routes, math, image loading,
search, declaration links, themes, and legacy redirects. Check both graph views, search, selection,
zoom, and dependency links at desktop and mobile widths. Chapter agenda ledes remain absent.

Update this contract when the intended website behavior changes. Explicit user instructions take
precedence over older design notes.
