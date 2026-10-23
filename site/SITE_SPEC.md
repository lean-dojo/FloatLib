# FloatLib website specification

FloatLib's website is a technical book: an introduction, twenty-one chapters, and a bibliography. It
explains the numerical representations, executable algorithms, and proofs, and it presents the
performance measurements and external comparisons. In public the project is called FloatLib. The
Lean namespace is `FloatLib`, the Lake package is `floatlib`, and the repository lives at
`https://github.com/lean-dojo/FloatLib`.

## Reader and navigation

FloatLib's reader is a static React application with hash routes:

- `#/`: the FloatLib introduction, highlights, and a chapter index.
- `#/chapter/<slug>`: a chapter, with its title followed directly by the article.
- `#/node/<id>`: a Lean declaration's statement, documentation, source, and proof information.
- `#/references`: the bibliography.
- `#/graph`: every library module and its direct FloatLib imports, including meta imports.
- `#/graph?view=declarations`: the selected declarations from the guide and their dependencies.

The sidebar holds chapter navigation, the dependency graph, and references, and search, theme
selection, keyboard access, and mobile navigation all stay available. Inside this reader the graph
is a page of its own. Legacy map URLs open the declaration graph and keep a selected declaration,
and each declaration page links to its neighborhood in the graph. Put the supplied FloatLib logo in
the navigation header, with “Verified floating point in Lean” beside it. That's the same cropped
artwork the README uses.

Label the two graph views for what they show. The module graph covers every source module under
`FloatLib` plus the root entry point, and the declaration graph covers the guide's selected
definitions and theorems. Give the graph search, selection, immediate dependencies and dependents,
group filtering, zoom, and pan. Keep its controls usable on mobile, and provide connection lists
that work from the keyboard.

Chapter summaries are search metadata, so don't display them as agenda paragraphs under chapter
titles. The landing page opens with a short definition of FloatLib and the author byline, then an
introduction to what the library implements and proves. No fictional origin story, and no
instructions about which kind of reader should read which chapter. Since the navigation already
names FloatLib, don't repeat it as a visible heading on the landing page, but keep an accessible
heading for the overview. Invite readers to build on the library and link to the contributing guide.

In chapter 1 the book starts with using FloatLib and a short code tour. Put the detailed source tour
beside the explanations it belongs to, and don't write a second directory-by-directory chapter. In
reading order, the book goes from a working program to machine numbers, the history and its incident
case studies, and verification. Then come execution, models, and rounding, the format families, and
kernels and dispatch, followed by performance and the native-float comparison, external validation,
interval proof automation, and further examples. Decimal arithmetic and elementary functions get
their own chapters after the binary formats, and native-float semantics come after the performance
chapter. Keep the bibliography as a reference list of its own, with no chapter number. When material
moves, keep old chapter and section bookmarks working. A reordering should update chapter labels and
links, but it shouldn't rename historical result records or duplicate their figures.

## Typography and figures

Keep the restrained book typography the site already has: readable serif prose, monospace Lean,
generous line height, and a centered measure. On large screens the type and the article width scale
together, and on mobile the navigation collapses. Long code and tables may scroll inside their own
containers, but the page itself must never overflow. Render math with the bundled MathJax assets,
and highlight Lean code without changing what gets copied.

Put each figure next to the explanation that makes it useful, which means performance and validation
plots go in their own chapters. A caption names the measured quantity and gives enough scope that
nobody misreads it. Explain log scales, missing series, and qualified outcomes where they come up.
Don't present a large case count as a percentage of coverage, or the duration of a test campaign as
library performance. Keep diagrams that explain a representation or an algorithm, and don't swap the
article for dashboards, decorative cards, or proof inventories.

A Markdown image can use its optional title as the visible caption and keep a description in the alt
text. Do this on chapter figures, so the description and the caption don't repeat each other. Timing
plots should say that lower is faster, and comparison-count plots should say they count cases, not
time.

Figures are numbered within each chapter: Figure 2.1, Figure 2.2, and so on. Refer to each figure
from nearby prose and tell the reader what to look for. Link the reference to
`#/chapter/<slug>/figure-<asset-stem>`, for example
`[Figure 2.1](#/chapter/from-reals-to-machine-numbers/figure-ch01-binary32-layout)`. Because the
anchor comes from the image filename, reordering figures changes their displayed numbers without
breaking any link. Do update the numbers in the prose when you change the order.

A wide explanatory figure may come with an `<asset-stem>-mobile.png` arrangement, which the reader
uses below 600px. Both layouts must show the same mathematics. Performance generators also write
individual operation views and an `<asset-stem>-series.json` manifest, and from those the reader
offers an operation selector that starts with one operation on phones and with the overview on
larger screens. The image and both full-size links must follow the selected view. Their shared
measurement scope goes in the caption.

## Writing

Explain the subject in depth. Take a worked example far enough that the reader can follow the
mechanism, and then connect it to the mathematics and the implementation. Keep the useful
explanations, equations, checked examples, citations, and qualifications that are already there. Fix
weak framing, but don't squash a substantial chapter into a summary.

If the `research-storytelling` skill is available, follow it, and borrow whichever explanatory
technique from its reference authors fits: a running example, a diagram built up over several steps,
an experiment read from its evidence, or a derivation that makes sense of the implementation. Pick
the technique to fit the chapter. Each chapter keeps its own argument and rhythm.

Use direct explanations and worked calculations together. Keep a clear existing explanation when
adding an example, and follow the calculation far enough to explain its result. Use “we” naturally
for the authors' work or for a calculation, without rewriting sentences merely to add personality.
Keep grounded opinions, uncertainty, and occasional informality when they help explain the work.
An occasional “:)” fits a light moment such as an admitted weakness or an invitation, at most once
or twice a chapter. Do not make an invitation or an imperative the default chapter opening.
Keep related sentences together, and break paragraphs when the topic changes, for example from a
calculation to its API or from a theorem to its hypotheses. Don't invent the
authors' experiences, motives, conversations, or development history. First person is fine for walking through a
calculation or describing a choice the exposition makes, but an autobiographical claim needs
evidence from the authors' actual work. Leave out canned chapter agendas, paragraphs that route
different audiences to different chapters, repeated promises about what the reader will learn,
dramatic one-line conclusions, and generic recaps. A chapter can open with an example, a definition,
or an observation. It doesn't need a ritual question or a syllabus sentence. Explain each design
decision by its technical consequences, and don't force one paragraph template on every chapter.

A claim about proof scope has to name its contract, because binary arithmetic, a P3109 projection, a
block-format encoding, and an approximate transcendental function come with different correctness
guarantees. Keep each numerical assumption or limitation with the claim it qualifies.

Link to source code from descriptive words in the sentence, such as “allocation measurements” or
“the rounding proof”, and keep long file paths out of the prose. Literal paths belong in commands
and instructions, where the reader has to type them. Check every link against the actual source
location.

## Source layout

- `content/landing.md`: opening definition, author byline, introduction, and highlights.
- `content/chapters/NN-slug.md`: the twenty-one chapters.
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
- `serve.py`: local preview server with cache revalidation and redirects to the app entry page.

Chapter front matter has `number`, `slug`, `title`, `summary`, and optional internal `phases`, and
landing front matter has `lede` and `authors`. Keep the recorded author names and affiliations
unless the authors send a change. A Markdown image such as `![Caption](assets/figure.png)` becomes a
figure with its caption. When the reader copies published assets, it leaves plotting code and input
data out of the public bundle. Figure-view manifests are embedded in the rendered HTML and never
copied out as public files of their own.

## Declaration data

`data/nodes.json` holds `source`, `phases`, and `nodes`. Its source provenance gives the repository,
the revision, and the working-tree status. With an unborn HEAD the revision is null and there is no
worktree diff digest, and every node is uncommitted with no source URL. Each selected node keeps its
full Lean name as its id, along with its kind, title, phase ID, module, file and line range, source
URL, statement, documentation, axioms, selected dependencies, source excerpt, and dirty status. A
phase holds just its `id` and `title`. The phase list can't be empty, and every phase needs a node.
Names must resolve and be unique, and the dependencies, source ranges, and provenance all get
validated. Dependencies are computed through unselected declarations and then transitively reduced.
All of this supports a declaration's page, and the book isn't organized around it. From the
source import headers the reader also generates its complete module graph. When it does, ignore
comments, include public and meta imports, and reject missing project imports and cycles. External
dependencies such as Mathlib stay outside this graph. Don't infer proof dependencies from module
imports.

When the declaration is exported, a link `[[Full.Lean.Name]]` resolves to
`#/node/<URL-encoded-name>`. A missing name renders as code and the checker reports it, and the
strict site build rejects any unresolved link. Source links have to represent the exported revision
and working-tree status honestly.

## Reader data

To build, the reader needs `data/nodes.json`, Markdown chapters, `content/landing.md`, and
`content/references.json`. It writes `public/data/site.json` with:

- `generatedAt`, `source`, and `origin`: generation time, declaration provenance, and input paths.
- `phases`: group IDs and titles.
- `nodes`: exported declarations with dependents, chapter mentions, highlighted statement/source
  lines, and rendered documentation.
- `modules`: the complete module graph, with each module's ID, file, group, direct dependencies,
  and meta dependencies.
- `chapters`: chapter number, slug, title, summary, source file, rendered HTML, search text,
  declaration mentions, and second-level headings for section navigation.
  Internal frontmatter phase names are validated while reading the chapters.
- `landing`: rendered `html` with optional `lede` and `authors` from the front matter.
- `references`: bibliography entries with key, authors, title, venue, year, and source URL.

On the landing page the reader renders the HTML as one article with the chapter index after it.
Numbered citations link to bibliography entries, and the entries' source URLs point to the cited
publications. The data build also writes `data/reader-warnings.md` and the bundled MathJax
stylesheet and fonts.

## Evidence and measurement claims

Check numerical claims against the recorded results:

- `benchmarks/results/main/release/benchmark/`: scalar timings, ratios, metadata, and preflight results.
- `benchmarks/results/flocq-matched/`: matched binary timings, full-value comparisons, and captured sources.
- `benchmarks/results/public-binary/`: paired public binary arithmetic timings, trial metadata, and fixture hashes.
- `tests/results/main/release/external/`: direct external comparisons and their diagnostics.
- `tests/results/main/ecosystem/`: wider upstream and workload results, including qualified outcomes.

Before you interpret a series, read `benchmarks/docs/Comparison.md`, `tests/EXTERNAL.md`, and the
result metadata that goes with it. The performance chapter opens with the public binary measurements
in `content/assets/public-binary-performance.png`, and `format-comparison-main.png` compares the
wider set of formats and libraries. Each figure script names its authoritative inputs, so don't keep
duplicate benchmark CSVs under the site. Next to the detailed results, keep the machine, affinity,
workload, implementation boundaries, exclusions, and measurement date. Different total widths need
not imply equal precision across formats. Tell direct FloatLib comparisons apart from another
project's own tests. When results disagree, keep the disagreement and explain it instead of showing
one universal pass label.

## Verification and build directories

Build outputs, dependency caches, and scratch checks stay outside the source tree.
`tests/lib/lake.sh` defines the shared per-checkout `FLOATLIB_BUILD_DIR`, and the site scripts take
their defaults from it. `BUILD_DIR` controls the reader build mirror, `OUT_DIR` the finished site,
and `FLOATLIB_SITE_SCRATCH` the chapter scratch directory. By default the site goes to
`${FLOATLIB_BUILD_DIR}-site`, never to a build directory in the checkout. Source files and
maintained published figures stay in the repository.

`bash site/build.sh` runs the full site check. Its export builds the modules listed in
`content/phases.json`, including the optional binary transcendental and unchecked host APIs. After
prose-only edits, `--skip-lean` may reuse a current declaration export, and it still checks chapter
examples and figure freshness. The build regenerates result-derived figures in local scratch and
compares their bytes with the maintained assets. For a release build it must never skip missing
evidence silently. Other development flags, strictness settings, and the clean-source requirement
are in the [build-options table](tooling/README.md#build-options).

Every fenced `lean` block in `content/chapters/` is extracted into a per-chapter scratch file,
prefixed with `import FloatLib`, and compiled against the local library build. Claimed evaluation
outputs are checked as well. An unresolved link, an unexpected compiler warning, an output mismatch,
or a failing example fails the strict build. The chapter extractor never looks at the landing page,
so a new Lean example there has to be checked in local scratch or copied verbatim from a checked
chapter example. Delete temporary test sources once you've checked them, and don't add persistent
test modules for prose or reader edits.

To preview, run `python3 site/serve.py --dir <local-output>`. Look at the built site in a browser at
desktop and mobile widths: the introduction, all chapter routes, math, image loading, search,
declaration links, themes, and moved section bookmarks. At both widths, check both graph views,
search, selection, zoom, and dependency links. Chapter agenda ledes should still be absent.

When the intended website behavior changes, update this contract. If a user's instructions conflict
with an older design note, the instructions win.
