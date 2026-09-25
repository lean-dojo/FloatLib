// Shape of public/data/site.json, produced by scripts/build-data.mjs from data/nodes.json
// (schema in site/SITE_SPEC.md) and the Markdown under site/content.

export type SiteNode = {
  id: string;
  name: string;
  kind: string;
  phase: string;
  title: string;
  module: string;
  file: string;
  line: number;
  endLine: number;
  // GitHub link at source.revision. Exact (with a #L..-L.. fragment) when the committed text at
  // those lines is the excerpt; without the fragment when the file exists at the revision but
  // these lines changed in the working tree; empty when the file is not in the repository at the
  // revision at all. See node_url in site/tooling/export_atlas.py.
  url: string;
  statement: string;
  docstring: string;
  axioms: string[];
  dependencies: string[];
  leanSource: string;
  // True when the file differs from the recorded revision (uncommitted work): the excerpt and
  // line numbers are the working tree's. Whether the URL can be trusted is encoded in `url`.
  dirty: boolean;
  // Added by the build step.
  dependents: string[];
  chapters: string[];
  statementLines: string[];
  sourceLines: string[];
  docstringHtml: string;
};

export type SitePhase = {
  id: string;
  title: string;
};

export type SiteModule = {
  id: string;
  file: string;
  group: string;
  dependencies: string[];
  metaDependencies: string[];
};

export type Chapter = {
  number: string;
  slug: string;
  title: string;
  summary: string;
  file: string;
  html: string;
  searchText: string;
  mentions: string[];
  headings: { id: string; title: string }[];
};

export type Reference = {
  key: string;
  authors: string;
  title: string;
  venue: string;
  year: string;
  url: string;
  accessed: string;
};

export type SiteData = {
  generatedAt: string;
  source: {
    repository: string;
    // Null before the first commit; declaration URLs are then empty and all nodes are dirty.
    revision: string | null;
    branch?: string;
    // Number of library files that differ from `revision` when the data was exported, and the
    // SHA-256 of `git diff --binary HEAD` (present when dirtyFiles > 0 and HEAD exists).
    dirtyFiles?: number;
    worktree?: string;
  };
  origin: { nodes: string; chapters: string };
  phases: SitePhase[];
  nodes: SiteNode[];
  modules: SiteModule[];
  chapters: Chapter[];
  landing: { lede?: string; authors?: string[]; html: string };
  references: Reference[];
};
