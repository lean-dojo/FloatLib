// Hash routes. Node ids are full Lean names and may contain characters such as `?`, so the
// node route takes the whole remainder of the path. Legacy map bookmarks may carry a query.

import chapterAliases from './chapter-aliases.json';

export type Route =
  | { kind: 'landing' }
  | { kind: 'chapter'; slug: string; heading?: string }
  | { kind: 'node'; id: string }
  | { kind: 'graph'; view: 'modules' | 'declarations'; selected?: string }
  | { kind: 'references'; key?: string }
  | { kind: 'missing'; path: string };

type ChapterTarget = { slug: string; heading?: string };
type ChapterAlias = ChapterTarget & { headings?: Record<string, ChapterTarget> };

const aliases = new Map<string, ChapterAlias>(Object.entries(chapterAliases));

function decode(value: string): string {
  try { return decodeURIComponent(value); } catch { return value; }
}

// Bookmarks made before the library rename keep their declaration or module selection.
function currentName(name: string): string {
  return name.replace(/^LeanFloat(?=\.|$)/, 'FloatLib');
}

// Merged chapters have a default section; bookmarks to individual sections keep their heading
// unless that section moved elsewhere. Resolve before lookup so navigation uses the current slug.
function currentChapter(slug: string, heading?: string): Extract<Route, { kind: 'chapter' }> {
  const alias = aliases.get(slug);
  if (!alias) return { kind: 'chapter', slug, heading };
  if (heading !== undefined && alias.headings && Object.hasOwn(alias.headings, heading)) {
    const target = alias.headings[heading];
    return { kind: 'chapter', slug: target.slug, heading: target.heading };
  }
  return { kind: 'chapter', slug: alias.slug, heading: heading ?? alias.heading };
}

export function parseRoute(hash = location.hash): Route {
  const raw = hash.replace(/^#/, '') || '/';
  if (raw === '/' || raw === '') return { kind: 'landing' };
  const node = raw.match(/^\/node\/(.+)$/);
  if (node) return { kind: 'node', id: currentName(decode(node[1])) };
  const [pathPart, queryPart] = splitQuery(raw);
  const query = new URLSearchParams(queryPart);
  const selected = query.get('node');
  if (pathPart === '/graph' || pathPart === '/graph/') {
    return {
      kind: 'graph',
      view: query.get('view') === 'declarations' ? 'declarations' : 'modules',
      selected: selected ? currentName(selected) : undefined,
    };
  }
  const chapter = pathPart.match(/^\/chapter\/([^/]+)(?:\/(.+))?$/);
  if (chapter) {
    const slug = decode(chapter[1]);
    // The bibliography replaces the former references chapter, including its section bookmarks.
    if (slug === 'references') return { kind: 'references', key: undefined };
    return currentChapter(slug, chapter[2] ? decode(chapter[2]) : undefined);
  }
  const map = pathPart.match(/^\/map(?:\/([^/]+))?\/?$/);
  if (map) {
    return { kind: 'graph', view: 'declarations',
      selected: selected ? currentName(selected) : undefined };
  }
  const references = pathPart.match(/^\/references(?:\/([^/]+))?\/?$/);
  if (references) return { kind: 'references', key: references[1] ? decode(references[1]) : undefined };
  return { kind: 'missing', path: raw };
}

function splitQuery(value: string): [string, string] {
  const index = value.indexOf('?');
  return index === -1 ? [value, ''] : [value.slice(0, index), value.slice(index + 1)];
}

export function landingPath(): string { return '/'; }
export function chapterPath(slug: string, heading?: string): string {
  return `/chapter/${encodeURIComponent(slug)}${heading ? `/${encodeURIComponent(heading)}` : ''}`;
}
export function nodePath(id: string): string { return `/node/${encodeURIComponent(id)}`; }
export function graphPath(view: 'modules' | 'declarations' = 'modules', selected?: string): string {
  const query = new URLSearchParams();
  if (view === 'declarations') query.set('view', view);
  if (selected) query.set('node', selected);
  return `/graph${query.size ? `?${query}` : ''}`;
}
export function referencesPath(key?: string): string {
  return key ? `/references/${encodeURIComponent(key)}` : '/references';
}

export function href(path: string): string { return `#${path}`; }

export function navigate(path: string, replace = false): void {
  const next = `#${path}`;
  if (replace) {
    history.replaceState(null, '', next);
    window.dispatchEvent(new HashChangeEvent('hashchange'));
  } else location.hash = path;
}
