import { Fragment, useEffect, useLayoutEffect, useRef, useState } from 'react';
import LeanBlock from './LeanBlock';
import Search from './Search';
import DependencyGraph from './DependencyGraph';
import { DottedName, shortName, type SiteIndex } from './data';
import {
  chapterPath, graphPath, href, landingPath, nodePath, parseRoute, referencesPath, type Route,
} from './routes';
import { updateOverflow } from './overflow';
import { useTheme } from './theme';
import { useCopyButtons } from './useCopyButtons';
import type { Chapter, SiteNode } from './types';

const STANDARD_AXIOMS = new Set(['propext', 'Classical.choice', 'Quot.sound']);

// ---------------------------------------------------------------------------------------------
// Chapter navigation collapses to a menu bar on narrow screens.

function Sidebar({ index, route, onSearch }: { index: SiteIndex; route: Route; onSearch: () => void }) {
  const container = useRef<HTMLElement>(null);
  const menuToggle = useRef<HTMLButtonElement>(null);
  const [menuOpen, setMenuOpen] = useState(false);
  const [theme, toggleTheme, explicitTheme] = useTheme();
  useEffect(() => setMenuOpen(false), [route]);
  useEffect(() => {
    if (!menuOpen) return;
    const dismiss = (event: PointerEvent) => {
      if (event.target instanceof Node && !container.current?.contains(event.target)) setMenuOpen(false);
    };
    const escape = (event: KeyboardEvent) => { if (event.key === 'Escape') setMenuOpen(false); };
    document.addEventListener('pointerdown', dismiss);
    document.addEventListener('keydown', escape);
    return () => {
      document.removeEventListener('pointerdown', dismiss);
      document.removeEventListener('keydown', escape);
    };
  }, [menuOpen]);
  useLayoutEffect(() => {
    // Keep the active entry visible in the scrolling navigation list.
    const nav = container.current?.querySelector<HTMLElement>('.contents-nav');
    if (!nav || window.matchMedia('(max-width: 900px)').matches) return;
    const current = nav.querySelector<HTMLElement>('.nav-link.is-active');
    if (!current) return;
    const bounds = nav.getBoundingClientRect();
    const own = current.getBoundingClientRect();
    if (own.top < bounds.top + 16) nav.scrollTop += own.top - bounds.top - 16;
    else if (own.bottom > bounds.bottom - 16) nav.scrollTop += own.bottom - bounds.bottom + 16;
  }, [route]);
  useLayoutEffect(() => {
    // The list is taller than its box on most screens. While it can still scroll down, it gets
    // `has-more-below` and styles.css fades out from the top of the first row that is cut off,
    // so a row is either fully legible or visibly fading, never a grey "disabled" looking link.
    // Scrolled to the end, the mask goes away and the last row is as dark as the others.
    const nav = container.current?.querySelector<HTMLElement>('.contents-nav');
    if (!nav) return;
    const update = () => {
      const more = nav.scrollTop + nav.clientHeight < nav.scrollHeight - 1;
      nav.classList.toggle('has-more-below', more);
      if (!more) {
        nav.style.removeProperty('--fade-from');
        return;
      }
      const top = nav.getBoundingClientRect().top;
      const bottom = top + nav.clientHeight;
      let from = nav.clientHeight - 10;
      for (const row of Array.from(nav.children)) {
        const bounds = row.getBoundingClientRect();
        if (bounds.bottom > bottom) {
          from = Math.max(0, bounds.top - top);
          break;
        }
      }
      nav.style.setProperty('--fade-from', `${Math.round(from)}px`);
    };
    update();
    nav.addEventListener('scroll', update, { passive: true });
    const observer = new ResizeObserver(update);
    observer.observe(nav);
    return () => {
      nav.removeEventListener('scroll', update);
      observer.disconnect();
    };
  }, []);

  const activeChapter = route.kind === 'chapter' ? route.slug : undefined;
  const { data } = index;
  return <aside ref={container} className={`contents${menuOpen ? ' is-open' : ''}`}>
    <div className="site-heading">
      <a className="site-title" href={href(landingPath())}>
        <img className="site-logo" src="assets/floatlib-logo.png" alt="FloatLib" width="960" height="833" />
        <small>Verified floating point in Lean</small>
      </a>
    </div>
    <button ref={menuToggle} type="button" className="mobile-menu-toggle" aria-expanded={menuOpen}
      aria-controls="contents-menu" onClick={() => setMenuOpen(open => !open)}>
      <span className="visually-hidden">{menuOpen ? 'Close menu' : 'Open menu'}</span>
      <span /><span /><span />
    </button>
    <div id="contents-menu" className="contents-menu">
      <button type="button" className="reader-search" onClick={() => {
        // Closing the mobile menu hides Search; return focus to its visible menu button.
        if (menuToggle.current?.getClientRects().length) menuToggle.current.focus();
        setMenuOpen(false);
        onSearch();
      }}>
        Search <kbd>/</kbd>
      </button>
      <nav className="contents-nav" aria-label="Chapters">
        <a className={`nav-link nav-link-plain${route.kind === 'landing' ? ' is-active' : ''}`} href={href(landingPath())}>
          <span className="nav-number" aria-hidden="true" /><span className="nav-name">Overview</span>
        </a>
        <div className="contents-label">Chapters</div>
        {data.chapters.map(chapter => <a key={chapter.slug}
          className={`nav-link${activeChapter === chapter.slug ? ' is-active' : ''}`}
          href={href(chapterPath(chapter.slug))}>
          <span className="nav-number">{chapter.number}</span>
          <span className="nav-name">{chapter.title}</span>
        </a>)}
        <div className="contents-label">Sources</div>
        <a className={`nav-link nav-link-plain${route.kind === 'graph' ? ' is-active' : ''}`} href={href(graphPath())}>
          <span className="nav-number" aria-hidden="true" /><span className="nav-name">Dependency graph</span>
        </a>
        <a className={`nav-link nav-link-plain${route.kind === 'references' ? ' is-active' : ''}`} href={href(referencesPath())}>
          <span className="nav-number" aria-hidden="true" /><span className="nav-name">Reference list</span>
        </a>
      </nav>
      <footer className="contents-footer">
        <button type="button" className="theme-toggle" onClick={toggleTheme}
          aria-label={theme === 'dark' ? 'Switch to light mode' : 'Switch to dark mode'}>
          {theme === 'dark' ? 'Light mode' : 'Dark mode'}{explicitTheme ? '' : ' (system)'}
        </button>
        <p className="site-provenance">
          <a href={data.source.repository} target="_blank" rel="noreferrer">Source on GitHub</a>
          <br /><a href="third-party-licenses.txt">Third-party licenses</a>
          {data.source.revision === null && <><br />
            <span className="uncommitted">Uncommitted source; no revision yet.</span></>}
        </p>
      </footer>
    </div>
  </aside>;
}

// ---------------------------------------------------------------------------------------------
// Pages.

function Landing({ index }: { index: SiteIndex }) {
  const { data } = index;
  const body = useRef<HTMLDivElement>(null);
  const html = data.landing.html;
  useCopyButtons(body, html);
  useOverflowMarks(body, html);
  // "Name (Affiliation)" from the front matter of landing.md; a name without parentheses is shown alone.
  const authors = (data.landing.authors ?? []).map(entry => {
    const match = entry.match(/^(.*?)\s*\(([^)]*)\)\s*$/);
    return match ? { name: match[1], affiliation: match[2] } : { name: entry, affiliation: '' };
  });
  return <article className="page landing">
    <header className="page-header">
      <h1 className="visually-hidden">Overview</h1>
      {data.landing.lede && <p className="lede">{data.landing.lede}</p>}
      {authors.length > 0 && <ul className="byline">
        {authors.map(author => <li key={author.name}>
          <span>{author.name}</span>
          {author.affiliation && <span className="affiliation">{author.affiliation}</span>}
        </li>)}
      </ul>}
    </header>
    <div ref={body} className="prose landing-body" dangerouslySetInnerHTML={{ __html: html }} />
    <nav className="landing-section" aria-labelledby="chapter-index-heading">
      <h2 id="chapter-index-heading">Chapters</h2>
      {data.chapters.length ? <ol className="chapter-index">
        {data.chapters.map(chapter => <li key={chapter.slug}>
          <a className="chapter-index-link" href={href(chapterPath(chapter.slug))}>
            <span className="chapter-index-number">{chapter.number}</span>
            <span className="chapter-index-title">{chapter.title}</span>
          </a>
        </li>)}
      </ol> : <p className="muted">No chapters are available yet.</p>}
    </nav>
  </article>;
}

// An inline formula wider than its paragraph
// cannot wrap, so on narrow screens it becomes a scrollable block instead of widening the page.
// A table or a Lean block wider than the column scrolls inside its wrapper, and the wrapper gets
// a right-edge fade while there is content beyond the edge (hidden scrollbars give no other cue).
// All are checked after render, on resize, and (for the scrolling wrappers) on scroll. This
// covers the chapter HTML from the build step; the LeanBlock component handles its own block.
function markOverflow(root: HTMLElement | null): void {
  if (!root) return;
  for (const element of root.querySelectorAll<HTMLElement>('mjx-container:not([display="true"])')) {
    element.classList.remove('is-wide');
    const parent = element.parentElement;
    if (parent && element.getBoundingClientRect().width > parent.clientWidth) element.classList.add('is-wide');
  }
  for (const wrapper of root.querySelectorAll<HTMLElement>('.table-scroll, .lean-block pre, .math-display')) {
    if (!wrapper.dataset.scrollWatched) {
      wrapper.dataset.scrollWatched = 'true';
      wrapper.addEventListener('scroll', () => updateOverflow(wrapper), { passive: true });
    }
    updateOverflow(wrapper);
  }
}

function useOverflowMarks(root: React.RefObject<HTMLDivElement | null>, key: string): void {
  useLayoutEffect(() => {
    markOverflow(root.current);
    let frame = 0;
    const onResize = () => {
      cancelAnimationFrame(frame);
      frame = requestAnimationFrame(() => markOverflow(root.current));
    };
    window.addEventListener('resize', onResize);
    return () => {
      window.removeEventListener('resize', onResize);
      cancelAnimationFrame(frame);
    };
  }, [key, root]);
}

function ChapterPage({ index, chapter, heading }: { index: SiteIndex; chapter: Chapter; heading?: string }) {
  const { data } = index;
  const position = data.chapters.findIndex(candidate => candidate.slug === chapter.slug);
  const previous = position > 0 ? data.chapters[position - 1] : undefined;
  const next = position < data.chapters.length - 1 ? data.chapters[position + 1] : undefined;
  const body = useRef<HTMLDivElement>(null);
  useCopyButtons(body, chapter.html);
  useOverflowMarks(body, chapter.slug);
  useEffect(() => {
    if (!heading) return;
    const target = body.current?.querySelector<HTMLElement>(`#${CSS.escape(heading)}`);
    target?.scrollIntoView({ block: 'start' });
  }, [chapter.slug, heading]);
  return <article className="page chapter">
    <header className="page-header">
      <p className="eyebrow">Chapter {chapter.number}</p>
      <h1>{chapter.title}</h1>
    </header>
    <div ref={body} className="prose chapter-body" dangerouslySetInnerHTML={{ __html: chapter.html }} />
    <nav className="chapter-pager" aria-label="Neighbouring chapters">
      {previous ? <a className="pager-previous" href={href(chapterPath(previous.slug))}>
        <small>Previous</small><span>{previous.number}. {previous.title}</span></a> : <span />}
      {next ? <a className="pager-next" href={href(chapterPath(next.slug))}>
        <small>Next</small><span>{next.number}. {next.title}</span></a> : <span />}
    </nav>
  </article>;
}

function NodeList({ index, ids }: { index: SiteIndex; ids: string[] }) {
  if (!ids.length) return <p className="muted">None among the declarations included in this guide.</p>;
  return <ul className="node-list">
    {ids.map(id => {
      const node = index.nodeById.get(id);
      if (!node) return <li key={id}><code>{id}</code></li>;
      return <li key={id}>
        <a href={href(nodePath(id))}>{node.title}</a>
        <code className="node-list-name" title={node.name}>{node.kind} {shortName(node.name)}</code>
      </li>;
    })}
  </ul>;
}

function NodePage({ index, node }: { index: SiteIndex; node: SiteNode }) {
  const extraAxioms = node.axioms.filter(axiom => !STANDARD_AXIOMS.has(axiom));
  const chapters = node.chapters.map(slug => index.chapterBySlug.get(slug)).filter((c): c is Chapter => Boolean(c));
  return <article className="page node-page">
    <header className="page-header">
      <p className="eyebrow">{node.kind}</p>
      <h1>{node.title}</h1>
      <p className="node-name"><code><DottedName name={node.name} /></code></p>
      <p className="node-meta">
        <code>{node.file.split('/').map((part, position) => <Fragment key={position}>
          {position > 0 && <>/<wbr /></>}{part}</Fragment>)}</code>, lines {node.line} to {node.endLine}.{' '}
        {/* The exporter downgrades the URL when the working tree differs from the recorded
            revision: no URL when GitHub does not have the file there, a file-level URL when
            these lines changed, the exact link otherwise (see node_url in export_atlas.py). */}
        {!node.url
          ? <span className="uncommitted">This local file is not on GitHub yet.</span>
          : !node.url.includes('#')
            ? <><a href={node.url} target="_blank" rel="noreferrer">View the file on GitHub</a>.{' '}
              <span className="uncommitted">The code below includes local changes that are not on GitHub yet.</span></>
            : <><a href={node.url} target="_blank" rel="noreferrer">View on GitHub</a>.</>}
      </p>
    </header>
    <section>
      <h2>Statement</h2>
      <LeanBlock lines={node.statementLines} copyText={node.statement} wrap />
    </section>
    {node.docstringHtml && <section>
      <h2>Documentation</h2>
      <div className="prose docstring" dangerouslySetInnerHTML={{ __html: node.docstringHtml }} />
    </section>}
    <section>
      <h2>Source</h2>
      <LeanBlock lines={node.sourceLines} copyText={node.leanSource} startLine={node.line}
        label={node.module} url={node.url.includes('#') ? node.url : undefined} collapsedLines={40} />
    </section>
    <section>
      <h2>Axioms</h2>
      {node.axioms.length === 0
        ? <p className="muted">{node.kind === 'theorem' ? 'No axioms recorded.' : 'Axiom dependencies are listed for theorems.'}</p>
        : <p className="axioms">
          {node.axioms.map(axiom => <code key={axiom} className={STANDARD_AXIOMS.has(axiom) ? '' : 'is-unusual'}>{axiom}</code>)}
          {extraAxioms.length === 0
            ? <span className="muted"> Only standard Lean axioms are used here.</span>
            : <span className="warning"> This declaration relies on an axiom beyond the standard three.</span>}
        </p>}
    </section>
    <div className="two-columns">
      <section><h2>Depends on</h2><NodeList index={index} ids={node.dependencies} /></section>
      <section><h2>Used by</h2><NodeList index={index} ids={node.dependents} /></section>
    </div>
    <p><a href={href(graphPath('declarations', node.id))}>Explore these dependencies in the graph</a></p>
    <section>
      <h2>Mentioned in</h2>
      {chapters.length ? <ul className="plain-list">{chapters.map(chapter => <li key={chapter.slug}>
        <a href={href(chapterPath(chapter.slug))}>{chapter.number}. {chapter.title}</a></li>)}</ul>
        : <p className="muted">No chapter links to this declaration yet.</p>}
    </section>
  </article>;
}

function ReferencesPage({ index, selected }: { index: SiteIndex; selected?: string }) {
  useEffect(() => {
    if (!selected) return;
    document.getElementById(`reference-${selected}`)?.scrollIntoView({ block: 'center' });
  }, [selected]);
  const { references } = index.data;
  // Numbered citations point to this list.
  return <article className="page references">
    <header className="page-header">
      <h1>Reference list</h1>
    </header>
    {references.length ? <ol className="reference-list">
      {references.map(reference => <li key={reference.key} id={`reference-${reference.key}`}
        className={reference.key === selected ? 'is-targeted' : undefined}>
        <span>{reference.authors}{reference.authors ? ', ' : ''}</span>
        {reference.url ? <a href={reference.url} target="_blank" rel="noreferrer"><cite>{reference.title}</cite></a>
          : <cite>{reference.title}</cite>}
        {reference.venue && <span>, {reference.venue}</span>}
        {reference.year && <span> ({reference.year})</span>}.
        {reference.accessed && <span> Accessed <time dateTime={reference.accessed}>{reference.accessed}</time>.</span>}
      </li>)}
    </ol> : <p className="muted">No references are available yet.</p>}
  </article>;
}

function Missing({ path }: { path: string }) {
  return <article className="page">
    <header className="page-header"><h1>Not found</h1></header>
    <p>There is nothing at <code>#{path}</code>. Start from the <a href={href(landingPath())}>overview and chapters</a>.</p>
  </article>;
}

// ---------------------------------------------------------------------------------------------

export default function App({ index }: { index: SiteIndex }) {
  const [route, setRoute] = useState<Route>(() => parseRoute());
  const [search, setSearch] = useState(false);
  useEffect(() => {
    const update = () => setRoute(parseRoute());
    window.addEventListener('hashchange', update);
    return () => window.removeEventListener('hashchange', update);
  }, []);
  useEffect(() => {
    const shortcut = (event: KeyboardEvent) => {
      if (event.key !== '/' || event.metaKey || event.ctrlKey || event.altKey) return;
      const target = event.target as HTMLElement | null;
      if (target && (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA' || target.isContentEditable)) return;
      event.preventDefault();
      setSearch(true);
    };
    window.addEventListener('keydown', shortcut);
    return () => window.removeEventListener('keydown', shortcut);
  }, []);
  const routeKey = route.kind === 'chapter' ? `chapter:${route.slug}` : route.kind === 'node' ? `node:${route.id}`
    : route.kind === 'references' ? 'references' : route.kind;
  useLayoutEffect(() => {
    if (route.kind === 'chapter' && route.heading) return;
    if (route.kind === 'references' && route.key) return;
    window.scrollTo(0, 0);
  }, [routeKey]);
  useEffect(() => {
    const title = route.kind === 'chapter' ? index.chapterBySlug.get(route.slug)?.title
      : route.kind === 'node' ? index.nodeById.get(route.id)?.title
      : route.kind === 'references' ? 'Reference list' : route.kind === 'graph' ? 'Dependency graph' : undefined;
    document.title = title ? `${title}: FloatLib` : 'FloatLib: verified floating point in Lean 4';
  }, [index, route]);

  let content: React.ReactNode;
  switch (route.kind) {
    case 'landing': content = <Landing index={index} />; break;
    case 'chapter': {
      const chapter = index.chapterBySlug.get(route.slug);
      content = chapter ? <ChapterPage key={chapter.slug} index={index} chapter={chapter} heading={route.heading} />
        : <Missing path={`/chapter/${route.slug}`} />;
      break;
    }
    case 'node': {
      const node = index.nodeById.get(route.id);
      content = node ? <NodePage key={node.id} index={index} node={node} /> : <Missing path={`/node/${route.id}`} />;
      break;
    }
    case 'references': content = <ReferencesPage index={index} selected={route.key} />; break;
    case 'graph': content = <DependencyGraph key={route.view} index={index} view={route.view} selected={route.selected} />; break;
    default: content = <Missing path={route.path} />;
  }
  return <>
    <div className="page-shell">
      <Sidebar index={index} route={route} onSearch={() => setSearch(true)} />
      <main className="reader" id="main">{content}</main>
    </div>
    {search && <Search index={index} close={() => setSearch(false)} />}
  </>;
}
