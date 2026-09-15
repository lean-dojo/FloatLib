import { useLayoutEffect, useRef, useState } from 'react';
import { shortName, type SiteIndex } from './data';
import { chapterPath, navigate, nodePath } from './routes';

type Hit =
  | { kind: 'node'; id: string; title: string; detail: string; path: string }
  | { kind: 'chapter'; id: string; title: string; detail: string; path: string };

function score(haystack: string, query: string): number {
  const text = haystack.toLowerCase();
  if (text === query) return 0;
  if (text.startsWith(query)) return 1;
  const index = text.indexOf(query);
  if (index === -1) return Infinity;
  return text[index - 1] === ' ' || text[index - 1] === '.' || text[index - 1] === '_' ? 2 : 3;
}

export default function Search({ index, close }: { index: SiteIndex; close: () => void }) {
  const [query, setQuery] = useState('');
  const [active, setActive] = useState(-1);
  const activeOption = useRef<HTMLButtonElement>(null);
  const dialog = useRef<HTMLDialogElement>(null);
  const input = useRef<HTMLInputElement>(null);
  useLayoutEffect(() => {
    const element = dialog.current!;
    element.showModal();
    input.current?.focus();
    return () => element.close();
  }, []);
  const normalized = query.trim().toLowerCase();
  const hits: Hit[] = [];
  if (normalized) {
    const scored: Array<{ hit: Hit; rank: number; order: number }> = [];
    index.data.chapters.forEach((chapter, order) => {
      const bodyRank = score(chapter.searchText, normalized);
      const rank = Math.min(score(chapter.title, normalized), score(chapter.summary, normalized) + 2,
        bodyRank + 5);
      const match = chapter.searchText.toLowerCase().indexOf(normalized);
      const start = Math.max(0, match - 55);
      const excerpt = match < 0 ? '' : `${start ? '…' : ''}${chapter.searchText.slice(start, match + normalized.length + 95)}`
        + (match + normalized.length + 95 < chapter.searchText.length ? '…' : '');
      if (rank < Infinity) scored.push({ order, rank: rank - 0.5, hit: {
        kind: 'chapter', id: chapter.slug, title: chapter.title,
        detail: `Chapter ${chapter.number}${excerpt ? ` · ${excerpt}` : ''}`, path: chapterPath(chapter.slug),
      } });
    });
    index.data.nodes.forEach((node, order) => {
      const rank = Math.min(score(node.title, normalized), score(shortName(node.name), normalized),
        score(node.name, normalized) + 1);
      if (rank < Infinity) scored.push({ order, rank, hit: {
        kind: 'node', id: node.id, title: node.title,
        detail: `${node.kind} ${shortName(node.name)}`,
        path: nodePath(node.id),
      } });
    });
    scored.sort((left, right) => left.rank - right.rank || left.order - right.order);
    hits.push(...scored.slice(0, 40).map(entry => entry.hit));
  }
  useLayoutEffect(() => { activeOption.current?.scrollIntoView({ block: 'nearest' }); }, [active]);
  const choose = (hit: Hit) => { close(); navigate(hit.path); };
  const move = (step: 1 | -1) => {
    if (!hits.length) return;
    setActive(current => current < 0 ? (step === 1 ? 0 : hits.length - 1) : (current + step + hits.length) % hits.length);
  };
  return <dialog ref={dialog} className="search-backdrop" aria-labelledby="search-label"
    onCancel={event => { event.preventDefault(); close(); }}
    onKeyDown={event => {
      if (event.key === 'Escape') { event.preventDefault(); close(); }
      if (event.key !== 'Tab') return;
      const controls = event.currentTarget.querySelectorAll<HTMLElement>(
        'input, button:not([tabindex="-1"])',
      );
      const first = controls[0];
      const last = controls[controls.length - 1];
      if (event.shiftKey && document.activeElement === first) {
        event.preventDefault();
        last?.focus();
      } else if (!event.shiftKey && document.activeElement === last) {
        event.preventDefault();
        first?.focus();
      }
    }}
    onMouseDown={event => event.target === event.currentTarget && close()}>
    <section className="search-dialog">
      <header className="dialog-heading">
        <label id="search-label" htmlFor="search">Search declarations and chapters</label>
        <button type="button" className="dialog-close" onClick={close}>Close</button>
      </header>
      <input ref={input} id="search" type="search" role="combobox" aria-autocomplete="list"
        aria-expanded="true" aria-controls="search-results" placeholder="roundAt, Sterbenz, rounding"
        aria-activedescendant={active < 0 ? undefined : `search-hit-${active}`}
        value={query} onChange={event => { setQuery(event.target.value); setActive(-1); }}
        onKeyDown={event => {
          if (event.key === 'ArrowDown') { event.preventDefault(); move(1); }
          else if (event.key === 'ArrowUp') { event.preventDefault(); move(-1); }
          else if (event.key === 'Enter' && active >= 0) { event.preventDefault(); choose(hits[active]); }
          else if (event.key === 'Enter' && hits.length) { event.preventDefault(); choose(hits[0]); }
        }} />
      <ol id="search-results" className="search-results" role="listbox">
        {hits.map((hit, position) => <li key={`${hit.kind}:${hit.id}`}>
          <button type="button" ref={active === position ? activeOption : null} id={`search-hit-${position}`}
            role="option" tabIndex={-1} aria-selected={active === position}
            onMouseEnter={() => setActive(position)} onClick={() => choose(hit)}>
            <small>{hit.detail}</small>
            <strong>{hit.title}</strong>
          </button>
        </li>)}
        {normalized && !hits.length && <li className="search-empty">Nothing matches {JSON.stringify(query.trim())}.</li>}
      </ol>
    </section>
  </dialog>;
}
