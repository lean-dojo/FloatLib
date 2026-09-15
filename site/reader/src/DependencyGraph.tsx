import { useEffect, useMemo, useRef, useState } from 'react';
import { DottedName, type SiteIndex } from './data';
import { graphPath, href, navigate, nodePath } from './routes';

type Entry = { id: string; label: string; group: string; dependencies: string[]; metaDependencies: string[] };
type Point = { x: number; y: number };
type Box = { x: number; y: number; width: number; height: number };
const COLORS = [
  '#2563eb', '#b45309', '#15803d', '#9333ea', '#be123c', '#0e7490', '#6d5b20',
  '#e6550d', '#507d29', '#c03593', '#5361a6', '#935b50', '#077f73', '#817b00',
  '#aa3970', '#3b749d', '#79509b', '#627b69', '#a24a21', '#736a96',
];

function arrange(entries: Entry[]) {
  const byId = new Map(entries.map(entry => [entry.id, entry]));
  const levels = new Map<string, number>();
  const visiting = new Set<string>();
  function level(id: string): number {
    if (levels.has(id)) return levels.get(id)!;
    // Selected declarations may be mutually dependent through a structure's generated API.
    if (visiting.has(id)) return 0;
    visiting.add(id);
    const dependencies = byId.get(id)!.dependencies.filter(dependency => byId.has(dependency));
    const value = dependencies.length ? 1 + Math.max(...dependencies.map(level)) : 0;
    visiting.delete(id);
    levels.set(id, value);
    return value;
  }
  entries.forEach(entry => level(entry.id));
  const rows = new Map<number, Entry[]>();
  entries.forEach(entry => {
    const n = levels.get(entry.id)!;
    rows.set(n, [...rows.get(n) ?? [], entry]);
  });
  const detailed = entries.length < 60;
  const gap = detailed ? 190 : 18;
  const columns = detailed ? 3 : Infinity;
  const width = Math.max(detailed ? 400 : 600,
    ...[...rows.values()].map(row => Math.min(columns, row.length) * gap + 80));
  const positions = new Map<string, Point>();
  let visualRow = 0;
  for (const [, row] of [...rows].sort(([a], [b]) => a - b)) {
    const center = (entry: Entry) => {
      const points = entry.dependencies.map(id => positions.get(id)).filter((p): p is Point => !!p);
      return points.length ? points.reduce((total, p) => total + p.x, 0) / points.length : width / 2;
    };
    row.sort((a, b) => center(a) - center(b) || a.group.localeCompare(b.group) || a.id.localeCompare(b.id));
    const rowWidth = Math.min(columns, row.length);
    for (let start = 0; start < row.length; start += rowWidth) {
      const chunk = row.slice(start, start + rowWidth);
      chunk.forEach((entry, i) => positions.set(entry.id, {
        x: (width - (chunk.length - 1) * gap) / 2 + i * gap,
        y: 55 + visualRow * (detailed ? 85 : 45),
      }));
      visualRow++;
    }
  }
  return { positions, detailed, box: { x: 0, y: 0, width, height: Math.max(300, visualRow * (detailed ? 85 : 45) + 80) } };
}

function Drawing({ entries, selected, select, colors }: {
  entries: Entry[]; selected?: string; select: (id: string) => void; colors: Map<string, string>;
}) {
  const layout = useMemo(() => arrange(entries), [entries]);
  const [box, setBox] = useState<Box>(layout.box);
  const [size, setSize] = useState({ width: 600, height: 350 });
  const svg = useRef<SVGSVGElement>(null);
  const drag = useRef<{ pointerId: number; x: number; y: number; box: Box; moved: boolean } | null>(null);
  useEffect(() => setBox(layout.box), [layout]);
  useEffect(() => {
    if (!svg.current) return;
    const observer = new ResizeObserver(([entry]) => {
      setSize({ width: entry.contentRect.width, height: entry.contentRect.height });
    });
    observer.observe(svg.current);
    return () => observer.disconnect();
  }, []);
  const scale = Math.min(size.width / box.width, size.height / box.height);
  const labelSize = Math.min(22, 12 / Math.max(scale, 0.01));
  const zoom = (factor: number) => setBox(previous => {
    const width = Math.max(100, Math.min(layout.box.width * 4, previous.width * factor));
    const height = previous.height * width / previous.width;
    return { x: previous.x + (previous.width - width) / 2,
      y: previous.y + (previous.height - height) / 2, width, height };
  });
  return <div className={`dependency-drawing${layout.detailed ? ' is-detailed' : ''}${layout.detailed && entries.length > 10 ? ' is-tall' : ''}`}>
    <div className="graph-zoom" aria-label="Graph zoom">
      <button type="button" onClick={() => zoom(0.7)} aria-label="Zoom in">+</button>
      <button type="button" onClick={() => zoom(1.4)} aria-label="Zoom out">−</button>
      <button type="button" onClick={() => setBox(layout.box)}>Fit graph</button>
    </div>
    <svg ref={svg} viewBox={`${box.x} ${box.y} ${box.width} ${box.height}`}
      aria-label={`Dependency graph with ${entries.length} nodes`} role="img"
      onPointerDown={event => {
        if (event.button !== 0 || !event.isPrimary || drag.current) return;
        drag.current = { pointerId: event.pointerId, x: event.clientX, y: event.clientY, box, moved: false };
        event.currentTarget.setPointerCapture(event.pointerId);
      }}
      onPointerMove={event => {
        const start = drag.current;
        if (!start || start.pointerId !== event.pointerId || !svg.current) return;
        const rect = svg.current.getBoundingClientRect();
        const scale = Math.max(start.box.width / rect.width, start.box.height / rect.height);
        const dx = event.clientX - start.x, dy = event.clientY - start.y;
        if (Math.abs(dx) + Math.abs(dy) > 4) start.moved = true;
        if (start.moved) setBox({ ...start.box, x: start.box.x - dx * scale, y: start.box.y - dy * scale });
      }}
      onPointerUp={event => {
        const start = drag.current;
        if (!start || start.pointerId !== event.pointerId) return;
        drag.current = null;
        if (event.currentTarget.hasPointerCapture(event.pointerId)) {
          event.currentTarget.releasePointerCapture(event.pointerId);
        }
        if (start.moved) return;
        const target = document.elementFromPoint(event.clientX, event.clientY)?.closest('[data-node]');
        if (target?.getAttribute('data-node')) select(target.getAttribute('data-node')!);
      }}
      onPointerCancel={event => {
        if (drag.current?.pointerId === event.pointerId) drag.current = null;
      }}>
      <defs><marker id="dependency-arrow" viewBox="0 0 10 10" refX="10" refY="5"
        markerWidth="5" markerHeight="5" orient="auto-start-reverse">
        <path d="M 0 0 L 10 5 L 0 10 z" fill="currentColor" />
      </marker></defs>
      <g className="dependency-edges">
        {entries.flatMap(entry => entry.dependencies.map(id => {
          const from = layout.positions.get(entry.id)!, to = layout.positions.get(id);
          if (!to) return null;
          return <path key={`${entry.id}:${id}`} d={`M${from.x},${from.y - 5} L${to.x},${to.y + 6}`}
            className={`${selected === entry.id || selected === id ? 'is-connected ' : ''}${entry.metaDependencies.includes(id) ? 'is-meta' : ''}`}
            markerEnd={layout.detailed ? 'url(#dependency-arrow)' : undefined} />;
        }))}
      </g>
      <g>
        {entries.map(entry => {
          const p = layout.positions.get(entry.id)!;
          return <g key={entry.id} data-node={entry.id} className="dependency-node"
            transform={`translate(${p.x},${p.y})`}>
            <title>{entry.id}</title>
            <circle r={selected === entry.id ? 8 : layout.detailed ? 5 : 3.5}
              fill={colors.get(entry.group)} stroke={selected === entry.id ? 'var(--ink)' : 'var(--paper)'} />
            {layout.detailed && <text y={12 + labelSize} textAnchor="middle" style={{ fontSize: labelSize }}>
              {entry.id.split('.').slice(-2).map((part, i) =>
                <tspan key={i} x="0" dy={i ? '1.15em' : 0}>{part.length > 12 ? `${part.slice(0, 11)}…` : part}</tspan>)}
            </text>}
          </g>;
        })}
      </g>
    </svg>
  </div>;
}

export default function DependencyGraph({ index, view, selected }: {
  index: SiteIndex; view: 'modules' | 'declarations'; selected?: string;
}) {
  const [query, setQuery] = useState('');
  const search = useRef<HTMLInputElement>(null);
  const [group, setGroup] = useState('');
  const [nearby, setNearby] = useState(Boolean(selected));
  const entries = useMemo<Entry[]>(() => view === 'modules'
    ? index.data.modules.map(module => ({ ...module, label: module.id }))
    : index.data.nodes.map(node => ({ ...node, label: node.title, group: node.phase, metaDependencies: [] })),
  [index, view]);
  const byId = useMemo(() => new Map(entries.map(entry => [entry.id, entry])), [entries]);
  const groups = useMemo(() => [...new Set(entries.map(entry => entry.group))].sort(), [entries]);
  const colors = useMemo(() => new Map(groups.map((name, i) => [name, COLORS[i % COLORS.length]])), [groups]);
  const current = selected ? byId.get(selected) : undefined;
  const dependents = useMemo(() => {
    const result = new Map<string, string[]>();
    entries.forEach(entry => entry.dependencies.forEach(id => result.set(id, [...result.get(id) ?? [], entry.id])));
    return result;
  }, [entries]);
  useEffect(() => { setNearby(Boolean(selected)); setGroup(''); }, [selected]);
  const visible = useMemo(() => {
    const neighbors = current && nearby
      ? new Set([current.id, ...current.dependencies, ...dependents.get(current.id) ?? []]) : null;
    return entries.filter(entry => (!group || entry.group === group) && (!neighbors || neighbors.has(entry.id)));
  }, [entries, current, nearby, group, dependents]);
  const matches = useMemo(() => {
    const needle = query.trim().toLowerCase();
    return needle ? entries.filter(entry => `${entry.id} ${entry.label}`.toLowerCase().includes(needle)) : [];
  }, [entries, query]);
  const select = (id: string) => { setQuery(''); navigate(graphPath(view, id)); };
  const groupName = (id: string) => view === 'declarations'
    ? index.data.phases.find(phase => phase.id === id)?.title ?? id : id;
  const links = (ids: string[], incoming = false) => ids.length
    ? <ul className="graph-relations">{ids.map(id => <li key={id}>
      <a href={href(graphPath(view, id))}><DottedName name={id} /></a>
      {view === 'modules' && current && (incoming
        ? byId.get(id)?.metaDependencies.includes(current.id) : current.metaDependencies.includes(id))
        && <small> meta import</small>}
    </li>)}</ul> : <p className="muted">None in this graph.</p>;
  return <article className="page dependency-page">
    <header className="page-header"><h1>Dependency graph</h1>
      <p>We think it’s pretty cool to see the library like this :) Pick a node and follow the
        connections back to the pieces it uses.</p>
    </header>
    <nav className="graph-tabs" aria-label="Graph type">
      <a href={href(graphPath())} aria-current={view === 'modules' ? 'page' : undefined}>All library modules</a>
      <a href={href(graphPath('declarations'))} aria-current={view === 'declarations' ? 'page' : undefined}>Guide declarations</a>
    </nav>
    <p className="graph-explanation">{view === 'modules'
      ? `All ${entries.length.toLocaleString()} FloatLib modules are here, including the optional ones and examples. Read upward to see what each module imports.`
      : `Here are ${entries.length.toLocaleString()} definitions and theorems we meet in the guide. Read upward to see what a result builds on, or downward to find where we use it.`}</p>
    <details className="graph-reading">
      <summary>How to read the links</summary>
      {view === 'modules'
        ? <p>Each line connects a module to one it imports directly. Dashed lines are Lean’s
          meta imports. We only show FloatLib’s own modules here; imports from Mathlib and
          other libraries are left out.</p>
        : <p>This is the guide’s selection. For every source module, switch to “All library modules.”
          For definitions, we follow their types and bodies. For theorems, we follow their
          statements and the theorems used in their proofs, without entering unlisted runtime
          definition bodies. We hide a direct link when another path already connects the
          same two nodes.</p>}
    </details>
    <div className="graph-controls">
      <label>Find {view === 'modules' ? 'a module' : 'a declaration'}
        <input ref={search} type="search" value={query} onChange={event => setQuery(event.target.value)}
          placeholder={view === 'modules' ? 'e.g. Posit.Rounding' : 'e.g. Sterbenz'} />
      </label>
      <label>Group
        <select value={group} onChange={event => setGroup(event.target.value)}>
          <option value="">All groups</option>
          {groups.map(id => <option key={id} value={id}>{groupName(id)}</option>)}
        </select>
      </label>
    </div>
    {query.trim() && <div className="graph-matches" aria-live="polite">
      <p>{matches.length} matches{matches.length > 30 ? '; first 30 shown. Narrow the search to see more.' : '.'}</p>
      <ul>{matches.slice(0, 30).map(entry => <li key={entry.id}>
        <button type="button" onClick={() => {
          select(entry.id);
          search.current?.focus({ preventScroll: true });
        }}><DottedName name={entry.id} /></button>
      </li>)}</ul>
    </div>}
    {selected && !current && <p role="status">This name is not in this graph. Try the other view or search for its current name.</p>}
    {current && <div className="graph-selection">
      <label><input type="checkbox" checked={nearby} onChange={event => setNearby(event.target.checked)} />
        Show only immediate connections</label>
      <a href={href(graphPath(view))}>Clear selection</a>
    </div>}
    <p className="graph-count">{visible.length.toLocaleString()} of {entries.length.toLocaleString()} nodes shown.
      {' '}Drag to pan; use + and − to zoom. Search and the lists below also work with the keyboard.</p>
    {visible.length ? <Drawing entries={visible} selected={selected} select={select} colors={colors} />
      : <p>No nodes in this selection.</p>}
    <ul className="graph-legend" aria-label="Node groups">{groups.filter(id => visible.some(entry => entry.group === id)).map(id =>
      <li key={id}><span style={{ background: colors.get(id) }} />{groupName(id)}</li>)}</ul>
    {current && <section className="graph-detail">
      <h2><DottedName name={current.id} /></h2>
      {view === 'declarations' && <p><a href={href(nodePath(current.id))}>Read the statement, proof dependencies, and source</a></p>}
      <div className="two-columns">
        <section><h3>{view === 'modules' ? 'Imports' : 'Depends on'}</h3>{links(current.dependencies)}</section>
        <section><h3>{view === 'modules' ? 'Imported by' : 'Used by'}</h3>{links(dependents.get(current.id) ?? [], true)}</section>
      </div>
    </section>}
  </article>;
}
