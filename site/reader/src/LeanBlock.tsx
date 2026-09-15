import { useLayoutEffect, useRef, useState } from 'react';
import { fitLeanBlock, watchOverflow } from './overflow';

// A line whose only content is a comment: a `-- result` line under #eval, or one line of a doc
// comment. Once the block is at its wide stop these wrap inside the visible width (styles.css,
// .lean-line.is-comment) instead of scrolling away with the code, so the printed result the prose
// talks about stays readable at every width. The highlighter emits exactly one span for such a
// line, containing only text and the <wbr> it puts after the joints of names, which makes the
// test reliable; build-data.mjs applies the same test to chapter code blocks.
const COMMENT_LINE = /^\s*<span class="lean-(?:comment|doc)">(?:[^<]|<wbr>)*<\/span>\s*$/;

// A highlighted Lean block. The lines arrive as HTML from the build step (one string per line);
// `copyText` is the verbatim source, so what the reader copies is exactly what is in the
// repository. Line numbers are rendered outside the selectable text.
//
// `wrap` is for statements: a signature is the primary content of a node page and of the map
// card, so it wraps (with a hanging indent, see styles.css) instead of scrolling sideways behind
// a scrollbar that many platforms hide. Source excerpts keep the scrolling pre, because wrapping
// would misrepresent the layout of the code; the pre gets a right-edge fade while more code is
// hidden to the right. Both kinds start at the measure and move to the wide stop when a line
// does not fit (fitLeanBlock), which is re-decided when the window is resized.
export default function LeanBlock({ lines, copyText, startLine, label, url, collapsedLines, wrap }: {
  lines: string[];
  copyText: string;
  startLine?: number;
  label?: string;
  url?: string;
  collapsedLines?: number;
  wrap?: boolean;
}) {
  const [expanded, setExpanded] = useState(false);
  const [copied, setCopied] = useState(false);
  const root = useRef<HTMLDivElement>(null);
  const pre = useRef<HTMLPreElement>(null);
  const limit = collapsedLines ?? Infinity;
  const collapsible = lines.length > limit + 4;
  const shown = collapsible && !expanded ? lines.slice(0, limit) : lines;
  useLayoutEffect(() => {
    const block = root.current;
    const element = pre.current;
    if (!block || !element) return;
    fitLeanBlock(block);
    const stopWatching = watchOverflow(element);
    let frame = 0;
    const onResize = () => {
      cancelAnimationFrame(frame);
      frame = requestAnimationFrame(() => fitLeanBlock(block));
    };
    window.addEventListener('resize', onResize);
    return () => {
      stopWatching();
      window.removeEventListener('resize', onResize);
      cancelAnimationFrame(frame);
    };
  }, [shown]);
  const copy = async () => {
    try {
      await navigator.clipboard.writeText(copyText);
      setCopied(true);
      window.setTimeout(() => setCopied(false), 1400);
    } catch { /* clipboard may be unavailable over plain http */ }
  };
  const className = ['lean-block', startLine !== undefined ? 'has-line-numbers' : '', wrap ? 'is-wrap' : '']
    .filter(Boolean).join(' ');
  return <div ref={root} className={className}>
    <div className="lean-block-bar">
      <span>Lean</span>
      {label && <code className="lean-block-label" title={label}>{label}</code>}
      <span className="lean-block-actions">
        {url && <a href={url} target="_blank" rel="noreferrer">GitHub</a>}
        <button type="button" onClick={copy} aria-live="polite">{copied ? 'Copied' : 'Copy'}</button>
      </span>
    </div>
    <pre ref={pre}><code className="lean">
      {shown.map((line, index) => <span className={`lean-line${COMMENT_LINE.test(line) ? ' is-comment' : ''}`} key={index}>
        {startLine !== undefined && <span className="lean-line-number" aria-hidden="true">{startLine + index}</span>}
        <span className="lean-line-code" dangerouslySetInnerHTML={{ __html: line }} />
      </span>)}
    </code></pre>
    {collapsible && <button type="button" className="lean-block-expand" aria-expanded={expanded}
      onClick={() => setExpanded(current => !current)}>
      {expanded ? 'Show fewer lines' : `Show all ${lines.length} lines`}
    </button>}
  </div>;
}
