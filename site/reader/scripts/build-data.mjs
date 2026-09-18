#!/usr/bin/env node
// Build-time data step for the FloatLib reader.
//
// Reads the exported node data (site/data/nodes.json) and the Markdown content (site/content),
// renders Markdown and math to HTML,
// highlights Lean, resolves [[Full.Lean.Name]] links, and writes:
//   public/data/site.json           everything the app needs, fetched once at startup
//   public/mathjax.css, public/mathjax/fonts/woff-v2/   offline MathJax output
//   public/third-party-licenses.txt   notices for distributed code and fonts
//
// The site root defaults to the parent of this reader directory. build.sh sets
// FLOATLIB_SITE_ROOT because it builds from a copy of reader/ on local disk.

import { createRequire } from 'node:module';
import { cp, mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import MarkdownIt from 'markdown-it';
import { highlightLeanLines, isCommentLine } from './lean-highlight.mjs';
import { buildModuleGraph } from './module-graph.mjs';
import { writeThirdPartyLicenses } from './build-licenses.mjs';

const require = createRequire(import.meta.url);
const readerDir = path.resolve(import.meta.dirname, '..');
const siteRoot = process.env.FLOATLIB_SITE_ROOT
  ? path.resolve(process.env.FLOATLIB_SITE_ROOT) : path.resolve(readerDir, '..');
const publicDir = path.join(readerDir, 'public');
const warnings = [];
const unresolvedLinks = [];
const warn = message => { warnings.push(message); console.warn(`warning: ${message}`); };

function describePath(file) {
  const relative = path.relative(siteRoot, file);
  return relative.startsWith('..') ? file : relative;
}

function escapeHtml(value) {
  return value.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;');
}

// Inline code at 15px mono is about 9px per character on the 528px measure and 8.7px at 14.5px
// on a 320px phone (284px of text): a token of 32 characters fits a line alone everywhere.
const JOINT_MIN_LENGTH = 32;

/**
 * Escaped HTML for a code span, with a <wbr> after every joint inside a token longer than
 * JOINT_MIN_LENGTH. A path (a token with a slash) breaks only at its slashes, so `Runtime.lean`
 * stays whole at the end of a path; a name breaks at dots, underscores and hyphens. The joint
 * must follow an identifier character (so the leading dashes of `--skip-lean` are not joints)
 * and precede a letter (so `2026-09-07` and `3.75` stay whole). Tokens are split on whitespace
 * after escaping; the entities escapeHtml produces contain no joint characters.
 */
function jointsHtml(text) {
  return escapeHtml(text).split(/(\s+)/).map(part => {
    if (part.length <= JOINT_MIN_LENGTH) return part;
    const joints = part.includes('/') ? /(?<=[\p{L}\p{N}?!'])(\/+)(?=\p{L})/gu : /(?<=[\p{L}\p{N}?!'])([._-]+)(?=\p{L})/gu;
    return part.replace(joints, '$1<wbr>');
  }).join('');
}

/** An inline code span: joints in long tokens, `is-short` on a span that should move whole. */
function codeHtml(text, extraClass = '') {
  const classes = [extraClass, text.length <= JOINT_MIN_LENGTH ? 'is-short' : ''].filter(Boolean);
  const attribute = classes.length ? ` class="${classes.join(' ')}"` : '';
  return `<code${attribute}>${jointsHtml(text)}</code>`;
}

async function readText(file) {
  return readFile(file, 'utf8');
}

async function listMarkdown(dir) {
  if (!existsSync(dir)) return [];
  const entries = await readdir(dir);
  return entries.filter(name => name.endsWith('.md')).sort()
    .map(name => path.join(dir, name));
}

// ---------------------------------------------------------------------------------------------
// Required inputs.

async function loadNodes() {
  const file = path.join(siteRoot, 'data', 'nodes.json');
  if (!existsSync(file)) throw new Error(`${file}: missing declaration data; run site/tooling/export.sh`);
  const data = JSON.parse(await readText(file));
  if (!Array.isArray(data.nodes) || !Array.isArray(data.phases)) {
    throw new Error(`${file}: expected {source, phases, nodes}`);
  }
  if (data.nodes.some(node => !node.id?.startsWith('FloatLib.')
    || !node.module?.startsWith('FloatLib.'))) {
    throw new Error(`${file}: stale declaration data; build FloatLib and rerun site/tooling/export.sh`);
  }
  return { data, file };
}

async function chapterFiles() {
  const directory = path.join(siteRoot, 'content', 'chapters');
  const files = await listMarkdown(directory);
  if (!files.length) throw new Error(`${directory}: no Markdown chapters found`);
  return files;
}

// ---------------------------------------------------------------------------------------------
// MathJax, run once at build time so the site ships no MathJax JavaScript.

const MathJax = await require('mathjax').init({
  loader: { load: ['input/tex', 'output/chtml'] },
  tex: { packages: { '[+]': ['ams'] } },
  chtml: { adaptiveCSS: false, fontURL: './mathjax/fonts/woff-v2' },
});
const adaptor = MathJax.startup.adaptor;

function typesetMath(tex, display, where) {
  const node = MathJax.tex2chtml(tex, { display });
  const html = adaptor.outerHTML(node);
  if (html.includes('mjx-merror')) warn(`${where}: MathJax could not parse ${JSON.stringify(tex)}`);
  return html;
}

// ---------------------------------------------------------------------------------------------
// Node index and identifier resolution.

let nodeIndex = { byId: new Map(), byShort: new Map() };

function shortName(fullName) {
  return fullName.slice(fullName.lastIndexOf('.') + 1);
}

function buildNodeIndex(nodes) {
  const byId = new Map();
  const byShort = new Map();
  for (const node of nodes) {
    byId.set(node.id, node);
    const short = shortName(node.name);
    if (!byShort.has(short)) byShort.set(short, []);
    byShort.get(short).push(node);
  }
  nodeIndex = { byId, byShort };
}

/** Resolve a written name to a node id: exact id, then a unique suffix on a dot boundary. */
function resolveNodeName(written) {
  if (nodeIndex.byId.has(written)) return written;
  const candidates = nodeIndex.byShort.get(shortName(written)) ?? [];
  const suffixMatches = candidates.filter(node => node.name === written
    || node.name.endsWith(`.${written}`));
  return suffixMatches.length === 1 ? suffixMatches[0].id : null;
}

/** Resolver for identifiers inside Lean code: only unambiguous matches become links. */
function identifierResolver(selfId) {
  return name => {
    const target = resolveNodeName(name);
    return target && target !== selfId ? target : null;
  };
}

// ---------------------------------------------------------------------------------------------
// Markdown: markdown-it plus rules for math, node links, citations, figures, heading ids.

function mathInlineRule(state, silent) {
  const source = state.src;
  const start = state.pos;
  if (source.charCodeAt(start) !== 0x24 /* $ */) return false;
  const display = source.charCodeAt(start + 1) === 0x24;
  const marker = display ? '$$' : '$';
  const contentStart = start + marker.length;
  if (!display) {
    // Inline math must not start with whitespace, end with whitespace, or span lines, and a
    // closing dollar directly followed by a digit is a price, not math.
    if (/\s/.test(source[contentStart] ?? ' ')) return false;
  }
  let end = source.indexOf(marker, contentStart);
  while (end !== -1) {
    if (display) break;
    const before = source[end - 1];
    const after = source[end + 1];
    if (!/\s/.test(before) && !/[0-9]/.test(after ?? '') && !source.slice(contentStart, end).includes('\n')) break;
    if (source.slice(contentStart, end).includes('\n')) return false;
    end = source.indexOf(marker, end + 1);
  }
  if (end === -1 || end === contentStart) return false;
  if (!silent) {
    const token = state.push(display ? 'math_display_inline' : 'math_inline', 'math', 0);
    token.content = source.slice(contentStart, end);
  }
  state.pos = end + marker.length;
  return true;
}

function mathBlockRule(state, startLine, endLine, silent) {
  let pos = state.bMarks[startLine] + state.tShift[startLine];
  const max = state.eMarks[startLine];
  if (state.sCount[startLine] - state.blkIndent >= 4) return false;
  if (state.src.slice(pos, pos + 2) !== '$$') return false;
  const firstLine = state.src.slice(pos + 2, max);
  if (silent) return true;
  let content;
  let nextLine = startLine;
  if (firstLine.trim().endsWith('$$') && firstLine.trim().length > 2) {
    content = firstLine.trim().slice(0, -2);
    nextLine = startLine + 1;
  } else {
    const lines = [firstLine];
    nextLine = startLine + 1;
    let closed = false;
    while (nextLine < endLine) {
      pos = state.bMarks[nextLine] + state.tShift[nextLine];
      const lineText = state.src.slice(pos, state.eMarks[nextLine]);
      if (lineText.trim().endsWith('$$')) {
        lines.push(lineText.trim().slice(0, -2));
        closed = true;
        nextLine += 1;
        break;
      }
      lines.push(lineText);
      nextLine += 1;
    }
    if (!closed) return false;
    content = lines.join('\n');
  }
  state.line = nextLine;
  const token = state.push('math_block', 'math', 0);
  token.block = true;
  token.content = content.trim();
  token.map = [startLine, nextLine];
  return true;
}

function nodeLinkRule(state, silent) {
  const source = state.src;
  const start = state.pos;
  if (source.slice(start, start + 2) !== '[[') return false;
  const end = source.indexOf(']]', start + 2);
  if (end === -1) return false;
  const inner = source.slice(start + 2, end);
  if (inner.includes('\n') || !inner.trim()) return false;
  if (!silent) {
    const [written, label] = inner.split('|').map(part => part.trim());
    const token = state.push('node_link', 'a', 0);
    token.content = written;
    token.meta = { label: label || null };
  }
  state.pos = end + 2;
  return true;
}

function citationRule(state, silent) {
  const source = state.src;
  const start = state.pos;
  if (source.slice(start, start + 2) !== '[@') return false;
  const end = source.indexOf(']', start + 2);
  if (end === -1) return false;
  const key = source.slice(start + 2, end).trim();
  if (!/^[A-Za-z0-9_:.-]+$/.test(key)) return false;
  if (!silent) {
    const token = state.push('citation', 'a', 0);
    token.content = key;
  }
  state.pos = end + 1;
  return true;
}

function slugify(text) {
  return text.toLowerCase().normalize('NFKD').replace(/[^\w\s-]/g, '').trim()
    .replace(/[\s_]+/g, '-').replace(/-+/g, '-') || 'section';
}

function headingIdsRule(state) {
  const tokens = state.tokens;
  const seen = new Map();
  for (let index = 0; index < tokens.length; index += 1) {
    const token = tokens[index];
    if (token.type !== 'heading_open') continue;
    const inline = tokens[index + 1];
    const text = inline.children
      .filter(child => child.type === 'text' || child.type === 'code_inline')
      .map(child => child.content).join('');
    let id = slugify(text);
    const count = seen.get(id) ?? 0;
    seen.set(id, count + 1);
    if (count) id = `${id}-${count + 1}`;
    token.attrSet('id', id);
  }
}

function figureRule(state) {
  const tokens = state.tokens;
  const seen = new Map();
  state.env.figures = state.env.figures ?? [];
  for (let index = 0; index + 2 < tokens.length; index += 1) {
    const [open, inline, close] = [tokens[index], tokens[index + 1], tokens[index + 2]];
    if (open.type !== 'paragraph_open' || inline.type !== 'inline' || close.type !== 'paragraph_close') continue;
    const children = inline.children.filter(child => !(child.type === 'text' && !child.content.trim()));
    if (children.length !== 1 || children[0].type !== 'image') continue;
    const image = children[0];
    const src = image.attrGet('src') ?? '';
    const alt = image.content;
    const caption = image.attrGet('title') ?? alt;
    const stem = `figure-${slugify(path.basename(src, path.extname(src)))}`;
    const count = (seen.get(stem) ?? 0) + 1;
    seen.set(stem, count);
    const id = count === 1 ? stem : `${stem}-${count}`;
    const ordinal = state.env.figures.length + 1;
    const number = state.env.chapterNumber
      ? `${Number(state.env.chapterNumber)}.${ordinal}` : String(ordinal);
    const figure = new state.Token('html_block', '', 0);
    figure.block = true;
    // The image links to its own file so a plot downscaled to the measure can be opened at full
    // size; the caption repeats the link in words for readers who do not try clicking an image.
    const fullSize = `href="${escapeHtml(src)}" target="_blank" rel="noreferrer"`;
    figure.content = `<figure class="figure" id="${escapeHtml(id)}"><a ${fullSize} title="Open the full-size image">`
      + `<img src="${escapeHtml(src)}" alt="${escapeHtml(alt)}" loading="lazy"></a>`
      + `<figcaption><strong class="figure-number">Figure ${number}.</strong> `
      + `${caption ? escapeHtml(caption) : ''}<a class="figure-full" ${fullSize}>Full size</a></figcaption>`
      + '</figure>\n';
    state.env.figures.push(src);
    tokens.splice(index, 3, figure);
  }
}

function dropLeadingTitle(state) {
  const tokens = state.tokens;
  if (tokens[0]?.type === 'heading_open' && tokens[0].tag === 'h1') tokens.splice(0, 3);
}

function createMarkdown(references) {
  const md = new MarkdownIt({ html: true, linkify: false, typographer: false });
  md.inline.ruler.before('escape', 'math_inline', mathInlineRule);
  md.inline.ruler.before('link', 'node_link', nodeLinkRule);
  md.inline.ruler.before('link', 'citation', citationRule);
  md.block.ruler.before('fence', 'math_block', mathBlockRule, { alt: ['paragraph', 'reference', 'blockquote', 'list'] });
  md.core.ruler.push('drop_leading_title', dropLeadingTitle);
  md.core.ruler.push('heading_ids', headingIdsRule);
  md.core.ruler.push('figures', figureRule);

  // Tables scroll inside a wrapper when their columns do not fit the measure; the reader marks
  // the wrapper while there is more to the right (see markOverflow in App.tsx).
  md.renderer.rules.table_open = () => '<div class="table-scroll"><table>\n';
  md.renderer.rules.table_close = () => '</table></div>\n';

  // A long token in inline code gets a break opportunity after each joint (a slash, dot,
  // underscore or hyphen that follows a word character and precedes a letter), the rule the Lean
  // highlighter uses for identifiers. A path such as `Formats/BinaryInterchange/Format/
  // Definition.lean` then wraps at a slash, in prose and in a table cell, instead of at an
  // arbitrary letter (styles.css keeps break-word only as the fallback for a jointless token).
  // A short span (at most JOINT_MIN_LENGTH characters) fits a line by itself at every width the
  // reader serves, so it gets no joints and is marked `is-short`, which styles.css keeps on one
  // line: without that the browser's own rule breaks `pass5-final2` after the hyphen at a line
  // end, where moving it whole reads better. <wbr> has no text content, so copied text is
  // unchanged.
  md.renderer.rules.code_inline = (tokens, index) => codeHtml(tokens[index].content);

  md.renderer.rules.math_inline = (tokens, index, options, env) =>
    typesetMath(tokens[index].content, false, env.where);
  md.renderer.rules.math_display_inline = (tokens, index, options, env) =>
    `<span class="math-display-inline">${typesetMath(tokens[index].content, true, env.where)}</span>`;
  md.renderer.rules.math_block = (tokens, index, options, env) =>
    `<div class="math-display">${typesetMath(tokens[index].content, true, env.where)}</div>\n`;

  md.renderer.rules.node_link = (tokens, index, options, env) => {
    const written = tokens[index].content;
    const label = tokens[index].meta?.label;
    const target = resolveNodeName(written);
    if (target) {
      env.mentions = env.mentions ?? new Set();
      env.mentions.add(target);
      return `<a class="node-link" href="#/node/${encodeURIComponent(target)}" title="${escapeHtml(target)}">`
        + `${codeHtml(label ?? shortName(written))}</a>`;
    }
    env.unresolved = env.unresolved ?? [];
    env.unresolved.push(written);
    // Show the short name, as a resolved link would, so a miss reads the way the author wrote the
    // sentence; the full name stays in the title attribute for anyone who wants to look it up.
    const title = `${escapeHtml(written)} (not among the exported declarations)`;
    return codeHtml(label ?? shortName(written), 'node-link-missing').replace('<code', `<code title="${title}"`);
  };

  md.renderer.rules.citation = (tokens, index) => {
    const key = tokens[index].content;
    const position = references.findIndex(reference => reference.key === key);
    if (position === -1) return `[@${escapeHtml(key)}]`;
    return `<a class="citation" href="#/references/${encodeURIComponent(key)}">[${position + 1}]</a>`;
  };

  md.renderer.rules.fence = (tokens, index, options, env) => {
    const token = tokens[index];
    const language = (token.info || '').trim().split(/\s+/)[0];
    const code = token.content.replace(/\n$/, '');
    const copyButton = `<span class="lean-block-actions"><button type="button"`
      + ` data-copy-code="${escapeHtml(token.content)}" aria-live="polite">Copy</button></span>`;
    if (language === 'lean') {
      // Same markup as the LeanBlock component: one block-level span per line (so a copied
      // selection keeps its line breaks) and `is-comment` on comment-only lines, which the
      // stylesheet wraps so a `-- result` stays visible when the code is wider than the column.
      // The info string may carry `standalone` or `nocheck` for the chapter checker; both are
      // rendered the same way here.
      const lines = highlightLeanLines(code, identifierResolver(null));
      const body = lines.map(line => `<span class="lean-line${isCommentLine(line) ? ' is-comment' : ''}">`
        + `<span class="lean-line-code">${line}</span></span>`).join('');
      return `<div class="lean-block"><div class="lean-block-bar"><span>Lean</span>${copyButton}</div>`
        + `<pre><code class="lean">${body}</code></pre></div>\n`;
    }
    const attribute = language ? ` data-language="${escapeHtml(language)}"` : '';
    return `<div class="command-block"><div class="lean-block-bar"><span>${escapeHtml(language || 'Text')}</span>`
      + `${copyButton}</div><pre class="code-block"${attribute}><code>${escapeHtml(code)}</code></pre></div>\n`;
  };
  return md;
}

function renderMarkdown(md, text, where, chapterNumber) {
  const env = { where, chapterNumber };
  const tokens = md.parse(text, env);
  const html = md.renderer.render(tokens, md.options, env);
  const tokenText = token => {
    if (token.children) return token.children.map(tokenText).join('');
    if (token.type === 'softbreak' || token.type === 'hardbreak') return ' ';
    if (token.type === 'html_inline' || token.type === 'html_block') return '';
    return token.content;
  };
  return {
    html,
    searchText: tokens.map(tokenText).join(' ').replace(/\s+/g, ' ').trim(),
    mentions: [...(env.mentions ?? [])],
    unresolved: env.unresolved ?? [],
    figures: env.figures ?? [],
  };
}

// ---------------------------------------------------------------------------------------------
// Chapter front matter: a small YAML subset (scalars, [a, b] lists, and "- item" lists).

function parseFrontMatter(text, file) {
  const match = text.match(/^---\r?\n([\s\S]*?)\r?\n---\r?\n?/);
  if (!match) return { meta: {}, body: text };
  const meta = {};
  let currentList = null;
  for (const rawLine of match[1].split(/\r?\n/)) {
    const line = rawLine.replace(/\s+$/, '');
    if (!line.trim() || line.trim().startsWith('#')) continue;
    const item = line.match(/^\s+-\s*(.+)$/);
    if (item && currentList) { currentList.push(unquote(item[1])); continue; }
    const pair = line.match(/^([A-Za-z_][\w-]*):\s*(.*)$/);
    if (!pair) { warn(`${file}: cannot parse front matter line ${JSON.stringify(line)}`); continue; }
    const [, key, rawValue] = pair;
    if (rawValue === '') { currentList = []; meta[key] = currentList; continue; }
    currentList = null;
    if (rawValue.startsWith('[') && rawValue.endsWith(']')) {
      meta[key] = rawValue.slice(1, -1).split(',').map(part => unquote(part.trim())).filter(Boolean);
    } else meta[key] = unquote(rawValue);
  }
  return { meta, body: text.slice(match[0].length) };
}

function unquote(value) {
  const trimmed = value.trim();
  if ((trimmed.startsWith('"') && trimmed.endsWith('"')) || (trimmed.startsWith("'") && trimmed.endsWith("'"))) {
    return trimmed.slice(1, -1);
  }
  return trimmed;
}

// ---------------------------------------------------------------------------------------------
// Main.

async function main() {
  const { data, file: nodesFile } = await loadNodes();
  buildNodeIndex(data.nodes);
  const phases = data.phases.map(({ id, title }) => ({ id, title }));
  const phaseIds = new Set(phases.map(phase => phase.id));

  const parsed = JSON.parse(await readText(path.join(siteRoot, 'content', 'references.json')));
  const references = (Array.isArray(parsed) ? parsed : parsed.references ?? []).map(reference => ({
    key: String(reference.key),
    authors: reference.authors ?? '',
    title: reference.title ?? '',
    venue: reference.venue ?? '',
    year: reference.year === undefined ? '' : String(reference.year),
    url: reference.url ?? '',
  }));

  const md = createMarkdown(references);

  // Chapters.
  const files = await chapterFiles();
  const assetsDir = path.join(siteRoot, 'content', 'assets');
  const chapters = [];
  for (const file of files) {
    const text = await readText(file);
    const { meta, body } = parseFrontMatter(text, file);
    const base = path.basename(file, '.md');
    const numberFromName = base.match(/^(\d{2})-/);
    const slug = meta.slug ?? base.replace(/^\d{2}-/, '');
    const number = String(meta.number ?? numberFromName?.[1] ?? '').padStart(2, '0');
    const rendered = renderMarkdown(md, body, path.relative(siteRoot, file), number);
    const chapterPhases = Array.isArray(meta.phases) ? meta.phases : meta.phases ? [meta.phases] : [];
    for (const id of chapterPhases) {
      if (!phaseIds.has(id)) warn(`${path.relative(siteRoot, file)}: unknown phase ${id} in front matter`);
    }
    if (rendered.unresolved.length) {
      unresolvedLinks.push({ file: path.relative(siteRoot, file), names: rendered.unresolved });
      console.warn(`warning: ${path.relative(siteRoot, file)}: ${rendered.unresolved.length} [[node link]]`
        + `${rendered.unresolved.length === 1 ? '' : 's'} not among the exported declarations`);
    }
    for (const figure of rendered.figures) {
      const relative = figure.replace(/^assets\//, '');
      if (!figure.startsWith('assets/') || !existsSync(path.join(assetsDir, relative))) {
        warn(`${path.relative(siteRoot, file)}: figure ${figure} not found under content/assets`);
      }
    }
    chapters.push({
      number,
      slug,
      title: meta.title ?? slug,
      summary: meta.summary ?? '',
      file: path.relative(siteRoot, file),
      html: rendered.html,
      searchText: rendered.searchText,
      mentions: rendered.mentions,
    });
  }
  chapters.sort((left, right) => left.number.localeCompare(right.number) || left.slug.localeCompare(right.slug));
  const slugs = new Set();
  for (const chapter of chapters) {
    if (slugs.has(chapter.slug)) warn(`duplicate chapter slug ${chapter.slug}`);
    slugs.add(chapter.slug);
  }

  // Landing.
  // The overview's header comes from landing.md's front matter: `lede` (one paragraph under the
  // title) and `authors` (a list of "Name (Affiliation)" strings). Both are optional.
  const { meta, body } = parseFrontMatter(
    await readText(path.join(siteRoot, 'content', 'landing.md')), 'landing.md');
  for (const key of Object.keys(meta)) {
    if (!['lede', 'authors'].includes(key)) warn(`landing.md: unknown front matter key ${key}`);
  }
  const landing = {
    lede: typeof meta.lede === 'string' ? meta.lede : undefined,
    authors: Array.isArray(meta.authors) ? meta.authors : undefined,
    html: renderMarkdown(md, body, 'landing.md').html,
  };

  // Nodes: highlighted statement and source, rendered docstring, dependents, mentions.
  const dependents = new Map();
  for (const node of data.nodes) {
    for (const dependency of node.dependencies ?? []) {
      if (!nodeIndex.byId.has(dependency)) {
        warn(`${node.id}: dependency ${dependency} is not an exported node`);
        continue;
      }
      if (!dependents.has(dependency)) dependents.set(dependency, []);
      dependents.get(dependency).push(node.id);
    }
    if (!phaseIds.has(node.phase)) warn(`${node.id}: unknown phase ${node.phase}`);
  }
  const mentionedBy = new Map();
  for (const chapter of chapters) {
    for (const id of chapter.mentions) {
      if (!mentionedBy.has(id)) mentionedBy.set(id, []);
      mentionedBy.get(id).push(chapter.slug);
    }
  }
  const nodes = data.nodes.map(node => {
    const resolve = identifierResolver(node.id);
    const docstring = node.docstring ?? '';
    return {
      ...node,
      dependencies: (node.dependencies ?? []).filter(id => nodeIndex.byId.has(id)),
      dependents: dependents.get(node.id) ?? [],
      chapters: mentionedBy.get(node.id) ?? [],
      statementLines: highlightLeanLines(node.statement ?? '', resolve),
      sourceLines: highlightLeanLines(node.leanSource ?? '', resolve),
      docstringHtml: docstring ? renderMarkdown(md, docstring, `${node.id} docstring`).html : '',
    };
  });

  const site = {
    generatedAt: new Date().toISOString(),
    source: data.source,
    origin: {
      nodes: describePath(nodesFile),
      chapters: 'content/chapters',
    },
    phases,
    nodes,
    modules: await buildModuleGraph(path.resolve(siteRoot, '..')),
    chapters,
    landing,
    references,
  };

  await mkdir(path.join(publicDir, 'data'), { recursive: true });
  await writeFile(path.join(publicDir, 'data', 'site.json'), JSON.stringify(site));
  await writeFile(path.join(publicDir, 'mathjax.css'), `${adaptor.textContent(MathJax.chtmlStylesheet())}\n`);
  const fontsSource = path.join(path.dirname(require.resolve('mathjax')), 'output', 'chtml', 'fonts', 'woff-v2');
  await mkdir(path.join(publicDir, 'mathjax', 'fonts'), { recursive: true });
  await cp(fontsSource, path.join(publicDir, 'mathjax', 'fonts', 'woff-v2'), { recursive: true });
  await writeThirdPartyLicenses(publicDir, path.dirname(siteRoot));

  const report = [
    `# Reader build warnings (${site.generatedAt})`,
    '',
    ...warnings.map(message => `- ${message}`),
    '',
    '# Unresolved [[node links]] by chapter',
    '',
    ...unresolvedLinks.flatMap(entry => [`## ${entry.file}`, ...entry.names.map(name => `- ${name}`), '']),
  ];
  await writeFile(path.join(siteRoot, 'data', 'reader-warnings.md'), `${report.join('\n')}\n`);

  console.log(`site data: ${nodes.length} nodes, ${phases.length} phases, ${chapters.length} chapters, `
    + `${references.length} references (nodes from ${site.origin.nodes}, chapters from ${site.origin.chapters})`);
  console.log(`wrote ${path.relative(readerDir, path.join(publicDir, 'data', 'site.json'))}`);
  const unresolvedCount = unresolvedLinks.reduce((sum, entry) => sum + entry.names.length, 0);
  if (warnings.length || unresolvedCount) {
    console.log(`${warnings.length} warning${warnings.length === 1 ? '' : 's'}, ${unresolvedCount} unresolved node link`
      + `${unresolvedCount === 1 ? '' : 's'}; details in ${describePath(path.join(siteRoot, 'data', 'reader-warnings.md'))}`);
  }
}

await main();
