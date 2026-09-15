// A small Lean 4 tokenizer for syntax highlighting at build time.
//
// The Conway reader gets its highlighting from SubVerso, which runs the Lean elaborator and knows
// what every identifier refers to. We do not have that here: the export pipeline gives us source
// text, and chapter code blocks are plain Markdown fences. So we tokenize lexically (comments,
// strings, numbers, keywords, attributes, commands) and leave identifiers alone, except that a
// resolver may turn an identifier into a link when it names a node of the map. The text of every
// token is emitted verbatim, so the code a reader copies is exactly the code in the repository.

const KEYWORDS = new Set([
  'theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'instance', 'inductive', 'where',
  'with', 'match', 'fun', 'let', 'have', 'show', 'from', 'by', 'do', 'return', 'if', 'then', 'else',
  'namespace', 'section', 'end', 'open', 'import', 'export', 'variable', 'universe', 'deriving',
  'example', 'mutual', 'private', 'protected', 'noncomputable', 'partial', 'unsafe', 'macro',
  'macro_rules', 'syntax', 'elab', 'termination_by', 'decreasing_by', 'at', 'in', 'axiom', 'opaque',
  'set_option', 'attribute', 'local', 'scoped', 'notation', 'infix', 'infixl', 'infixr', 'prefix',
  'postfix', 'module', 'public', 'extends', 'for', 'unless', 'try', 'catch', 'finally', 'break',
  'continue', 'calc', 'exact', 'intro', 'intros', 'apply', 'refine', 'rw', 'rwa', 'simp', 'simpa',
  'simp_all', 'obtain', 'rcases', 'rintro', 'cases', 'induction', 'constructor', 'omega', 'decide',
  'rfl', 'trivial', 'ring', 'linarith', 'nlinarith', 'positivity', 'norm_num', 'field_simp', 'use',
  'exists', 'ext', 'funext', 'congr', 'gcongr', 'aesop', 'grind', 'tauto', 'contradiction',
  'exfalso', 'assumption', 'specialize', 'generalize', 'subst', 'change', 'unfold', 'delta', 'dsimp',
  'split', 'next', 'case', 'left', 'right', 'symm', 'trans', 'push_cast', 'norm_cast', 'lift',
  'exact_mod_cast', 'nomatch', 'nofun', 'this', 'Type', 'Prop', 'Sort',
]);
const SORTS = new Set(['Type', 'Prop', 'Sort']);
const SYMBOL_KEYWORDS = new Set(['∀', '∃', 'λ', 'Π', 'Σ']);

const IDENT_START = /[\p{L}_]/u;
const IDENT_REST = /[\p{L}\p{N}_'!?\u2080-\u209C\u1D62-\u1D6A]/u;

function escapeHtml(value) {
  return value.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;');
}

/**
 * An identifier as HTML, with a break opportunity after every dot and underscore inside it. In a
 * scrolling block (white-space: pre) a <wbr> does nothing; in a wrapped statement it lets a name
 * such as `Configured.StoragePlan` or `sumWithStatus_eq_round_of_finite_nonzero` wrap at its
 * joints instead of mid-word. <wbr> has no text content, so copied text is unchanged.
 */
function identifierHtml(text) {
  return escapeHtml(text).replace(/([._])(?=.)/g, '$1<wbr>');
}

// A comment token of this many characters or fewer fits a line by itself in every Lean block the
// reader shows (32 characters at 13px mono is about 250px), so it gets no joints: a joint in a
// short name would only let `Nat.sqrt` split across a line end where moving it whole reads better.
const COMMENT_JOINT_MIN_LENGTH = 32;

/**
 * Comment text as HTML, with a break opportunity after a dot or underscore that sits between
 * word characters inside a long token (a name such as
 * `FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode.nearestEven` printed by
 * #eval). Comment lines wrap when the block is at its wide stop, and without these joints a long
 * printed name broke mid-word. Sentence punctuation (a dot before a space) and numbers (a dot
 * before a digit) get no break. Tokens are split on whitespace after escaping; the entities
 * escapeHtml produces contain no joint characters.
 */
function commentHtml(text) {
  return escapeHtml(text).split(/(\s+)/).map(part => part.length > COMMENT_JOINT_MIN_LENGTH
    ? part.replace(/(?<=[\p{L}\p{N}_?!'])([._])(?=[\p{L}_])/gu, '$1<wbr>') : part).join('');
}

/**
 * Whether a highlighted line consists of a comment and nothing else (a `-- result` line, or one
 * line of a doc comment). The reader wraps such lines inside the visible width once the block is
 * at its wide stop; see .lean-line.is-comment in styles.css. The tokenizer emits one span per
 * comment line, escapes every `<` in its text, and adds only <wbr> tags, so the test is exact.
 * LeanBlock.tsx carries the same expression.
 */
export function isCommentLine(lineHtml) {
  return /^\s*<span class="lean-(?:comment|doc)">(?:[^<]|<wbr>)*<\/span>\s*$/.test(lineHtml);
}

/** Split `source` into [{kind, text}] tokens whose concatenated text is the source. */
export function tokenizeLean(source) {
  const tokens = [];
  const push = (kind, text) => { if (text) tokens.push({ kind, text }); };
  let index = 0;
  const length = source.length;
  while (index < length) {
    const char = source[index];
    const next = source[index + 1];
    // Block comments, nested, doc comments included.
    if (char === '/' && next === '-') {
      const doc = source[index + 2] === '-' || source[index + 2] === '!';
      let depth = 0;
      let end = index;
      while (end < length) {
        if (source[end] === '/' && source[end + 1] === '-') { depth += 1; end += 2; continue; }
        if (source[end] === '-' && source[end + 1] === '/') {
          depth -= 1; end += 2;
          if (depth === 0) break;
          continue;
        }
        end += 1;
      }
      push(doc ? 'doc' : 'comment', source.slice(index, end));
      index = end;
      continue;
    }
    // Line comments.
    if (char === '-' && next === '-') {
      let end = source.indexOf('\n', index);
      if (end === -1) end = length;
      push('comment', source.slice(index, end));
      index = end;
      continue;
    }
    // Strings.
    if (char === '"') {
      let end = index + 1;
      while (end < length && source[end] !== '"') {
        if (source[end] === '\\') end += 1;
        end += 1;
      }
      end = Math.min(end + 1, length);
      push('str', source.slice(index, end));
      index = end;
      continue;
    }
    // Character literals: 'a' or '\n', but not the prime in h'.
    if (char === "'" && index > 0 && !IDENT_REST.test(source[index - 1])) {
      const literal = source.slice(index).match(/^'(?:\\.|[^'\\])'/u);
      if (literal) {
        push('str', literal[0]);
        index += literal[0].length;
        continue;
      }
    }
    // Attributes: @[simp], @[csimp], @[grind =] ...
    if (char === '@' && next === '[') {
      let end = source.indexOf(']', index);
      end = end === -1 ? length : end + 1;
      push('attr', source.slice(index, end));
      index = end;
      continue;
    }
    // Commands such as #eval and #float_info.
    if (char === '#') {
      const command = source.slice(index).match(/^#[A-Za-z_][A-Za-z_!?]*/u);
      if (command) {
        push('cmd', command[0]);
        index += command[0].length;
        continue;
      }
    }
    // Numbers.
    if (/[0-9]/.test(char)) {
      const number = source.slice(index)
        .match(/^(?:0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|[0-9][0-9_]*(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)/u);
      push('num', number[0]);
      index += number[0].length;
      continue;
    }
    // Identifiers, possibly dotted, possibly «guillemet-quoted».
    if (IDENT_START.test(char) || char === '«') {
      let end = index;
      const consumePart = () => {
        if (source[end] === '«') {
          const close = source.indexOf('»', end);
          end = close === -1 ? length : close + 1;
          return true;
        }
        if (!IDENT_START.test(source[end])) return false;
        end += 1;
        while (end < length && IDENT_REST.test(source[end])) end += 1;
        return true;
      };
      consumePart();
      while (source[end] === '.' && end + 1 < length
        && (IDENT_START.test(source[end + 1]) || source[end + 1] === '«')) {
        end += 1;
        consumePart();
      }
      const text = source.slice(index, end);
      if (text === 'sorry') push('sorry', text);
      else if (SORTS.has(text)) push('sort', text);
      else if (KEYWORDS.has(text)) push('kw', text);
      else push('ident', text);
      index = end;
      continue;
    }
    if (SYMBOL_KEYWORDS.has(char)) {
      push('kw', char);
      index += 1;
      continue;
    }
    // Whitespace and everything else, one run at a time.
    if (char === '\n') {
      push('text', '\n');
      index += 1;
      continue;
    }
    let end = index + 1;
    while (end < length && !/[\s"'@#0-9/\-«]/u.test(source[end]) && !IDENT_START.test(source[end])
      && !SYMBOL_KEYWORDS.has(source[end])) end += 1;
    push('text', source.slice(index, end));
    index = end;
  }
  return tokens;
}

/**
 * Highlight Lean source and return one HTML string per line. `resolve(name)` may return a node
 * id for an identifier (full or short), in which case the identifier becomes a link.
 */
export function highlightLeanLines(source, resolve) {
  const lines = [''];
  const append = html => { lines[lines.length - 1] += html; };
  for (const token of tokenizeLean(source)) {
    const pieces = token.text.split('\n');
    pieces.forEach((piece, pieceIndex) => {
      if (pieceIndex > 0) lines.push('');
      if (!piece) return;
      if (token.kind === 'text') { append(escapeHtml(piece)); return; }
      if (token.kind === 'ident') {
        const target = resolve ? resolve(piece) : null;
        if (target) {
          append(`<a class="lean-ref" href="#/node/${encodeURIComponent(target)}" `
            + `title="${escapeHtml(target)}">${identifierHtml(piece)}</a>`);
        } else append(identifierHtml(piece));
        return;
      }
      const html = token.kind === 'comment' || token.kind === 'doc' ? commentHtml(piece) : escapeHtml(piece);
      append(`<span class="lean-${token.kind}">${html}</span>`);
    });
  }
  return lines;
}
