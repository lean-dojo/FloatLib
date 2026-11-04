import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import test from 'node:test';
import ts from 'typescript';

const source = await readFile(new URL('../src/routes.ts', import.meta.url), 'utf8');
const { outputText } = ts.transpileModule(source, {
  compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022 },
});
// The transpiled router runs from a data URL, so give its JSON import an absolute module URL.
const aliasesText = await readFile(new URL('../src/chapter-aliases.json', import.meta.url), 'utf8');
const aliases = JSON.parse(aliasesText);
const aliasModule = `export default JSON.parse(${JSON.stringify(aliasesText)});`;
const aliasUrl = `data:text/javascript;base64,${Buffer.from(aliasModule).toString('base64')}`;
const aliasImport = /(['"])\.\/chapter-aliases\.json\1/;
assert.match(outputText, aliasImport);
const moduleText = outputText.replace(aliasImport, JSON.stringify(aliasUrl));
const { chapterPath, graphPath, nodePath, parseRoute } = await import(
  `data:text/javascript;base64,${Buffer.from(moduleText).toString('base64')}`);

test('declaration links preserve question marks and Unicode', () => {
  const id = 'FloatLib.Numerics.toDyadic?';
  assert.deepEqual(parseRoute(`#${nodePath(id)}`), { kind: 'node', id });
  assert.deepEqual(parseRoute('#/node/FloatLib.Numerics.α?'), {
    kind: 'node', id: 'FloatLib.Numerics.α?',
  });
});

test('graph links preserve the view and selected declaration', () => {
  assert.deepEqual(parseRoute('#/graph'), { kind: 'graph', view: 'modules', selected: undefined });
  assert.deepEqual(parseRoute('#/graph?node='), { kind: 'graph', view: 'modules', selected: undefined });
  assert.deepEqual(parseRoute('#/graph?view=declarations&node=FloatLib.Numerics.%CE%B1%3F'), {
    kind: 'graph', view: 'declarations', selected: 'FloatLib.Numerics.α?',
  });
  for (const view of ['modules', 'declarations']) {
    const selected = 'FloatLib.Numerics.α?';
    assert.deepEqual(parseRoute(`#${graphPath(view, selected)}`), { kind: 'graph', view, selected });
  }
});

test('chapter anchors and malformed escapes retain their existing behavior', () => {
  assert.deepEqual(parseRoute(`#${chapterPath('using-the-library', 'choosing the format')}`), {
    kind: 'chapter', slug: 'using-the-library', heading: 'choosing the format',
  });
  assert.deepEqual(parseRoute('#/node/%invalid'), { kind: 'node', id: '%invalid' });
});

test('reference links open the bibliography', () => {
  assert.deepEqual(parseRoute('#/references'), { kind: 'references', key: undefined });
  assert.deepEqual(parseRoute('#/references/ieee754_2019'), {
    kind: 'references', key: 'ieee754_2019',
  });
  assert.deepEqual(parseRoute('#/chapter/using-the-library/what-the-theorems-give-you'), {
    kind: 'chapter', slug: 'using-the-library', heading: 'how-to-prove-your-first-theorem',
  });
});

test('moved sections resolve directly across the revised chapters', () => {
  const destinations = [
    ['using-the-library', 'library-structure', 'using-the-library',
      'where-do-the-theorems-come-from'],
    ['using-the-library', 'complex-arithmetic', 'ieee-binary-formats', 'how-to-work-with-complex-numbers'],
    ['using-the-library', 'reductions-that-round-once', 'the-mathematics-of-rounding',
      'how-to-add-a-list-with-one-rounding'],
    ['why-execution-and-proofs-are-separate', 'lean-compilation-and-code-extraction',
      'the-numerical-models', 'how-is-this-different-from-code-extraction'],
    ['ieee-binary-formats', 'applying-a-real-valued-arithmetic-theorem', 'ieee-binary-formats',
      'what-the-theorems-give-you'],
    ['ieee-binary-formats', 'decimal-interchange', 'decimal-arithmetic',
      'how-decimal-numbers-are-stored-in-bits'],
    ['ieee-binary-formats', 'stable-decimal-exponential-and-logarithm', 'elementary-functions',
      'how-to-use-these-functions-with-decimal-numbers'],
    ['low-precision-formats-for-machine-learning', 'affine-integer-quantization',
      'fixed-point-logarithmic-codebook-and-block-scaled', 'what-is-affine-quantization'],
    ['posits-and-the-quire', 'where-the-posit-work-stops', 'posits-and-the-quire',
      'how-does-a-posit-round'],
    ['kernels-fixed-word-algorithms', 'capacity-bounds-and-compiler-assumptions',
      'performance', 'what-are-the-capacity-bounds'],
    ['backends-and-the-planner', 'choosing-and-caching-an-implementation',
      'performance', 'how-an-ordinary-addition-reaches-its-kernel'],
    ['performance', 'timing-results', 'performance', 'how-fast-are-the-calls-you-write-yourself'],
    ['performance', 'comparing-with-leans-native-floats', 'performance',
      'how-does-floatlib-compare-with-softfloat-mpfr-and-native-c'],
  ];
  for (const [oldSlug, oldHeading, slug, heading] of destinations) {
    assert.deepEqual(parseRoute(`#${chapterPath(oldSlug, oldHeading)}`), {
      kind: 'chapter', slug, heading,
    });
  }
});

test('native-float section bookmarks follow the split from the performance chapter', () => {
  const destinations = [
    ['leans-model-and-its-compiled-operations', 'what-are-float-and-float32'],
    ['both-implementations-lose-associativity', 'do-lean-and-floatlib-give-the-same-answers'],
    ['converting-to-native-floats-changes-nan-payloads', 'why-do-nans-come-out-different'],
    ['proofs-relating-floatlib-to-leans-float-model', 'how-to-convert-between-leans-floats-and-floatlib'],
    ['integer-conversions-in-lean-434', 'how-to-convert-integers-to-floats-and-back'],
    ['arithmetic-through-the-same-model', 'what-is-proved-about-leans-arithmetic'],
    ['formats-rounding-directions-and-status', 'what-does-floatlib-add-to-float-and-float32'],
    ['opting-into-guarded-host-operations', 'how-to-use-the-processors-own-arithmetic'],
    ['the-same-finite-bits-including-rounding-effects', 'do-lean-and-floatlib-give-the-same-answers'],
    ['nan-payloads-change-at-the-native-conversion-boundary',
      'why-do-nans-come-out-different'],
    ['the-proved-conversion-and-arithmetic-bridges',
      'how-to-convert-between-leans-floats-and-floatlib'],
  ];
  for (const [oldHeading, heading = oldHeading] of destinations) {
    assert.deepEqual(parseRoute(`#${chapterPath('performance', oldHeading)}`), {
      kind: 'chapter', slug: 'lean-native-floats', heading,
    });
  }
});

test('alias destinations never require a second router pass', () => {
  // Include headings inherited through a chapter rename, not just its explicit overrides.
  const headings = new Set(Object.values(aliases).flatMap(alias => Object.keys(alias.headings ?? {})));
  for (const slug of Object.keys(aliases)) {
    for (const heading of [undefined, ...headings]) {
      const path = chapterPath(slug, heading);
      const route = parseRoute(`#${path}`);
      assert.equal(route.kind, 'chapter', path);
      assert.deepEqual(parseRoute(`#${chapterPath(route.slug, route.heading)}`), route, path);
    }
  }
});

test('alias resolution decodes names once and ignores inherited object properties', () => {
  assert.deepEqual(parseRoute('#/chapter/perform%61nce/timing-%72esults'), {
    kind: 'chapter', slug: 'performance', heading: 'how-fast-are-the-calls-you-write-yourself',
  });
  for (const heading of ['toString', '__proto__', 'unknown-section', '%invalid']) {
    assert.deepEqual(parseRoute(`#${chapterPath('performance', heading)}`), {
      kind: 'chapter', slug: 'performance', heading,
    });
  }
  for (const slug of ['toString', '__proto__', 'unknown-chapter', '%invalid']) {
    assert.deepEqual(parseRoute(`#${chapterPath(slug, 'section')}`), {
      kind: 'chapter', slug, heading: 'section',
    });
  }
});
