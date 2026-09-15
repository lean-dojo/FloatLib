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

test('map bookmarks open the declaration graph and preserve the selected declaration', () => {
  for (const hash of ['#/map', '#/map/', '#/map/rounding', '#/map/rounding/', '#/map?node=']) {
    assert.deepEqual(parseRoute(hash), { kind: 'graph', view: 'declarations', selected: undefined });
  }
  assert.deepEqual(parseRoute('#/map?node=FloatLib.Numerics.%CE%B1%3F'), {
    kind: 'graph', view: 'declarations', selected: 'FloatLib.Numerics.α?',
  });
  assert.deepEqual(parseRoute('#/graph'), { kind: 'graph', view: 'modules', selected: undefined });
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

test('merged chapter bookmarks open the corresponding section', () => {
  const defaults = [
    ['what-imprecision-has-cost', 'a-short-history-of-floating-point', 'what-imprecision-has-cost'],
    ['comparing-with-lean-native-floats', 'performance', 'comparing-with-leans-native-floats'],
    ['a-tour-of-the-codebase', 'using-the-library', 'a-tour-of-the-codebase'],
  ];
  for (const [oldSlug, slug, heading] of defaults) {
    assert.deepEqual(parseRoute(`#${chapterPath(oldSlug)}`), { kind: 'chapter', slug, heading });
  }
});

test('incident and native-float bookmarks preserve individual headings', () => {
  for (const [oldSlug, slug] of [
    ['what-imprecision-has-cost', 'a-short-history-of-floating-point'],
    ['comparing-with-lean-native-floats', 'performance'],
  ]) {
    for (const heading of ['an-existing-section', 'a heading/with α?', '%invalid']) {
      assert.deepEqual(parseRoute(`#${chapterPath(oldSlug, heading)}`), {
        kind: 'chapter', slug, heading,
      });
    }
  }
});

test('old references chapter bookmarks open the bibliography', () => {
  for (const heading of [
    undefined, 'the-incidents-in-chapter-03', 'the-incidents-in-chapter-04', 'another-section',
  ]) {
    assert.deepEqual(parseRoute(`#${chapterPath('references', heading)}`), {
      kind: 'references', key: undefined,
    });
  }
  assert.deepEqual(parseRoute('#/references'), { kind: 'references', key: undefined });
  assert.deepEqual(parseRoute('#/references/ieee754_2019'), {
    kind: 'references', key: 'ieee754_2019',
  });
  assert.deepEqual(parseRoute('#/chapter/using-the-library/what-the-theorems-give-you'), {
    kind: 'chapter', slug: 'using-the-library', heading: 'what-the-theorems-give-you',
  });
});

test('every old tour heading follows its section to the current chapter', () => {
  const destinations = [
    ['the-shape-of-the-tree', 'using-the-library', 'a-tour-of-the-codebase'],
    ['numerics-exact-values-and-contracts', 'the-numerical-models'],
    ['kernels-fixed-word-algorithms-and-limb-arrays', 'kernels-fixed-word-algorithms'],
    ['formats-encodings-and-their-meaning', 'ieee-binary-formats'],
    ['execfloat-the-carrier-and-its-backends', 'backends-and-the-planner'],
    ['public-and-private-imports', 'why-execution-and-proofs-are-separate'],
    ['tests-what-is-validated', 'external-validation'],
    ['benchmarks-and-the-website', 'why-execution-and-proofs-are-separate',
      'how-the-website-examples-are-checked'],
    ['what-the-check-scripts-enforce', 'why-execution-and-proofs-are-separate',
      'the-check-that-enforces-the-split'],
    ['examples-and-extension-guides', 'using-the-library'],
  ];
  for (const [oldHeading, slug, heading = oldHeading] of destinations) {
    const route = parseRoute(`#${chapterPath('a-tour-of-the-codebase', oldHeading)}`);
    assert.deepEqual(route, { kind: 'chapter', slug, heading });
    assert.deepEqual(parseRoute(`#${chapterPath(route.slug, route.heading)}`), route);
  }
});

test('alias resolution decodes names once and ignores inherited object properties', () => {
  assert.deepEqual(parseRoute('#/chapter/a-tour-of-the-%63odebase/the-shape-of-the-%74ree'), {
    kind: 'chapter', slug: 'using-the-library', heading: 'a-tour-of-the-codebase',
  });
  for (const heading of ['toString', '__proto__', 'unknown-section', '%invalid']) {
    assert.deepEqual(parseRoute(`#${chapterPath('a-tour-of-the-codebase', heading)}`), {
      kind: 'chapter', slug: 'using-the-library', heading,
    });
  }
  for (const slug of ['toString', '__proto__', 'unknown-chapter', '%invalid']) {
    assert.deepEqual(parseRoute(`#${chapterPath(slug, 'section')}`), {
      kind: 'chapter', slug, heading: 'section',
    });
  }
});
