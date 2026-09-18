import { createRequire } from 'node:module';
import { readFile, readdir, writeFile } from 'node:fs/promises';
import path from 'node:path';

const require = createRequire(import.meta.url);

// These packages contribute code, styles, or fonts to the static site. Read their installed
// notices so a dependency update also updates the license text shipped with the reader.
export async function writeThirdPartyLicenses(publicDir, repoDir) {
  const reactDomRequire = createRequire(require.resolve('react-dom/package.json'));
  const packages = [
    ['react', require, 'LICENSE'],
    ['react-dom', require, 'LICENSE'],
    ['scheduler', reactDomRequire, 'LICENSE'],
    ['mathjax', require, 'LICENSE'],
    ['vite', require, 'LICENSE.md'],
  ];
  const sections = ['FloatLib website: third-party licenses'];
  for (const [name, resolveFrom, licenseFile] of packages) {
    const manifest = resolveFrom.resolve(`${name}/package.json`);
    const root = path.dirname(manifest);
    const { version } = JSON.parse(await readFile(manifest, 'utf8'));
    sections.push(`${name} ${version}`, await readFile(path.join(root, licenseFile), 'utf8'));
    for (const file of (await readdir(root)).filter(file => /^NOTICE(?:\..+)?$/i.test(file)).sort()) {
      sections.push(`${name}: ${file}`, await readFile(path.join(root, file), 'utf8'));
    }
    if (name === 'mathjax') {
      // The TeX font metadata specifies OFL-1.1, separately from MathJax's Apache license.
      // Review the embedded font notices when updating MathJax.
      if (version !== '3.2.2') {
        throw new Error('Review licenses/mathjax-fonts.txt for the updated MathJax fonts.');
      }
      sections.push(await readFile(new URL('../licenses/mathjax-fonts.txt', import.meta.url), 'utf8'));
    }
  }
  // The reader also retains adaptations from Conway, outside the npm dependency graph.
  const conwayDir = path.join(repoDir, 'third_party', 'licenses', 'conway');
  sections.push(
    await readFile(path.join(conwayDir, 'NOTICE.txt'), 'utf8'),
    await readFile(path.join(conwayDir, 'LICENSE'), 'utf8'),
  );
  await writeFile(path.join(publicDir, 'third-party-licenses.txt'), `${sections.join('\n\n')}\n`);
}
