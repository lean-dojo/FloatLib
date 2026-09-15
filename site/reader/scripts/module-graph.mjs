import { readdir, readFile } from 'node:fs/promises';
import path from 'node:path';

// Read only the import header. Nested comments can contain examples of imports; neither those
// examples nor strings in later declarations belong in the module graph.
export function moduleImports(source) {
  let offset = 0;
  function token() {
    for (;;) {
      const space = /^\s+/.exec(source.slice(offset));
      if (space) { offset += space[0].length; continue; }
      if (source.startsWith('--', offset)) {
        const end = source.indexOf('\n', offset);
        offset = end < 0 ? source.length : end + 1;
        continue;
      }
      if (!source.startsWith('/-', offset)) break;
      let depth = 1;
      offset += 2;
      while (offset < source.length && depth) {
        if (source.startsWith('/-', offset)) { depth++; offset += 2; }
        else if (source.startsWith('-/', offset)) { depth--; offset += 2; }
        else offset++;
      }
      if (depth) throw new Error('Unclosed comment in a Lean module header');
    }
    const word = /^[\p{L}_][\p{L}\p{N}_'.]*/u.exec(source.slice(offset));
    if (!word) return '';
    offset += word[0].length;
    return word[0];
  }
  const imports = [];
  for (let word = token(); word; word = token()) {
    if (word === 'module' || word === 'prelude') continue;
    let meta = false;
    while (word === 'public' || word === 'meta') {
      meta ||= word === 'meta';
      word = token();
    }
    if (word !== 'import') break;
    let name = token();
    if (name === 'all') name = token();
    if (!name) throw new Error('Missing module name after import');
    imports.push({ name, meta });
  }
  return imports;
}

export async function buildModuleGraph(root) {
  async function files(directory) {
    const entries = await readdir(path.join(root, directory), { withFileTypes: true });
    const groups = await Promise.all(entries.map(entry => {
      const relative = path.join(directory, entry.name);
      return entry.isDirectory() ? files(relative)
        : entry.isFile() && entry.name.endsWith('.lean') ? [relative] : [];
    }));
    return groups.flat();
  }
  const sources = ['FloatLib.lean', ...await files('FloatLib')].sort();
  const modules = await Promise.all(sources.map(async file => {
    const id = file.replaceAll(path.sep, '.').replace(/\.lean$/, '');
    const parts = id.split('.');
    const group = parts[1] === 'Floats' ? parts[2] === 'Formats' ? parts[3] ?? 'Formats'
      : parts[2] ?? 'Floats' : parts[1] ?? 'FloatLib';
    const imports = moduleImports(await readFile(path.join(root, file), 'utf8'))
      .filter(entry => entry.name === 'FloatLib' || entry.name.startsWith('FloatLib.'));
    return {
      id, file: file.replaceAll(path.sep, '/'), group,
      dependencies: [...new Set(imports.map(entry => entry.name))],
      metaDependencies: [...new Set(imports.filter(entry => entry.meta).map(entry => entry.name))],
    };
  }));
  const byId = new Map(modules.map(module => [module.id, module]));
  const visiting = new Set();
  const done = new Set();
  function visit(id) {
    if (!byId.has(id)) throw new Error(`Module graph has a missing import: ${id}`);
    if (visiting.has(id)) throw new Error(`Module graph has an import cycle at ${id}`);
    if (done.has(id)) return;
    visiting.add(id);
    byId.get(id).dependencies.forEach(visit);
    visiting.delete(id);
    done.add(id);
  }
  modules.forEach(module => visit(module.id));
  return modules;
}
