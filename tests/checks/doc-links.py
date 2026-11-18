#!/usr/bin/env python3
"""Check the links of the repository's Markdown files.

For every tracked ``.md`` file outside ``benchmarks/``, ``third_party/`` and the result bundles this
checks

* guide links ``#/chapter/<slug>`` and ``#/chapter/<slug>/<anchor>``: the chapter exists, and the
  anchor is a heading, an explicit ``<a id>`` or a figure of that chapter;
* relative links: the file exists, and an anchor into a Markdown file is one of its headings;
* links to ``github.com/lean-dojo/FloatLib/blob/main/<path>``: the path exists in this checkout;
* in the guide chapters, ``[@key]`` citations against ``site/content/references.json`` and
  ``[[Full.Lean.Name]]`` links against the nodes of ``site/content/phases.json``.

The reader's own build resolves the same links when it renders the site. This check needs no
build and no JavaScript, so ``tests/verify.sh`` can run it first. It prints one line per broken
link and exits 1 when there is one. Python standard library only.
"""
import json, re, subprocess, sys, unicodedata
from pathlib import Path

root = Path(__file__).resolve().parents[2]
files = subprocess.run(['git', '-C', str(root), 'ls-files', '*.md'], capture_output=True, text=True).stdout.split('\n')
files = [f for f in files if f and not f.startswith(('benchmarks/', 'third_party/', 'tests/results/'))]
chapters_dir = root / 'site/content/chapters'

def strip_code(text):
    return re.sub(r'```.*?```', '', text, flags=re.S)

def reader_slug(text):
    text = re.sub(r'\$[^$]*\$', '', text)
    text = text.replace('`', '')
    text = re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', text)
    text = unicodedata.normalize('NFKD', text.lower())
    text = re.sub(r'[^\w\s-]', '', text).strip()
    text = re.sub(r'[\s_]+', '-', text)
    return re.sub(r'-+', '-', text) or 'section'

def github_slug(text):
    text = text.replace('`', '')
    text = re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', text)
    text = text.strip().lower()
    text = re.sub(r'[^\w\s-]', '', text)
    return text.replace(' ', '-')

def headings(text):
    return [m.group(2).strip() for m in re.finditer(r'^(#{1,6}) +(.+?)\s*$', strip_code(text), flags=re.M)]

def ids(text, slug):
    seen, out = {}, set()
    for h in headings(text):
        s = slug(h)
        n = seen.get(s, 0); seen[s] = n + 1
        out.add(s if n == 0 else (f'{s}-{n + 1}' if slug is reader_slug else f'{s}-{n}'))
    out.update(re.findall(r'<a id="([^"]+)"', text))
    return out

chapter = {}
for path in sorted(chapters_dir.glob('*.md')):
    text = path.read_text()
    m = re.search(r'^slug: *"?([A-Za-z0-9-]+)"?', text, flags=re.M)
    anchors = ids(text, reader_slug)
    for img in re.findall(r'!\[[^\]]*\]\(assets/([^)\s"]+)', text):
        anchors.add('figure-' + reader_slug(Path(img).stem))
    chapter[m.group(1)] = anchors

refs = {e['key'] for e in json.loads((root / 'site/content/references.json').read_text())}
nodes = set()
for phase in json.loads((root / 'site/content/phases.json').read_text())['phases']:
    for node in phase['nodes']:
        nodes.add(node if isinstance(node, str) else node['name'])

bad = []
for rel in files:
    path = root / rel
    text = path.read_text()
    body = re.sub(r'`[^`\n]*`', '``', strip_code(text))
    is_chapter = path.parent == chapters_dir
    for m in re.finditer(r'\]\(([^)\s]+)(?:\s+"[^"]*")?\)', body):
        target = m.group(1)
        if target.startswith('#/chapter/'):
            parts = target[len('#/chapter/'):].split('/')
            if parts[0] not in chapter:
                bad.append((rel, target, 'no such chapter'))
            elif len(parts) > 1 and parts[1] not in chapter[parts[0]]:
                bad.append((rel, target, 'no such anchor in the chapter'))
        elif target.startswith('#/'):
            continue
        elif target.startswith('https://github.com/lean-dojo/FloatLib/blob/main/'):
            p, _, anchor = target[len('https://github.com/lean-dojo/FloatLib/blob/main/'):].partition('#')
            if not (root / p).exists():
                bad.append((rel, target, 'no such file in the repository'))
            elif anchor and p.endswith('.md') and anchor not in ids((root / p).read_text(), github_slug):
                bad.append((rel, target, 'no such heading in the file'))
        elif target.startswith('https://github.com/lean-dojo/FloatLib/tree/main/'):
            p = target[len('https://github.com/lean-dojo/FloatLib/tree/main/'):].split('#')[0]
            if not (root / p).exists():
                bad.append((rel, target, 'no such directory in the repository'))
        elif re.match(r'^[a-z]+:', target):
            continue
        elif target.startswith('#'):
            if is_chapter:
                slug = re.search(r'^slug: *"?([A-Za-z0-9-]+)"?', text, flags=re.M).group(1)
                if target[1:] not in chapter[slug]:
                    bad.append((rel, target, 'no such anchor in this chapter'))
            elif target[1:] not in ids(text, github_slug):
                bad.append((rel, target, 'no such heading in this file'))
        else:
            p, _, anchor = target.partition('#')
            if is_chapter and p.startswith('assets/'):
                if not (root / 'site/content' / p).exists():
                    bad.append((rel, target, 'no such asset'))
                continue
            dest = (path.parent / p).resolve()
            if not dest.exists():
                bad.append((rel, target, 'no such file'))
            elif anchor and dest.suffix == '.md' and anchor not in ids(dest.read_text(), github_slug):
                bad.append((rel, target, 'no such heading in the file'))
    if is_chapter:
        for key in re.findall(r'\[@([A-Za-z0-9_:.-]+)\]', body):
            if key not in refs:
                bad.append((rel, '[@' + key + ']', 'no such reference'))
        for name in re.findall(r'\[\[([^\]]+)\]\]', body):
            if name not in nodes:
                bad.append((rel, '[[' + name + ']]', 'no such node in phases.json'))
for rel, target, why in bad:
    print(f'{rel}: {target}: {why}')
print(f'{len(files)} files, {len(bad)} broken link(s)')
sys.exit(1 if bad else 0)
