#!/usr/bin/env python3
"""A.3-style comparison for the osp paper's blueprint (adapted from the osp-triviality model's check_a3.py).

Compares, node by node, the declarations that the rendered site records for each node
(blueprint-manifest.json, the statement previews' externalDecls) with the node map's (NODE_MAP.md),
and checks the manifest's warnings and the `uses` edges.

usage (from blueprint/): python3 check_nodes.py [--manifest FILE] [--node-map FILE]
"""
import json, re, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
arg = lambda k, d: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else d
MAN = arg('--manifest', os.path.join(HERE, '_out', 'site', 'html-multi', '-verso-data', 'blueprint-manifest.json'))
NMAP = arg('--node-map', os.path.join(HERE, 'NODE_MAP.md'))
NS = {'N.': 'OspOddDeformations.OspN.', 'M.': 'OspOddDeformations.OspN.Multi.', 'P.': 'OspOddDeformations.OspN.Presented.',
      'B.': 'OspOddDeformations.OspN.GroupB.', 'G.': 'OspOddDeformations.General.'}
def full(d):
    d = d.strip().strip('`')
    for k, v in NS.items():
        if d.startswith(k): return v + d[len(k):]
    raise SystemExit(f'unexpected declaration {d!r}')
def nid(tex): return tex.replace(':', '_').replace('-', '_')

text = open(NMAP, encoding='utf-8').read()
exp = {}
for line in text.splitlines():
    m = re.match(r'\|\s*(\d+)\s*\|\s*`([^`]+)`\s*\|[^|]*\|\s*(\w+)\s*\|([^|]*)\|', line)
    if m:
        cell = m.group(4).strip()
        exp[nid(m.group(2))] = [] if cell in ('—', '-', '') else [full(x) for x in cell.split(',')]
c1 = re.search(r'\*\*C1, Controls\*\*.*?Declarations:\s*(.*?)\. Its text', text, re.S).group(1).replace('\n', ' ')
exp['app_controls'] = [full(x) for x in c1.split(',')]
_c2 = re.search(r'\*\*C2, the text after Prop 5\.4\*\*.*?declarations?\s+(`.*?`), covers:', text, re.S)
exp['after_prop_factor'] = [full(x) for x in _c2.group(1).split(',')]
assert len(exp) == 27, len(exp)

man = json.load(open(MAN))
prev = {}
for p in man['previews']:
    if p.get('key', '').endswith('--statement') and p.get('label') in exp:
        prev[p['label']] = p
decls = lambda p: (p.get('codeData') or {}).get('externalDecls') or []
got = {l: sorted(d['canonical'] for d in decls(p)) for l, p in prev.items()}
present = {l: all(d['present'] for d in decls(p)) for l, p in prev.items()}
ok = True
print(f'{"node":26} {"node map":>8} {"site":>5}  result')
for l, want in exp.items():
    same = l in got and sorted(want) == got[l] and present[l]
    ok &= same
    print(f'{l:26} {len(want):8d} {len(got.get(l, [])):5d}  {"MATCH" if same else "MISMATCH"}')
extra = sorted(p['label'] for p in man['previews'] if p.get('key', '').endswith('--statement') and p['label'] not in exp)
print('nodes on the site but not in the node map:', extra); ok &= not extra
# warnings and nodes
nodes = man['graphs'][0]['nodes']
labels = sorted(n['label'] for n in nodes)
print('nodes on the site:', len(nodes), '  expected:', len(exp)); ok &= labels == sorted(exp)
w = {k: sum(1 for n in nodes if n['warnings'][k]) for k in ('missingExternalDecl', 'unknownRef', 'leanOnlyNoStatement')}
print('nodes with warnings:', w); ok &= not any(w.values())
# uses edges
edges = sorted((e['source'], e['target']) for e in man['graphs'][0]['edges'])
mine = sorted((nid(b.split()[0]), nid(a)) for a, b in (l.strip().split(' -> ') for l in open(os.path.join(HERE, 'uses_edges.txt'))
              if ' -> ' in l and not l.startswith('#')))
print('uses edges: site', len(edges), ' uses_edges.txt', len(mine), ' equal:', edges == mine); ok &= edges == mine
tot = sum(len(v) for v in exp.values())
print('declarations in the node map:', tot, ' unique:', len({x for v in exp.values() for x in v}))
print('RESULT:', 'ALL MATCH' if ok else 'MISMATCH'); sys.exit(0 if ok else 1)
