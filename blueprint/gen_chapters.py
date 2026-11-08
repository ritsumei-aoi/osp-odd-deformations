#!/usr/bin/env python3
"""Generate the blueprint chapters from the paper's .tex and the binding node map.

usage (from blueprint/): python3 gen_chapters.py --tex PATH/TO/aoi2026_osp_odd_deformations.tex

Inputs
  * the paper's LaTeX source (--tex)     statement environments, proofs, labels
  * NODE_MAP.md                          the node map: statuses and declarations
Outputs
  * OspOddDeformationsBlueprint/Chapters/*.lean    one chapter per paper section (2-6), and App. A
  * uses_edges.txt                       every `uses` edge, node -> node, with its source

Nothing here is mathematics: a node's statement is the paper's statement environment, converted
mechanically from LaTeX to the blueprint's markup; its proof is one line; its status is one of
three fixed sentences chosen from the node map.
"""
import re, sys, os, json

HERE = os.path.dirname(os.path.abspath(__file__))
if '--tex' not in sys.argv:
    raise SystemExit('gen_chapters: give the paper with --tex PATH (the paper is not part of this repository)')
TEX = sys.argv[sys.argv.index('--tex') + 1]
src = open(TEX, encoding='utf-8').read()

# ------------------------------------------------------------------ node map
NS = {'N.': 'OspOddDeformations.OspN.', 'M.': 'OspOddDeformations.OspN.Multi.', 'P.': 'OspOddDeformations.OspN.Presented.',
      'B.': 'OspOddDeformations.OspN.GroupB.', 'G.': 'OspOddDeformations.General.'}
def full_decl(d):
    d = d.strip().strip('`')
    for k, v in NS.items():
        if d.startswith(k):
            return v + d[len(k):]
    raise SystemExit(f'gen_chapters: unexpected declaration prefix in {d!r}')

def parse_decls(cell):
    cell = cell.strip()
    if cell in ('—', '-', ''):
        return []
    return [full_decl(x) for x in cell.split(',')]

NODES = []            # dicts, in the node map's order
for line in open(os.path.join(HERE, 'NODE_MAP.md'), encoding='utf-8'):
    m = re.match(r'\|\s*(\d+)\s*\|\s*`([^`]+)`\s*\|([^|]*)\|\s*(\w+)\s*\|([^|]*)\|(.*)\|\s*$', line)
    if not m:
        continue
    num, label, kt, status, decls, covers = m.groups()
    NODES.append(dict(n=int(num), tex=label, kt=kt.strip(), status=status, decls=parse_decls(decls),
                      covers=covers.strip()))
assert len(NODES) == 25, len(NODES)
# the two extra nodes, from the node map's last paragraph
_nm = open(os.path.join(HERE, 'NODE_MAP.md'), encoding='utf-8').read().replace('\n', ' ')
_c1 = re.search(r'\*\*C1, Controls\*\*.*?covers: "(.*?)"\. Declarations: (.*?)\. Its text', _nm)
C1_COVERS = re.sub(r' +', ' ', _c1.group(1))
C1_DECLS = [full_decl(x) for x in _c1.group(2).split(',')]
assert len(C1_DECLS) == 8, C1_DECLS
_c2 = re.search(r'\*\*C2, the text after Prop 5\.4\*\*.*?declarations?\s+(`.*?`), covers: "(.*?)"\.', _nm, re.S)
C2_DECLS = [full_decl(x) for x in _c2.group(1).split(',')]
C2_COVERS = re.sub(r'\s+', ' ', _c2.group(2))

# ------------------------------------------------------------------ numbering (as LaTeX would)
sec = 0; sub = 0; thm = 0; eqn = 0; appendix = False
num_of = {}       # label -> printed number
sec_of = {}       # label -> "section.subsection" of the place it occurs (for "§x.y")
env_pos = {}      # label -> (env, start, end) of the statement environment
cur_sub = ''
def secnum():
    return chr(ord('A') + sec - 1) if appendix else str(sec)

pat = re.compile(r'\\(section\*?|subsection|appendix)\b'
                 r'|\\begin\{(theorem|proposition|lemma|corollary|definition|remark)\}(\[[^\]]*\])?'
                 r'|\\begin\{(equation|align\*?)\}(.*?)\\end\{\4\}'
                 r'|\\label\{([^}]*)\}', re.S)
pending = None
lines_at = []
for m in pat.finditer(src):
    if m.group(1):
        k = m.group(1)
        if k == 'appendix': appendix = True; sec = 0
        elif k == 'section': sec += 1; sub = 0; thm = 0; eqn = 0; cur_sub = secnum()
        elif k == 'subsection': sub += 1; cur_sub = f'{secnum()}.{sub}'
    elif m.group(2):
        thm += 1
        pending = f'{secnum()}.{thm}'
        pending_env = m.group(2)
    elif m.group(4):
        body = m.group(5); kind = m.group(4)
        if kind == 'equation':
            eqn += 1
            for l in re.findall(r'\\label\{([^}]*)\}', body):
                num_of[l] = f'{secnum()}.{eqn}'; sec_of[l] = cur_sub
        elif kind == 'align':
            for row in re.split(r'\\\\', body):
                if re.search(r'\\nonumber|\\notag', row):
                    continue
                eqn += 1
                for l in re.findall(r'\\label\{([^}]*)\}', row):
                    num_of[l] = f'{secnum()}.{eqn}'; sec_of[l] = cur_sub
    elif m.group(6):
        l = m.group(6)
        if pending is not None and l not in num_of:
            num_of[l] = pending; sec_of[l] = cur_sub; pending = None
        elif l not in num_of:
            num_of[l] = cur_sub if l.startswith(('sec:', 'subsec:')) else secnum()
            sec_of[l] = cur_sub
# section labels: number of the innermost section/subsection just opened
# (the loop above gives \label{sec:*} the current (sub)section number)

# ------------------------------------------------------------------ brace helpers
def brace_arg(s, i):
    """s[i] == '{'; return (content, index after the closing brace)."""
    assert s[i] == '{', s[i:i + 20]
    d = 0
    for j in range(i, len(s)):
        if s[j] == '{': d += 1
        elif s[j] == '}':
            d -= 1
            if d == 0:
                return s[i + 1:j], j + 1
    raise SystemExit('unbalanced braces')

def replace_cmd(s, name, fn, nargs=1, opt=False):
    """Replace \\name[opt]{a1}...{an} by fn(opt, [a1..an])."""
    out = []; i = 0
    tok = '\\' + name
    while True:
        j = s.find(tok, i)
        if j < 0:
            out.append(s[i:]); break
        k = j + len(tok)
        if k < len(s) and s[k].isalpha():
            out.append(s[i:k]); i = k; continue
        out.append(s[i:j])
        o = None
        while k < len(s) and s[k] == ' ': k += 1
        if opt and k < len(s) and s[k] == '[':
            e = s.index(']', k); o = s[k + 1:e]; k = e + 1
        args = []
        for _ in range(nargs):
            while k < len(s) and s[k] in ' \n': k += 1
            a, k = brace_arg(s, k); args.append(a)
        out.append(fn(o, args)); i = k
    return ''.join(out)

# ------------------------------------------------------------------ math
MATH_MACROS = [(re.compile(r'\\osp(?![A-Za-z])'), r'\\mathfrak{osp}'),
               (re.compile(r'\\ad(?![A-Za-z])'), r'\\operatorname{ad}')]
macro_log = set()
def conv_math(m, tag=None):
    for rx, rep in MATH_MACROS:
        if rx.search(m): macro_log.add(rx.pattern)
        m = rx.sub(lambda _: rep.replace('\\\\', '\\'), m)
    m = re.sub(r'\\label\{[^}]*\}', '', m)
    m = re.sub(r'\\(nonumber|notag)\b', '', m)
    m = re.sub(r'\\eqref\{([^}]*)\}', lambda x: '(' + num_of[x.group(1)] + ')', m)
    m = m.replace('\n', ' ')
    m = re.sub(r' +', ' ', m).strip()
    assert '`' not in m
    return m

def inline_math(m):
    return '$`' + conv_math(m) + '`'

def display_math(m, tag=None):
    m = conv_math(m)
    if tag:
        m = m + r' \tag{' + tag + '}'
    return '\n\n$$`' + m + '`\n\n'

def conv_align(body, starred):
    rows = re.split(r'\\\\', body)
    out = []
    for row in rows:
        if not row.strip():
            continue
        lab = re.findall(r'\\label\{([^}]*)\}', row)
        r = conv_math(row)
        if lab and not starred:
            r += r' \tag{' + num_of[lab[0]] + '}'
        out.append(r)
    return display_math_raw(r'\begin{align*} ' + r' \\ '.join(out) + r' \end{align*}')

def display_math_raw(m):
    return '\n\n$$`' + m + '`\n\n'

# ------------------------------------------------------------------ text
footnotes = []
def conv_footnote(_, a):
    footnotes.append(a[0])
    return f'@@FN{len(footnotes)}@@'

def cite(o, a):
    keys = a[0]
    return '\\[' + keys + (', ' + o.replace('~', ' ').replace('\\S', '§') if o else '') + '\\]'

def conv_tabular(env_text):
    m = re.match(r'\\begin\{tabular\}\{(\w+)\}(.*)\\end\{tabular\}', env_text, re.S)
    cols, body = m.groups()
    body = body.replace('\\hline', ' \\hline ')
    rows = [r for r in re.split(r'\\\\', body)]
    out_rows = []
    for r in rows:
        if not r.strip():
            continue
        head = ''
        if '\\hline' in r:
            r = r.replace('\\hline', ''); head = '\\hline '
        cells = []
        for c in r.split('&'):
            c = c.strip()
            parts = re.split(r'(?<!\\)\$', c)
            cell = ''
            for k, p in enumerate(parts):
                p = p.strip()
                if not p: continue
                cell += conv_math(p) + ' ' if k % 2 == 1 else r'\text{' + p + '} '
            cells.append(cell.strip())
        out_rows.append(head + ' & '.join(cells))
    return display_math_raw(r'\begin{array}{' + cols + '} ' + r' \\ '.join(out_rows) + r' \end{array}')

def conv_text(s):
    """Convert one stretch of LaTeX prose (no math) to the blueprint markup."""
    s = s.replace('\\S', '§')
    s = s.replace('~', ' ')
    s = replace_cmd(s, 'emph', lambda o, a: '_' + conv_text(a[0]) + '_')
    s = replace_cmd(s, 'textbf', lambda o, a: '*' + conv_text(a[0]) + '*')
    s = replace_cmd(s, 'texttt', lambda o, a: '`' + a[0].replace('\\_', '_') + '`')
    s = replace_cmd(s, 'cite', cite, nargs=1, opt=True)
    s = replace_cmd(s, 'ref', lambda o, a: num_of[a[0]])
    s = replace_cmd(s, 'eqref', lambda o, a: '(' + num_of[a[0]] + ')')
    s = s.replace('---', '—').replace('--', '–')
    s = s.replace('\\\\', ' ')
    s = re.sub(r'\\,|\\;|\\!|\\ ', ' ', s)
    s = s.replace("``", '“').replace("''", '”')
    s = s.replace('\\%', '%')
    s = re.sub(r'\\(small|centering)\b', '', s)
    s = re.sub(r'\\(begin|end)\{center\}', '', s)
    assert '\\' not in re.sub(r'\\\[|\\\]', '', s), s[:200]
    return s

def convert(body):
    """A statement or proof body -> markup."""
    body = replace_cmd(body, 'footnote', conv_footnote)
    out = []; i = 0
    tok = re.compile(r'(?<!\\)\$|\\\[|\\begin\{(equation|align\*?|tabular)\}')
    while i < len(body):
        m = tok.search(body, i)
        if not m:
            out.append(conv_text(body[i:])); break
        out.append(conv_text(body[i:m.start()]))
        t = m.group(0)
        if t == '$':
            e = re.search(r'(?<!\\)\$', body[m.end():]).start() + m.end()
            out.append(inline_math(body[m.end():e])); i = e + 1
        elif t == '\\[':
            e = body.index('\\]', m.end())
            out.append(display_math(body[m.end():e])); i = e + 2
        else:
            env = m.group(1)
            e = body.index('\\end{' + env + '}', m.end())
            inner = body[m.end():e]
            end_i = e + len('\\end{' + env + '}')
            if env == 'equation':
                lab = re.findall(r'\\label\{([^}]*)\}', inner)
                out.append(display_math(inner, num_of[lab[0]] if lab else None))
            elif env.startswith('align'):
                out.append(conv_align(inner, env.endswith('*')))
            else:
                out.append(conv_tabular(body[m.start():end_i]))
            i = end_i
    return re.sub(r'@@FN(\d+)@@', lambda m: '$`{}^{' + m.group(1) + '}`', ''.join(out))

# ------------------------------------------------------------------ statement / proof extraction
STMT = re.compile(r'\\begin\{(theorem|proposition|lemma|corollary|definition|remark)\}(?:\[([^\]]*)\])?'
                  r'(?:\\label\{([^}]*)\})?(.*?)\\end\{\1\}', re.S)
stmt = {}
for m in STMT.finditer(src):
    env, title, label, body = m.groups()
    if label is None:
        continue
    e = m.end()
    # the statement's proof: the next proof environment, with text allowed in between (Thm 4.9 is followed by a
    # paragraph citing Sch79 and Duf02), provided no other statement environment or section starts before it
    pm = re.search(r'\\begin\{proof\}(.*?)\\end\{proof\}', src[e:], re.S)
    if pm and re.search(r'\\begin\{(theorem|proposition|lemma|corollary|definition|remark)\}|\\(sub)?section\{',
                        src[e:e + pm.start()]):
        pm = None
    stmt[label] = dict(env=env, title=title, body=body, proof=pm.group(1) if pm else None, start=m.start(), end=m.end())

def line_of(pos): return src.count('\n', 0, pos) + 1

# equation labels inside each statement environment -> node
node_labels = {n['tex'] for n in NODES}
eq_owner = {}
for l, s in stmt.items():
    if l in node_labels:
        for el in re.findall(r'\\label\{([^}]*)\}', s['body']):
            eq_owner[el] = l

def node_id(tex): return tex.replace(':', '_').replace('-', '_')

# ------------------------------------------------------------------ headings and texts
KINDS = {'Lemma': 'lemma_', 'Proposition': 'proposition', 'Theorem': 'theorem', 'Corollary': 'corollary',
         'Remark': 'proposition'}      # Verso has no `remark` directive: remarks are emitted as `proposition`
def parse_kt(kt):
    m = re.match(r'(\w+)(?:,\s*(.*)|\s*\((.*)\))?$', kt)
    return m.group(1), (m.group(2) or m.group(3))

def esc_brackets(s):
    parts = s.split('`')
    return '`'.join(p.replace('[', '\\[').replace(']', '\\]') if k % 2 == 0 else p
                    for k, p in enumerate(parts))

def cell_text(c):
    return c.rstrip().rstrip('.')

def status_sentence(n):
    decls = ', '.join('`' + d + '`' for d in n['decls'])
    c = cell_text(n['covers'])
    if n['status'] == 'formalized':
        s = f'Formalized in Lean: {decls}.'
        if c:
            s += ' ' + (c if c.startswith('(') else f'({c})')
        return s
    if n['status'] == 'partial':
        return f'Partially formalized: {esc_brackets(c)}. Declarations: {decls}.'
    return f'Not formalized: {esc_brackets(c)}.' if c else 'Not formalized.'

def render_node(n):
    tex = n['tex']; s = stmt[tex]
    kind, ntitle = parse_kt(n['kt'])
    title = s['title'] or ntitle
    heading = f'{kind} {num_of[tex]}' + (f' ({title})' if title else '')
    text = convert(s['body'].strip())
    # the paper's optional title may contain math; convert it like the body
    heading = convert(heading) if '$' in heading else heading
    nid = node_id(tex)
    lean = (' (lean := "' + ', '.join(n['decls']) + '")') if n['decls'] else ''
    out = [f':::{KINDS[kind]} "{nid}"{lean}', f'*{heading}.* ' + text.strip()]
    # footnotes are not available inside a directive: each is a paragraph after the text, marked ^k
    for k, t in enumerate(footnotes):
        out += ['', f'$`{{}}^{{{k + 1}}}` ' + convert(t.strip())]
    out += ['', status_sentence(n), ':::', '']
    edges = []
    if s['proof'] is not None:
        refs = re.findall(r'\\(?:eqref|ref)\{([^}]*)\}', s['proof'])
        uses = []
        for r in refs:
            t = r if r in node_labels else eq_owner.get(r)
            if t and t != tex and t not in uses:
                uses.append(t)
        # the node map is the binding list of nodes; `uses` follow the proof's own order
        opt = (' (uses := "' + ', '.join(node_id(u) for u in uses) + '")') if uses else ''
        out += [f':::proof "{nid}"{opt}', f'Proof: the paper, §{sec_of[tex]}.', ':::', '']
        edges = [(tex, u) for u in uses]
    return '\n'.join(out), edges, s

# ------------------------------------------------------------------ chapters
def chapter_header(title):
    return ('import Verso\nimport VersoManual\nimport VersoBlueprint\nimport OspOddDeformations.OspN.Audit\n\n'
            'open Verso.Genre\nopen Verso.Genre.Manual\nopen Informal\n\n'
            f'#doc (Manual) "{title}" =>\n\n')

by_tex = {n['tex']: n for n in NODES}
CHAPTERS = [
    ('Setting', 'The source algebra and the lifts', 2, [(None, ['rem:central'])]),
    ('Untwisting', 'The untwisting and the identification with osp(N|2n)', 3,
     [(None, ['lem:untwist', 'lem:base', 'prop:independence', 'prop:osp'])]),
    ('Single', 'The deformed bracket for one odd parameter', 4,
     [('The lifts and the coefficient',
       ['prop:lift-change', 'thm:recovery', 'thm:unique', 'prop:gamma']),
      ('Triviality and the primitives',
       ['thm:triv-single', 'lem:inner', 'thm:fbeta', 'cor:tbeta', 'thm:all-primitives',
        'cor:normalization', 'cor:complex'])]),
    ('Multi', 'The deformed bracket for multiple odd parameters', 5,
     [('Recovery and triviality', ['thm:untwist-multi', 'prop:lift-change-multi', 'thm:multi']),
      ('Factorization through an even deformation',
       ['prop:factor', 'C2', 'prop:not-additive', 'rem:even-generated', 'rem:fock'])]),
    ('Special', 'Specializations and remarks', 6,
     [(None, ['rem:even', 'rem:d21'])]),
    ('Formalization', 'Machine-checked formalization', 'A', [('What is proved', ['C1'])]),
]

# the text after Proposition 5.4 (node C2) and item 9 of App. A (node C1)
c2_start = src.index('In particular, if $\\Omega\\neq0$, then $U(T^{(1)}')
c2_end = src.index('\n\n', c2_start)
C2_BODY = src[c2_start:c2_end]
c1_start = src.index('\\item Controls.')
# item 9 ends at the next top-level \item (item 10) or at the end of the list
c1_end = min(x for x in (src.find('\n\\item ', c1_start + 1), src.index('\\end{enumerate}', c1_start)) if x >= 0)
C1_BODY = src[c1_start + len('\\item '):c1_end]

os.makedirs(os.path.join(HERE, 'OspOddDeformationsBlueprint', 'Chapters'), exist_ok=True)
all_edges = []; covered = []
for fname, title, secn, subs in CHAPTERS:
    text = chapter_header(title)
    for stitle, labels in subs:
        if stitle:
            text += f'# {stitle}\n\n'
        for lab in labels:
            if lab == 'C2':
                footnotes.clear()
                body = convert(C2_BODY.strip())
                text += (':::proposition "after_prop_factor" (uses := "prop_factor") (lean := "' + ', '.join(C2_DECLS) + '")\n' +
                         '*Text after Proposition ' + num_of['prop:factor'] + '.* ' + body.strip() +
                         '\n\nPartially formalized: ' + esc_brackets(C2_COVERS) + '. Declarations: ' +
                         ', '.join('`' + d + '`' for d in C2_DECLS) + '.\n:::\n\n')
                covered.append('C2'); continue
            if lab == 'C1':
                footnotes.clear()
                body = convert(C1_BODY.strip())
                lean = ', '.join(C1_DECLS)
                text += (f':::proposition "app_controls" (lean := "{lean}")\n*Controls (Appendix {num_of["subsec:formal-proved"]}, item 9).* ' +
                         body.strip().replace('Controls. ', '', 1) + '\n\nPartially formalized: ' + esc_brackets(C1_COVERS) + '. Declarations: ' +
                         ', '.join('`' + d + '`' for d in C1_DECLS) + '.\n:::\n\n')
                covered.append('C1'); continue
            footnotes.clear()
            block, edges, s = render_node(by_tex[lab])
            text += block + '\n'
            all_edges += edges; covered.append(lab)
    open(os.path.join(HERE, 'OspOddDeformationsBlueprint', 'Chapters', fname + '.lean'), 'w', encoding='utf-8').write(text)

assert sorted(c for c in covered if c not in ('C1', 'C2')) == sorted(node_labels), \
    set(node_labels) ^ set(c for c in covered if c not in ('C1', 'C2'))
ADDED = [('after_prop_factor', 'prop:factor')]     # C2 uses Prop 5.4, as its first words say
with open(os.path.join(HERE, 'uses_edges.txt'), 'w') as f:
    f.write('# node -> node used by its proof (a \\ref/\\eqref in the proof environment; an equation label\n'
            '# counts as the node whose statement environment contains it)\n')
    for a, b in all_edges:
        f.write(f'{a} -> {b}\n')
    f.write('# added by the node map (not from a proof environment):\n')
    for a, b in ADDED:
        f.write(f'{a} -> {b}  (added)\n')
print(f'gen_chapters: {len(covered)} nodes, {len(all_edges)} + {len(ADDED)} added uses edges; macros expanded: {sorted(macro_log)}')
