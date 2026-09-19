"""Local blueprint check and preview (no leanblueprint / graphviz needed).

  python3 scripts/blueprint_preview.py            # check + write blueprint/preview.html
  python3 scripts/blueprint_preview.py --no-check # skip the Lean declaration check

1. Parses blueprint/src/content.tex: nodes, \\lean{...}, \\leanok, \\uses{...}.
2. Checks that every \\lean{...} name exists (what CI's `checkdecls` step checks) by
   compiling `#check @name` for each against the built library.  Needs `lake build` first.
3. Checks that every \\uses{...} label exists.
4. Writes blueprint/preview.html: a dependency graph coloured by status plus a table per
   chapter.  The official site is built by .github/workflows/blueprint.yml on a schedule.

Exit status 1 if a check fails.
"""
import html, json, os, re, subprocess, sys, tempfile
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, 'blueprint', 'src', 'content.tex')
OUT = os.path.join(ROOT, 'blueprint', 'preview.html')


def parse(s):
    chapters = [(m.start(), m.group(1)) for m in re.finditer(r'\\chapter\{([^}]*)\}', s)]
    env = re.compile(r'\\begin\{(definition|lemma|theorem|remark|corollary|proposition)\}'
                     r'(\[[^\]]*\])?\s*\\label\{([^}]*)\}')
    nodes = []
    for m in env.finditer(s):
        kind, title, label = m.group(1), (m.group(2) or '')[1:-1], m.group(3)
        end = s.find('\\end{' + kind + '}', m.end())
        body = s[m.end():end]
        pm = re.match(r'\\end\{' + kind + r'\}\s*\\begin\{proof\}(.*?)\\end\{proof\}',
                      s[end:end + 4000], re.S)
        proof = pm.group(1) if pm else ''
        ch = [c for p, c in chapters if p < m.start()]
        uses = {u.strip() for x in re.findall(r'\\uses\{([^}]*)\}', body + proof)
                for u in x.split(',') if u.strip()}
        nodes.append(dict(
            label=label, kind=kind, title=title, chapter=ch[-1] if ch else '',
            stmt_ok='\\leanok' in body, proof_ok='\\leanok' in proof, has_proof=bool(pm),
            lean=[l.strip() for x in re.findall(r'\\lean\{([^}]*)\}', body)
                  for l in x.split(',') if l.strip()],
            uses=sorted(uses)))
    return nodes


def check_decls(nodes):
    names = sorted({l for n in nodes for l in n['lean']})
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write('import RBM1D\n' + ''.join(f'#check @{n}\n' for n in names))
        path = f.name
    try:
        r = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)
    errs = [line for line in (r.stdout + r.stderr).splitlines() if 'error' in line]
    return names, errs


def detex(t):
    rep = {r'\SB': 'S⁽ᴮ⁾', r'\Th': 'Θ', r'\Kcal': '𝒦', r'\mathcal{T}_{SP}': 'T_SP',
           r'\mathcal T_{SP}': 'T_SP', r'\prec': '≺', r'\S': '§', r'\rho': 'ρ', r'\xi': 'ξ',
           r'\Gamma': 'Γ', r'\otimes': '⊗', r'\le': '≤', '--': '–'}
    for a, b in rep.items():
        t = t.replace(a, b)
    t = re.sub(r'\\[a-zA-Z]+', '', t)
    return re.sub(r'\s+', ' ', t.replace('$', '').replace('{', '').replace('}', '')).strip()


def status(n):
    if n['kind'] == 'remark':
        return 'remark'
    if n['kind'] == 'definition':
        return 'done' if n['stmt_ok'] else 'todo'
    if n['stmt_ok'] and (n['proof_ok'] or not n['has_proof']):
        return 'done'
    return 'stated' if n['stmt_ok'] else 'todo'


def render(nodes, sha):
    by = {n['label']: n for n in nodes}
    for n in nodes:
        n['status'] = status(n)
    depth = {}

    def d(l):
        if l not in depth:
            depth[l] = 0
            depth[l] = 1 + max((d(u) for u in by[l]['uses'] if u in by), default=-1)
        return depth[l]
    for n in nodes:
        d(n['label'])
    chap_order = list(dict.fromkeys(n['chapter'] for n in nodes))
    layers = {}
    for n in nodes:
        layers.setdefault(depth[n['label']], []).append(n)
    W, H, GX, GY = 150, 34, 18, 56
    maxw = max(len(v) for v in layers.values())
    svgw, svgh = maxw * (W + GX) + 40, len(layers) * (H + GY) + 40
    pos = {}

    def place(k, row):
        off = (maxw - len(row)) * (W + GX) / 2
        for i, n in enumerate(row):
            pos[n['label']] = (20 + off + i * (W + GX), 20 + k * (H + GY))
    for k in sorted(layers):
        layers[k].sort(key=lambda n: (chap_order.index(n['chapter']), nodes.index(n)))
        place(k, layers[k])
    for _ in range(3):
        for k in sorted(layers)[1:]:
            def bc(n):
                xs = [pos[u][0] for u in n['uses'] if u in pos]
                return sum(xs) / len(xs) if xs else pos[n['label']][0]
            layers[k].sort(key=bc)
            place(k, layers[k])
    edges, boxes = [], []
    for n in nodes:
        x2, y2 = pos[n['label']]
        for u in n['uses']:
            if u in pos:
                x1, y1 = pos[u]
                edges.append(f'<path d="M{x1+W/2:.0f},{y1+H} C{x1+W/2:.0f},{y1+H+GY/2} '
                             f'{x2+W/2:.0f},{y2-GY/2} {x2+W/2:.0f},{y2}" class="edge" '
                             f'data-from="{html.escape(u)}" data-to="{html.escape(n["label"])}"/>')
    for n in nodes:
        x, y = pos[n['label']]
        t = detex(n['title'])
        short = t if len(t) <= 22 else t[:21] + '…'
        tip = t + ' [' + n['label'] + ']' + ('\n' + '\n'.join(n['lean'][:12]) if n['lean'] else '')
        rx = 4 if n['kind'] == 'definition' else 17
        boxes.append(f'<g class="node s-{n["status"]}" data-label="{html.escape(n["label"])}">'
                     f'<title>{html.escape(tip)}</title><rect x="{x:.0f}" y="{y:.0f}" '
                     f'width="{W}" height="{H}" rx="{rx}"/><text x="{x+W/2:.0f}" '
                     f'y="{y+H/2+4:.0f}">{html.escape(short)}</text></g>')
    cnt = Counter(n['status'] for n in nodes)
    names = {'done': 'formalized', 'stated': 'statement only', 'todo': 'not yet', 'remark': 'remark'}
    rows = []
    for ch in chap_order:
        rows.append(f'<h3>{html.escape(detex(ch))}</h3><table><thead><tr><th>Node</th>'
                    '<th>Status</th><th>Lean declarations</th><th>Uses</th></tr></thead><tbody>')
        for n in nodes:
            if n['chapter'] != ch:
                continue
            lean = ', '.join(f'<code>{html.escape(l.replace("RBM.", ""))}</code>'
                             for l in n['lean']) or '—'
            rows.append(f'<tr><td><b>{html.escape(detex(n["title"]))}</b><br>'
                        f'<span class="lbl">{html.escape(n["label"])} · {n["kind"]}</span></td>'
                        f'<td><span class="pill p-{n["status"]}">{names[n["status"]]}</span></td>'
                        f'<td class="lean">{lean}</td>'
                        f'<td class="uses">{html.escape(", ".join(n["uses"])) or "—"}</td></tr>')
        rows.append('</tbody></table>')
    dark = ('--bg:#161615;--fg:#ecebe6;--mut:#9d9c96;--line:#34332f;--card:#1f1f1d;--done:#6fc28f;'
            '--doneb:#1f3a29;--st:#6fc28f;--todo:#e3a15d;--todob:#3b2c1a;--rem:#8d8c86;'
            '--edge:#4a4944;--hi:#7aa7f5')
    css = f'''
:root{{--bg:#fbfbf9;--fg:#1d1d1b;--mut:#6b6b66;--line:#d6d5cf;--card:#fff;--done:#2f7d4f;--doneb:#dcefe2;--st:#2f7d4f;--todo:#b0661f;--todob:#fbeedd;--rem:#8a8a84;--edge:#b9b8b1;--hi:#2d5fb8}}
@media (prefers-color-scheme:dark){{:root:not([data-theme="light"]){{{dark}}}}}
:root[data-theme="dark"]{{{dark}}}
body{{margin:0;background:var(--bg);color:var(--fg);font:15px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}}
main{{max-width:1180px;margin:0 auto;padding:24px 16px 60px}} h1{{font-size:24px;margin:0 0 4px}}
.sub{{color:var(--mut);margin:0 0 18px}} .stats{{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:18px}}
.stat{{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:8px 14px}} .stat b{{font-size:20px;display:block}}
.graph{{background:var(--card);border:1px solid var(--line);border-radius:10px;overflow:auto;margin-bottom:26px}}
.legend{{display:flex;gap:16px;flex-wrap:wrap;font-size:13px;color:var(--mut);margin:0 0 10px}}
.sw{{display:inline-block;width:14px;height:10px;border-radius:3px;margin-right:5px;vertical-align:middle;border:2px solid}}
.edge{{fill:none;stroke:var(--edge);stroke-width:1.2}} .edge.hi{{stroke:var(--hi);stroke-width:2}}
.node rect{{stroke-width:2;fill:var(--card)}} .node text{{font-size:11px;text-anchor:middle;fill:var(--fg);pointer-events:none}}
.s-done rect{{stroke:var(--done);fill:var(--doneb)}} .s-stated rect{{stroke:var(--st)}}
.s-todo rect{{stroke:var(--todo);fill:var(--todob);stroke-dasharray:4 3}} .s-remark rect{{stroke:var(--rem)}}
.node{{cursor:pointer}} .node.dim{{opacity:.25}} .node.hi rect{{stroke:var(--hi);stroke-width:3}}
table{{width:100%;border-collapse:collapse;margin-bottom:20px;font-size:13.5px}}
th,td{{text-align:left;padding:7px 8px;border-bottom:1px solid var(--line);vertical-align:top}}
th{{color:var(--mut);font-weight:600}} .lbl,td.uses{{color:var(--mut);font-size:12px}} td.lean{{font-size:12px}} code{{font-size:11.5px}}
.pill{{border-radius:10px;padding:1px 8px;font-size:12px;white-space:nowrap}} .p-done{{background:var(--doneb);color:var(--done)}}
.p-stated{{border:1px solid var(--st);color:var(--st)}} .p-todo{{background:var(--todob);color:var(--todo)}} .p-remark{{color:var(--rem);border:1px solid var(--rem)}}
@media (max-width:700px){{td.uses,th:nth-child(4){{display:none}}}}'''
    js = '''const rev={};for(const[k,v]of Object.entries(uses))for(const u of v)(rev[u]=rev[u]||[]).push(k);
function closure(l,m){const s=new Set([l]),q=[l];while(q.length){const x=q.pop();for(const y of(m[x]||[]))if(!s.has(y)){s.add(y);q.push(y)}}return s}
let cur=null;document.querySelectorAll('.node').forEach(g=>g.addEventListener('click',()=>{const l=g.dataset.label;
if(cur===l){cur=null;document.querySelectorAll('.node').forEach(x=>x.classList.remove('dim','hi'));document.querySelectorAll('.edge').forEach(e=>e.classList.remove('hi'));return}
cur=l;const s=new Set([...closure(l,uses),...closure(l,rev)]);
document.querySelectorAll('.node').forEach(x=>{x.classList.toggle('dim',!s.has(x.dataset.label));x.classList.toggle('hi',x.dataset.label===l)});
document.querySelectorAll('.edge').forEach(e=>e.classList.toggle('hi',s.has(e.dataset.from)&&s.has(e.dataset.to)))}));'''
    uses = json.dumps({n['label']: n['uses'] for n in nodes})
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>RBM1D Blueprint</title><style>{css}</style></head>
<body><main><h1>RBM1D blueprint</h1>
<p class="sub">Yau–Yin, <i>Delocalization of 1D Random Band Matrices</i> — local preview of <code>blueprint/src/content.tex</code> at {html.escape(sha)}</p>
<div class="stats"><div class="stat"><b>{len(nodes)}</b>nodes</div><div class="stat"><b>{cnt["done"]}</b>formalized</div>
<div class="stat"><b>{cnt["stated"]}</b>statement only</div><div class="stat"><b>{cnt["todo"]}</b>not yet</div>
<div class="stat"><b>{sum(len(n["lean"]) for n in nodes)}</b>linked Lean declarations</div></div>
<div class="legend"><span><span class="sw" style="border-color:var(--done);background:var(--doneb)"></span>formalized</span>
<span><span class="sw" style="border-color:var(--st)"></span>statement only</span>
<span><span class="sw" style="border-color:var(--todo);background:var(--todob);border-style:dashed"></span>not yet</span>
<span>square corners = definition · arrows run from prerequisite to user · click a node to highlight its dependencies</span></div>
<div class="graph"><svg width="{svgw:.0f}" height="{svgh:.0f}" viewBox="0 0 {svgw:.0f} {svgh:.0f}" role="img" aria-label="Dependency graph">{"".join(edges)}{"".join(boxes)}</svg></div>
{"".join(rows)}</main><script>const uses={uses};{js}</script></body></html>'''


def main():
    s = open(SRC, encoding='utf-8').read()
    nodes = parse(s)
    ok = True
    labels = {n['label'] for n in nodes}
    dangling = sorted({u for n in nodes for u in n['uses'] if u not in labels})
    if dangling:
        ok = False
        print('unknown \\uses labels:', ', '.join(dangling))
    if '--no-check' not in sys.argv:
        names, errs = check_decls(nodes)
        if any('object file' in e for e in errs):
            print('declaration check skipped: the library is not built (run `lake build`); '
                  + next(e for e in errs if 'object file' in e).split('error: ')[-1])
        elif errs:
            ok = False
            print(f'\\lean names that do not exist ({len(errs)}):')
            print('\n'.join(errs[:40]))
        else:
            print(f'all {len(names)} \\lean names exist')
    sha = subprocess.run(['git', 'log', '-1', '--format=%h (%cd)', '--date=format:%Y-%m-%d %H:%M'],
                         cwd=ROOT, capture_output=True, text=True).stdout.strip()
    open(OUT, 'w', encoding='utf-8').write(render(nodes, sha))
    c = Counter(status(n) for n in nodes)
    print(f'{len(nodes)} nodes: {c["done"]} formalized, {c["stated"]} statement only, '
          f'{c["todo"]} not yet -> {os.path.relpath(OUT, ROOT)}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
