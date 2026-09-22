#!/usr/bin/env python3
"""Rebuild the blueprint artifact page from blueprint/src/content.tex.

Usage:  python3 build.py <path-to-content.tex> <theorem-count>
Writes ch2.svg, ch3.svg, ch4.svg (as needed) and blueprint.html.
"""
import re, sys, io, subprocess, html

TEX = sys.argv[1] if len(sys.argv) > 1 else '../../blueprint/src/content.tex'
NTHM = sys.argv[2] if len(sys.argv) > 2 else '?'

src = io.open(TEX, encoding='utf-8').read()

# count-conservation guard (lesson: checkers must not silently drop nodes)
import re as _re, sys as _sys
_nenv = len(_re.findall(r'\\begin\{(definition|lemma|theorem|corollary)\}', src))

# ---- chapters -------------------------------------------------------------
chaps = []
for m in re.finditer(r'\\chapter\{(.*?)\}', src):
    chaps.append((m.start(), m.group(1)))
def chapter_of(pos):
    idx = 0
    for i, (p, _) in enumerate(chaps):
        if p <= pos: idx = i
    return idx

# ---- nodes ----------------------------------------------------------------
NODE, ORDER = {}, []
for m in re.finditer(
        r'\\begin\{(definition|lemma|theorem|corollary)\}(\[[^\]]*\])?\s*\\label\{([^}]*)\}(.*?)\\end\{\1\}',
        src, re.S):
    kind, title, label, body = m.group(1), (m.group(2) or '[]')[1:-1], m.group(3), m.group(4)
    lean = re.search(r'\\lean\{(.*?)\}', body, re.S)
    uses = re.findall(r'\\uses\{(.*?)\}', body, re.S)
    NODE[label] = dict(
        kind='def' if kind == 'definition' else 'lem',
        title=title, chap=chapter_of(m.start()),
        lean=[x.strip() for x in re.split(r',\s*', lean.group(1).replace('\n', ' ')) if x.strip()] if lean else [],
        leanok='\\leanok' in body,
        uses=sorted({u.strip() for g in uses for u in g.replace('\n', ' ').split(',') if u.strip()}))
    ORDER.append(label)
_nparsed = len(ORDER)
if _nparsed != _nenv:
    _sys.exit(f'COUNT MISMATCH: {_nenv} environments but {_nparsed} parsed nodes')

# nodes the paper supplies but we deliberately do not formalize
CITED = set()  # lem:3.2 proved by T185 (2026-09-21)

def status(lab):
    n = NODE[lab]
    if lab in CITED: return 'cited'
    if n['leanok']: return 'done'
    deps = [d for d in n['uses'] if d in NODE]
    if all(NODE[d]['leanok'] or d in CITED for d in deps): return 'ready'
    return 'todo'

# ---- display names (fallback: the LaTeX title, de-TeXed) -------------------
SHORT = {
 'def:SB':'S(B)  §2.1', 'lem:SB-basic':'S(B) basics',
 'def:model':'band model S = S(B)⊗S_W', 'lem:model':'E_a, row sums of S',
 'lem:2.8':'m_sc, m(E), z_t   Lem 2.8', 'def:2.1-ii':'≺   Def 2.1(ii)',
 'lem:2.1-ii-closure':'≺  closure props', 'def:Theta':'Θξ   Def 2.13',
 'lem:norm-SB':'|S(B)| = 1', 'lem:Theta-inv':'two-sided inverse',
 'lem:Theta-sym':'2.14(1) symmetry', 'lem:Theta-transl':'2.14(2) translation',
 'lem:Theta-comm':'2.14(3) commuting', 'lem:Theta-series':'2.14(5) Neumann',
 'lem:Theta-rowsum':'row sums', 'lem:Theta-deriv':'(2.51)  ∂Θ = ΘSΘ',
 'lem:Theta-bounds':'(3.35)(3.36) bounds', 'lem:Theta-band':'band + first decay',
 'eq:B.1':'(B.1) Fourier rep', 'lem:rho':'ρ(ξ):  |ρ| < 1',
 'lem:closed-form':'closed form  A(ρ^d+ρ^{L-d})', 'lem:rho-rate':'rate:  1-ρ ≍ √(1-t)',
 'lem:prefactor':'prefactor  |A| ≤ 4/((1-t)ℓ̂)', 'lem:Theta-decay':'2.14(4) sharp decay  (2.52)',
 'lem:Theta-diff':'(2.53)(2.54) differences', 'eq:2.10':'(2.10) eigenvector bound',
 'def:loops':'loops, cut-and-glue', 'lem:loops-length':'lengths under cut/glue',
 'def:primitive':'primitive eq  (2.48)', 'eq:2.55':'index check at n = 2',
 'ex:2.15':'Example 2.15   K = W⁻¹m₁m₂Θ', 'lem:3.2':'Lemma 3.2  partitions',
 'def:TSP':'T_SP = crossing-free sets', 'lem:TSP-small':'Figure 6:   3, 11, 45',
 'lem:3.4':'Lemma 3.4  tree rep', 'lem:3.6':'Lemma 3.6  Ward',
 'lem:3.10':'Lemma 3.10  sum-zero', 'lem:3.11':'Lemma 3.11  bound on K',
 'lem:star':'star graph + n=4 trees',
}
def detex(s):
    s = re.sub(r'\\[a-zA-Z]+\{(.*?)\}', r'\1', s)
    s = s.replace('\\"o', 'ö').replace('\\"u', 'ü')
    s = s.replace('\\', '').replace('$', '').replace('--', '–')
    return s.replace('"', '').strip()
def _greedy(words, w0):
    lines, cur = [], ''
    for w in words:
        if not cur:
            cur = w
        elif len(cur) + 1 + len(w) <= w0:
            cur += ' ' + w
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    return lines

def wrap(s, width=16):
    """Break a node label onto two lines (three only when it is really long), with the
    lines balanced, so nodes are not pancakes.  A double space in a hand-written SHORT
    label marks the author's own split point and wins."""
    s = s.strip()
    if len(s) <= width:
        return s
    if '  ' in s:
        pts = [i for i in range(len(s) - 1) if s[i:i+2] == '  ']
        mid = len(s) / 2
        i = min(pts, key=lambda j: abs(j - mid))
        a, b = s[:i].strip(), s[i:].strip()
        if a and b and max(len(a), len(b)) <= width + 8:
            return a + '\\n' + b
    words = s.split()
    n = min(3, max(2, -(-len(s) // width)))
    lo, hi = max(len(w) for w in words), len(s)
    best = _greedy(words, hi)
    while lo <= hi:
        m = (lo + hi) // 2
        ls = _greedy(words, m)
        if len(ls) <= n:
            best, hi = ls, m - 1
        else:
            lo = m + 1
    return '\\n'.join(best)

def clip(s, n=52):
    """Truncate to at most `n` characters, at a word boundary, never mid-token."""
    s = s.strip()
    if len(s) <= n:
        return s
    cut = s[:n].rstrip()
    if ' ' in cut:
        cut = cut[:cut.rfind(' ')].rstrip()
    return cut.rstrip(' ,;:.(–-') + '…'

def disp(lab):
    return wrap(SHORT.get(lab) or clip(detex(NODE[lab]['title'])) or lab)

def style(kind, st, ext=False):
    if ext:
        return ('shape=box, style="filled,dashed,rounded", fillcolor="#f1f3f5", '
                'color="#b9c1c9", fontcolor="#7d8791", fontsize=10')
    if st == 'done':
        if kind == 'def':
            return 'shape=box, style="filled,rounded", fillcolor="#cfe9dc", color="#7cbfa4", fontcolor="#123a2b"'
        return 'shape=ellipse, style=filled, fillcolor="#1f9d6b", color="#177a54", fontcolor="#ffffff"'
    if st == 'cited':
        return 'shape=ellipse, style="filled,dashed", fillcolor="#fdf3e0", color="#c99a4a", fontcolor="#6b4d17"'
    fill, col, fc = ('#dbe8f5', '#5d8cb8', '#16344d') if st == 'ready' else ('#ffffff', '#bcc4cc', '#6b7480')
    sh, stl = ('box', '"filled,rounded"') if kind == 'def' else ('ellipse', 'filled')
    return f'shape={sh}, style={stl}, fillcolor="{fill}", color="{col}", fontcolor="{fc}"'

EDGES = [(d, lab) for lab in ORDER for d in NODE[lab]['uses'] if d in NODE]

def build(chap, name):
    keep = [l for l in ORDER if NODE[l]['chap'] == chap]
    ks = set(keep)
    inner = [(a, b) for a, b in EDGES if a in ks and b in ks]
    ext = sorted({a for a, b in EDGES if b in ks and a not in ks})
    L = ['digraph G {',
         '  graph [rankdir=TB, splines=true, nodesep=0.08, ranksep=1.25, bgcolor="transparent"];',
         '  node [fontname="Helvetica", fontsize=11, penwidth=1.4, height=0.52, margin="0.14,0.10"];',
         '  edge [color="#aeb6bf", penwidth=1.1, arrowsize=0.7];']
    for lab in keep:
        L.append(f'  "{lab}" [label="{disp(lab)}", {style(NODE[lab]["kind"], status(lab))}];')
    for lab in ext:
        L.append(f'  "{lab}" [label="{disp(lab)}  →前章", {style("lem","done",ext=True)}];')
    for a, b in inner:
        L.append(f'  "{a}" -> "{b}";')
    for a, b in [(a, b) for a, b in EDGES if b in ks and a not in ks]:
        L.append(f'  "{a}" -> "{b}" [style=dashed];')
    L.append('}')
    open(name + '.dot', 'w').write('\n'.join(L))
    svg = subprocess.run(['dot', '-Tsvg', name + '.dot'], capture_output=True, text=True).stdout
    svg = svg[svg.find('<svg'):]
    head = svg.split('>', 1)[0]
    w = float(head.split('width="')[1].split('pt')[0])
    h = float(head.split('height="')[1].split('pt')[0])
    svg = re.sub(r'<svg width="[\d.]+pt" height="[\d.]+pt"',
                 '<svg class="depgraph" preserveAspectRatio="xMinYMin meet"', svg, count=1)
    open(name + '.svg', 'w').write(svg)
    return w, h, len(keep)

# ---- rows -----------------------------------------------------------------
PILL = {'done': ('done', '已证'), 'ready': ('ready', '可开工'),
        'todo': ('todo', '待解锁'), 'cited': ('cited', '引用未证')}
def rows(chap):
    out = []
    for lab in [l for l in ORDER if NODE[l]['chap'] == chap]:
        st = status(lab)
        p = PILL[st]
        code = ' · '.join(x.replace('RBM.', '') for x in NODE[lab]['lean'][:4]) or '—'
        if len(NODE[lab]['lean']) > 4:
            code += ' …'
        out.append(
            f'<li class="row"><div class="row-main"><span class="row-name">{html.escape(detex(NODE[lab]["title"]))}'
            f'</span></div><div class="row-side"><span class="pill {p[0]}">{p[1]}</span>'
            f'<code>{html.escape(code)}</code></div></li>')
    return '\n'.join(out)

CHTITLE = {
 'The model': ('第 1 章 · 模型', '论文 §2.1：块协方差 S^(B)、带模型 S = S^(B)⊗S_W、块投影 E_a，以及半圆律与 z_t 流的代数。'),
 'The propagator': ('第 2 章 · 传播子 Θ<sub>ξ</sub>', 'Definition 2.13、Lemma 2.14、附录 B。箭头由前提指向结论；绿色 = 已在 Lean 中证完，圆角绿框 = 已形式化的定义，蓝色 = 前提齐备可开工，橙色虚线 = 引用论文结论不形式化。图默认按宽度缩到整节可见，可缩放、拖动平移、双击切换。'),
 'The primitive equation and $\\Kcal$': ('第 3 章 · 原始方程与 𝒦', '论文的原创内核：cut-and-glue、原始方程 (2.48)、树表示、Ward 恒等式、sum-zero。全部确定性。虚线灰框是前面章节的节点。'),
 'Delocalization from the local law': ('第 4 章 · 由 local law 推退局域化', 'Theorem 2.2 的确定性一半：谱定理加一条 Green 函数不等式。'),
 'The stochastic layer (out of scope for now)': ('第 5 章 · 随机层', 'Itô 演算、loop hierarchy、Theorem 2.21。Mathlib 目前没有相应基础设施，作为假设接口挂起。'),
}

counts = {s: sum(1 for l in ORDER if status(l) == s) for s in ('done', 'ready', 'todo', 'cited')}

sections = []
for ci, (_, raw) in enumerate(chaps):
    labs = [l for l in ORDER if NODE[l]['chap'] == ci]
    if not labs:
        continue
    zh, blurb = CHTITLE.get(raw, (detex(raw), ''))
    body = [f'  <h2>{zh}</h2>', f'  <p>{blurb}</p>']
    if len(labs) >= 3:
        w, h, n = build(ci, f'g{ci}')
        svg = (f'<img class="depgraph" src="g{ci}.svg" alt="dependency graph" '
               f'width="{int(w)}" height="{int(h)}">')
        body.append(f"""  <figure class="graph" data-basew="{w:.0f}" data-baseh="{h:.0f}">
    <div class="gbar">
      <span class="gcap">{zh.replace('<sub>','').replace('</sub>','')} 依赖图 · {n} 个节点</span>
      <div class="gtools">
        <button type="button" data-act="out" aria-label="缩小">&minus;</button>
        <button type="button" data-act="fit">看全</button>
        <button type="button" data-act="in" aria-label="放大">+</button>
        <span class="gpct" aria-live="polite">100%</span>
      </div>
    </div>
    <div class="plate">{svg}</div>
  </figure>""")
    body.append('  <ul class="rows">')
    body.append(rows(ci))
    body.append('  </ul>')
    sections.append('\n'.join(body))

LEGEND = """  <div class="legend">
    <span><i style="background:#1f9d6b"></i>已在 Lean 中证明</span>
    <span><i style="background:#cfe9dc"></i>定义（已形式化）</span>
    <span><i style="background:#dbe8f5"></i>前提就绪，可开工</span>
    <span><i style="background:#fdf3e0"></i>引用论文结论，不形式化</span>
    <span><i style="background:#ffffff"></i>尚被上游阻塞</span>
  </div>"""

tpl = io.open('template.html', encoding='utf-8').read()
try:
    papermap = io.open('papermap.html', encoding='utf-8').read()
except FileNotFoundError:
    papermap = ''
out = tpl.replace('<!--PAPERMAP-->', papermap)
out = out.replace('<!--SECTIONS-->', LEGEND + '\n\n' + '\n\n'.join(sections))
try:
    chips = io.open('chips.html', encoding='utf-8').read()
except FileNotFoundError:
    chips = ''
out = out.replace('<!--CHIPS-->', chips)
out = re.sub(r'<b>[\d ]+</b><span>Lean 定理', f'<b>{NTHM}</b><span>Lean 定理', out)
import datetime
BPDATE = sys.argv[3] if len(sys.argv) > 3 else datetime.date.today().isoformat()
out = re.sub(r'· \d{4}-\d{2}-\d{2}</p>', '· ' + BPDATE + '</p>', out)
io.open('blueprint.html', 'w', encoding='utf-8').write(out)
print('nodes', len(ORDER), 'counts', counts, 'sections', len(sections))
