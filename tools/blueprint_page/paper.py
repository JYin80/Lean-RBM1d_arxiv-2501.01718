#!/usr/bin/env python3
"""Whole-paper dependency map, at FULL granularity.

Every node of every chapter graph (parsed from content.tex, i.e. one node per
formalization step) PLUS every paper item that is not formalized yet (suspended
hypotheses and open work orders).  One picture of the entire paper.
"""
import subprocess, re, io, html, sys

TEX = sys.argv[1] if len(sys.argv) > 1 else '../../blueprint/src/content.tex'
src = io.open(TEX, encoding='utf-8').read()

# count-conservation guard (lesson: checkers must not silently drop nodes)
import re as _re, sys as _sys
_nenv = len(_re.findall(r'\\begin\{(definition|lemma|theorem|corollary)\}', src))

# ---------- 1. the formalized nodes, straight from content.tex --------------
CH = [(m.start(), m.group(1)) for m in re.finditer(r'\\chapter\{(.*?)\}', src)]
def chap(p):
    i = 0
    for k, (q, _) in enumerate(CH):
        if q <= p: i = k
    return i

NODE, ORDER = {}, []
for m in re.finditer(
        r'\\begin\{(definition|lemma|theorem|corollary)\}(\[[^\]]*\])?\s*\\label\{([^}]*)\}(.*?)\\end\{\1\}',
        src, re.S):
    kind, title, label, body = m.group(1), (m.group(2) or '[]')[1:-1], m.group(3), m.group(4)
    uses = re.findall(r'\\uses\{(.*?)\}', body, re.S)
    NODE[label] = dict(kind='def' if kind == 'definition' else ('thm' if kind == 'theorem' else 'lem'),
                       title=title, chap=chap(m.start()),
                       st=('done' if '\\leanok' in body else ('cited' if label == 'lem:3.2' else 'todo')),
                       tk='',
                       uses=sorted({u.strip() for g in uses for u in g.replace('\n', ' ').split(',') if u.strip()}))
    ORDER.append(label)
_nparsed = len(ORDER)
if _nparsed != _nenv:
    _sys.exit(f'COUNT MISMATCH: {_nenv} environments but {_nparsed} parsed nodes')

# Cowork overrides: nodes whose Lean proof is conditional on a hypothesis still being discharged
STATUS_OVERRIDE = {
    'thm:fluc-high': ('repl', '旧接口在 B≍Ψ 处不可满足（T171/T172）；已由带基数预算的条件化版取代，(4.12)→Eq45Flow 闭合（T177/T188）'),
    'thm:step2': ('repl', '截断矩 Duhamel（T197）；(5.47) 锐化到 (η_s/η_u)²（T207）；(5.48) 漂移钉死（T208）、已从 Theorem 2.21 假设表消失（T239）；(5.48) 数据：init（T241）、meas（T244）已关，modulus 对每个 ω 为假（T244、T249 空真第 11、12 例）→ 窗口左端取 s_N ≥ N^{−C} 并用不依赖 ‖X‖ 的 Lipschitz（T249、T251、T252）；停时的替代 (A′)：cut 已由定理产出（APrimeHyp → MomentHypCutEv），只剩全测度加权矩 WeightedMoment 的 Grönwall 收口（T230、T250）'),
}
for _l, (_st, _tk) in STATUS_OVERRIDE.items():
    if _l in NODE:
        NODE[_l]['st'] = _st; NODE[_l]['tk'] = _tk

def detex(s):
    s = re.sub(r'\\(Kcal|mathcal\{K\})', '𝒦', s)
    s = re.sub(r'\\(Th|Theta)', 'Θ', s); s = re.sub(r'\\xi', 'ξ', s)
    s = re.sub(r'\\SB', 'S(B)', s); s = re.sub(r'\\prec', '≺', s)
    s = re.sub(r'\\ell', 'ℓ', s); s = re.sub(r'\\infty', '∞', s)
    s = re.sub(r'\\emptyset', '∅', s); s = re.sub(r'\\otimes', '⊗', s)
    s = re.sub(r'\\sqrt', '√', s)
    s = re.sub(r'\\"o', 'ö', s)
    s = re.sub(r'\\,', ' ', s)
    s = re.sub(r'\\[a-zA-Z]+', '', s)
    s = re.sub(r'[{}$\\^_]', '', s)
    return s.replace('"', '').replace('  ', ' ').strip(' ,')

def wrap(s, w=17):
    out, line = [], ''
    for tok in s.split(' '):
        if len(line) + len(tok) + 1 > w and line:
            out.append(line); line = tok
        else:
            line = (line + ' ' + tok).strip()
    if line: out.append(line)
    return '\\n'.join(out[:4])

# ---------- 2. the nodes the paper has and Lean does not (yet) --------------
EXTRA = [
 ('eq2.34', '(2.34) 的流 —— 实现为 H_u = √u·X', 'def','done',''),
 ('eq5.1',  '(5.1) 时间连续性 —— 换成确定性 Lipschitz', 'lem','done',''),
 ('stein',  'Stein 分部积分（一维 + 矩阵版）\nMatrixStein 已卸', 'lem','done',''),
 ('lem5.3a','Lem 5.3  漂移部分 (Duhamel)',  'lem','done',''),
 ('eq5.12', '(5.12)–(5.15) L−K 的动力学',   'lem','done',''),
 ('def5.4', 'Def 5.4  E⊗E',                 'def','done',''),
 ('lem5.5', 'Lem 5.5  (5.24) —— 已不用 BDG','lem','done',''),
 ('thm2.2', 'Theorem 2.2  退局域化',        'thm','done',''),
 ('itoG',   'G_t 的 Itô 方程',              'lem','repl','T76'),
 ('lem2.11','Lem 2.11  loop 层级 (2.45)',   'lem','repl','T76/T134/T140：矩形式只剩 MatrixStein（已卸）'),
 ('lem5.15','Lem 5.15 / p.50  高斯分部积分显式式','lem','done','T83/T117/T136'),
 ('ext39',  '[39] Lem 3.3  大偏差\n已完全自证', 'lem','done',''),
 ('ext40',  '[40] (4.11) 涨落平均', 'lem','repl','T110/T137/T142：(4.12) 已达论文强度 Ψ²'),
 ('opnorm', '‖X‖ ≺ 1（OpNormBound）\n已完全证出', 'lem','done',''),
 ('lem5.3b','Lem 5.3  随机积分（逐路径形状）','lem','hyp',''),
 ('eq2.39', '(2.39) 分布相等\n逐点恒等式，已证',   'lem','done',''),
 ('eq6.1',  '(6.1) 分布标度\n逐点恒等式，已证',    'lem','done',''),
 ('thm2.21','Theorem 2.21  六步总装',       'thm','todo','一份总装同时关掉四槽（T245）；余：第 2、3 槽同一个 WeightedMoment 障碍 → T230 (A′)；Lemma514 的 hErr*/换线 → T253、T254；Eq45FlowInputs 的网格数据 → T124 续；(5.48) 的 near → Step2Near47、modulus → T251、T252、moment → T230；(2.71) 第二遍三条分析性假设已关（T247）'),
]
for i, (x, lab, k, st, tk) in enumerate(EXTRA):
    NODE[x] = dict(kind=k, title=lab, chap=9, st=st, tk=tk, uses=[])
    ORDER.append(x)

# ---------- 3. the edges that cross the two worlds --------------------------
XE = [
 ('def:model','eq2.34'),('def:gauss-model','eq2.34'),('def:gauss-model','eq5.1'),
 ('stein','thm:generator'),('def:gauss-model','thm:generator'),
 ('eq2.34','itoG'),('itoG','lem2.11'),
 ('def:gloop','lem2.11'),('def:loops','lem2.11'),('lem2.11','def:primitive'),
 ('lem2.11','eq5.12'),('lem2.11','lem5.3b'),('def:primitive','eq5.12'),
 ('def:5.2','lem5.3a'),('lem5.3a','lem5.3b'),
 ('thm:generator','thm:moment-gronwall'),('thm:moment-gronwall','lem5.5'),
 ('thm:moment-gronwall','lem5.15'),('lem:envelope','thm:moment-gronwall'),
 ('stein','lem:condrow'),('lem:condrow','ext40'),('stein','ext39'),
 ('stein','lem5.15'),
 ('def:gauss-model','opnorm'),('opnorm','eq5.1'),
 ('thm:discharge-bdg','lem5.5'),('thm:discharge-bdg','def5.4'),
 ('def:gloop','def5.4'),('def5.4','lem5.5'),('lem5.3b','lem5.5'),
 ('def5.4','lem:5.10'),('def5.4','thm:step2'),('def5.4','thm:7.2-gue'),
 ('ext39','lem:4.1'),('ext40','lem:4.1'),('ext39','lem:A.2'),
 ('eq6.1','lem:5.1'),
 ('lem:5.1','thm:step1'),('lem:4.1','thm:step1'),('eq5.1','thm:step1'),
 ('lem:3.11','thm:step1'),('thm:step1','thm:step2'),
 ('lem:7.3','thm:step2'),('lem5.5','thm:step2'),('def:5.2','thm:step2'),
 ('lem:stretched-exp','thm:step2'),('lem:3.35','thm:step2'),
 ('thm:step2','lem:5.10'),('lem:3.4','lem:5.10'),('lem:4.1','lem:5.10'),
 ('eq5.12','lem:5.10'),('lem:3.11','lem:5.10'),('lem:7.3','lem:5.10'),
 ('lem5.5','lem:5.10'),
 ('def:5.12','lem:5.14'),('lem:5.10','lem:5.14'),('lem:7.3','lem:5.14'),
 ('lem:3.6','lem:5.14'),('lem5.5','lem:5.14'),('eq5.12','lem:5.14'),
 ('lem:5.14','thm:step3'),('lem:5.14','thm:step45'),('lem5.15','thm:step6'),
 ('thm:step1','thm2.21'),('thm:step2','thm2.21'),('thm:step3','thm2.21'),
 ('thm:step45','thm2.21'),('thm:step6','thm2.21'),
 ('thm2.21','thm:2.18-from-2.21'),('eq2.39','thm:2.3-2.4'),
 ('lem5.5','thm:7.2-gue'),('lem:3.4','thm:7.2-gue'),
 ('thm:2.18-from-2.21','thm:7.2-gue'),('lem:zero-mode','thm:7.2-gue'),
 ('thm:7.2-gue','thm:2.5-2.6'),
 ('eq:2.10','thm2.2'),('thm:2.3-2.4','thm2.2'),

]
E = [(d, l) for l in ORDER for d in NODE[l]['uses'] if d in NODE]
E += [(a, b) for a, b in XE if a in NODE and b in NODE]
missing = [(a, b) for a, b in XE if a not in NODE or b not in NODE]
if missing: print('WARN unresolved edge endpoints:', missing, file=sys.stderr)

# ---------- 4. render -------------------------------------------------------
def sty(k, st):
    if st == 'cited':
        return 'shape=ellipse, style="filled,dashed", fillcolor="#fdf3e0", color="#c99a4a", fontcolor="#6b4d17"'
    if st == 'done':
        if k == 'def':
            return 'shape=box, style="filled,rounded", fillcolor="#cfe9dc", color="#7cbfa4", fontcolor="#123a2b"'
        sh = 'doubleoctagon' if k == 'thm' else 'ellipse'
        return f'shape={sh}, style=filled, fillcolor="#1f9d6b", color="#177a54", fontcolor="#ffffff"'
    if st == 'hyp':
        sh = 'box' if k == 'def' else 'ellipse'
        stl = '"filled,rounded"' if k == 'def' else 'filled'
        return f'shape={sh}, style={stl}, fillcolor="#f6d99a", color="#c99a4a", fontcolor="#5a3f10"'
    if st == 'repl':
        sh = 'box' if k == 'def' else 'ellipse'
        stl = '"filled,rounded"' if k == 'def' else 'filled'
        return f'shape={sh}, style={stl}, fillcolor="#dbe8f5", color="#5d8cb8", fontcolor="#16344d"'
    sh = 'box' if k == 'def' else ('doubleoctagon' if k == 'thm' else 'ellipse')
    stl = '"filled,rounded"' if k == 'def' else 'filled'
    return f'shape={sh}, style={stl}, fillcolor="#ffffff", color="#9aa3ac", fontcolor="#495159"'

L = ['digraph P {',
     '  graph [rankdir=TB, splines=true, nodesep=0.09, ranksep=1.12, newrank=true,'
     ' bgcolor="transparent"];',
     '  node [fontname="Helvetica", fontsize=10, penwidth=1.3, height=0.44, margin="0.12,0.07"];',
     '  edge [color="#b3bac2", penwidth=0.9, arrowsize=0.6];']
for lab in ORDER:
    n = NODE[lab]
    text = wrap(detex(n['title']) or lab)
    if n['tk']: text += '\\n[' + '；\\n'.join(n['tk'].split('；')) + ']'
    L.append(f'  "{lab}" [label="{text}", {sty(n["kind"], n["st"])}];')
for a, b in sorted(set(E)):
    L.append(f'  "{a}" -> "{b}"' + (' [style=dashed]' if NODE[a]['st'] == 'hyp' else '') + ';')
L.append('}')
io.open('paper.dot', 'w', encoding='utf-8').write('\n'.join(L))
svg = subprocess.run(['dot', '-Tsvg', 'paper.dot'], capture_output=True, text=True).stdout
svg = svg[svg.find('<svg'):]
head = svg.split('>', 1)[0]
w = float(head.split('width="')[1].split('pt')[0])
h = float(head.split('height="')[1].split('pt')[0])
svg = re.sub(r'<svg width="[\d.]+pt" height="[\d.]+pt"',
             '<svg class="depgraph" preserveAspectRatio="xMinYMin meet"', svg, count=1)
io.open('paper.svg', 'w', encoding='utf-8').write(svg)

cnt = {s: sum(1 for l in ORDER if NODE[l]['st'] == s) for s in ('done', 'hyp', 'repl', 'todo', 'cited')}
hyp  = [l for l in ORDER if NODE[l]['st'] == 'hyp']
repl = [l for l in ORDER if NODE[l]['st'] == 'repl']
todo = [l for l in ORDER if NODE[l]['st'] == 'todo']
def li(l):
    n = NODE[l]
    tk = f' <code>{html.escape(n["tk"])}</code>' if n['tk'] else ''
    return f'<li><b>{html.escape(detex(n["title"]))}</b>{tk}</li>'

frag = f"""  <h2>全文依赖图</h2>
  <p>整篇论文一张图，{len(ORDER)} 个节点、{len(set(E))} 条边，箭头由前提指向结论。
  下面各章的图是这张图按章切开的子图，粒度完全一致（一个节点 = 一个形式化步骤，
  不是论文的一条编号命题），只是这里还多画了<strong>尚未形式化的和被矩路线替代的</strong>。
  可缩放、拖动平移、双击切换。</p>
  <div class="legend">
    <span><i style="background:#1f9d6b"></i>已在 Lean 中证明（{cnt['done']}）</span>
    <span><i style="background:#cfe9dc"></i>定义（已形式化）</span>
    <span><i style="background:#dbe8f5"></i>矩路线替代中（{cnt['repl']}）</span>
    <span><i style="background:#f6d99a"></i>仍作为假设（{cnt['hyp']}）</span>
    <span><i style="background:#ffffff"></i>待形式化（{cnt['todo']}）</span>
    <span><i style="background:#fdf3e0"></i>引用论文结论不证（{cnt['cited']}）</span>
  </div>
  <figure class="graph" data-basew="{w:.0f}" data-baseh="{h:.0f}">
    <div class="gbar">
      <span class="gcap">全文依赖图 · {len(ORDER)} 个节点 · {len(set(E))} 条边</span>
      <div class="gtools">
        <button type="button" data-act="out" aria-label="缩小">&minus;</button>
        <button type="button" data-act="fit">看全</button>
        <button type="button" data-act="in" aria-label="放大">+</button>
        <span class="gpct" aria-live="polite">100%</span>
      </div>
    </div>
    <div class="plate"><img class="depgraph" src="paper.svg" alt="whole-paper dependency graph" width="{int(w)}" height="{int(h)}"></div>
  </figure>

  <div class="scope">
    <div class="panel in">
      <h3>矩路线替代中的 {cnt['repl']} 条（蓝）</h3>
      <ul>{''.join(li(l) for l in repl)}</ul>
      <p>矩路线不去证它们，而是<strong>接管它们的作用</strong>。
      <b>Lemma 5.5 的 (5.24) 已经不需要 BDG 了</b>（生成元恒等式 + 对矩的 Grönwall 直接给出），
      <b>(5.43) 的停时也已换成连续归纳</b>——这两个原来的橙点现在是绿的。
      剩下这几个里，Itô 方程与 loop 层级 (2.45) 由生成元恒等式的矩形式接管（矩阵 Stein 已证）；
      [40] 的涨落平均由带基数预算的条件化版接管，(4.12) 已达论文强度 Ψ²；
      Step 2 与 (4.12) 两个蓝点的余项见各自说明。方括号里是相关工单。</p>
    </div>
    <div class="panel out">
      <h3>仍作为假设的 {cnt['hyp']} 条（橙）</h3>
      <ul>{''.join(li(l) for l in hyp)}</ul>
      <p><strong>只剩一条</strong>：Lemma 5.3 的随机积分在<strong>逐路径形状</strong>下不可卸
      —— 矩路线只需要它的期望版，那一版已经证了（<code>thm:moment-hierarchy</code>）。
      两处<strong>分布相等</strong>（(2.39)、(6.1)）已于 2026-09-21 卸掉——在 <code>H_u = √u·X</code> 的实现下
      它们是<strong>逐点恒等式</strong>，根本不需要分布论证。
      <b>Itô 那一整族、BDG、停时、两条分布相等，以及两条外部文献，都已经不在这张表上了。</b></p>
    </div>
  </div>

  <div class="note">
    <strong>还没做的 {cnt['todo']} 条</strong>：{'、'.join(detex(NODE[l]['title']) + (f" [{NODE[l]['tk']}]" if NODE[l]['tk'] else '') for l in todo)}。
  </div>
"""
io.open('papermap.html', 'w', encoding='utf-8').write(frag)

import sys as _sys
_nthm = _sys.argv[2] if len(_sys.argv) > 2 else '?'
_chips = (
  f'<div class="chip done"><b>{cnt["done"]}</b><span>全文节点已证（共 {len(ORDER)}）</span></div>\n'
  f'      <div class="chip ready"><b>{cnt["repl"]}</b><span>矩路线替代中</span></div>\n'
  f'      <div class="chip todo"><b>{cnt["hyp"] + cnt["todo"]}</b><span>仍作为假设 / 待形式化</span></div>\n'
  f'      <div class="chip done"><b>{_nthm}</b><span>Lean 定理 · 0 sorry · 0 项目公理</span></div>'
)
io.open('chips.html', 'w', encoding='utf-8').write(_chips)
print('nodes', len(ORDER), 'edges', len(set(E)), 'counts', cnt, 'size', int(w), int(h))
