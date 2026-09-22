# 接管手册：Cowork 调度断线时，由 ChatGPT / Codex 接手

> 写于 2026-09-22 02:45 UTC，作者 Cowork（Claude）。
> 用途：Cowork 断线、额度用完或长时间无响应时，让另一个模型（Codex 或 ChatGPT）**临时接手「调度」这个角色**，项目不停。
> 这份文件与 `docs/cowork-*.md` 三份文档是 Cowork 侧全部工作方法的**仓库内副本**（原件在 Claude 项目里，别的模型读不到）。

---

## 0. 三十秒版

* **项目**：用 Lean 4 + Mathlib 形式化 Yau–Yin《Delocalization of One-Dimensional Random Band Matrices》（arXiv:2501.01718）。论文基准版本 `paper/250520-YinJun-v2.pdf`。
* **两层结构**：**调度**（原来是 Cowork）只读论文、审计、开单、记账、做路由类决定；**工人**（Claude Code 终端或 Codex）写 Lean、编译、提交。**调度不写 Lean**（Jun：「你不要再当工人啦，只当调度。」）。
* **进度的唯一真相**：`docs/TASKS.md`（工单队列，第 3 行是优先级横幅）、`docs/STATUS.md`（短的当前状态与有效裁定；旧记录已存档）、`docs/paper-deltas.md`（Lean 与论文的偏差）、`CLAUDE.md`（仓库规则，对所有 agent 适用）。
* **接手后的第一件事**：读本文件 §2（Jun 的规则）、§7（已定的裁定，不要重开），再读当前 `docs/STATUS.md` 与 TASKS 第 3 行，做一次 §4 的心跳；本文件旧 §8 是历史快照，不代替 STATUS。

---

## 1. 角色

| 角色 | 谁 | 做什么 | 不做什么 |
|---|---|---|---|
| 调度 | 原 Cowork → **接手者** | 心跳、审计完成的单、开新单、给 paper-deltas 赋号、路由类裁定、向 Jun 汇报 | 不写 Lean；不改论文陈述；不替 Jun 定范围 |
| 工人 | Claude Code 终端（协调者 + 最多 6 个子 agent）；T217 起也用 Codex | 认领工单、写 Lean、`lake build`、提交、`git push` | 不改冻结签名；不写 `axiom`；不 `git add -A` |
| 决策 | **Jun** | 论文陈述、编号、范围、外部输入 | — |

---

## 2. Jun 的永久规则（逐字，不要改写）

1. 「不要参考其他文献，就用这个」——只依据仓库里的论文 PDF。
2. 「如果文章有小错误，可以自行修改」
3. 「其他类似问题都同意」——**路由类**决定（新文件还是就地改、哪张单负责、Lean 内部走哪条证明路线）不需要问 Jun。
4. 「你不要再当工人啦，只当调度。」
5. 外部输入：「Step 1好像的确只能用外部假设。1. 我们只能用他们论文中standard 结果（main result） 不能编造类似结论作为input，2 最后lean 报告里要提到Universality部分用到了外部input， 其他都是独立完整的Lean。 其他部分全部自己来证明。」
6. 「你就以complex 形式的Theorem 2.2. 作为外部输入口」——唯一外部假设 = [51] Theorem 2.2 的复 Hermitian 形式（GOE → GUE，其余逐字）。
7. 心跳：「心跳时间不要自行放慢超过20分钟一次」。
8. Theorem 2.6：「等其余各块无高风险项后再开启」。
9. 范围变更、发布/删除、不可逆操作要先问 Jun；**论文陈述改动**要 Jun 确认；论文改动要**尽量小、不重新编号**。
10. 永不写 `axiom`；不改冻结签名（要改就加带撇版 `Foo'`）；不 `git add -A`，只提交具体文件；根文件 `RBM1D.lean` 只做点插入 import。

---

## 3. 文件地图

| 文件 | 内容 | 谁写 |
|---|---|---|
| `CLAUDE.md` | 仓库规则（构建、硬规则、可满足性纪律、外部输入边界、构建陷阱） | 调度 + 工人 |
| `AGENTS.md` | 给 Codex 等非 Claude agent 的入口，指向本文件与 `CLAUDE.md` | 调度 |
| `docs/TASKS.md` | **只放活跃单**。每行 `\| Txxx \| 描述 \| 文件 \| 负责人 \| 状态 \|`；**第 3 行**是优先级横幅；完成的行用 `scripts/archive_done_tasks.py --apply` 移进 `docs/archive/TASKS-done.md` | 调度开单；工人改状态栏 |
| `docs/STATUS.md` | **目标 ≤ 120 行**，只保留当前依赖、有效裁定、阻塞与最多八条最近验收；过时叙述立即存入带日期的 `docs/archive/STATUS-*.md`，不等到超过上限 | 两边 |
| `docs/reports/Txxx.md` | 每张单的完成报告全文 | 工人 |
| `docs/archive/` | 历史全文（`STATUS-2026-09-19_22.md` 6900 行、`TASKS-2026-09-19_22.md`、`TASKS-done.md`）。**只 grep，不整份读** | 调度 |
| `docs/paper-deltas.md` | Lean 与论文的偏差表；`#` 栏由调度赋数字号 | 工人写临时号，调度赋号 |
| `docs/REPORT.md` | 最终 Lean 报告（活文档；§9 是 R1–R5 裁定） | T217 在改 |
| `docs/agent-playbook.md` | 工人侧的并行 agent 手册（派单 prompt 骨架、空真九例表） | 工人 |
| `docs/cowork-paper-edit-budget.md` | **论文改动清单**（第 6–17 条全部经 Jun 确认） | 调度 |
| `docs/cowork-theorem-2.6-analysis.md` | Theorem 2.6 的外部输入分析与 Jun 的裁定 | 调度 |
| `docs/cowork-lessons.md` | 调度的经验与审计清单（写 skill 的底稿） | 调度 |
| `tools/blueprint_page/` | 蓝图网页生成器（python3 + graphviz），见 §10 | 调度 |
| `paper/250520-YinJun-v2.pdf` | 论文基准版本（页码以此为准；**引用以公式编号为主**） | — |
| `paper/1609.09011v3.pdf` | [51]（Theorem 2.6 的外部输入） | — |

⚠ **论文 PDF 不进版本库**（`.gitignore` 里 `paper/*.pdf`）：只在 Jun 的 Mac 上 `~/Lean_proof/RBM1D/paper/`。在本机跑的 Codex 读得到；从 GitHub 克隆的副本、网页版 ChatGPT 读不到——要把 PDF 作为附件给它们。另外 `docs/` 下只有**顶层** `*.md` 入库（`docs/*` 被忽略、`!docs/*.md` 放行），新文档不要建子目录。

---

## 4. 一次「心跳」怎么做

间隔 ≤ 20 分钟。接手者没有定时器的话，Jun 说一声「心跳」就做一轮；Codex 可以在一轮做完后自己再开始下一轮。

```bash
cd ~/Lean_proof/RBM1D
git log --oneline -15            # 新提交；工人提交信息以 "Txxx:" 开头
git status --short               # 在飞 agent 的半成品；docs/ 有别人的未提交改动时不要提交那个文件
tail -3 build.log                # "lake build exit=0" 且 "errors: 0" 才算绿（注意时间戳，可能是旧的）
grep -nE '^\| *T[0-9]+[a-z] *\|' docs/paper-deltas.md   # 待赋号的临时号
```

每轮固定动作：

1. **审计新完成的单**：读提交信息 + STATUS 里对应的节，按 §5 过一遍。有问题就在 STATUS 追加「审计」段并开修复单。
2. **把「无主」全部开单**：完成报告里凡写「无主」「没有单负责」「建议新单」「待定夺」的，同一轮开单或裁定（§6）。拖一轮就会被淹没。
3. **paper-deltas 赋号**（仅当 `docs/paper-deltas.md` 没有别人的未提交改动时）：
   ```python
   import re
   p='docs/paper-deltas.md'; s=open(p,encoding='utf-8').read(); L=s.split('\n'); n0=len(L)
   nxt=max(int(m.group(1)) for l in L for m in [re.match(r'^\| *(\d+) *\|',l)] if m)+1
   for k,l in enumerate(L):
       m=re.match(r'^\| *(T\d+[a-z]) *\|',l)
       if m:
           l2=re.sub(r'^\| *T\d+[a-z] *\|', f'| {nxt} |', l, count=1).rstrip()
           L[k]=l2[:-1].rstrip()+f'（原临时号 {m.group(1)}） |'; nxt+=1
   assert len(L)==n0; open(p,'w',encoding='utf-8').write('\n'.join(L))
   ```
   若同一条偏差既有数字号初稿、又有临时号终版，用终版内容覆盖该数字号并删掉临时号那行（先例：#151/#152）。
4. **队列深度**：尽量保持至少三张已过数学预审、文件互斥的可领单。不得为了凑数把尚无真实量级或非循环输入的目标派出去；不足三张时，在 STATUS 写明数学障碍和下一步核查。
   **瘦身**：每轮先跑 `python3 scripts/archive_done_tasks.py` 预览，再用 `--apply` 把已审计完成/关闭的行移出 TASKS；STATUS 只保留当前有效信息与最多八条最近验收，一旦叙述过时便先存到 `docs/archive/STATUS-<日期>.md` 再删，不等行数达到上限。无变化心跳不追加段落。审计时读 `docs/reports/Txxx.md` 与提交信息，**不要整份读 archive**。
5. **先做数学预审，再开单和派单**（Jun 2026-09-22）：调度亲自对照指定论文 PDF 的公式、目标 Lean 定义与现有生产者，写出精确量词和假设、关键不等式或时间正则性、每项 N/W/时间幂次、最小长度与首格、事件交集及非循环依赖。至少做一次具体参数或边界情形检查。判定为「数学上可行」「仍需某条明确的数学输入」或「原目标错误」；后两者不得包装成正面证明单。心跳汇报必须列出本轮实际核过的式子、依据、判定与剩余条件；不能只写“已审”。已经派出的单若发现目标不成立，立即通知工人调整或停止。
   **每轮实际派单**（Jun 2026-09-22）：逐一核对既有工人任务的 active/idle 和文件所有权；审计完成件后，对每个空闲槽优先找已过数学预审、文件互斥的真实余项，立即发送工单消息并确认任务启动。不能只把单写进 TASKS 或只汇报状态。确无合格目标时不空派，在 STATUS 写明各空闲槽的具体数学障碍和下一轮先核什么。
   数学预审通过后，用 python 按唯一锚点插行（`split('\n')` → 插入 → `'\n'.join`，**断言行数只增不减**；终端侧曾把 TASKS 从 2695 行截成 4 行）。新单号 = 现有最大号 + 1。每张单写清：来源、论文公式、要交付的声明、预审依据、**验收标准**（通常是「某探针的假设表里不再有 X」+ 公理干净 + **非退化**可满足性见证）、禁止事项和文件所有权。
6. **提交**：只暂存已审计的具体文件，勿混入在飞工人的改动；在 Jun 已授权的本项目中，将验收提交推送 `origin/main`。无实际改动时不制造心跳提交。
7. **汇报 Jun**：一小段话；只有需要他定的事才问，一次一件，给出倾向。

常用命令：

```bash
# 定理数（完整口径）
R='^\s*(@\[[^]]*\]\s*)?((private|protected|nonrec|noncomputable)\s+)*(theorem|lemma)\s'
git grep -hE "$R" HEAD -- 'RBM1D/*.lean' | wc -l
# 全量构建（结果写进 build.log）
./check.sh
```

---

## 5. 审计清单（每张完成的单都过一遍）

编译通过 + 公理干净 **不等于有内容**。这个项目最常见的缺陷是**空真**（假设不可满足 → 定理平凡成立），至今九例（表见 `docs/agent-playbook.md` §一）。

* **可满足性见证**：交付含新假设的定理时，必须附一组显式参数使全部假设同时成立，且是**非退化**的（不是 `s = t = 0`、`J ≡ 0`、`Ξ = ∅`、漂移 = 0）。最好在临界标度上。
* **fiat**：结构里有自由数据字段、定理对它全称量化 → 取平凡值即满足。数据必须是 `def` 或由恒等式钉死。
* **量词**：次序对照论文（「`p` 固定、`N → ∞`」不能写成 `∀ p N`）；量化范围对照使用范围（第九例：`∀ v : ℝ` 应为窗口）；`∀ N` 含 `N = 0` 时要警惕。
* **`ω = 0` 同形检查**：确定性不等式在 `H = 0` 处是否仍成立且有内容。
* **冻结签名**：`git show <commit> -- <file> | grep '^-theorem'`，旧签名必须原样还在；改动只能是加带撇版或 `@[deprecated]`。
* **「搬家不是消灭」**：假设从一个名字换到另一个字段，不算卸掉。
* **构建**：新文件必须 `lake build RBM1D.<模块>` 过（`lake env lean` 不施加 `autoImplicit` 等选项，会放过坏文件）。
* **推翻旧说法**：每次集成都问——这次结论是否推翻了先前告诉 Jun 的东西？是就当面更正。

---

## 6. 决策分流

* **路由类**（Lean 内部走哪条路、接口怎么改、哪张单负责、新文件还是就地改）且**论文陈述一字不动** → 调度当轮定，在 STATUS 追加「裁定」段写理由，汇报时告诉 Jun「已代定，可推翻」。
* **先对照 §7**：agent 交来的选项若与 Jun 已有裁定冲突，直接排除（先例：D15 的选项 1/2 要给模型加滤子，与 (a) 冲突）。
* **必须上交 Jun**：改论文陈述、新增/重排编号、改范围、外部输入的形状、Theorem 2.6 何时开。
* 论文笔误级的小错：列进 `docs/cowork-paper-edit-budget.md`，汇报 Jun（规则 2）。

---

## 7. 已定的裁定（不要重开）

| 编号 | 裁定 | 谁定 |
|---|---|---|
| (a) | 论文保留布朗运动模型，随机层零改动；Lean 用 `H_u = √u·X`，只在一时刻律层面对齐；矩 Duhamel 是 Lean 内部路线 | Jun |
| 外部输入 | [51] Theorem 2.2 的复 Hermitian 形式为唯一外部假设；[35] Prop 3.3 已排除；报告写明 | Jun |
| D12 | 两遍：先不含 (2.71) 的 Theorem 2.21（T204 已完成），再 (2.71) 第二遍（T205/T227/T234） | Jun |
| D13 | Theorem 2.21 补 `t ≤ 1 − N^{−1+τ}`；Lean 最终版收 `Cond272Reg`；T209 证明六步不需要 (2.72) 的 `N^c` 增益 | Jun |
| D14 | Lemma 5.14 的矩路线改以 `Hyp.momentDuhamelQ` 为接口（论文 (5.92)/(7.16) 的路线） | Cowork |
| D15 | (5.48) 远场改光滑阈值（`6ℓ* → 12ℓ*`），`M_m` 整条删掉；不加滤子 | Cowork |
| `xi2` | 第二半漏共轭，原地改定义（T223 已落地） | Cowork |
| #155 | 矩不等式常数取 `C_{n,p}`（论文 (5.103) 印有 `C_n`，(5.24) 写作 `C_{n,p}`） | Cowork |
| T232 | `CutHyp` 的 `modulus`/`mesh_fine` 改 `∀ᶠ N` | Cowork |
| T235 | 重复证明脚本一律上移共享，不接受第四份重复 | Cowork |
| R1–R5 | 报告：2.2–2.5 并列主定理；否定结论单列一节，分「论文修正」与「自设接口被证伪」；2.6 标③直到 `OUFlow` 钉死 | Jun 同意 |
| 论文改动 | `docs/cowork-paper-edit-budget.md` 第 6–17 条**全部确认** | Jun |
| (5.43) | Jun：「(5.43)–(5.47) 当时好像不是用的停时方案」——原意是连续性论证，与 T230 路线 (B) 一致 | Jun |

---

## 8. 历史快照（2026-09-22 03:45 UTC；实时状态以当前 `docs/STATUS.md` 为准）

* **规模**：约 5760 条定理、0 sorry、0 项目公理，HEAD 构建绿；paper-deltas 编到 #163。
* **Theorem 2.21 第一遍**已总装在 `Flow/Thm221Assembly.lean`（T239），(5.48) 已从假设表消失。**完整假设表与每槽归属见 `docs/reports/T239.md`**：`Step1.Hyp` → T242；`MomentHypCut` → T230 (A′)/T232；`hΘ`/`Eq45Flow` → T243；`Lemma514` → T236；`Eq548EntryData` 的 `init` → T241、`near`/`meas`/`modulus` → T244、`moment` → T230。
* **最高风险：T230**。路线 (B)（高概率前缀 + 包络）已被编译否定（坏质量沿网格几何放大）；改走 (A′)：前缀权重取光滑函数之积 `∏χ(|lk|²/(ΘT)²)`，权重是 `X` 的函数，Stein 在全测度上用。实现前先交只读设计。
* **(2.71) 第二遍**：T234 后 `Bounds` 在 `s > 0` 余 7 项；`hKd` 不是数学缺口（衰减长度就是 `ℓ_v`）。
* **之后**：T159 端到端核对 → Theorem 2.6（约 12–18 张单，见 `docs/cowork-theorem-2.6-analysis.md`）→ 最终报告（T217 在改）。

## 9. 如果工人（终端）也停了

Codex 可以直接当工人（T217 已经这么做了）：

* 读 `CLAUDE.md`（全部规则对任何 agent 适用）、`docs/TASKS.md` 里要做的那一行、`docs/STATUS.md` 里相关的节。
* 认领：改那一行的状态栏为「进行中（Codex，时间）」并只提交 `docs/TASKS.md`。
* 并发上限 6；同一文件的两张单串行。
* 收工：`lake build RBM1D.<模块>` 与 `./check.sh` 都绿、`#print axioms` 只有 `propext / Classical.choice / Quot.sound`、附非退化可满足性见证；在 STATUS 追加完成报告（含「无主的活」清单）；只 `git add` 具体文件。
* agent 集体中断（HTTP 529 或会话退出）后：逐单登记半成品（文件、是否编译、「未验证」），**重派时重新核，不要照登记处置**——登记是快照。

---

## 10. 蓝图

* **公开站点**：GitHub Pages（`.github/workflows/blueprint.yml`，每 3 小时定时 + 手动 `workflow_dispatch`）。
* **总览网页**（依赖图 + 进度）：原来发布在 claude.ai 的 artifact 上，只有 Claude 能更新。生成器已复制到 `tools/blueprint_page/`，接手者可在本地生成 HTML：
  ```bash
  cd tools/blueprint_page
  python3 paper.py ../../blueprint/src/content.tex <定理数>
  python3 build.py ../../blueprint/src/content.tex <定理数>
  # 产出 blueprint.html + paper.svg + g0–g3.svg，浏览器直接打开
  ```
  需要 `python3` 与 graphviz 的 `dot`。脚本有「环境数 ≠ 解析节点数就退出」的守卫。`paper.py` 里 `STATUS_OVERRIDE` 与 `EXTRA` 的说明文字要随工单进度手改。

---

## 11. 开场 prompt（可直接粘贴）

### Codex 当调度（推荐；它能直接在仓库里跑命令）

> 你现在接手这个仓库的「调度」角色。先读 `docs/HANDOVER.md` 的规则与固定裁定、`CLAUDE.md`、当前短版 `docs/STATUS.md`，再定向读 `docs/TASKS.md` 的优先级横幅和在飞/可领行。整个项目目标是全文 Lean 化，不以眼前几张单为终点。
> 你**不写 Lean 证明**，按 HANDOVER §4 心跳：审计新完成单、给每个真实余项开边界清楚且文件互斥的单、维护未认领队列、按规则处理 paper-deltas；每轮把完成单移进 `docs/archive/TASKS-done.md`，把过时 STATUS 叙述存档，保持短版状态准确，不为无变化心跳追加段落。只提交已审计的具体文件；Jun 已授权将验收提交推送 GitHub。§7 已定裁定不要重开；需要 Jun 定的事一次只提一件。

### ChatGPT（网页版，没有仓库权限时）

只适合做**数学审阅与决策参谋**，不能当调度：

> 这是一个 Lean 4 形式化项目（Yau–Yin 1D 带状矩阵离域化）。附件是 `docs/HANDOVER.md`、`docs/STATUS.md` 最后一段、相关工单行和论文 PDF。请只做两件事：(1) 审阅这张完成报告，按 HANDOVER §5 的清单指出空真/fiat/量词/冻结签名问题；(2) 对「待定夺」给出倾向和理由。不要写 Lean 代码。

若 ChatGPT 能连 GitHub（连接器），可让它读仓库，但**提交仍由 Codex 或终端做**。

---

## 12. Claude 回来之后

在 Cowork 里说一句：「读 `docs/HANDOVER.md` §8 和 STATUS 里所有『接手者记录』，恢复心跳。」
接手者追加的「接手者记录」就是交接凭证——Cowork 会据此审一遍接手期间的裁定，有冲突当面报告 Jun。

---

## 13. 已知的坑

* **git 锁**：Cowork 会话重连后删除权限会被重置，`git commit` 删不掉 `.git/HEAD.lock`，残留会卡住终端的下一次提交。处理：把 `.git/*.lock` 挪进 `.git/_to_delete/`，再申请删除权限。
* **`lake env lean` 不算数**：不施加 `leanOptions`（`autoImplicit`），会放过 `lake build` 拒收的文件。
* **`git add -A <目录>`** 会把在飞 agent 的半成品一起提交（发生过一次）。永远逐文件 `git add`。
* **build.log 可能是旧的**：看第一行时间戳；并行 agent 的半成品会让工作区构建变红而 HEAD 是绿的。
* **页码**：以公式编号为准；仓库 PDF 是基准版本（Jun 曾用错版本对页码）。
* **读论文公式**：`pdftotext` 会丢上下标与符号；逐字核对要把页面渲染成图像看（`pdftoppm -f P -l P -r 110 -png`）。
* **paper-deltas 撞号**：并行 agent 各取 max+1 必撞（一天撞五次）。agent 只写临时号 `T<单号><字母>`，数字号由调度统一赋。
* **完成报告里的「更正工单」**：工人经常推翻调度写在工单里的猜测（技术路线、来源、文件行号）。以编译探针为准，接受更正，并在 STATUS 记下。
