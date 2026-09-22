# CLAUDE.md — RBM1D

用 Lean 4 + Mathlib 形式化 Yau–Yin《Delocalization of 1D Random Band Matrices》(d=1)。

## 唯一真相来源

- **论文**：`paper/250520-YinJun-v2.pdf`（95 页）。**只依据这篇论文，不引用任何其他文献。**
- **路线图**：`docs/PLAN.md` — 阶段划分与每阶段的 Lean 声明清单
- **当前进度**：`docs/STATUS.md` — **每次会话开始先读；有实质状态变化才更新**。单张工单的完整过程写在 `docs/reports/Txxx.md`
- **与论文的偏差**：`docs/paper-deltas.md` — 凡 Lean 陈述 ≠ 论文字面陈述，必须在这里记一条
- **调度交接**：`docs/HANDOVER.md` — Cowork 离线时由 Codex / ChatGPT 接手调度的手册；`AGENTS.md` 是非 Claude agent 的入口；`docs/cowork-*.md` 是 Cowork 侧文档（论文改动清单、Theorem 2.6 分析、调度经验）的仓库内副本
- **⚠ 读文档的纪律（2026-09-22，Jun：「STATUS + TASKS 文件太大了」）**：`docs/STATUS.md` 只保留当前状态、有效裁定、阻塞和最近验收，目标 ≤ 120 行；`docs/TASKS.md` 只放活跃单——**按工单号定向搜索**。完成单每轮用 `scripts/archive_done_tasks.py --apply` 移到 `docs/archive/TASKS-done.md`；STATUS 的过时记录及时存入带日期的 archive 快照，不等它长到上限，也不为无变化心跳重复追加。历史全文在 `docs/archive/`（**永远只 grep，不整份读**）。完成报告全文写 `docs/reports/Txxx.md`；无主/待定夺写当前 STATUS 并开单。派单 prompt 里贴相关节正文，明禁子 agent 读整份文档。

## 环境

Lean `4.34.0` / Mathlib `v4.34.0`（rev `5ed2965256`），cache 已拉好。
Mathlib 源码在 `.lake/packages/mathlib/Mathlib/` —— 找 API 就 grep 这里。

## 构建回路

```bash
lake env lean RBM1D/Propagator/Xxx.lean   # 单文件，秒级 —— 默认用这个
./check.sh                                 # 全量，结果写进 build.log
./watch.sh                                 # 另开终端，改动即自动重编
```

**绝不在没有实际跑过编译的情况下说"写好了"。** 每次回报前必须有一次 exit=0。

## 硬性规则

1. **不留 `sorry`。** 证不出来就停下说「卡在 X」，不要 sorry 占位然后继续往下写。
2. **不许发明 Mathlib 引理名。** 先 `grep -rn "circulant_mul" .lake/packages/mathlib/Mathlib/`，
   或在 scratch 文件里 `#check @foo` 编译看签名。`exact?` / `apply?` / `rw?` / `aesop` 鼓励用。
   已核实的 API 记在 `docs/mathlib-api.md`（原 `Probe.lean` 已删），先查它。
3. **公理审计。** 每条主定理证完跑 `#print axioms RBM.xxx`，只允许出现
   `propext` / `Classical.choice` / `Quot.sound`。出现 `sorryAx` 就是没做完。
   `RBM1D.lean` 末尾的 `#assert_rbm_axioms`（`Test/Axioms.lean`）对整个 `RBM` 命名空间做硬性检查，违规即编译失败。
4. **陈述逐字对应论文。** 不得不加假设（如 `3 ≤ L`）或换陈述形式，必须写进 `docs/paper-deltas.md`。
5. **小步提交。** 一次只动一条引理 / 一个文件；绿了就 `git commit`，不要攒一大坨再一起编译。
6. **不碰随机层**（Itô、Dyson Brownian motion、loop hierarchy、universality）。
   Mathlib 没有随机分析，那部分只写 `axiom` 接口，而且现在还不到时候。
7. **常数不求最优。** 统一写成 `∃ C > 0, ∃ c > 0, ∀ ...`；`≺` 用 `DetDom` 封装。

## 命名与风格

- namespace `RBM`；声明名走 Mathlib 风格（`Theta_apply_add_right`、`sum_SB_row`、`norm_Theta_le`）
- 变量约定：`L : ℕ`、`[Fact (3 ≤ L)]`、指标类型 `ZMod L`、谱参数 `ξ ζ : ℂ` 且 `‖ξ‖ < 1`
- 文件头 copyright 块照抄现有文件
- 每落地一个声明，去 `blueprint/src/content.tex` 对应节点补 `\lean{}` + `\leanok`；
  节点名与论文编号一一对应（`lem:2.14`、`eq:2.52`、`lem:3.6`）

## 分工：Claude Code 与 Cowork

两边都在用，边界按**迭代延迟**划，不按角色划。

| | Claude Code（本机） | Cowork / chat（云端） |
|---|---|---|
| 证明的试错循环 | **主场**。`lake env lean 单文件` 秒级返回 | 一轮约 2 分钟，不适合高频试错 |
| 读论文 PDF | 需要 `paper/` 下有 PDF（本地有，不入库） | PDF 在会话里，随时翻页 |
| 蓝图渲染 / 依赖图 | 需本机装 plasTeX + graphviz | 工具链现成，可直接发布成网页 |
| 路线规划、阶段划分 | — | **主场** |
| git / CI / GitHub Pages | 都行 | 都行 |

### 任务队列

`docs/TASKS.md` 是两边共用的工单表。**开工前先在表里认领并提交**。
分工按**文件**切分，不按难度切分：同一时间两边不碰同一个文件，合并就永远是平凡的。
推之前先 `git pull --rebase`。

### 交接契约

`docs/STATUS.md` 是两边**唯一**的共享状态。任何一边：

- 开工前先读它
- 收工时把完整声明、验证和尝试过程写进 `docs/reports/Txxx.md`；只在 STATUS 更新对主链有影响的结论、真实阻塞及下一工单
- 卡住时在报告中写清「卡在 X，试过 Y 和 Z，失败原因是 W」，STATUS 只留一句精确缺口和报告指针

`docs/paper-deltas.md` 同理：偏离论文字面陈述的地方，谁发现谁记，不要只在对话里说。
**引用论文位置的纪律（Jun 2026-09-21）**：**以公式/定理编号为准，页码只作辅助**。仓库里所有页码指 `paper/250520-YinJun-v2.pdf`（Acta 投稿版）的印刷页码——**这是基准版本**（Jun 2026-09-21 确认：之前页码对不上是他手上开错了版本）。引用未编号的显示式时，写「(5.67) 之后那行」并引一句原文，不要只写页码。
**取号纪律（2026-09-21 修订：撞号四次后改为临时编号）**：**agent 新增 paper-delta 一律不写数字号**，`#` 栏写 `T<工单号><字母>`（如 `T165a`、`T165b`），STATUS/提交信息里也这样引用；**数字号由 Cowork 在心跳时统一分配**（按提交顺序），并把临时编号替换掉、在该行末尾注明「原临时号 T165a」。已有数字号的行**不许改号**。

### 常设授权

路由决策（某项工作该在 Claude Code 还是 Cowork 做）不必每次征求同意，按上表直接定。
需要征求同意的只有：改变项目范围、公开/删除内容、以及任何不可逆操作。

### 论文 PDF

`paper/250520-YinJun-v2.pdf` 放在本地供 Claude Code 读，已在 `.gitignore` 里排除，
不会推到公开仓库。

## 当前位置与下一步

当前优先级以 `docs/TASKS.md` 第 3 行和 `docs/STATUS.md` 为准。早期 Phase 1 的下一步计划已存入 `docs/archive/CLAUDE-phase1-plan.md`，不要将它作为当前调度命令。

## 会话结束前的检查单

1. `./check.sh` → `build.log` 里 `errors: 0`、`exit=0`
2. `grep -rn "sorry" RBM1D/` → 只有 `Test/Sanity.lean` 里那句注释
3. 有实质变化时更新 `docs/STATUS.md`（当前依赖与下一步）；无变化时不追加记录
4. `git commit`

## 队列空了怎么办

**不要停下来等新工单。** `docs/TASKS.md` 末尾有「永不停工规则」和储备工单 B1–B6：
队列一空就按那个顺序自己挑活（先 T8–T11 的一般 Fourier 机器，再 B1–B6，再常规维护），
并在工单表里补一行说明你在做什么。空转是这个项目里唯一不可接受的状态。

## 读 build.log 的陷阱（2026-09-19，实际踩过）

`build.log` 是 `watch.sh` 轮询重写的，**它可能还是上一轮的**。看到 `errors: 0`
不等于你刚才那次改动通过了。判断"我的改动真的编译过了"要同时满足：

1. `build.log` 第一行的时间戳晚于你最后一次写文件；
2. `.lake/build/lib/lean/<你的文件>.olean` 的 mtime 晚于 `.lean` 的 mtime。

我就是漏了这一步，把一段根本不编译的代码提交了，两分钟后才发现。
**提交前跑一次 `ls -l --time-style=+%H:%M:%S <你的.lean> <对应的.olean> build.log`。**

**补充（后来遇到的假阴性）**：olean 比 .lean 旧**不一定**说明没编译过——
文件被 `touch`（内容不变）也会刷新 mtime，而 lake 按内容哈希判断，会直接
「Replayed」而不重建 olean。这时候看 build.log 里那一行
`Replayed RBM1D.Xxx` 以及它后面 warning 的**行号是否对得上你现在的文件**，
再加上末尾的 `errors: 0`，才是准的。

**补充（T222，2026-09-22）：`lake env lean <文件>` 不施加 library 的 `leanOptions`**（`autoImplicit` 等），
所以它会放过 `lake build` 拒收的文件——单文件 exit=0 而模块 exit=1，未定义的标识符靠 auto-bound 蒙过。
**新文件收工前必须额外跑一次 `lake build RBM1D.<模块名>`**，只看单文件编译不算数。

## 造轮子之前先查

证任何**通用工具引理**之前，先在仓库里搜一遍：

```
grep -rn "sum_pow\|zdist\|geom_sum\|exp_neg" RBM1D/ --include=*.lean
```

典型的通用工具：`ZMod L` 上的求和与重标、几何级数的界、`exp` 的初等不等式、
`Finset` 的重排。这些两边都会用到，而**按文件分工只能避免改同一个文件，
避免不了各证一遍**。已经发生过一次（旧记录见 `docs/archive/STATUS-2026-09-19_22.md`；只定向搜索）。

需要别的文件里已有的工具时：能 import 就 import；
若会造成不该有的依赖方向（比如 `Propagator/` 依赖 `Loop/`），
就把它下沉到 `RBM1D/Defs/` 里的共享文件。


## 关于 `sorry` 与红色的 build

硬性规则是**不提交 `sorry`**。在工作树里临时留一个 `sorry` 当脚手架、边填边编译，
是可以的——但它会让**共享的 build 变红**，另一边就没法用全局的 `errors:` 计数
判断自己的改动是否通过了。

所以：

* 留着 `sorry` 的时候，**提交前一定要清掉**；`RBM1D.lean` 末尾的 `#assert_rbm_axioms`
  会拦下漏网的（已经实际拦下过一次）。
* build 红着的时候，另一边判断自己那个文件是否编译通过，看
  `build.log` 里 `Built/Replayed RBM1D.<你的文件>` 那一行和它后面 warning 的行号，
  而不是末尾的 `errors:`。


## `watch.sh` 的一个竞态（实际踩过）

`watch.sh` 靠 `find ... -newer build.log` 决定要不要重编。如果你的改动**正好落在
一次编译进行中**，那次编译结束时写出的 `build.log` 会比你的文件更新，
于是 `find` 什么也找不到，**你的改动就一直不会被编译**——看上去像"编译很慢"，
其实是根本没排上。

症状：文件改了两分钟，`build.log` 的时间戳在动，但你那个文件的 olean 一直不变。

处理：`touch` 一下你改的文件（让它比 `build.log` 新），下一轮轮询就会捡起来。

## 并行度：自己扇出子 agent（2026-09-20，Jun 指定）

Jun 要 4 条并行车道，但他不在机器旁边、开不了新终端窗口。所以**已经在跑的 agent 自己用
Task/Agent 工具扇出子 agent**：保留手上这张单，另外从 `docs/TASKS.md` 挑一张待认领的，
**先改表格认领成「<你的名字> 子 agent」并提交**，再派子 agent 去做，把该单的「规格」段整段贴给它。

* **每人最多扇出 1 个**，全队合计不超过 4 条车道 —— 周额度是真会撞的
  （T108 那个 agent 就是在读文档阶段撞上限直接中断，工单原样退回）。
* 子 agent 守全部硬规则：只碰自己那个新文件、不留 `sorry`、不写 `axiom`、
  不改冻结签名、认领先提交、绿了就 commit + push。
* 子 agent 做完或中断，**由派出它的 agent 把表格改回真实状态**，不许留假的「进行中」。

挑单顺序：**T58（表示桥，卡主定理）> T110（最高风险）> T109 > T111 > T1**。
五张的规格都已写在 `docs/TASKS.md` 下半部分，接手不需要再做判断。

## 改了公共命名空间里的名字，收工前跑一次全量构建

单文件 `lake env lean` **查不出跨文件重名**。2026-09-20 就因此红过一次
（`condRow_zero` 在 `Gauss/IBP.lean` 与 `Gauss/FlucIter.lean` 各声明一次，
全量 `lake build` 拼 import 链时才炸）。

## ⭐⭐⭐ 最高优先级是 T149（2026-09-21 07:50，据 T147 审计）

**下一个空出来的 agent 去接 T149**：拆 `Steps` 包 + `0 ≤ s`——零新数学，解开总装的形状。其次 T132b/T146/T148 并行，再 T150/T151 接线。
矩路线的纪律照旧：**禁止**实例化 `SumZeroDyn.Hierarchy`；收口不用常系数 Grönwall；T58 的四项交付物已按 TASKS 顶部重新归属（T58 降为清理单）。
**协调者转派工单前先重读工单全文（含审查段）。**

## Cowork 心跳间隔（Jun 2026-09-21 永久规则）

**心跳间隔不得自行放慢到超过 20 分钟**（默认约 12 分钟），终端车道空闲时也一样。

## 可满足性纪律（Cowork 2026-09-21，T164 的教训）

**「编译通过 + 公理干净」不等于「有内容」**：若一条假设按字面不可满足，下游所有定理都是空真的，编译器发现不了。
T164 查出 `MinorGood`/`MinorGood'` 对**所有**样本点 `ω` 量化，在 `ω = 0`（`H = 0`、`G = −z⁻¹`）处就假，整支 `MinorDiffGain` 因此悬空。
规则：
1. **随机模型上的确定性不等式不许对所有 `ω` 量化**——一律带事件限制（`ω ∈ Good`、`HighProb`、`StochDom`、行条件概率）。
2. 新写任何「逐点」假设或结构字段时，**先在 `ω = 0` 与「大常数倍单位阵」两个样本点上心算一遍**；按字面为假就不要写。
3. 审计完成的单时，除 fiat（可被平凡满足）外，**还要查空真（不可满足）**——两者方向相反，都让定理失去内容。
4. **量词次序也会造成空真**（T188）：论文是「`p` 固定、`N → ∞`、`δ_N → 0`」，写成 `∀ p N, 8(2p)δ_N ≤ 1` 再配 `0 < δ_N` 就不可满足（固定 `N` 令 `p → ∞`）。渐近条件一律写成 `∀ p, ∀ᶠ N in atTop, …`。
5. **类/结构的正则性要求只要证明实际用到的阶数**（T145、T180、T187：`∀ M` 该是 `∀ M Hermitian`；时间 `C²` 可能只需 `C¹`）——要求多了，具体对象就放不进去。
6. 交付含新假设的定理时，**附一个可满足性见证**（一组显式参数使全部假设同时成立），仿 `EEDef.ee_hyp_consistent`。

## 外部输入的边界（Jun 2026-09-21，永久规则）

**全项目唯一允许的外部输入是 Theorem 2.6 Step 1 的 [51] 主定理**，必须逐字按其陈述写成假设、量化在所有满足其前提的模型上，**不得编造类似结论作为 input**；其余一切（包括 Theorem 2.6 的 Step 2/3 与 §7.2）都要自证。最终报告必须写明 Universality 部分用了外部 input。

**β = 2 的处理（Jun 2026-09-21 定为方案 (A)）**：[51]（`paper/1609.09011v3.pdf`）的 Theorem 2.2 字面只陈述 β = 1（`W` 是 GOE，比较对象 `p_GOE`），摘要声称「classical values of β … GOE/GUE」，正文无 β = 2 的编号定理。
我们的矩阵是复 Hermitian，所以**唯一的外部假设 = [51] Theorem 2.2 逐字、只把 (2.1) 的 GOE 与 (2.9) 的 `p_GOE` 换成 GUE**（前提 `(g,G)`-正则、时间窗、能量窗、结论形状一字不改）。
最终 Lean 报告必须写明这一点：「[51] 正文陈述 β = 1；此处使用其摘要所声称的 β = 2 版本」。
**Jun 2026-09-21 09:50 明确指示：「以 complex 形式的 Theorem 2.2 作为外部输入口」。****待更新**：Jun 正请 [51] 的作者在 arXiv 版里补上「complex 同理」（2026-09-21）；补上后外部假设改为逐字引用新版，报告措辞随之简化。
已核过的替代方案 (B)（[35] = Erdős–Péché–Ramírez–Schlein–Yau, CPAM 2010, `paper/0905.4176v2.pdf`, Prop. 3.3）**不可用**：旧论证见 `docs/archive/STATUS-2026-09-19_22.md`（定向搜索 Theorem 2.6 外部输入）。
