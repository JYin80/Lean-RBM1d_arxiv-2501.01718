# 给 Codex / ChatGPT 的 Lean 工单包（2026-09-22 08:10 UTC，Cowork 编）

> 用法（Jun）：每个 Codex 会话只做**一张**单。开场白贴：
> 「读 `AGENTS.md`，再读 `docs/CODEX-TICKETS.md` 的 §0–§2 与你那张单（§3），然后读 `docs/TASKS.md` 里同号那一行（完整规格）。只做这一张单。」
> 工单全文以 `docs/TASKS.md` 对应行为准；本文件补背景、依赖、文件归属与 Codex 专用的纪律。

## §0 硬规则（完整版见 `CLAUDE.md`，对所有 agent 适用）

1. 不留 `sorry`，不写 `axiom`；`#print axioms` 只允许 `propext` / `Classical.choice` / `Quot.sound`。
2. 不改冻结签名——要改就加带撇版 `Foo'`，旧版保留。只写本单「可写文件」栏里的文件，其余只读。
3. 收工前：`lake build RBM1D.<你的模块>` exit=0，**再跑全量** `lake build RBM1D` exit=0（单文件 `lake env lean` 不算数）。新模块要在 `RBM1D.lean` **点插入**一行 import。
4. **可满足性**：凡引入新假设，必须附**非退化**见证（显式参数使全部假设同时成立）。本项目已有 12 次「假设按字面不可满足 → 下游空真」。三条最常见的坑：
   * 对**所有 ω** 的确定性大小不等式（`H = 0` 或 `‖X‖` 很大时就破）——只许在好事件 `Good N` 上或以 `StochDom`/`HighProb` 形式出现；
   * 量词次序：论文是「`p` 先定、再 `∀ᶠ N`」，写成 `∀ p N` 就空；`∀ N` 写死（非 `∀ᶠ N`）在 `N = 0` 处常退化；
   * `∀ p : ℕ` 含 `p = 0`，被积函数会退化，单独一支处理。
5. 与论文字面不同的地方写进 `docs/paper-deltas.md`，`#` 栏写临时号 `T<单号><字母>`（数字号由调度分配）。**只依据** `paper/250520-YinJun-v2.pdf`（该 PDF 不在 git 里；工单都以公式编号给出）。
6. 「若按字面为假，停下报告，不要硬凑」；能编译成否定结论（`¬ Nonempty …`）最好。

## §1 Git 与文档纪律（Codex 专用）

* 只 `git add` 你自己的文件（Lean 文件、`RBM1D.lean` 的那一行、`docs/reports/Txxx.md`、你那一行 TASKS、paper-deltas 你那一条）。**永不** `git add -A` / `git add .`。
* 多个 Codex 在同一工作树并行时：提交前 `git status`，只提交自己的文件；遇到 `.git/index.lock` 等几秒再试。若用 Codex 云端（GitHub 分支/PR）：一单一分支，PR 标题写单号。**先请 Jun 把本地提交 push 上去**（本地领先 origin）。
* 改 `docs/TASKS.md` 只改**自己那一行的最后一栏（状态）**：按 `' | '` 切分并断言恰好 5 栏；单元格里不写 ASCII `|`（绝对值竖线写 `∣`，U+2223）；读到空文件就中止，写回后行数不能变少。
* 完成报告写 `docs/reports/Txxx.md`（格式照 `docs/reports/T271.md`）：文件、验收（build/axioms）、做了什么、仍是假设的逐条点名、见证、没做的。
* **不要整份读** `docs/STATUS.md` 之外的大文件；`docs/archive/` 只 `grep`。

## §2 背景速读：Step 2 的路线 (A′)（替代论文 (5.43) 的停时）

* 流实现为 `H_u = √u·X`（`X` 固定高斯带矩阵，只用一时刻律）；Itô/BDG 由「生成元恒等式 + Stein + 对矩的不等式」代替。
* 停时 (5.43) 换成**光滑前缀权重** `w = χ(J̃/Θ)^{2p}`，`J̃` = 早时刻网点上的 ℓ^q 软最大值（`q` 偶、`≍ log N`，`max ≤ J̃ ≤ e·max`）。权重是 `X` 的函数，Stein 在全测度上成立；代价是一个论文里没有的**交叉项**。
* 数学已由独立审稿确认：`docs/reports/V548-referee.md`（§0 结论、§2c 推导、§5 完整方案、§6 陈述 (S1)–(S8)）。注意其中「锐远场带 `W⁻¹`」是笔误（报告开头有更正）：锐远场就是 `Lemma57.ee_far_le` 的 `(J*)²` 形状。
* 裁定：`docs/STATUS.md` §2 的 D17（第一格从 `u = 0` 起、在 `{‖X‖ ≤ N}` 上取 Hölder-½ 时间模）、D18（审稿五处修补）、D19（**不要**走「全局 C² 中值不等式 / 确定性 `b₁`」路线，那条量级是 `p²θ^{2p}W^{2D}N`，闭合不了）。
* 已落地的砖（都在 `RBM1D/Gauss/`）：
  `APrimeGronwall.lean`（T264：(★) `hasDerivAt_integral_weighted`、(G) `weightedMinkowski_of_deriv_le`）·
  `APrimeDuhamel.lean` §8（T265：(S2) `sqrt_quadVar_softMax_le`、(S5) `sum_gvar_crossTerm_le`）·
  `EarlyQVRate.lean`（T262：(S3) `quadVar_lkFun_le_ee_sym`）· `EarlyQVRateEv.lean`（T267/T273：(S3) 概率版 `stochDom_quadVar_grid`）·
  `StepSideAPrime.lean`（T263：`phi_arith''`、`StepSide''`）· `APrimeTimeInt.lean`（T268/T273：时间积分，含 `s = 0` 无 log 分支）·
  `APrimePrior.lean`（T269：先验界传播、`qvBd`/`kappaBd`/`QBd` 闭式包络）· `APrimeOneStep.lean`（T270：单步矩界骨架）·
  `APrimeOneStepSharp.lean`（T272：第二遍骨架）· `APrimeModel.lean`（T271：模型层、`APrimeSlot`、合并总装 `thm221NoEL_of_inputs_mergedOnAll_aprime`）。

## §3 工单与依赖

**第一批（现在就能并行，文件两两不相交）**

| 单 | 内容一句话 | 可写文件 | 依赖 |
|---|---|---|---|
| T274 | `APrimeSlot` 在 `jSnorm` 处的确定性字段 + 好事件 + `init` 去留 + 迁移规范总装 | `Gauss/APrimeSlotFields.lean`、`Flow/Step345Producer.lean` | 无 |
| T275 | 模型层 Duhamel 展开：(G) 分析包 + `hBbd` | `Gauss/APrimeDuhamelModel.lean` | 无 |
| T276 | 槽算术 `hfit`/`hbudget`（`p`-常数由 `∀ᶠ N` 吸收） | `Gauss/APrimeSlotArith.lean` | 无 |
| T277 | (5.42) 的 `U`-传播：`Q_u` 的端点界 | `Gauss/APrimeQVEndpoint.lean` | 无 |
| T278 | 第 4 槽 Lemma 5.14：`hnum` 渐近卸掉 | `Gauss/Lemma514QAssembly.lean`、`Gauss/Lemma514NonAlt.lean` | 无 |
| T279 | 第 5 槽 `Eq45FlowInputs` 的网格数据 `hΩ`/`hHol`/`hfix` | `Gauss/Eq45FlowGrid.lean` | 无 |

⚠ 08:09 时 T274、T275、T276 已由 Claude Code 子 agent 开工（未提交的文件 `APrimeSlotFields.lean`、`APrimeDuhamelModel.lean` 在工作树里）。若改交 Codex：**先让 Jun 决定**是等它们交完，还是停掉它们、把未提交文件留作 Codex 的起点（Codex 开工前 `git status` 看一眼，别覆盖）。

**第二批（第一批落地后）**

| 单 | 内容 | 依赖 |
|---|---|---|
| T280 | 第一遍收口：组装 `APrimeSlot` 在 `jSnorm` 处的完整见证（T274 字段 + T275/T276/T277 交割 `weightedMoment`），合并总装第 2 槽由定理产出；跑探针确认 `#check` 的假设表 | T274–T277 |
| T281 | 第二遍的模型层实例化（照 T271+T274–T277 的模板，目标 `weightedMoment_of_stepBoundSharp''`，归一化 `jSnorm2`，先验界 = 第一遍结论） | T280 |
| T282 | 第 3 槽（`Ξ^{(L−K)}_{·,2}` 的 `CutHypEvOn`）与 (5.48) 的 `moment` 字段：同一个 `WeightedMoment` 机制各实例化一次（(5.48) 的权重对**全部**早时刻网点与块对取） | T280 |
| T283 | T159 端到端核对：按 1→2→3→4/5→6 串出 `Thm221` 与 Lemmas 2.18–2.20，全链可满足性审计 | T278–T282 |

第二批的规格届时由调度（Cowork 或接手的协调者，见 `docs/HANDOVER.md`）写进 `docs/TASKS.md`。
