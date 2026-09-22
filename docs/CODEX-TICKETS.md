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
| T274（Claude Code） | `APrimeSlot` 在 `jSnorm` 处的确定性字段 + 好事件 + `init` 去留 + 迁移规范总装 | `Gauss/APrimeSlotFields.lean`、`Flow/Step345Producer.lean` | 无 |
| T275（Claude Code） | 模型层 Duhamel 展开：(G) 分析包 + `hBbd` | `Gauss/APrimeDuhamelModel.lean` | 无 |
| T276（Claude Code） | 槽算术 `hfit`/`hbudget`（`p`-常数由 `∀ᶠ N` 吸收） | `Gauss/APrimeSlotArith.lean` | 无 |
| T277 | (5.42) 的 `U`-传播：`Q_u` 的端点界 | `Gauss/APrimeQVEndpoint.lean` | 无 |
| T278 | 第 4 槽 Lemma 5.14：`hnum` 渐近卸掉 | `Gauss/Lemma514QAssembly.lean`、`Gauss/Lemma514NonAlt.lean` | 无 |
| T279 | 第 5 槽 `Eq45FlowInputs` 的网格数据 `hΩ`/`hHol`/`hfix` | `Gauss/Eq45FlowGrid.lean` | 无 |

⚠ **分工（Jun 08:12 定）**：T274、T275、T276 **由 Claude Code 做完**（08:09 已开工）；**Codex 只接 T277、T278、T279**。Codex 不要碰 `APrimeSlotFields.lean`、`APrimeDuhamelModel.lean`、`APrimeSlotArith.lean`、`Flow/Step345Producer.lean`。

**第二批（第一批落地后）**

| 单 | 内容 | 依赖 |
|---|---|---|
| T280 | 第一遍收口：组装 `APrimeSlot` 在 `jSnorm` 处的完整见证（T274 字段 + T275/T276/T277 交割 `weightedMoment`），合并总装第 2 槽由定理产出；跑探针确认 `#check` 的假设表 | T274–T277 |
| T281 | 第二遍的模型层实例化（照 T271+T274–T277 的模板，目标 `weightedMoment_of_stepBoundSharp''`，归一化 `jSnorm2`，先验界 = 第一遍结论） | T280 |
| T282 | 第 3 槽（`Ξ^{(L−K)}_{·,2}` 的 `CutHypEvOn`）与 (5.48) 的 `moment` 字段：同一个 `WeightedMoment` 机制各实例化一次（(5.48) 的权重对**全部**早时刻网点与块对取） | T280 |
| T283 | T159 端到端核对：按 1→2→3→4/5→6 串出 `Thm221` 与 Lemmas 2.18–2.20，全链可满足性审计 | T278–T282 |

第二批的规格届时由调度（Cowork 或接手的协调者，见 `docs/HANDOVER.md`）写进 `docs/TASKS.md`。

## §4 T278 改向（Cowork 08:30，读 T278 报告后）

T278 编译出的否定结论是对的，但它否定的是**过强的 `hnum` 形状**，不是 Lemma 5.14：

* 目标 `Rhs514QAt H c v`（`Gauss/Lemma514QAssembly.lean:132`）本身是 `∀ ε > 0, ∀ p ≥ 1, ∃ C > 0, ∀ᶠ N, 左端 ≤ C·N^{ε/2}·c N·scale^{−(n+2)}`——**有常数 `C` 与 `N^{ε/2}` 的余量**，正是论文 `≺` 的形状。
* 而生产者 `rhs514QAt_of_kernel_inputs'`（:1050）的 `hnum`（:1177）是**无余量的精确不等式**，且 `Kd`、`ζ`、`δ'` 等核输入在 `ε` **之前**就固定了。于是 `cKer716 (n+2) (4Kd) > 1` 这个常数、以及 `Kd = W^τ` 时它的 `W^{O(τ)}` 增长，都没有地方吸收——这就是 `not_hnum_*` 编译出来的东西。
* **修法（带撇新生产者，旧签名不动）**：`rhs514QAt_of_kernel_inputs''`，把**整个核输入包**（`Kd, ζ, δ', Msz, Pb, esz` 及 `hEnv*`、`hδ'` 等）放到 `ε` **之后**量化：`∀ ε > 0, ∃ 核输入包 (Kd_ε = W^{τ(ε)}，τ(ε) 取得足够小), ∃ C₀ > 0, ∀ᶠ N, 旧 hnum 的左端 ≤ C₀·N^{ε/2}·c N·scale^{−(n+2)}`。证明里把 `C₀` 乘进 `Rhs514QAt` 的 `C`。`cKer716 m (4Kd)` 关于 `Kd` 是多项式，`Kd = W^{τ}`、`W ≤ N` 时 `≤ N^{Cτ} ≤ N^{ε/4}`；`(1 + 6(v−s)) ≤ 7` 进 `C₀`。快衰减输入（(5.74)、Lemma 5.9）本来就对**每个**固定的小 `τ` 成立，所以按 `ε` 取 `τ` 是合法的。Case 1 的 `rhsNonAltAt_of_kernel_inputs'` 同法出 `''` 版。
* 然后在 `lemma514_of_momentDuhamelQ` 的 `hrhs`/`hrhsNA` 上接新生产者，交割第 4 槽。
* **验收**：`not_hnum_*` 保留（记录旧形状为何不行）；新 `hnum''` 在 p.24 网格首格与 `R > 1` 的窗口上各有非退化见证（`Φ > 0`、窗口长度 > 0、`Kd ≥ 1`）；`#check` 显示合并总装第 4 槽的假设只剩已有生产者的输入。若按新形状仍证不出，**精确写明卡在哪个因子**（例如 `hMψ` 的包络 `Phi` 与控制 `c = Λ^{1/2}+Φ` 之间是否真差一个 `N` 的正幂），停下报 Cowork。

## §5 T277 续做（Cowork 08:33，读 T277 部分报告后）

T277 的两个发现都对：(i) 在求和里逐点用对角的 `ee_le_EEpath_sym` 不行（`b′ ≠ b` 的非对角项）；(ii) `APrimeModel.qvRate` 是**未演化**的 `quadVar(lkFun)`，而 (G) 的二次变差项要的是 `Ψ_u = U_{u,t}∘(L−K)_u / T_t` 的二次变差。**绕开非对角项的办法：先 Minkowski，再用对角界**——

* `√QV(Ψ_u)(a) = √(Σ_α σ_α² ∣Σ_b U_{u,t}(a,b)·∂_α lk_{u,b}∣²) / T_t(a) ≤ Σ_b ∣U_{u,t}(a,b)∣·√QV(lk_{u,b}) / T_t(a)`。这一步就是 T265 已证的 `RBM.Gauss.sqrt_wsum_sum_le`（`Gauss/APrimeDuhamel.lean:725`，加权 ℓ² 的 Minkowski）。**只用到对角的 `QV(lk_{u,b})`**。
* 对角项用 T262 的 `EarlyQVRate.quadVar_lkFun_le_ee_sym`（(5.36)@`u`，`t = u`）：`√QV(lk_{u,b}) ≤ T_{u,D}(b)·√rate_u(b)`，近场 `η_u^{−1}r_u^5·1(∣b₁−b₂∣ ≤ 4ℓ*_u)`，远场 `Lemma57.ee_far_le` 的锐 `(J*)²` 形状。
* 剩下的是核与尾函数的卷积 `Σ_b ∣U_{u,t}(a,b)∣·T_{u,D}(b) ≲ (η_u/η_t)²·T_{t,D}(a)`（外加近场指示从 `4ℓ*_u` 放到 `6ℓ*_t`）——这正是论文由 (5.35)/(5.36) 推 (5.41)/(5.42) 用的那一步，仓库里 (5.40)/(5.41) 的 `U`-传播已有同型引理（在 `Hierarchy/Step2.lean`、`Hierarchy/Step2MomentStep.lean`、`Gauss/MomentDuhamelRhs.lean` 里 grep `(5.41)`、`Uker`、`tailT`）。
* 于是得到端点 (5.42)：`QV(Ψ_u)(a) ≲ (η_u/η_t)⁴·[η_u^{−1}r_u^5·1(近) + 远场]`，比原来的有限和少掉那个 `L⁴`。
* **消费端**：请在报告里写明 `APrimeModel.qvRate` 应改为（或另立）演化版 `qvRateEvolved := quadVar(Ψ_u)`；**T275（Claude Code）在认同 (G) 的二次变差项时用的就该是演化版**，T269 的 `div_le_QBd_of_le_qvShape` 的前提由你这条供给。`APrimeModel.lean` 不在你的可写范围，只写明、不改。
* 验收不变：(5.42) 形状的逐点界由定理供给、无 `∀ω` size 假设、非退化见证。

## §6 T279 续做（Cowork 08:42，读 T279 报告后；Cowork 已亲自核对接口）

T279 的 `no_joint_grid_scales` 是真发现（**空真第 13 例**）：`Gauss/Eq45FlowInputs.lean` 里同一个 `δ` 身兼两职——
* **好事件阈值**：`goodSetFlow d E s t δ`（:278）= 每个 `u` 上 `GoodEvent (green …) (mE E) (δ N)`，由局部律供给，要求 `δ ≥ N^τ·Ψ ≥ N^τ·W^{−1/2}`；
* **时间网距**：`flucRowFlow_of_gain'`/`flucBlkFlow_of_gain'`（:1336/:1368）的 `hfine : 4η_t^{−3}N³·δ^{1/2} ≤ 1` 与 `hδnet`，要求 `δ ≤ N^{−6}`。
两者不可能同时成立。

**修法（本单可写范围扩到 `Gauss/Eq45FlowInputs.lean`，只追加带撇版，旧签名一字不动）**：
1. 第 0 步：在 `ibpFlow_of_unifDom`（:553）、`flucRowFlow_of_gain'`、`flucBlkFlow_of_gain'` 及其上游（`flowNetEvent`（:407）、网格引理 `stochDom_timeIcc_of_unifDom*`、`hHol*` 的生产者 `holIBP/holRow/holBlk_of_inputs`）里，把 `δ` 的每一次出现归类为「阈值」或「网距」。
2. 出 `''` 版，参数拆成 `δ`（阈值，进 `goodSetFlow`/`GoodEvent`）与 `μ`（网距，进 `hfine`/`hδnet`/网点间距）；`hfine''` 只约束 `μ`。
3. 联合可满足性见证：`δ_N = N^{τ}Ψ_N`（局部律能给的量级）、`μ_N = N^{−C}`（`C` 大），在 p.24 首格与 `R > 1` 窗口上**同时**满足全部前提，并编译 `¬`（旧的同参数版）与 `✓`（新版）两条对照。
4. 用新版接第 5 槽：`Eq45FlowInputs` 在合并总装里只剩已有生产者的输入。
若第 0 步发现某处 `δ` 两种角色真的不可拆（证明本质上要求阈值 ≤ 网距的某个幂），**停下报 Cowork**，写明那一步。

## §7 T278 第三步（Cowork 08:47，读 T278 第二份报告后）

T278 已交：`rhs514QAt_of_kernel_inputs''` / `rhsNonAltAt_of_kernel_inputs''`（`η` 在核参数之前）、`*_of_scaled_family`、`lemma514_of_momentDuhamelQ_of_scaled_families`、系数指数引理 `cKer716_four_le_rpow` / `cKer716Short_le_rpow`。第 4 槽现在精确等于「两条 scaled family 在高斯模型上实例化」。

**下一步先做第 0 步只读，再动手**（Cowork 没有逐条核过这些包络，所以不写成「接线」）：
1. 对 `''` 生产者的每个输入——`hEnvI/F/C/D/E`、`hMψ`、`hMψE`、`ζ`、`δ'`（`errBudget`）、`cE`、`Msz`、`Pb`、`esz`——列出仓库里已有的**模型层**供给者。先看 T236（`Gauss/Lemma514NonAlt.lean`，报告 `docs/reports/T236.md`：Case 1 的 `hrhsNA` 当时就有生产者和网格见证，常数不含 `N`/`W`/`τ′`/`k`）、T237/T246/T253/T254（Q 侧的事件限制版与 `exists_uniform_errBudget`）、`Gauss/FastDecayFlow.lean`。
2. 对每个加性误差项（`A_N^m·(errKer716_m + cE_N)`、`A_N^{2m}·(errKer716_{2m} + cE_N)`）写出它的 `W^{−D}` / 指数小因子与多项式因子（`A_N ≤ N^{C}`、`L_N ≤ N`、`(L_N)^k δ_N`）。`δ_N` 来自快衰减，对**每个** `D` 成立，所以 `D` 可在 `m, η` 之后取大——若某项的小因子不是 `W^{−D}` 型，停下报告。
3. 对 `Phi ≲ c = Λ^{1/2} + Φ` 与 `√PhiE ≲ c`：写明 `ψ`/`ψE` 的矩由 `Lemma514Premises` 的哪几条推出。**这一步是 Lemma 5.14 本身的数学（(5.93)–(5.103)）**，若仓库里没有现成推导，交一页只读分析，Cowork 再开单。
第 0 步交报告后再实现。可写范围不变（`Lemma514QAssembly.lean`、`Lemma514NonAlt.lean`）。

## §8 T278 第四步：包络层（Cowork 09:00，读 T278 第 0 步清单后；Cowork 已核对 `Gauss/Envelope.lean` 与 `Gauss/Domination.lean` 的签名）

T278 的清单准确：卡在 `ζ_N` 与 `ψ/ψE` 的矩包络。**这两处可以一起解开，不需要新的核估计**：

1. **把 `ψ` 取成被界的量本身，`ζ ≡ 0`。** 对 `hEnvI/F/C/D` 取 `ψ N u q ω := scale_u^m · max_b ‖对应张量_b‖`（五行可取各自的 `ψ` 再相加，或取最大者），`hEnvE` 同理取 `ψE := scale_u^{2m}·max_c ‖eeFun_c‖`。于是五行「对所有 ω」的包络**按定义成立**（这不是空真：左端就是右端的一个分量）。清单里的 `ζ` 缺口与账本里 `K_N^{2r}ζ_N` 那一项随之消失。
2. **矩包络 `hMψ`/`hMψE` = 反向桥。** 仓库已有 `RBM.Gauss.momentDom_of_stochDom_of_nonneg`（`Gauss/Envelope.lean:209`）：非负、可测、各阶可积、**确定性多项式包络** `Y ≤ Env_N ≤ N^{Kenv}`、`Φ ≥ N^{−B}`、再加 `StochDom Y Φ`，就给出 `MomentDom`（`Gauss/Domination.lean:100`：`∀ ε ∀ p ∃ C ∀ᶠ N ∀ u, ∫∣Y∣^{2p} ≤ C·N^{εp}·Φ^{2p}`），**正是** `hMψ` 的形状。参数集 `U N` 取 `TimeIcc s v N × LoopData`，所以对 `u`、`q` 一致。
   * 确定性包络：`‖G‖ ≤ η_u^{−1}`、`scale_u ≤ N`、`L_N ≤ N` ⇒ `ψ ≤ N^{Kenv}`（`Gauss.scale_le_mul`、`LKDecayQuant.eventually_L_le`，清单里已点名）。
   * `StochDom ψ Phi`：由 `Lemma514Premises`（`Lemma514Moment.lean:388`）——第 2、4 条管 `lkT`（`hEnvI`、`hEnvC/D` 经 `Qop`/`Psum`/`ϑ` 的确定性算子界），第 3 条管漂移（`hEnvF`，经 `MomentDuhamel.Hyp.F_unique_flow` 与 `DriftDef` 把 `H.F` 写成两条低阶环之积除以 `flowA`，T236 已指明这条路），第 1 条经 `EEDef.norm_eeFun_le_W_sum` 管 `ψE`。`Phi := c = √Λ + Φ`（Case 1 取 `max(…,1)`）。
3. **加性误差账**：`ζ ≡ 0` 后只剩 `δ'`（`errBudget`，含 `L_N^{2k}δ_N`）与 `cE`。`δ_N` 取两个衰减事件（`lkGood` 的 `N^{τ₁−D}`、G-loop 的 `W·m·L·N^{−D}`）的较大者，`D` 在 `m, η` 之后取；`Msz/Pb/esz` 用同一个确定性多项式包络；`cE ≤ N^{−D_e}` 由 `eventually_env_mul_lkGood_le`（`Env` 多项式）。`R_N` 只在 p.24 网格相邻格上用（那里是 `W` 的幂），在一般终点 `v` 上不要求一致界——把终点限制写进实例化的前提。
4. **验收**：两条 scaled family 在高斯模型上由 `Lemma514Premises` 实例化，`lemma514_of_momentDuhamelQ_of_scaled_families` 交出 `Step3.Lemma514`，合并总装第 4 槽只剩已有生产者的输入；见证在 p.24 首格与 `R > 1` 窗口上、`Phi > 0`。若第 2 步的某条 `StochDom` 由 `Lemma514Premises` 推不出（例如算子界丢了 `scale` 的幂），**停下写明那一行**。

## §9 T280：第一遍收口的六个接口决定（Cowork 09:05，D20；读 `docs/reports/T280-step0.md` 后）

T280 第 0 步审计准确：`APrimeSlot'` 的完整见证还导不出，缺口不在数学（审稿 V548 §2a/§5 都有），而在接口。逐条裁定：

1. ⚠ **（§18 D22：对完整 `jSnorm` 走 `weightedMoment_of_stepBound_mono` 这条作废，改走逐坐标 → 族 → `weightedMoment_of_widened_family`）** **权重 `W` 没有 `p` 参数，而估计要 `softW^{2p}`** → 接口权重取 `p` 无关的 `W := χ(J̃/Θ′)`；估计时对每个 `p` 用 `W_p := χ(J̃/(2Θ′))^{2p}`，逐点 `W ≤ W_p`（`J̃ ≤ 2Θ′` 处 `χ(J̃/(2Θ′)) = 1`）。新增引理 `weightedMoment_of_stepBound_mono`：若对每个 `p` 有 `W ≤ W_p` 且 `Hstep` 对 `W_p` 成立，则 `WeightedMoment` 对 `W` 成立。
2. **`hdom`：`jSnorm` 是 `1 + max_a`，不被单个坐标 `Y_a` 支配** → 用族版：`∣cutTrunc θ J∣^{2p} ≤ 2^{2p−1}(1 + Σ_a ∣Ψ^{(a)}_{u_k}∣^{2p})`（端点处 `U_{t,t} = id`，`Ψ^{(a)}_t = lk_{t,a}/(T R⁴)`）；对每个 `a` 跑一次 (G)，`a` 的求和付 `L² ≤ N²`，`p ≥ 4/δ` 时被 `N^{δp/2}` 吸收，小 `p` 用 Lyapunov（审稿 §5 第 4 步）。
3. **数值 `hinit`**（加权 `2p` 阶矩的初值）→ 反向桥 `Gauss.momentDom_of_stochDom_of_nonneg` 作用在 (5.39)@`s` 上：`Ψ^{(a)}_s = U_{s,t}(L−K)_s/T_t` 的 `≺` 界由 `BoundsCore X E s`（p.24 归纳在每一格都给）+ Lemma 7.1 给出，确定性包络 `‖G‖ ≤ η⁻¹`；`W ≤ 1` 故加权 ≤ 不加权。**不循环**：只用左端点的 `BoundsCore`，不用 `W_dom`。
4. ⚠ **（§17 D21-2：其中「交 `EarlyQVRateEv` 的 (S3) 事件」撤回，`J` 改由 T280f 供给）** **`Good` 固定 vs (S3)/Step 1 事件依赖 `δ`** 与 5. **`hwDoff`** → `APrimeSlot'.Good` **只取** `{‖X‖ ≤ N}`（只为时间模）。(S3)、Step 1 等事件 `E_{δ,p,N}` **只在 `Hstep` 的证明内部**出现，而且**在范数里**拆坏事件：`‖Z‖_{W,2p} ≤ ‖Z·1_E‖_{W,2p} + ‖Z·1_{Eᶜ}‖_{W,2p}`，后者 ≤ 确定性多项式包络 × `P(Eᶜ)^{1/(2p)} ≤ N^{−1}`（`D′` 按 `p` 取）。交叉项用 T265 的**逐点、无事件** (S5) `sum_gvar_crossTerm_le`，事件只在界 `‖√(Q·κ̂)‖_{2p}` 时进来——**不需要 `hwDoff`**，T275 的 `crossPart_le_of_S5` 那条路不走。
6. **前缀 vs 全网**（T269 的传播对 `netFinset`）→ 出前缀版：`v ∈ [s, u_k]` 由前缀点 `u_j`（`j < k`）经时间模覆盖（`[u_{k−1}, u_k]` 用左端 `u_{k−1}`）。**`W_dom` 对所有 `k`、所有 `N`**：定义 `W δ N k := if k ≤ cutNetTop ∧ N ≥ N₀ then χ(J̃/Θ′) else 1`，界外 `W = 1` 平凡满足，`WeightedMoment` 本来只在 `k ≤ cutNetTop`、`∀ᶠ N` 上要求。
7. **T276 的 `≺ 1` 前提的实际指数**（T280 点名 `QBd` 含 `Λ³ = N^{6δ}`）→ 要核：远场 `N^{6δ}R^{12}/A_t`，由 (2.72)+论文改动第 16 条 `A_t ≥ N^{c}R^{30}` 得 `≤ N^{6δ−c}R^{−18}`，需 `6δ < c`（T263 是 `5δ < c`）——把 `δ₀` 收紧到 `c/7` 并逐项核其余各项；若某项需要 `δ` 以外的余量，停下报。

**拆单（都是新文件，旧签名不动）**：
* **T280a**（Codex）：第 1、6 条——`weightedMoment_of_stepBound_mono`、前缀版传播、分段权重 `W` 及其四个字段。文件 `Gauss/APrimeWeight.lean`。
* **T280b**（Codex）：第 2、3 条——族版 `hdom` 与 `max_a` 求和、Lyapunov 小 `p`；`hinit` 的反向桥。文件 `Gauss/APrimeInit.lean`。
* **T280c**（Codex）：第 4、5 条——范数内坏事件拆分的通用引理 + `hdrift`/`hqv`/交叉项三处用法（等 T277 的演化版 (5.42)）。文件 `Gauss/APrimeBadSplit.lean`。
* **T280d**（Codex，纯算术）：第 7 条。文件 `Gauss/APrimeExponents.lean`。
* **T280e**（最后，谁有空谁做）：把 a–d + T274–T277 组装成 `APrimeSlot'` 在 `jSnorm` 处的见证，第 2 槽由定理产出。
每单：先 `#check` 核对所用声明的签名；若发现本节某条裁定在 Lean 里不成立，编译成否定结论并停下。

## §10 T278 第五步：包络对时间 `u` 带权（Cowork 09:08，读 T278 §8 报告后）

T278 精确定位了：漂移行与 `E⊗E` 行的 `≺` 控制都带一个 **`η_u^{−1}`**（`DriftBound.norm_driftF_le`、`SumZeroDyn.hgood_QF`、`Gauss.stochDom_norm_eeFun_det`）。这是论文本来就有的——(5.40)–(5.42) 的被积函数都是「`η_u^{−1}` × …」，论文**对 `u` 积分**：在 p.24 相邻格上 `∫_s^v η_u^{−1} du = log((1−s)/(1−v)) / Im m = τ′·log W / Im m`，只是对数，被 `N^ε` 吸收。**卡住的是接口**：现在的 `''` 生产者用 `(v−s)·sup_u` 处理时间积分，而 `(v−s)·sup_u η_u^{−1} = (1−s)/(1−v) − 1 ≈ W^{τ′}`，是正幂。

**修法（带撇 `'''`，旧签名不动）**：
* `hMψ`/`hMψE` 的包络允许依赖 `u`：`momNorm(ψ N u q) ≤ C·N^{ε/2}·ρ_N(u)·Phi N q`，`ρ_N(u) := (etaT E u)^{−1}`（或一般的非负可积权 `ρ`）。
* `hnum` 里漂移/交换子/`ϑ̇` 三项的 `(v−s)` 换成 `∫_s^v ρ_N(u) du`，`E⊗E` 项的 `√((v−s)·…)` 换成 `√(∫_s^v ρ_N(u) du · …)`。先核对生产者内部：它逐点把被积函数界成「核系数 × `scale_v^{−m}` × 包络」再对 `u` 积分，所以 `ρ(u)` 可以原样留在积分里——**若核系数本身也依赖 `u` 且与 `ρ` 不可分，停下报**。
* 积分算术：`∫_s^v (etaT E u)^{−1} du = log((1−s)/(1−v)) / Im(mE E) ≤ C·log N`，因为 `1−v ≥ N^{−1+τ}`（论文改动第 16 条，Theorem 2.21 的区间条件，仓库里已在 `Cond272Reg`/窗口条件中）。`log N ≤ N^{η/4}` 最终成立。
* 于是漂移行用 `SumZeroDyn.xiRhs_stochDom`（控制 `(2n+3)Φ_N`）+ `DriftBound.hdom_of_stochDom_driftF`，`E⊗E` 行用 `Gauss.stochDom_norm_eeFun_det`（控制 `Λ_N`），`ψ := A_u^m·max‖·‖·η_u`（把 `η_u^{−1}` 移到 `ρ` 里）再走 `momentDom_of_stochDom_of_nonneg`。
* **初值行** `lkT` 在 `s`：如你所说由外层的 `BoundsCore.LmK m`（`Gauss.hinit_of_stochDom`）供给，不从 `Lemma514Premises` 来——在 `'''` 生产者里把它作为独立输入，由总装交割。
* **验收**不变；见证在 p.24 相邻格（`1−v = W^{−(k+1)τ′}`）上，确认 `∫ρ` 是 `O(log W)` 而不是 `W^{τ′}`。

## §11 更正 §9 的第 7、2 条（Cowork 09:14，读 T280d、T280b 后）

两单编译出的否定结论都对，§9 的两条裁定错了。更正如下（这次都核对了签名与算术）：

**§9(7) 更正（T280d）**：`Cond272Reg` 给的是两条**分开**的下界 `R³⁰ ≤ A_t` 与 `N^c ≤ A_t`，不是乘积，`N^{6δ}R^{12}/A_t ≤ N^{6δ−c}R^{−18}` 这一步不成立（`not_eventually_product_scale_of_separate`）。正确做法是**插值**：`A = A^{2/5}·A^{3/5} ≥ (R³⁰)^{2/5}(N^c)^{3/5} = R^{12}·N^{3c/5}`。仓库已有这条引理：**`RBM.Cond272Reg.margin`**（`Flow/Thm221Bare.lean`，「在每个指数 `b < 30` 给出增益 `N^{c(1−b/30)}`」），取 `b = 12`。于是远场项 `N^{6δ}R^{12}/A_t ≤ N^{6δ − 3c/5}`，需 **`δ < c/10`**。其余各项同法：每项 `N^{aδ}R^{b}/A` 用 `margin` 在指数 `b` 处取增益 `N^{c(1−b/30)}`，要求 `aδ < c(1−b/30)`；取 `δ₀` 为各项约束的最小值。

**§9(2) 更正（T280b）**：`oneStep_of_slots` 的每坐标界是 `((cStep′+1)x²)^{2p} = C·N^{δp/2}`，已经用掉 `WeightedMoment` 的全部指数，`L²` 无处可放（`no_family_absorption_slot`）。问题出在 T276 的**槽取值**：`slotXi = slotKappa = x/2`（`APrimeSlotArith.lean:78,97`）是约束 `Ξ ≤ x`、`κ ≤ x`（`StepSide''`）的上限，不是真实大小。真实大小：`Ξ ≺ 1`，`κ ≲ N^{−2δ}(log N)^{1/2}`（审稿 §2c.6）。**改取 `Ξ = κ = x^{1/4}`**（仍满足 `StepSide''`，只是更小）。代入 `stepRhs''`（`StepSideAPrime.lean:215`）除以 `R⁴`：`xR²Ξ/R⁴ ≤ x^{5/4}`，`xR²κ/R⁴ ≤ x^{5/4}`，漂移 `Ξ·(…)/R⁴ ≲ Ξ·x/m = x^{5/4}/m`（`A_ge`、`ε_le`、`q ≤ R²` 使括号 `≲ x`），`x(R²+1)/R⁴ ≤ 2x`。故每坐标 `≤ C·x^{5/4}`，`2p` 次方 `= C·N^{5δp/16}`；目标 `N^{δp/2} = N^{8δp/16}`，余量 `N^{3δp/16} ≥ N²` 当 `p ≥ 32/(3δ)`，小 `p` 用 Lyapunov（`W ≤ 1`，`E[W·X^p] ≤ (E[W·X^{p′}])^{p/p′}`）。T276 的两条吸收余量随之变成 `slotDrift ≥ x^{5/4}/(4m)`、`slotTail² ≳ x^{5/2}/R⁴`，`η` 取 `< 5δ/32` 仍够。输入侧要多证 `Ξ_true ≤ x^{1/4} = N^{δ/32}`、`κ_true ≤ N^{δ/32}`（都由 `≺` 在 `τ = δ/32` 取）。

**续做**：T280d 按上面第一段做（用 `Cond272Reg.margin`），逐项列出 `(a, b)` 与所需 `δ₀`；T280b 按第二段先出 `slotXi′ = slotKappa′ = x^{1/4}` 的槽与 `stepRhs''` 的 `x^{5/4}` 上界（可在 `APrimeInit.lean` 里新写，不改 T276 的文件），再做族求和与 Lyapunov、`hinit`。**若 `stepRhs''` 里有某项在 `Ξ, κ ≤ x^{1/4}` 下仍 ≥ `x²`，编译出来并停下**。

## §12 T280e 重跑的前提与清单（Cowork 09:24）

T280e 停下的两条（`first_pass_D20_obstructions`）正是 §9(2)、§9(7)，已在 §11 更正；它与 §11 并行开跑，没看到更正。**等下面三件落地后再重跑 T280e**：
1. **T280b 按 §11 第二段**：槽 `Ξ = κ = x^{1/4}`、每坐标 `≤ C·x^{5/4}`、族求和（`p ≥ 32/(3δ)`）+ Lyapunov、`hinit` 反向桥。
2. **T280d 按 §11 第一段**：`Cond272Reg.margin` 插值，逐项 `(a,b)` 与 `δ₀`。
3. **T277**：演化版 (5.42) 的 `EvolvedQVBound`（§5 的 Minkowski 路线）。

重跑时的组装清单（取自 T280a/T280c 报告）：
* 权重：T280a 的 `piecewiseW`（`jSnorm_piecewiseW_fields` 给四个字段）+ `weightedMoment_of_stepBound_mono`；`k = 0` 那一格走初值估计（无前缀）。
* 坏事件：T280c 的 `drift_norm_le_of_event`、`evolved_qv_norm_le_of_event`、`crossPart_le_of_S5_event` → `crossPart_budget_of_event_bound`；每个 `(δ,p,N)` 自选事件 `E`，`HighProb` 指数取 `> 2p(a+1)`（`a` = 包络的多项式次数）。
* 仍要新证的小件（T280c 点名）：前缀权重梯度率 `hK` 的具体界与归一化（接 T265 (S5)）；漂移、演化 QV、交叉绝对和的全局多项式包络；`hYm/hQm/hYi/hQi/hProdInt` 可积性。可在 `APrimeAssembly.lean` 里补。
* 链：`aprimeHypOn_jSnorm_event`（T274）+ 权重 → `aprimeHypOn_of_stepBound''` → `APrimeSlot'` → `jsNormDom_of_aprimeSlot'` → `thm221NoEL_of_inputs_mergedOnAll_aprime'`。

## §13 T277 已交（Cowork 09:28）——T280e 清单补一项

T277 交出 `APrimeQVEndpoint.sqrt_evolvedQV_le_endpoint`（演化版 (5.42)，逐 `(u,ω)`，端点指示 `6ℓ*_v`、`(η_u/η_v)⁴`、锐 `(J*)²` 远场 + `(J*)³` 项 + `256e³W^{−D}T` 泄漏；确定性条件 `A_u ≥ 1`、`log W ≥ (4D)²`，见证 `endpoint_scale_witness`），并由 `quadVar_ukerObsT_eq_evolved_loopObs` 认同为 T275 `qvRateEvolved` 所界之量。
**T280e 重跑时加一步**：由它在事件 `E`（Step 1 事件，逐点前提在那里成立）上交割 T275 的 `EvolvedQVBound … E … Qev`，`Qev` 取端点界的平方；再按 T269 的 `qvShape` 归一化（`(T_t R⁴)²`）出 `QBd` 形的预算——T269 的 `div_le_QBd_of_le_qvShape` 是对未演化率写的，**另写演化版**，不要硬套。两个确定性条件 `A_u ≥ 1`、`log W ≥ (4D)²` 由 (2.72)/`Cond272Reg` 与 `D ≥ 60`、`W ≥ N^{1/2}` 最终成立给出。

## §14 T280d、T278 的下一步（Cowork 09:35）

**T280d（`δ₀ = c/11` 已证，四行 margin 全过）→ 余下的 `QBd` 各项有现成供给者，出 `4R⁴G ≺ 1` 与 `fitLhs ≺ 1`**：
* 近场 `cNear2·r⁵` 项：**T273 已证** `integral_inv_sqrt_mul_sqrt_kappa_qHatNear_le` / `qHatNear` 的积分界 `∫_s^t Q̂^{near} ≤ (Im m)⁻¹(η_t/η_s)⁴`（`APrimeTimeInt.lean` §(e)），`cNear2 = W^{o(1)}`（`Lemma57.cNear2`，`log` 的幂）。
* 二次远场 `A_u·√Smax`：**T273 的 `sMax_le`**（`EarlyQVRateEv.lean` §8）给 `Smax ≤ K′·(ℓ_u/ℓ_s)³A_u^{−3}`，所以 `A_u√Smax ≲ r^{3/2}A_u^{−1/2}`——与 `StepSide''.β_le` 同一行 `(4, 11/2)`，已在你的表里。
* ⛔ **本条作废（Cowork 的错，见 §17 D21-1）**：`ρfar`：它就是 `h564` 的水平，由 (2.73) 在 `n = 6` 给 `ρ ≲ r⁵A_u^{−3}`（T267 `h564` 由 `h273` 导出），比三次远场小。
* `W^{−D}` 尾项：`D` 在 `δ, p` 之后取，`W ≥ N^{1/2}`（`Band.bandwidth`）。
* `η_u^{−1}`、`T_{u}/T_t`、时间积分、`cWt³`：用 T268 的时间积分（`integral_inv_sqrt_mul_sqrt_kappa_le`，首格走 `integral_early_le_budget`）与 `(5.32)` 的 `T_u ≤ T_t`（`tailT_sub_le`）。
可写 `Gauss/APrimeExponents.lean`（续）。若某项的 `N` 幂在 `δ₀ = c/11` 下仍不够，编译出该行并停下。

**T278（`'''` 生产者与 `∫η⁻¹ ≤ log N` 已证）→ `Qop` 投影漂移的 `StochDom`，不许用 `hgood_QF`**：
* ⚠ `SumZeroDyn.hgood_QF` 吃 `SumZeroDyn.Hierarchy`，而 **D16 规定不引用它**（其 `mart :=` 残差是 fiat）。它要的 `Lemma510.F_decay` 也挂在那个结构上。
* 走确定性算子界：`norm_Qop_apply_le`（`Hierarchy/SumZero.lean:112`）给 `‖Qop F‖ ≤ ‖F‖ + ‖Psum F‖·‖ϑ_u‖`；`norm_vartheta_le`（`:99`）在实 `u ∈ [0,1)` 给 `‖ϑ_u‖ ≤ ∣1−u∣ⁿ(1−u)^{−n} = 1`。所以只剩 `‖Psum(H.F)_x‖`。
* **第 0 步（只读）**：`Psum` 是对一个指标求和（`L` 项）。先看它有没有**不付 `L` 的**界：(a) Ward 恒等式（Lemma 3.6 / `Hierarchy/Ward*`）把 `Σ_a` 环化成 `η⁻¹·低阶环`；(b) 漂移的快衰减 `FastDecayFlow.fastDecay_driftF_window`（`:453`）、`DriftDef.fastDecay_driftF`（`:430`）把求和截在 `ℓ_u N^τ` 内——这会付 `ℓ_u N^τ`，要核它能否被 `η_u`/`scale` 的幂抵消（论文 (5.99)–(5.103) 就是做这件事）。报告里写清哪条路不付正幂；若两条都付，精确写出多出的因子并停下。
* 那条 `ψ` 行的额外加性误差用 `ζ`（`'''` 生产者有 `ζ` 槽）或 T280c 的 `weighted_norm_le_of_event` 付。

## §15 T280d：δ₀ 是我们选的，逐行取最小即可（Cowork 09:37）

T280d 的否定结论对（`not_quadratic_far_margin_budget_at_delta0`、`not_quadratic_far_sup_margin_budget_at_delta0`），但它否定的只是 **`δ₀ = c/11` 这个具体取值**。`δ₀` 只要求 `> 0`：`APrimeHypOn`/`WeightedMoment` 对 `0 < δ ≤ δ₀` 量化，下游 `≺` 只用到「某个正的 `δ₀`」。所以二次远场行 `(8, 23/2)`（要 `δ < 37c/480`）只是让 `δ₀` 变小。

**改用的停止规则**：每一行化成 `N^{aδ}R^b/A`，
* 若 `b < 30`：记下 `δ < c(1 − b/30)/a`，**不停**，`δ₀` 取所有行的最小值（留严格余量，例如取最小值的一半）；
* **只有**当某行 `b ≥ 30`、或该行不能写成这种形状（例如多出不随 `δ` 缩小的 `N` 正幂、或需要 `R` 的下界），才编译否定结论并停下。

**续做**：先取 `δ₀ = c/20`（`< 37c/480`），把 §14 列的其余各行（近场、`ρfar`、`W^{−D}` 尾、`η_u^{−1}` 与时间积分、`cWt³`）逐行列 `(a,b)` 并更新 `δ₀`；然后做 `fitLhs ≺ 1`——它的 `tc`、`Qb`、`Qm`、`εs` 输入由 T268 的时间积分引理（`integral_early_le_budget`、`integral_inv_sqrt_mul_sqrt_kappa_le`、`integral_inv_sqrt_mul_sqrt_kappa_qHatNear_le`）给出，逐个核签名后接上。`sMax_le` 所需的四环界是 Step 1 的 (2.73)@`n = 4`（`Step1.apriori`），在事件上给，不是 `∀ω`。

## §16 T280b 收下；它的余项与 T280e 重跑（Cowork 09:42）

T280b 按 §11 做成：小槽 `x^{1/4}`、`stepRhs''/R⁴ ≤ (cStep′+1)x^{5/4}`（八项逐一核过）、族求和 `N²N^{5δp/16} ≤ N^{δp/2}`（`32 ≤ 3δp`）、加权 Lyapunov、反向桥的两端。**余项只有一件**：数值 `hinit`，即 `Ψ_s = U_{s,t}lk_s/(T_{t,D}R⁴)` 的加权 `2p` 矩。**这不需要新数学**，逐点化归到现成件：
* `∣Ψ_s(a)∣ ≤ Σ_b ∣U_{s,t}(a,b)∣·∣lk_s(b)∣/(T_t R⁴) ≤ J*_s · Σ_b ∣U_{s,t}(a,b)∣·T_{s,D}(b)/(T_t R⁴)`（`J*` 的定义，`Step2.le_jStar_mul`）；
* 核-尾卷积用 **T277 的 `APrimeQVEndpoint.weightedKernel_tail_le`**（`:385`，绝对核卷积，保留 `T` 尾）得 `≲ R^{O(1)}·T_t(a)`，除以 `T_t R⁴` 后 `≲ 1`（核对 `R` 的幂，若 `> 4` 停下报）；
* `J*_s ≺ 1` 由 **T274 的 `stochDom_jS_init_of_boundsCore`**（`APrimeSlotFields.lean:537`，吃 `BoundsCore X E s`）；
* 于是 `Ψ_s ≺ 1`，再走 T280b 的 `weightedMomentDom_of_stochDom_of_nonneg` → `numerical_hinit_of_weighted_integral`，常数与 `N^ε` 吸收进 `initTerm x R (slotXi′ x)/R⁴`（`x^{1/4}` 的余量）。

**T280e 现在就可以重跑**（不必等 T280d）：把 T280d 尚未交出的 `δ₀` 与 `4R⁴G ≺ 1`、`fitLhs ≺ 1` 写成组装文件里的**具名输入**，其余照 §12/§13 与本节接线；T280d 交出后逐个替换。T280e 顺带做上面的 `hinit` 化归（可写 `APrimeAssembly.lean`）。

## §17 D21：更正 §14 的 ρfar 条；(S3) 的 J 换接法；T278 的漂移投影行（Cowork 10:10；每条均已读源码核对，行号为 10:05 的工作区）

**D21 裁定**
1. **§14 的「`ρfar` 就是 (2.73) 水平、比三次远场小」作废——Cowork 的错。** `W·L·ρ` 对 `L` 个块求和再除以 `T_t²`，多出因子 `L`；T280d 的 `no_uniform_rho_row_at_principal_tail` 是对的。**修法**：`h564` 在 `Lemma57.ee_le_sym` 的证明里**只进近场分支**（`Hierarchy/Lemma57.lean:2702–2707`：近场调 `ee_near_le … h564`，远场分支里 `W·L·ρ` 只是被 `nlinarith` 加进去的余量）；论文 (5.64) 也只在 Case 1（p.61）。故把 `h564` 限在近场、以 `ε·T_u(d)²/(W·L)` 的形式给，余项并入近场系数，`ρ` 整个消失。见 T280g。
2. **`EarlyQVRateEv.jStar`（`Gauss/EarlyQVRateEv.lean:146`）不得用作任何带 `hJ : J ≤ cWt·Λ` 的 `J`。** 它取全局 `gMax`（`:112`，含对角元 `|G_xx| ≈ |m|`）作 `Gm`，于是 `J ≥ gMax²/tailT(远) ≳ W^D`（早期时刻存在远块对，尾函数只剩地板 `W^{−D}`）；`s3GridDet`（`:694`）用的正是它。**§9 第 4 条「交 `EarlyQVRateEv` 的 (S3) 事件」撤回**（`sMax` 不受影响，照用）。T277 的 `sqrt_evolvedQV_le_endpoint` 对 `Gm/Gsq/J` 不绑定，改由 T280f 用块级最大值 + (4.2) 带地板版供给。
3. **T278 的漂移投影行走 `SumZeroDyn.norm_Qop_le_of_fastDecay`**（`Hierarchy/SumZeroDyn.lean:2538`，纯确定性，签名无 `Hierarchy`，D16 允许）。它的两个输入与 `'''` 生产者已要的 `hAMF`/`hDecF` 同源，不引入新前提。

**所有单的通用规则**：先 `#check` 下列每个名字、核签名；本节任何一句在 Lean 里不成立 → 编译否定结论、停下报告。不 commit，不改旧签名（一律带撇新声明）。

### T280g（Codex，新；文件 `Gauss/APrimeNearRem.lean`）：近场限定的 `h564`，端点无残差
第 0 步 `#check`：`Lemma57.ee_le_sym`/`ee_near_le`/`ee_far_le_sym`，`EEDef.ee_le_EEpath_sym`/`eeL6_two_le_far`（:1134）/`eeL6k_two_one_le_glue`（:735）/`eeL6k_two_zero_le_glue`（:782）/`eeL6_two_eq`，`APrimeQVEndpoint.diagShape`（:280）/`sqrt_quadVar_Uker_le_diagShape`（:295）/`sqrt_diagShape_le_three`（:823）/`sqrt_evolvedQV_le_endpoint`（:865），`tailT_antitone`（`Analysis/StretchedExp.lean:307`），`zdist_sub_le_add`（:444），`Loop.norm_Gsig_le`（`Loop/Split.lean:534`），`zt_im_eq`（`SumZeroDyn.lean:5317`）。
* **(a)** `Lemma57.ee_le_sym'`：同 `ee_le_sym`，但去掉 `ρ`，`h564` 换成
  `h564' : (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu → ∀ b, ellStarStar W ℓu < zdist L (a₁ - b) → L6 b ≤ ε * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 / (W * L)`（`0 ≤ ε`）；
  结论同 `ee_le_sym`，去掉 `W*L*ρ`，近场系数 `cNear2 W ℓu * (ℓu/ℓs)^5` 换成 `cNear2 W ℓu * (ℓu/ℓs)^5 + ηu * ε`。证明抄 `split_ifs`：近场分支 `ee_near_le (ρ := ε*T²/(W*L)) … (h564' hd)`，远场分支原样。
* **(b)** `EEDef.ee_le_EEpath_sym'`：在 `ee_le_EEpath_sym` 里做同一替换。
* **(c)** 生产者 `EEDef.eeL6_le_nearFar`：设 `d ≤ 4ℓ*_u`、`ℓ**_u < dist(a₁,b)`，令 `F := ellStarStar W ℓu − 4·ellStar W ℓu`。则 `eeL6 b ≤ 2·Gbar·J²·tailT(F)²`，这里 `Gsq a₁ a₂ ≤ Gbar`、`Gsq a₂ a₁ ≤ Gbar` 是新前提。证明照 `eeL6_two_le_far`：它的 `hfar` **只**用于 `hA12/hA21`（(a₁,a₂) 那一对），换成 `Gbar`；两个 `b` 对走 `h42sq`，因为 `dist(a₂,b) ≥ ℓ** − 4ℓ* ≥ ℓ*/2`（`log W ≥ 3` 即可，从 `hlog` 推），再用 `tailT_antitone`。实例化时取 `Gbar = (etaT E u)⁻²`（`norm_Gsig_le` + `zt_im_eq`）。
* **(d)** 算术：近场 `d ≤ 4ℓ*_u` 时 `T_u(d) ≥ A_u^{−2}·exp(−2(log W)^{3/4})`。取
  `ε := W·L·2·η_u^{−2}·J²·tailT(F)² · A_u⁴·exp(4(log W)^{3/4})`，则 (c) 给出 `h564'`。再证 `ε ≤ W⁻¹`，前提是：`η_u ≥ N⁻¹`、`A_u ≤ N`、`N ≤ W²`、`J ≤ N^k`、`D ≥ 2k+14`、`(4D)² ≤ log W`。
  - 核算：指数部分 `≤ 4W^{6+4k}·e^{−√2(log W)^{3/2}+4(log W)^{3/4}}`（用 `(log W)³ − 4(log W)^{3/2} ≥ (log W)³/2`）；
  - 地板部分 `≤ 4W^{14+4k−2D}·e^{4(log W)^{3/4}} ≤ 4W^{−13}`。
* **(e)** T277 带撇链：`sqrt_quadVar_Uker_le_diagShape'`、`sqrt_diagShape_le_three'`、`sqrt_evolvedQV_le_endpoint'`。
  - `h564 : ∀ c b, …≤ ρ` 换成 `h564' : ∀ c, near(c) → ∀ b, far → eeL6 … ≤ ε·T_u(c)²/(W·L)`；
  - `diagShape` 里的 `ρ` 删掉，`diagResidual` 项消失，近场率换成 `diagNearRate + 2ε`（`diagShape` 外层有因子 2）。证明照抄。
* **停止条件**：`ee_le_sym` 的远场分支其实用到了 `h564`（与 :2706 矛盾）；或 T277 近场分支吃不下多出的 `ε`。

### T280f（Codex，新；文件 `Gauss/APrimeJG.lean`）：(5.42)/(S3) 的 `J` 用块级最大值
第 0 步 `#check`：`Gauss.EntryBoundFlow'`（`Gauss/EntryBoundTime.lean:126`）/`entryBoundFlow_floor`（:155），`Lre`（`Green/EntryBound.lean:1032`），`norm_gloop_pm_eq_Lre`（`Gauss/Lemma41Glue.lean:42`），`Step2FarInputs.norm_gloop_pm_le_jS_mul_tT`（:2146），`Step2.eq530`（`Hierarchy/Step2.lean:1909`，`δ` 任取 `>0`），`Step2FarInputs.eventually_norm_Kval_pm_le_tT`（:2093），`tailT_sub_le`（`StretchedExp.lean:337`），`Step2.jS`（:642），以及沿流 `goodSet` 的 `HighProb` 供给者（`goodSetFlow`/`FlowGoodEv`，先找）。
* **定义**
  - `gmBlk x y := max_{s, p∈I_x, q∈I_y} ‖Gsig s p q‖`；
  - `gsqBlk p q := max_{p' : SB p p' ≠ 0} gmBlk q p' * gmBlk p' q`；
  - `jG := 1 + max_{ℓ*/2 ≤ dist} gsqBlk/tT`。
* **确定性结论**（按定义）：`hGm`、`hGm0`、`hGsq0`；`hGsq2`（取 `p' = p`，`SB p p = 1/3 ≠ 0`）；`hrow`；`h42sq`（同 `gMax_sq_le_jStar_mul_tailT` 的写法）；`gsqBlk ≤ (etaT E u)⁻²`。
* **概率结论**：`StochDom P (fun N (u : TimeIcc s t N) ω => jG …) (fun N u ω => C * (1 + Step2.jS X E D N u ω))`。
  - (4.2) 带地板版取 `fl = 2N^{−B}`、`B := D`；于是 `N^{−D} ≤ W^{−D} ≤ tT`。
  - 远对不相邻，所以 `sbSupport` 项为 0。
  - 平移后的对上 `Lre ≤ jS·tT`：K 的界用 `eq530` 取 `δ = 1/4`，因为平移至多 3 格 `≤ ℓ*/4`。
  - 平移回来用 `tailT_sub_le`，`C·ℓ* = 3` 时代价是常数 `e^{√3}`。
  - `goodSet` 的指示函数：与它的 `HighProb` 事件相交。
* **停止条件**：`EntryBoundFlow'` 的块下标次序归不到远对上；或沿流 `goodSet` 在仓库里没有 `HighProb` 供给者。报告缺哪一件。

### T280d 续做（§15 的停止规则不变）
* **`ρfar` 行**改为 T280g 的 `ε` 行：`2ε·T_u(d)²/(T_t(d)R⁴)² ≤ 2ε ≤ 2W⁻¹`。你报告里说缺的时间比较**仓库里有**：`tailT_le_tailT_of_flow`（`Gauss/CutoffBounds.lean:427`）；`ℓ_u ≤ ℓ_t` 用 `ellHat_mono`（`Hierarchy/Step3.lean:693`），`A_t ≤ A_u` 用 `flowScale_antitoneOn`（`Flow/Scales.lean:100`）。
* **`W^{−D}` 行**：`16·W·L·W^{−D}·cWt³Λ³·T_u²/(T_tR⁴)² ≤ 16·N·W^{−D}·cWt³Λ³`，用同一个时间比较。`D` 在 `δ, p` 之后取，`N ≤ W²`（`bandwidth`）。
* **`J`**：是 T280f 的 `jG`。`hJ : jG ≤ cWt·Λ` 作具名输入；`Λ` 允许多带一个 `N^τ`。
* **形式**：`QBd` 的 `ρfar` 槽取 0，`ε` 单列一行或并入近场系数都可以，写进报告。
* 然后做 `fitLhs ≺ 1`（按 §15 原文）。

### T278 第六步：`hEnvF` 的 `ψ`
* 定义 `ψF N u q ω := A_u^{n+2} · sup_b ‖Qop_u (H.F N u (X.H N u ω) q.1) b‖`。这样 `hEnvF` 在 `ζ = 0` 时按定义成立。
* **`ψF` 的 `≺` 界，在 `Ξ` 上**：用 `norm_Qop_le_of_fastDecay`（取 `n := n+1`）。
  - `FastDecay` 输入：就是你给 `hDecF` 的那条（`DriftDef.F_eq_driftF` + `FastDecayFlow.fastDecay_driftF_window`，:453，半径 `ℓ_u·4K`）。
  - 尺寸输入用**逐点的** `DriftBound.norm_driftF_le`（`Hierarchy/DriftBound.lean:245`，形如 `A_u^{−(n+2)}η_u⁻¹(Krad+2)·cDrift·xiRhs + W·L·δ·…`）。**不要用 `hAMF` 的一致上界 `Msz`**：对 `u` 取 sup 会多出 `(A_u/A_v)^{n+2}`。
  - 得到 `ψF ≤ η_u⁻¹(1+(24e·cTwo52·K)^{n+1})(Krad+2)·cDrift·xiRhs + A_u^{n+2}·(加性尾项)`。
  - `K = N^τ` 吸收进 `≺`；`δ = N^{−D}`，`D` 在 `n` 之后取，使加性项 `≤ N⁻¹`；`η_u⁻¹` 就是 §10 的时间权 `ρ`。
* **`Ξ` 外**：用确定性包络 `‖G‖ ≤ η⁻¹`，走 §8 的反向桥。
* 第 0 步 `#check`：`norm_Qop_le_of_fastDecay`、`fastDecay_driftF_window`、`norm_driftF_le`、`F_eq_driftF`；核对 `B.ell N u` 与 `ellHat (B.L N) (u:ℂ)` 的关系，以及半径 `K → 4K` 的换算。
* **停止条件**：`norm_driftF_le` 的输入（`hKb` 的 `CK·A^{−(len−1)}`、`xiLK`）在 `hDecF` 所用的同一个 `Ξ` 上拿不到——报告缺哪一件。LoopDecay 输入与 Step 2 结论是否循环：这是既有问题，只报告，不在本步解决。

## §18 T280g、T280e 的回报（Cowork 10:23；已读两份报告与相关签名）

### T280g：否定成立，是 Cowork §17(c) 的疏漏
§17(c) 写「`log W ≥ 3`，从 `hlog` 推」，但 `hlog : (4D)² ≤ log W` 在 `D = 0` 时什么也不给；`not_log_three_of_endpoint_hlog` 对。**修法（路由，已核算）**：
* (c)、(d) 各加一条显式前提 `4 ≤ Real.log W`。(c) 需要 `(log W)^{3/2} ≥ 4.5`，也就是 `log W ≥ 2.73`；(d) 需要 `(log W)³ − 4(log W)^{3/2} ≥ (log W)³/2`，也就是 `(log W)^{3/2} ≥ 8`，即 `log W ≥ 4`。`4` 两处都够。
* (e) 的带撇端点定理加前提 `1 ≤ D`（T280e 的构造器本来就有 `hD : 1 ≤ D`）。由 `hlog` 得 `log W ≥ 16 ≥ 4`，再喂给 (c)(d)。
* (d) 的其余前提照旧：`D ≥ 2k+14`、`J ≤ N^k`、`η_u ≥ N⁻¹`、`A_u ≤ N`、`W·L ≤ N`、`N ≤ W²`。Cowork 逐项复核过：
  - 指数部分 `≤ 4W^{6+4k}e^{−√2(log W)^{3/2}+4(log W)^{3/4}}`：因为 `√(log W) ≥ 4D ≥ 8k+56`，指数 `≥ (11k+78)·log W`；
  - 地板部分 `≤ 4W^{14+4k−2D+4(log W)^{−1/4}} ≤ 4W^{−13}`。

继续做 (c)–(e)。

### T280e：改道收下（D22）
1. **D22**：§9 第 1 条「对完整 `jSnorm` 走 `weightedMoment_of_stepBound_mono`」**作废**。它要求完整 `jSnorm` 在族求和**之前**就达到小槽尺度 `N^{5δp/16}`；而 T280b 的族求和只给出**之后**的 `N^{δp/2}`，两者接不上，T280e 的判断对。**新路线**：逐坐标的 Hstep → T280b 的族求和（高 `p`）/ Lyapunov（小 `p`）→ 在宽权重 `Wp` 下得到 `hfamily` → 用 `weightedMoment_of_widened_family` 做单调转移。T280a 的 `weightedMoment_of_stepBound_mono` 保留，只是不再用于 `jSnorm`。
2. **端点恒等式已核**：`jSnorm = jS/R_u⁴`（`APrimeSlotFields.jSnorm_eq_mul`，:170），且 `jS = 1 + max_a ‖lk_u(a)‖/T_u(a)`（`Step2.jStar`）。所以在网点 `u_k` 取**端点 `v = u_k`** 时，`jSnorm(u_k) ≤ 1 + max_a |Ψ^{(a)}_{u_k}|`，其中 `Ψ` 按 `T_{u_k}·R_{u_k}⁴` 归一。
3. ⚠ **一致性要点**：第 `k` 个网点的坐标族以 `u_k` 为端点，所以逐坐标的输入都要对端点 `v ∈ [s_N, t_N]` 一致（`∀ᶠ N, ∀ v, ∀ a`），不能对固定的 `t` 取 `∀ᶠ`。`eventually_initial_hinit_gauss`（:628）现在是固定 `t` 序列的形式。

**T280e 下一步**（写在 `APrimeAssembly.lean`，旧声明不动）：
* **第 0 步（只读）**：`#check` 并列出以下三个声明的**全部前提**，逐条标注为「已证 / 具名输入 / T280c 件」：
  - `APrimeDuhamelModel.momFlowDeriv_le`（:638）；
  - `APrimeGronwall.weightedMinkowski_of_deriv_le`（:404，给 `hG`）；
  - `APrimeInit.coordinate_integral_of_small_slots`（:209）。
* **(i)** 把 hinit 改成对端点一致：先出 `initialEvolvedNorm_stochDom_sharp'`，指标集换成「`TimeIcc s t N` × 坐标」，端点 `v` 随指标走；再出对应的 `eventually_initial_hinit_gauss'`，形如 `∀ᶠ N, ∀ v ∈ [s_N,t_N], ∀ a`。若某个阈值依赖 `v` 且不一致，编译出否定并停下。
* **(ii)** `hfamily_of_coord_budgets`：由三组逐坐标的具名输入推出 `hfamily`，对 `v = u_k`、`∀ k ≤ cutNetTop`、`∀ a` 一致：
  - **(N1)** drift 预算 `2∫(Adr+Bcr) ≤ driftTerm/R⁴`：将由 T280d 的指数行和 T278 提供；
  - **(N2)** QV 预算 `√((2p−1)∫g) ≤ tailTerm/R⁴`：将由 T277 + T280f/T280g + T280d 的 `QBd` 行提供；
  - **(N3)** `momFlowDeriv_le` 里模型方面的前提，按第 0 步的清单具名写出。

  其余全部要证：`hG`（`weightedMinkowski_of_deriv_le` ∘ `momFlowDeriv_le`）、hinit（用 (i)）、`coordinate_integral_of_small_slots`、端点恒等式（第 2 条）、族求和的高 `p` 部分（`32 ≤ 3δp`）、小 `p` 的 Lyapunov（`momNormW_le_momNormW_of_exponent_le`）。最后接到 `aprimeSlot_of_widened_family`。
* **停止条件**：端点恒等式在 Lean 里不成立；或 (N1)–(N3) 之外还冒出新的模型前提。精确报告是哪一条。
