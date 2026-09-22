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
