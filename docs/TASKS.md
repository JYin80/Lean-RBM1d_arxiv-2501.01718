# 任务队列

> ## 通知（2026-09-19，由 Jun 授权、Cowork 转达）
>
> **范围已定：暂不自建 Itô / 随机积分。**（自建最小切片约 300–460 条定理，一般理论约 700 条；
> 论文剩余部分约 1500–2500 条，Itô 只占 15–20%，不是当前的瓶颈。）
> **现在全力做随机层之外的全部内容。**
>
> 给每一个新开的 agent 的一句话：
>
> > 读 `docs/TASKS.md` 的「第二批工单」（T42–T57），挑一张「待认领」的，
> > **先改表格把认领改成自己的名字并提交**，再开工。硬规则：
> > 不留 `sorry`；依赖随机流的东西一律写成 `structure` 字段或定理参数
> > （**绝不用 `axiom`**，仓库有硬性公理审计 `#assert_rbm_axioms`）；
> > 偏离论文记进 `docs/paper-deltas.md`；只按文件名 `git add` 自己那几个。
>
> 16 张单每张只碰一个新文件，互不重叠，**开多少个 agent 都不会撞**。
> 唯一的共享文件是根 `RBM1D.lean` 的 import 列表：只做点插入，绝不整体重排。
> 建议次序：**先 T42**（解锁下游六张）；T43/T47 适合最轻量的 agent；T45 给最强的。
>
> ---
>
> ## 方向变更（2026-09-20，Jun 授权）：**随机层改走「矩路线」，不造 Itô**
>
> Jun 原话：「按你觉得最好的方案走下去，只要证明跑通，我可以适当的改 paper」。
>
> 全文审计（`claude/stochastic-layer-audit.md`）发现：论文里真正路径化的只有
> **Lemma 5.3 的随机积分、Lemma 5.5 的 BDG、(5.43) 的那一个停时**，外加 Def 2.1(i) 的不可数并。
> 全文**没有**域流、Markov 性、两时刻联合律、Doob 不等式。
>
> 于是：把流实现成 **`H_u := √u · X`**（`X` 是固定的高斯带矩阵，一时刻边缘与 (2.34) 完全一致），
> 用**生成元恒等式 + 对矩的 Grönwall** 替掉 Duhamel + BDG，
> 用**连续归纳**替掉停时，用 **`N^{-C}` 时间网 + 确定性 Lipschitz** 替掉不可数并。
> 关键：生成元恒等式的二阶项 `|F|^{2p−2}·Σ_α S_α|∂_α F|²` **正好是 (5.25) 的二次变差**，即 BDG 的右端。
>
> Lean 侧只要有限维高斯测度 + 一条 Stein 分部积分，**Mathlib 全都有**（Stein 那条要自己证，但
> `gaussianPDFReal` 是显式的，`p′ = −(x/v)p`，一次分部积分的事）。
>
> **新工单 T69–T76，先做 T70（Stein 分部积分）**，它是整条线的地基。
> 完整路线与风险见项目文档 `claude/moment-route-plan.md`。
>
> 旧的「随机层写成假设接口挂起」的决定**到此取消**。已经写好的 `Flow/Hypotheses.lean`
>
> ### 硬性约定（2026-09-20，Jun 指定）：**对外一律保持论文的 `≺`，矩只在证明内部**
>
> Jun 原话：「这部分（形式）不能动论文太多，所以还让 lean 证明往论文靠吧」。
>
> 1. **所有 `structure` 字段的签名一个字都不改。** `SumZeroDyn` 的 `bdg` / `bdgQ`
>    进去是 `≺`、出来是 `≺`，**保持原样**——矩路线要做的是把它们**从假设变成定理**，
>    不是改它们的形状。
> 2. **Steps 1–6、Lemma 2.18–2.20、Theorem 2.3/2.4/2.5/2.6 的陈述不动。**
>    论文怎么写，Lean 就怎么陈述。
> 3. **矩只活在这一段里，对外不可见**：
>    `拿到 ≺ 输入 → 升成矩 → 生成元恒等式 + Grönwall → 降回 ≺ 输出`。
>    新文件全部放 `RBM1D/Gauss/` 下，不要往 `Hierarchy/` 里渗矩记号。
> 4. 因此需要一条**反向桥**（新工单 **T77**）：`≺` + 确定性包络 ⟹ 矩。
>    包络是白送的：`Im z ≥ η > 0` 使 `‖G‖ ≤ η⁻¹` 在**全空间**成立，
>    各阶导被 `k!·η^{-(k+1)}` 全局控制。T73 已经做了正向（矩 ⟹ `≺`，Markov）。
>
>
> ### 论文改动预算（2026-09-20，Jun 指定「调整要尽量小，尽可能不破坏之前结构」）
>
> 已经把论文要改的最小集合算清楚了，见项目文档 `claude/paper-edit-budget.md`。
> **零处陈述改动、零处重新编号**，只有五处局部编辑（一条注记、一句读法说明、
> Lemma 5.5 的证明、§5.3 的停时段落、一条脚注），合计约两页。
>
> 之所以这么小，是因为 **Lemma 5.5 的陈述 (5.24) 本来就是矩不等式**——两边都是期望，
> 没有一处轨道陈述。BDG 只在它的**证明**里，不在**陈述**里。
> 所以这是「同一条不等式换个证法」，不是「换一套语言」。
>
> **对应到干活的纪律：**
>
> 1. 矩形式的中间结果**一律不给论文编号**，全部放 `RBM1D/Gauss/`，名字带 `moment` 前缀，
>    **不出现在 `Hierarchy/` 或 `Flow/` 的任何陈述里**。
> 2. **凡是会迫使论文新增编号命题或重新编号的做法，先记进 `docs/paper-deltas.md`
>    并标「需 Jun 确认」，不要自行决定。**
> 3. **每条 paper-delta 必须写明「论文第几页、改哪一段、大约几行」**，
>    这样预算表随时可核对，不会悄悄膨胀。
> 4. ⚠️ **红线**：如果 Hölder 记账没法闭合在 Lemma 5.5 的证明内部，
>    逼得要改 (5.36)/(5.77) 的**陈述**——**立刻停下来报告，不要顺手改陈述**。
>
> **效果**：paper-delta 从「§5 每条 `≺` 都要改写」缩成
> 「**Lemma 5.5 的证明换一条路，陈述不变**」。量也小得多——实测下来要动的是
> `bdg`/`bdgQ` 两个接口加 4 条 QV 输入，不是那 157 条 `≺` 定理。
> 接口不用改——`Sample` 结构正好能被 `H_u = √u·X` 实例化；矩路线要做的是把那些**字段从假设变成定理**。


两边共用的工单。**认领前先改 `认领` 一栏并提交**，避免重复劳动。

分工原则：**按文件切分，不按难度切分**。同一时间两边不碰同一个文件，合并就永远是平凡的。

| # | 任务 | 文件 | 认领 | 状态 |
|---|---|---|---|---|
| T1 | `1 − ‖ρ(ξ)‖ ≍ \|1−ξ\|^{1/2}` 的定量估计 | `Propagator/Decay.lean` | **Cowork** | 进行中（精确恒等式已证） |
| T1c | T1 的复 ξ 情形：`‖1−ξ‖/8 ≤ (1−‖ρ‖)² ≤ 3‖1−ξ‖`，对全部 `‖ξ‖<1` 一致（实 ξ 情形 Cowork 已在 `c1210a4` 完成） | `Propagator/RateComplex.lean` | Claude Code #2 | **完成** |
| T2 | `‖A(ξ)‖` 的上界 | `Propagator/Decay.lean` | **Cowork** | **完成**（`norm_AA_le_of_real`、复 ξ 版在 `DiffComplex`） |
| T3 | 组装成论文 (2.52) 的形式 | `Propagator/Decay.lean` | **Cowork** | **完成**（实 ξ；复 ξ 由 Claude Code 的 Fourier 路线给出） |
| T4 | (2.53)(2.54) 差分估计 | `Propagator/Decay.lean`、`Propagator/DiffComplex.lean` | **Cowork** | **完成**（实 ξ 与复 ξ，均已补强到论文形式） |
| T5 | 附录 B (B.1) 的 Fourier 表示 | `Propagator/Symbol.lean` | Claude Code | **完成** |
| T6 | Def 2.1(ii) 的确定性 ≺ | `Defs/Domination.lean` | Claude Code | **完成** |
| T7 | 删掉 `RBM1D/Probe.lean` | — | Claude Code | **完成** |
| T8 | (B.3) 符号的双边界 `\|1−ξŜ(p)\| ≍ \|1−ξ\| + \|p\|²` | `Propagator/SymbolBound.lean` | Claude Code #2 | **完成** |
| T9 | 无穷体积核 + 围道平移 (B.4)(B.5) | `Propagator/Contour.lean` | Claude Code #2 | **完成** |
| T10 | Poisson 求和 / 周期化 → 环上的 (2.52) | `Propagator/Poisson.lean`、`Propagator/DecayComplex.lean` | Claude Code #2 | **完成** |
| T11 | dyadic 分解 → (2.53)(2.54) 的一般证明 | — | — | **已由 T33 以闭式路线解决**（不必再走 dyadic） |
| T12 | 数值回归测试 | `Test/Numeric.lean` | Claude Code | **完成** |
| T13 | Thm 2.2：由 local law 推 delocalization | `Delocalization.lean` | Claude Code | **完成**（确定性部分） |
| T15 | §2.1 模型层：S_W、S = S^(B)⊗S_W、E_a、N = WL | `Defs/Model.lean` | Claude Code | **完成** |
| T16 | Def 2.9/2.10：loop 的指标数据与 cut-and-glue 算子 | `Loop/Index.lean` | Claude Code | **完成** |
| T17 | Lemma 3.2 的组合内容：无交叉对角线集合 = `TSP` | `Loop/Crossing.lean` | Claude Code #2 | **完成** |
| T18 | Def 2.12 原始方程 + Example 2.15（n=2 闭式解） | `Loop/Primitive.lean` | Claude Code | **完成** |
| T19 | Lemma 2.8：`m_sc`、`m^{(E)}`、`t` 的代数 | `Defs/Semicircle.lean` | Claude Code | **完成**（代数部分；(2.40) 推迟） |
| T20 | Def 3.3：星图情形 + n=4 的三张图 | `Loop/Tree.lean` | Claude Code | **完成** |
| T21 | 一般树值 Γ 的递归定义（Def 3.3 完整版） | `Loop/Tree.lean` | Claude Code | **完成** |
| T22 | (2.48) 解的唯一性：双线性结构 + n=2 的 Grönwall | `Loop/Unique.lean` | Claude Code #2 | **完成** |
| T23 | Example 2.16（n=3）：第一个非平凡的树表示实例 | `Loop/Example3.lean` | Claude Code #2 | **完成** |
| T24 | 公理审计 + 删 `Probe.lean` + linter 清理 | `Test/Axioms.lean`（新建）等 | Claude Code | **完成** |
| T25 | **Lemma 3.4：树表示**（第 3 节主定理） | `Loop/TreeRep.lean` | Claude Code #2 | **完成（n ≤ 4）**；一般 n 见 T25b |
| T25b | Lemma 3.4 一般 n：`polyVal` 的轴无关性 + 边 ↔ (k,l) 双射（见 STATUS「T25」节） | `Loop/TreeRepGeneral.lean` | Claude Code #2 | **完成**（一般 n，`treeRep_general`） |
| T26 | Lemma 3.6：𝒦 的 Ward 恒等式 | `Loop/Ward*.lean`, `Loop/Cyclic.lean` | Claude Code | **完成** |
| T27 | Def 2.9 的 G-loop 本身（确定性 H） | `Loop/GLoop.lean` | **Cowork** | **完成**（G(σ)†=G(−σ)、预解式恒等式、loop 旋转不变） |
| T28 | Corollary 3.5：纯 loop 的界 | `Loop/Cor35.lean`（新建） | Claude Code #2 | **完成** |
| T29 | (3.35)(3.36) 的短边/长边两半（自查发现未覆盖） | `Propagator/Edges.lean` | **Cowork** | **完成**（四条齐） |
| T30 | Lemma 3.6 与循环不变性对真正的 `K`（`Kgen`）无条件成立 | `Loop/WardKgen.lean` | Claude Code | **完成** |
| T31 | Def 3.8/3.9：长内部边 `F_long`、按 π 分层、`K^(π)` 与 `Σ^(π)` | `Loop/Layer.lean`（新建） | Claude Code #2 | **完成** |
| T32 | Corollary 3.7（由 Lemma 3.6 直接推出） | `Loop/WardKgen.lean`, `Loop/Cyclic.lean` | Claude Code | **完成**（(3.14) 在 bulk `\|E\| ≤ 2−k` 无条件：`cor37_bulk`） |
| T33 | (2.53)(2.54) 推到复 ξ（原 T11，现已解锁） | `Propagator/DiffComplex.lean` | **Cowork** | **完成**（Lemma 2.14 全部六条现已覆盖整个圆盘） |
| T34 | Lemma 3.10：对称性与 sum-zero 性质 | `Loop/SumZero.lean`（新建） | Claude Code #2 | **完成** |
| T35 | 储备 B6：Lemma 2.8 的定量部分 (2.40)（`t ≥ c_κ`、`|E| ≤ 2−cκ`、`Im z_t ≍ Im z`） | `Defs/Semicircle.lean` | Claude Code | **完成**（`lemma28_quant`，常数与 κ 无关） |
| T36 | 维护：新组合定义 `Flong`/`TSPlong` 的 `decide` 回归（储备 B5 的组合部分；(2.48) 的数值核对已被 `hasDerivAt_Kgen_all` 取代）；蓝图 `\lean{}` 全部解析（405 个，已核） | `Test/Layers.lean`（新建） | Claude Code #2 | **完成** |
| T37 | Lemma 3.11：`K^(π)` 的界 (3.45)、`K` 的界 (3.46)（T34 落地后解锁） | `Propagator/LongDiff.lean`、`Loop/KBound.lean`（新建） | Claude Code | **完成**（(3.45) `norm_Kpi_le`、(3.46) `norm_Kgen_le`；不用 (3.66)，见 paper-deltas #22） |
| T38 | 下沉共用求和工具到 `Defs/Sums.lean`，消掉两处重复证明 | `Defs/Sums.lean` | Claude Code #2 + Cowork | **完成**（`Decay.lean` 那几条也已下沉） |
| T39 | 附录 A 的确定性部分：G-chain 的定义与代数（Def A.1、chain↔loop） | `Loop/Chain.lean` | **Cowork** | **完成** |
| T40 | Lemma 4.2：预解式的 minor 公式 (4.7)(4.8)(4.9)（Schur 补，纯线性代数） | `Green/Minor.lean` | **Cowork** | **完成**（(4.8) 的符号与论文相反，见 paper-deltas #23） |
| T41 | Def 2.1 (i)(iii)(iv)：概率版 `≺`（overwhelming probability、一致版） | `Defs/StochDom.lean`（新建） | Claude Code | **完成** |
| T42 | Def 5.2 的张量传播子 `Θ_{t,σ}` 与演化核 `U_{s,t,σ}`、恒等式 (5.18)、半群律、Lemma 7.1 (7.1)、Lemma 5.3 的确定性一半（Duhamel） | `Hierarchy/Kernel.lean` | **Cowork** | **完成**（含半群律 `Uker_comp`、`Uker_self`；签名见文件头） |
| T43 | `exp(−√·)` 演算：(5.27)(5.28)(5.32)、卷积积分 (5.50)(5.62)(5.72)、(7.12) | `Analysis/StretchedExp.lean`（新建） | Claude Code | **完成** |
| T44 | loop 的 Cauchy–Schwarz 劈分：(5.2)(5.114)–(5.118)、(6.4)、Lemma 6.1 | `Loop/Split.lean`（新建） | Claude Code | **完成** |
| T45 | Lemma 4.1：(4.2)(4.3)(4.5)，两条外部估计作为假设 | `Green/EntryBound.lean`（新建） | Claude Code | **完成** |
| T46 | §7.2 末尾的零模去除：`S̃^(B) = (1−ζ)S^(B) + (ζ/L)J` | `Propagator/ZeroMode.lean`（新建） | Claude Code | **完成** |
| T47 | (2.67)：`G_0(σ) = m(σ)·I` 与 `L_0 = K_0`（无条件，§2.7 归纳的基例） | `Flow/Initial.lean`（新建） | Claude Code | **完成** |
| T48 | 流的尺度层：`η_t`、`ℓ_t`、`A_t = Wℓ_tη_t` 的单调性、几何时间网格与 (2.72) | `Flow/Scales.lean`（新建） | Claude Code | **完成** |
| T49 | 附录 A 的确定性核心：双边 chain→loop、(A.8)–(A.10)、(A.18)、(A.21)–(A.27)、(A.15) | `Loop/ChainExpand.lean`（新建） | Claude Code | **完成**（(A.25) 界形式与 (A.20) 末步未做，见 STATUS） |
| T50 | §6 的确定性骨架：(6.3)(6.5)(6.7)(6.8)(6.9)(6.12) + `z̃` 的算术 | `Loop/Continuity.lean`（新建） | Claude Code | **完成** |
| T51 | Lemma 7.2 (7.2) 与 Lemma 7.3 (7.13)–(7.24)（核的快衰减/sum-zero 增益） | `Hierarchy/KernelDecay.lean`（新建） | Claude Code | **完成** |
| T52 | Def 5.12 的 `P`、`ϑ_t`、`Q_t`；Lemma 5.13 (5.87)、(5.90)(5.99)(5.104) | `Hierarchy/SumZero.lean` | **Cowork** | **完成**（Def 5.12 全部、p.66 恒等式的锐化等式形式、(5.90)、(5.99) 的定量核、(5.104) 的 `Q⊗Q` 两槽层） |
| T53 | Step 3：(5.76)(5.107)(5.108) 与 (n,k) 双重归纳 (5.109) ⟹ (2.77) | `Hierarchy/Step3.lean`（新建） | Claude Code | **完成** |
| T54 | 随机层假设接口：`Bounds`/`Thm221`/`Steps`/`Transfer`（**不得用 axiom**） | `Flow/Hypotheses.lean`（新建） | Claude Code | **完成** |
| T55 | Steps 4 与 5：(5.125) ⟹ (2.78)；两段劈分 ⟹ (2.79) | `Hierarchy/Step45.lean`（新建） | Claude Code | **完成** |
| T56 | Step 6：(5.126)–(5.136) ⟹ (2.80) | `Hierarchy/Step6.lean`（新建） | Claude Code | **完成** |
| T57 | Lemma 2.18/2.19/2.20 由 Theorem 2.21 推出（§2.7 p.24 的时间网格归纳） | `Flow/Iteration.lean`（新建） | Claude Code | **完成** |
| T58 | §5.2：(5.10)–(5.15) 的 `L−K` 层级重组、Def 5.4 的 `E⊗E`、(5.19)、积分形式 (5.20)(5.21) | `Hierarchy/Dynamics.lean` | **Cowork** | 进行中（(5.12)(5.13)(5.14)(5.15) 已落地；剩 (5.19)、(5.20)(5.21)、Def 5.4 的 `E⊗E`——都卡在下面那条**表示桥**上） |
| T59 | §5.4：Def 5.8 快衰减、Lemma 5.9、Lemma 5.10 (5.77) 的幂计数、Lemma 5.11 (5.83) | `Hierarchy/Decay.lean`（新建） | Claude Code | **完成**（E⊗E 仅抽象形式，待 T58 Def 5.4） |
| T60 | §5.5 的动力学半边：(5.88)(5.91)、**Lemma 5.14 (5.92)**、(5.95)–(5.101) | `Hierarchy/SumZeroDyn.lean`（新建） | Claude Code | **完成**（`lemma514_flow′` 给出 `Step3.Lemma514`；(5.77)(5.75) 仍为占位假设，见 STATUS） |
| T61 | §5.3 Step 2：Lemma 5.6、Lemma 5.7 (5.34)(5.35)(5.36)、(5.39)–(5.48) 的自改进不等式 | `Hierarchy/Step2.lean`（新建） | Claude Code | **完成**（`step2` 给出 (2.75)(2.76)；(2.72) 需 `N^c` 增益，见 STATUS；(5.35) 为 T58 占位假设） |
| T62 | §6 的总装：(6.10)(6.11)(6.13) 与 Lemma 5.1 | `Loop/ContinuityAssembly.lean`（新建） | Claude Code | **完成** |
| T63 | Theorem 2.3 与 2.4 由 Lemma 2.18/2.19/2.20 推出（§2.6 p.22） | `Flow/Consequences.lean`（新建） | Claude Code | **完成**（固定能量切片；(2.4) 需 `TransferLoop1`，见 STATUS） |
| T64 | 附录 A 的总装：(A.11)(A.12)(A.13)(A.14)(A.17)(A.20) ⟹ Lemma A.2 | `Loop/ChainBound.lean`（新建） | Claude Code | **完成** |
| T65 | §7.2 的 GUE 相：(7.25)–(7.36) 的 Grönwall 自举、(7.39)–(7.46) | `Hierarchy/GUEPhase.lean`（新建） | Claude Code | **完成**（`eq747_of_inputs` 给出 T68 的 `Eq747`；(7.45)(7.46) 仍为 T58 占位假设） |
| T66 | 维护：蓝图补上第二批的全部 `\lean{}` 节点 + `leanblueprint checkdecls`；linter 清理 | `blueprint/src/content.tex` 等 | Claude Code | **完成** |
| T67 | **§5.1 Step 1**：(2.73)(2.74)、三情形分解、(5.2)(5.3)(5.4)(5.8)、(5.9) 的禁区论证 | `Hierarchy/Step1.lean`（新建） | Claude Code | **完成** |
| T68 | §2.3 + §7.2 的出口：**Theorem 2.5（QUE）与 Theorem 2.6（普适性）** | `Flow/Universality.lean`（新建） | Claude Code | **完成** |
| T69 | 固定高斯带矩阵 `X`、流 `H_u := √u·X`、实例化 `Sample`、确定性 Lipschitz | `Gauss/Model.lean`（新建） | Claude Code | **完成**（`Sample` 三字段为定理；`‖X‖ ≺ 1` 与 `Dims` 实例两处缺口见 STATUS） |
| T70 | **Stein 分部积分**：一维实值 + ℂ 值 + 矩阵版 | `Gauss/Stein.lean`、`Gauss/SteinMatrix.lean` | **Cowork** | **完成**（`RBM.Gauss.matrixStein` 已卸掉 `MatrixStein`，见下） |
| T71 | **生成元恒等式** `∂_u E[Φ(H_u)] = ½ Σ S_ij E[∂_ij∂_ji Φ(H_u)]` | `Gauss/Generator.lean`（新建） | Claude Code | **完成**（`MatrixStein` 已由 T70 卸掉：填 `RBM.Gauss.matrixStein d`） |
| T72 | 对矩的 Grönwall：`φ′ ≤ aφ + b` ⟹ 界；**二阶项 = (5.25) 的二次变差** | `Gauss/MomentGronwall.lean`（新建） | Claude Code | **完成**（`secondOrder_eq_quadVar` 已证；与 `Hierarchy.EE` 的对接缺两座桥，见 STATUS） |
| T73 | `≺` ↔ 矩 的桥；`N^{-C}` 时间网 + Lipschitz ⟹ `u` 一致的 `≺` | `Gauss/Domination.lean`（新建） | Claude Code | **完成**（Hölder-γ 接口，T69 对接取 γ=1/2；`hmom` 待 T72） |
| T74 | 卸掉 Lemma 5.5（BDG）那个假设字段 | `Gauss/DischargeBDG.lean`（新建） | Claude Code | **完成**（结论：`bdg`/`bdgQ` 现有签名下**不可卸**，三条理由见 STATUS；Def 5.4 已有定义，(5.22)(5.25) 已证） |
| T75 | 用连续归纳替掉 Step 2 的停时 (5.43) | `Hierarchy/Step2Moment.lean`（新建） | Claude Code | **完成**（停时真的消失；结论与 T61 同形；`step` 字段待 T74/T76 的桥） |
| T76 | 卸掉 (2.34) 与 Lemma 2.11：不证 SDE，直接证期望/矩版本 | `Gauss/Hierarchy.lean`（新建） | Claude Code | **完成**（(2.45) 的期望版；`duhamel`/`duhamelQ` 在现有逐路径形状下不可卸，见 STATUS） |
| T77 | **反向桥**：`≺` + 确定性包络 ⟹ 矩（`MomentDom`）；包络由 `‖G‖ ≤ η⁻¹` 全局给出 | `Gauss/Envelope.lean`（新建） | Claude Code | **完成**（与 T73 的正向桥量词序一致，可复合；含 `norm_gloop_le_det`） |
| T81 | **线性 LDE**（高斯情形）：`LDERow` / `LDECol` 的 `StochDom` 版本 | `Gauss/LDELinear.lean`（新建） | Claude Code #2 | **完成**（行、列两条，`Gauss/RowIndep.lean`） |
| T82 | **二次 LDE**（高斯 Hanson–Wright）：`LDEQuad` 的 `StochDom` 版本 | `Gauss/LDEQuad.lean`（新建） | Claude Code | **完成**（矩递推与 p=1 精确恒等式；缺 `E[T^p] ≤ C_p E[Vq^p]`，文件头有草图） |
| T83 | 卸掉 `Green/EntryBound.lean` 的 `hIBP`（p.50 的高斯分部积分显式式） | `Gauss/IBP.lean`（新建） | **Cowork** | 进行中（T70 矩阵版已完成，用 `RBM.Gauss.matrixStein`） |
| T84 | **条件期望 = 坐标积分**：`E_k` 的定义与代数；`G^(k)` 与第 k 行严格独立 | `Gauss/CondRow.lean`（新建） | Claude Code | **完成**（`E_k` 为精确 Fubini；公共引理 `FinDepOffRow` 供 T81/T82/T86） |
| T85 | 替换误差 `\|G_ll − G^(k)_ll\| ≺ Ψ²`（由已证的 (4.9)） | `Gauss/MinorReplace.lean`（新建） | Claude Code | **完成**（含三元组版与 Ψ-级版；`|G_kk|` 下界由事件 (4.1) 读出，非额外假设） |
| T86 | **消失引理**：某指标只出现一次 ⟹ 期望 = O(替换误差) | `Gauss/FlucVanish.lean`（新建） | Claude Code | **完成**（替换后期望恰为 0；`B`/`ε` 与 T85 的 `≺` 之间的截断记账留给 T87/T88） |
| T87 | **计数**：按不同指标个数分层 ⟹ 额外一个 `Ψ` | `Gauss/FlucCount.lean`（新建） | Claude Code | **完成**（任意权重的分层矩界 + 两组均匀权重的计数；≺ 截断留给 T88） |
| T88 | 组装 ⟹ 卸掉 `EntryBound` 的 `hFA`（(4.12)），进而得 (4.5) | `Gauss/FlucAvg.lean`（新建） | Claude Code | **完成**（`hFA` 原签名卸掉、(4.5) 得证、可测性补齐；但 **(4.12) 有真实数学缺口**：T86 只迭代一阶，见 STATUS） |
| T78 | 连续归纳（bootstrap）原理：`φ` 连续 + 自改进 `φ ≤ C → φ ≤ B` ⟹ `φ ≤ B`；T75 卸停时 (5.43) 的分析内核，**不依赖 T72** | `Analysis/Bootstrap.lean`（新建） | Claude Code #2 | **完成**（`le_of_bootstrap`；T75 直接调用即可） |
| T89 | 维护：下沉矩阵可测性（`measurable_matrix_inv_apply` 在 `Gauss/FlucAvg.lean` 与 `Gauss/RowIndep.lean` 各证了一遍） | `Defs/MatrixMeasurable.lean`（新建） | Claude Code #2 | **完成** |
| T90 | 维护：全库重复扫描 + 下沉 `half_le_ellHat`（`Propagator/Edges.lean` 与 `Loop/Cor35.lean` 各一份）；其余重复项列入 STATUS 交各自负责人 | `Propagator/DecayComplex.lean` | Claude Code #2 | **完成**（`half_le_ellHat` 已下沉；其余 4 处列在 STATUS，归各自负责人） |
| T91 | 把 T81 的 `≺` 落成 `EntryBound` 需要的假设形式：高概率下的 `LDERow`/`LDECol`（含 `V = 0` 退化分支的 a.s. 论证） | `Gauss/LDEHyp.lean`（新建） | **Claude Code #2** | 已完成 |
| T92 | **对角 LDE**：`‖H_ii‖² ≺ S_ii`，即 `diag_bound_stochDom` 的 `hLdiag`（高斯情形，`H_ii = √u·ω⟨N,i,i,tt⟩` 是一维实高斯，直接用 T81 的矩机器 + `stochDom_of_momentDom`） | `Gauss/LDEDiag.lean`（新建） | **Claude Code #2** | 已完成 |
| T93 | **正混沌矩界 `E[T^p] ≤ C_p E[Vq^p]`**：T82 留下的唯一数学缺口（`LDEQuad.lean` 文件头「What is not done here」第 1 条）。做法：对 `E[T^p]` 再跑一次行 IBP，用导子 `D_l = r(∂_{a_l} − ε_l i ∂_{b_l})`（`D_l U_k = 0`、`D_l V̄_k = 0`、`D_l Ū_k = 2r²B̄_{kl}`、`D_l V_k = 2r²B_{lk}`），交叉项用 Cauchy–Schwarz 压成 `Vq·T`，再用 `young_pow` 闭合。**不碰 `Gauss/LDEQuad.lean`** | `Gauss/LDEQuadT.lean`（新建） | **Claude Code #2** | 已完成 |
| T94 | **把 `FlucVanish` 的机器迭代到 `2p` 阶**：卸掉 T88 隔离出来的 `hsmall`，让 (4.12) 真正成为定理 | `Gauss/FlucIter.lean`（新建） | Claude Code | 进行中 |
| T95 | **为高斯模型造 `RowChaos` 实例**（T82/T93 的 `LDEQuad.lean` 文件头「What is not done here」第 2 条）。关键：`B` 取**小方阵预解式** `(H^{(i)} − z)⁻¹` 而不是 `greenMinor`——它由 `norm_green_le` 全局有界 `η⁻¹`、连续、且只读 off-row 坐标（`Hflow_submatrix_congr_offRowCoord`），而 `greenMinor` 因 `G_ii` 无全局下界而无界；两者对**每个 ω** 相等，由 `inv_minor_resolvent` + T91 的 `green_diag_ne_zero`。`co`/`eps` 由 `Xentry` 的 `idxKey` 分支读出（同 T81）。**不碰 `Gauss/LDEQuad.lean`** | `Gauss/LDEQuadInst.lean`（新建） | **Claude Code #2** | 已完成 |
| T96 | **`hLquad` 的最后一段**：把 T95 的矩不等式 `E[ldeQuadLHS^p] ≤ C_p u^{2p} E[ldeQuadRHS^p]` 翻成 `diag_bound_stochDom` 要的 `StochDom P ldeQuadLHS ldeQuadRHS`。难点：控制 `ldeQuadRHS` 是**随机**的，`stochDom_of_momentDom`（T73）只接受确定性控制；走 `StochDom.of_det` 或先用好事件上的确定性控制夹住。**不碰 `Gauss/LDEQuad.lean`、`Green/EntryBound.lean`** | `Gauss/LDEQuadDom.lean`（新建） | **Claude Code #2** | 已完成 |
| T97 | **总装 (4.2)(4.3) 的高斯版**：把 T91/T92/T96 的四条 `StochDom`（`hLrow`/`hLcol`/`hLdiag`/`hLquad`）喂进 `entry_bound_stochDom` 与 `diag_bound_stochDom`，得到对高斯流无 LDE 假设的 Lemma 4.1。需核对 `zt E t` 的 `im ≠ 0`（由 `0 ≤ t < 1`）与各处 `Sblk` 参数一致。**不碰 `Green/EntryBound.lean`** | `Gauss/EntryBoundGauss.lean`（新建） | **Claude Code #2** | 进行中 |

---

## 路线决定（2026-09-19）

合作者倾向用附录 B 的一般 Fourier 方法，理由正确：闭式解是 **d=1 最近邻的偶然**，
一般 variance profile 或 d ≥ 2 时三项递推和特征方程都不存在，那条路断掉。

但有个事实：**在有限环上、d=1 时，Fourier 方法与闭式解是同一个计算。**
令 z = e^{ip}，(B.1) 是对 L 次单位根求和 `(1/L) Σ_{z^L=1} z^u g(z)`，
`g(z) = 1/(1 − (ξ/3)(1+z+z^{-1}))` 是 z 的有理函数，极点恰是 ρ 与 ρ^{-1}；
做留数/部分分式出来的就是 `ρ^u + ρ^{L-u}`。附录 B 引入无穷体积核、围道平移、
Poisson 求和、dyadic 分解，是因为**一般情形下做不了这个留数计算**（符号不再是有理函数）。

**当前决定：先用闭式把 (2.52)(2.53)(2.54) 完成，一般 Fourier 机器排在第 3 节之后做。**

这是**排期**，不是放弃，也不是留给以后的论文——一般机器仍在本项目的队列里（见下面 T8–T11），
只是先让第 3 节（树表示、Ward 恒等式、sum-zero —— 论文真正原创的部分）开工。
等第 3 节落地后回头补一般机器，届时 d=1 的闭式结果作为它的交叉验证。

T5（(B.1) 的 Fourier 表示）照做不误：它是 (3.48) 要用的结构性结果，
也是将来搭一般机器的地基，只是不再是 (2.52) 的路径。

---

## T5 — 附录 B (B.1) 的 Fourier 表示

新建 `RBM1D/Propagator/Symbol.lean`。**与 T1–T4 完全独立**，不依赖闭式解。

目标（论文 p.89）：设 `ζ = exp(2πi/L)`，特征标 `e_p(x) = ζ^(p·x)`。

1. `Shat L p = (1 + ζ^p + ζ^(-p))/3`，即论文的 `Ŝ(p) = (1 + 2cos p)/3`
2. `SB_mulVec_char`：`S^(B) *ᵥ e_p = Shat p • e_p`
   推导：`(S *ᵥ e_p)(x) = Σ_y sbKernel(x−y) ζ^{p y} = ζ^{p x} Σ_u sbKernel(u) ζ^{−p u}`
   —— 用 `RBM.sum_over_sbSupport`（已在 `Defs/Block.lean` 里）把求和展开成三项
3. `one_sub_xi_Shat_ne_zero`：`‖ξ‖ < 1` 时 `1 − ξ·Shat p ≠ 0`。
   注意 `‖Shat p‖ ≤ 1`（三项各模 ≤ 1/3），故 `‖ξ·Shat p‖ < 1`
4. `theta_apply_fourier`：`(Θ_ξ)_{xy} = (1/L) Σ_p ζ^{p(x−y)} / (1 − ξ Shat p)`

**下游用途**：(3.48) 用的是 Fourier 形式。衰减估计**不走**这条路（走闭式，见 T1–T4）。

可能要用的 Mathlib：`Complex.exp`、`Complex.isPrimitiveRoot_exp`、
`Finset.sum_nbij` / `ZMod` 上的特征标正交性。名字先 grep `.lake/packages/mathlib/Mathlib/`。

---

## T6 — Def 2.1(ii) 的确定性 ≺

新建 `RBM1D/Defs/Domination.lean`。**与其他任务完全独立**，纯定义 + 基本性质。

```lean
def DetDom (ξ ζ : ℕ → ℝ) : Prop := ∀ τ > 0, ∀ᶠ N in Filter.atTop, ξ N ≤ (N : ℝ) ^ τ * ζ N
```

要的基本性质：自反、传递、对加法与乘法封闭、常数倍不变、
`DetDom ξ ζ → DetDom (c • ξ) ζ`（c > 0）。

概率版本 Def 2.1 (i)(iii)(iv) **现在不做**，等随机层启动。
论文 (2.53)(2.54)(3.35)(3.36) 都是用 ≺ 陈述的，这一层是把它们写成论文原样的前提。

---

## 给 Claude Code 的一句话

> 读 `docs/TASKS.md`，做 T5（或 T6）。先在表格里把认领改成 Claude Code 并提交，
> 然后按 `CLAUDE.md` 的硬性规则做：不留 sorry、不发明 Mathlib 引理名、
> 每条主定理跑 `#print axioms`、偏离论文记进 `docs/paper-deltas.md`。

## 共享同一个工作树

两边指向的是**同一个文件夹、同一个 git 仓库、同一个工作树**，不是两份副本。
所以：工单不需要 push 对方就能看到；也**不需要 `git pull --rebase`**（没有第二份要拉）。

真正的风险因此不是合并冲突，而是三种并发争用：

1. **同时写同一个文件** —— 靠上面的按文件切分避免。共享文档（`docs/*.md`、
   `blueprint/src/content.tex`、`CLAUDE.md`）改动要小、要立刻提交，不要长时间持有。
2. **git index.lock 争用** —— 两边同时 `git add`/`commit` 会撞。撞到就等几秒重试；
   若残留 `.git/index.lock` 且确认没有别的 git 在跑，删掉它即可。
3. **绝不用 `git add -A`** —— 它会把对方正在写的文件暂存进你的提交。
   **只按文件名 `git add` 自己的那几个。**
4. **`build.log` 是共用的** —— `watch.sh` 全量编译，两边的报错都会写进同一个文件。
   读日志时按文件名过滤自己那部分，别把对方进行中的报错当成自己的。

`watch.sh` 只要开着，任何一边改动都会触发重编，这对双方都有用。
单文件快速检查用 `lake env lean RBM1D/Propagator/Xxx.lean`，它不抢 lake 的构建锁。

### 核实过的事实（2026-09-19）

`git worktree list` 只列出一个工作树；`git rev-list --count origin/main..HEAD` 与反向都是 0。
所以确实是**一个共享工作树**，没有第二份克隆。

若 `git pull --rebase` 看起来"带回"了对方的 commit：那是 rebase 重放**本地**提交时
git 列出的它们，不是从远端取回的新东西。同一个树里拉不回自己已有的提交。
这条无害，照做也行。


---

## T12 — 数值回归测试

新建 `RBM1D/Test/Numeric.lean`。`CLAUDE.md` 里 Phase 1 完成标准的第 3 条。

`L = 5, 7`、`ξ = 1/2` 时在 `ℚ` 上验证 `(1 − ξ·S^(B))·Θ = I`。做法：
用 `Matrix (Fin L) (Fin L) ℚ` 显式写出 `1 − ξS`，用 `decide` / `norm_num` 验证它乘以
显式给出的逆等于单位阵。**不必**与 `RBM.Theta` 直接挂钩（那是 ℂ 上的、noncomputable），
这条的价值在于它独立于整条符号推导链，能抓住定义层面的抄写错误。

闭式解现在已是定理（`kern_defect` 若 A 抄错就证不出来），所以这条不再是防抄错的必需品，
但作为独立回归测试仍然值得有。

---

## T13 — Theorem 2.2：由 local law 推 delocalization

新建 `RBM1D/Delocalization.lean`。**与传播子那条线完全独立**，只用 Mathlib 的 Hermitian 谱定理。

论文 p.9 的论证（(2.10)）：设 `H` Hermitian，`λ_k`、`ψ_k` 是特征值与单位特征向量，
`G(z) = (H − z)^{-1}`，`η = Im z > 0`。则对任意 `x`

    |ψ_k(x)|² ≤ Σ_l η²|ψ_l(x)|² / ((λ_k − λ_l)² + η²) ≤ η · Im G_xx(λ_k + iη)

**第一个不等号**：右边的和里 `l = k` 那一项就是 `|ψ_k(x)|²`（分母 `η²`），其余项非负。
**第二个等号/不等号**：谱分解给出 `Im G_xx(E + iη) = Σ_l η|ψ_l(x)|²/((λ_l − E)² + η²)`，
取 `E = λ_k` 即得。

于是：若 local law 给出 `‖G − m‖_max ≺ 1` 且 `m = O(1)`，则 `Im G_xx = O(1)`，
代入得 `|ψ_k(x)|² ≤ Cη`。论文取 `η = N^{-1+τ}` 得 Thm 2.2。

Mathlib 里要用的：`Matrix.IsHermitian.spectral_theorem`、`Matrix.IsHermitian.eigenvalues`、
`Matrix.IsHermitian.eigenvectorUnitary`（名字先 grep 确认）。

**建议先做纯谱论的那一半**（上面两个不等式），把 local law 作为假设写进陈述，
不要去碰随机层。这样这条定理现在就能无 sorry 地成立。

---

## T15 — §2.1 的模型层

新建 `RBM1D/Defs/Model.lean`。论文 p.6–7。纯定义 + 平凡性质，但下游全要用。

* `W L : ℕ`，`N = W * L`
* 块 `I_a = {aW, aW+1, …, aW+W−1}`，`a : ZMod L`
* `S_W : Matrix (Fin W) (Fin W) ℂ`，`(S_W)_{αβ} = W⁻¹`（全 1 矩阵除以 W）
* `S = S^(B) ⊗ S_W`（Kronecker 积，Mathlib `Matrix.kroneckerMap` / `⊗ₖ`）
* `E_a`：(2.5) 的块投影，`(E_a)_{ij} = δ_{ij} · W⁻¹ · 1(i ∈ I_a)`
* 要的性质：`Σ_a E_a = W⁻¹ · I`（Lemma 3.6 Step 1 用）、`E_a` 自伴、
  `S` 的行和为 1（由 `S^(B)` 与 `S_W` 的行和各为 1）

**注意**：`RBM.SB` 已经在 `Defs/Block.lean` 里，直接复用，不要重新定义。

---

## T16 — Def 2.9/2.10：loop 的指标数据与 cut-and-glue 算子

新建 `RBM1D/Loop/Index.lean`。**这是第 3 节的地基**，也是整个项目里最值得先做对的一块。

难点不在数学，在**指标记账**。先不要碰 Green 函数，只把 `(σ, a)` 上的组合操作定义对。

数据：`σ : Fin n → Bool`（`true` = `+`），`a : Fin n → ZMod L`。建议用
`List Bool × List (ZMod L)` 并带长度相等的证明，或者 `n` 显式的 `Fin n →` 函数——
**哪种更好用由你判断，但要能方便地做"取前 k 段、接上后一段"这类操作**，
所以 `List` 大概率更合适。

论文 Definition 2.10 的三个算子（1-based 记号，`n` = 当前长度）：

**`G^{(a)}_k`**（1 ≤ k ≤ n）：把第 k 条 G 边劈开插入 `E_a`。长度 n → n+1。
    σ′ = σ 在第 k 位插入一个 σ_k 的副本
    a′ = a 在第 k 位插入 a
论文例子（n = 4, k = 2）：
    σ = (σ₁,σ₂,σ₃,σ₄) → σ′ = (σ₁,σ₂,σ₂,σ₃,σ₄)
    a = (a₁,a₂,a₃,a₄) → a′ = (a₁,a,a₂,a₃,a₄)

**`G^{(a),L}_{k,l}`**（1 ≤ k < l ≤ n）：剪开第 k、l 条 G 边得两条链，
把**含 `E_{aₙ}` 的那条**（左链）的两端粘起来并在粘点插入新的 `E_a`。长度 k+n−l+1。
    σ′ = (σ₁,…,σ_k) ++ (σ_l,…,σ_n)
    a′ = (a₁,…,a_{k−1}) ++ (a) ++ (a_l,…,a_n)
论文例子（n = 5, k = 3, l = 5）：
    σ′ = (σ₁,σ₂,σ₃,σ₅)，a′ = (a₁,a₂,a,a₅)

**`G^{(a),R}_{k,l}`**：粘**不含 `E_{aₙ}` 的那条**（右链）。长度 l−k+1。
    σ′ = (σ_k,…,σ_l)
    a′ = (a_k,…,a_{l−1}) ++ (a)
论文例子（n = 5, k = 3, l = 5）：
    σ′ = (σ₃,σ₄,σ₅)，a′ = (a₃,a₄,a)

**必须证的性质**（这些是后面 Lemma 3.4、3.6 反复用的）：
1. 三个算子的**输出长度**：分别是 `n+1`、`k+n−l+1`、`l−k+1`
2. **两条链长度之和**：`(k+n−l+1) + (l−k+1) = n+2`
   —— 论文 (2.48) 之所以是二次方程就因为这个
3. 左右链的长度**都 ≤ n**（当 `1 ≤ k < l ≤ n` 时），这是 §2.4 末尾说"K 可以按长度归纳求解"的依据。
   注意 `k=1, l=n` 时右链长度恰好 `= n`，**等号可以取到**，归纳要按别的量递减——
   论文的说法是「the lengths are no greater than the length of K」
4. 论文 Figure 1、2、3 的三个例子，写成 `example ... := by decide` 或 `rfl` 当回归测试

**建议**：先把长度性质做对，`example` 跑通论文的三个例子，再谈别的。
这一层做扎实，第 3 节会顺很多；做糙了后面全是坑。

---

# 第二批工单（2026-09-19 开出）

T5、T6、T12、T13、T15、T16 全部完成，`lake build` 干净、170 条定理、0 sorry。
下面四条把战线推到第 3 节。**编号 T14 当初空缺，不补**，直接从 T17 开始。

**建议顺序：T18 → T17 → T19 → T20。**
把 T18 放最前面不是因为它最容易，而是因为它的第一步是一个**核对**：
它会立刻告诉我们 `Loop/Index.lean` 里 cut-and-glue 的下标约定是不是对的。
这个约定错了的话，第 3 节整个建在沙子上，越晚发现越贵。

---

## T18 — Def 2.12 原始方程 + Example 2.15（**优先，先做核对**）

新建 `RBM1D/Loop/Primitive.lean`。论文 p.18（Def 2.12）、p.20（Example 2.15）。
依赖 `Loop/Index.lean`（你自己写的）和 `Propagator/Basic.lean` + `Propagator/Deriv.lean`（我写的）。
**这是 loop 层与传播子层第一次接头。**

### 第一步（在写任何证明之前）：下标核对

论文 (2.48) 是

```
d/dt K_{t,σ,a} = W · Σ_{1≤k<l≤n} Σ_{a,b}  (G^{(a),L}_{k,l} ∘ K_{t,σ,a}) · S^(B)_{ab} · (G^{(b),R}_{k,l} ∘ K_{t,σ,a})
```

其中 `G^{(a),L}_{k,l} ∘ K_{t,σ,a} := K_{t, G^{(a),L}_{k,l}(σ,a)}`（(2.49)）。

论文 (2.55) 又独立地写出了 n = 2 的展开：

```
d/dt K_{t,σ,(a₁,a₂)} = W · Σ_{a,b}  K_{t,σ,(a₁,a)} · S^(B)_{ab} · K_{t,σ,(b,a₂)}
```

**请用你的 `cutGlueL` / `cutGlueR` 把一般式在 n = 2（只有 k=1, l=2 一项）展开，
逐字对照 (2.55)。** 我按论文 Def 2.10 的公式手算的结果是

* 左链 `G^{(a),L}_{1,2}(σ,(a₁,a₂))` = `(σ₁,σ₂), (a, a₂)`
* 右链 `G^{(b),R}_{1,2}(σ,(a₁,a₂))` = `(σ₁,σ₂), (a₁, b)`

即一般式给出 `Σ_{a,b} K_{σ,(a,a₂)} · S_{ab} · K_{σ,(a₁,b)}`，
而 (2.55) 给出 `Σ_{a,b} K_{σ,(a₁,a)} · S_{ab} · K_{σ,(b,a₂)}`。
两者相等，靠的是 **`S^(B)` 对称 + 把哑指标 a↔b 对换**（`RBM.SB_isSymm` 已有）。

要做的事：

1. 把这个相等**证出来**（不是口头核对）：写成一条引理，
   两边都用你的 `cutGlueL/cutGlueR` 表达，用 `Finset.sum_comm` + `SB_isSymm` 走通。
2. **如果对不上**：说明 `Loop/Index.lean` 的约定与论文差一个方向/一个偏移。
   这时候改 `Loop/Index.lean`（那是你的文件，随便改），并把差异记进 `docs/paper-deltas.md`，
   注明是「我们的约定」还是「论文的笔误」。**不要为了让它对上而临时改 (2.55) 的抄写。**

这一步做完，无论结果如何，都先提交一次。

### 第二步：把 (2.48) 写成一个谓词

```lean
def IsPrimitive (W : ℕ) (K : ℝ → LoopIdx (ZMod L) → ℂ) : Prop :=
  (∀ t (I : LoopIdx (ZMod L)), I.WF → HasDerivAt (fun s => K s I) (rhs W K t I) t) ∧
  (∀ I, I.WF → K 0 I = (W : ℂ)⁻¹ ^ (I.length - 1) * (∏ ...) * (if 所有 aᵢ 相等 then 1 else 0))
```

初值（论文 Def 2.12 下面那行）：`K_{0,σ,a} = W^{−n+1} · Π_k m(σ_k) · 1(a₁ = ⋯ = aₙ)`。
`m(σ)` 现在还没有（那是 T19 的 `m_sc` / `m^{(E)}`），所以**把 `m : Bool → ℂ` 作为参数传进来**，
不要 `sorry`，也不要提前定义它。等 T19 落地再在别处实例化。

n = 1 的特例（`K_{t,+,a} = m`，`K_{t,−,a} = m̄`，论文 (2.49) 之后那句）单独写，
不要试图从 (2.48) 推出来——那条求和在 n=1 时是空和。

### 第三步：Example 2.15（本工单的里程碑）

论文 (2.57)：`K_{t,σ,(a₁,a₂)} = W⁻¹ m₁ m₂ (Θ^{(B)}_{t·m₁m₂})_{a₁a₂}`，`mᵢ = m(σᵢ)`。

验证它满足 (2.55)。链条是：

* `d/dt (Θ_{t·m₁m₂})_{a₁a₂} = m₁m₂ · (Θ S Θ)_{a₁a₂}(t·m₁m₂)`
  —— 用我写的 `RBM.hasDerivAt_Theta_apply`（**逐项形式，ℂ 值**；矩阵值的版本因为
  Mathlib 的拓扑实例菱形做不出来，别去试，理由记在 `docs/paper-deltas.md`）
  再复合 `fun t => t * (m₁*m₂)`（`HasDerivAt.comp` 或 `HasDerivAt.mul_const`）
* 右端 `W · Σ_{a,b} W⁻¹m₁m₂(Θ)_{a₁a} S_{ab} W⁻¹m₁m₂(Θ)_{b a₂}`
  `= W⁻¹ (m₁m₂)² (Θ·S·Θ)_{a₁a₂}`，两个求和正好是两次矩阵乘法
  （`Matrix.mul_apply` 两次 + `Finset.sum_comm`）
* 初值：`Θ_0 = 1`，所以 `K_0 = W⁻¹ m₁m₂ δ_{a₁a₂}`，与 Def 2.12 的初值在 n=2 时一致。
  `Theta` 在 ξ=0 的值：`Ring.inverse (1 - 0 • SB) = Ring.inverse 1 = 1`，`simp` 应该就够。

**定义域**：`Θ_ξ` 只在 `‖ξ‖ < 1` 有意义，而 `HasDerivAt` 要的是**邻域**上的信息。
所以假设写成 `hξ : ‖t * m₁ * m₂‖ < 1`，并利用 `{ξ : ‖ξ‖ < 1}` 是开集
（`Metric.isOpen_ball` / `isOpen_lt`）把结论从"一点"提升到"邻域"。
真实情形下 `‖m‖ = 1`、`t < 1`（T19 会给出），所以这个假设不是空的。

论文 (2.58) 把 σ=(+,−) 与 σ=(+,+) 两种情形写开了，那只是把 `m₁m₂` 换成 `|m|²` 或 `m²`，
可以作为两条 `example` 收尾，不必单独立定理。

---

## T17 — Lemma 3.2 的组合内容：`TSP` = 无交叉对角线集合

新建 `RBM1D/Loop/Crossing.lean`。论文 p.27–28（Def 3.1、Lemma 3.2）。**纯组合，全可判定，零分析。**

### 关键的建模决定（请照做，并把理由记进 `docs/paper-deltas.md`）

论文的 `T SP (P_a)` 是「多边形的典范划分的等价类所对应的树」的集合。
**我们不形式化平面多边形的剖分**——那要拓扑，代价与收益完全不成比例。

Lemma 3.2 恰好给了我们逃生口。它说三件事：

1. `Γ'_a = Γ_a ⟺ F(Γ_a) = F(Γ'_a)`：树被它的非相邻配对集合 `F` **完全决定**；
2. `F(Γ_a)` 里没有交叉对；
3. 反过来，任何无交叉的 `F*` 都能被某个典范划分实现。

合起来就是一个双射：`T SP (P_a) ≃ {F ⊆ 对角线集合 : F 无交叉}`。
所以我们**把右边当作 `TSP` 的定义**，把 Lemma 3.2 记作「这是论文授权的等价定义」。
论文没有把它当引理证（它的证明是几何归纳），我们也不证——我们是**引用**它做定义。
`docs/paper-deltas.md` 里写清楚：这不是偏离，是把论文的分类定理当成定义，
代价是 Def 3.1 的几何内容不在形式化范围内，收益是第 3 节剩下的部分全部可判定。

### 内容

指标用 0-based（`Loop/Index.lean` 已经是 0-based 的 `List`，保持一致；
论文是 1-based，在文件头注释里写明这个平移）。

```lean
-- n 边形的对角线：{i,j}，i < j，且在 Z_n 里不相邻（注意 {0, n−1} 是边不是对角线）
def IsDiag (n : ℕ) (i j : Fin n) : Prop := i < j ∧ j.val ≠ i.val + 1 ∧ ¬(i.val = 0 ∧ j.val = n - 1)

-- 论文的交叉条件：i < k < j < l 或 k < i < l < j（序在 ℤ 上，不是 Z_n 上）
def Crossing (e f : Fin n × Fin n) : Prop := ...

def CrossingFree (F : Finset (Fin n × Fin n)) : Prop := ∀ e ∈ F, ∀ f ∈ F, ¬ Crossing e f

def TSP (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  ((diagonals n).powerset).filter CrossingFree
```

每个谓词都要 `DecidablePred` 实例（`decide` 能跑是这条工单的全部价值所在）。

### 必须证 / 必须跑的

1. `Crossing` 对称；**共端点不算交叉**（论文的 `i<k<j<l` 是严格不等号）——
   单独写一条 `example` 钉死这一点，这是最容易写错的地方。
2. `TSP 3`：只有 `∅`（三角形没有对角线）。
3. `TSP 4`：恰好 3 个元素，`∅`、`{(0,2)}`、`{(1,3)}`。
   —— **这就是论文 Figure 6 的三张图**，是这条工单与论文对接的锚点。
   注意 `(0,2)` 与 `(1,3)` 交叉，所以不能共存，这解释了为什么 n=4 只有 3 张而不是 4 张。
4. **强回归测试**：`(TSP 5).card = 11`、`(TSP 6).card = 45`。
   带非交叉对角线的凸多边形剖分数是 1, 3, 11, 45, 197, …（小 Schröder 数）。
   定义只要写偏一点点——把边误当成对角线、交叉条件用了 `≤`、忘了 `mod n` 的约定——
   这几个数立刻就不对。`decide` 在 n=6 时是 2^9 = 512 个子集，跑得动；
   n=7 若超时就别做，前四个数已经足够。
   这个测试**必须过**，不要用 `native_decide`（`CLAUDE.md` 的公理规则）。
5. 可选：`∀ F ∈ TSP n, F.card ≤ n - 3`。

**不要做**：树结构、内部顶点、`E(Γ)`、平面性。那些在 T20 里以另一种方式出现。

---

## T19 — Lemma 2.8：`m_sc`、`m^{(E)}` 与 `t` 的代数

新建 `RBM1D/Defs/Semicircle.lean`。论文 p.15。**与其他一切独立**，纯复数代数。
下游：Def 2.12 的初值、Example 2.15 里的 `m₁m₂`，以及 T18 需要的 `‖t·m₁m₂‖ < 1`。

### 内容

1. `m^{(E)}`：论文说它是 `m(m + E) = −1` 的解且 `Im m > 0`。对实的 `E`、`|E| < 2`，
   显式就是 `m^{(E)} = (−E + i√(4 − E²))/2`。给出定义并证：
   * `mE E * (mE E + E) = -1`
   * `0 < (mE E).im`（需要 `|E| < 2`）
   * **`‖mE E‖ = 1`** ← 这条最有用：`|m|² = (E² + (4−E²))/4 = 1`。
     T18 要的 `‖t·m₁m₂‖ = t < 1` 就是靠它。
2. `m_sc z`：半圆律的 Stieltjes 变换，`m² + z m + 1 = 0`、`Im m > 0`（`Im z > 0` 时）。
   * `msc z * (msc z + z) = -1`
   * `0 < (msc z).im` 当 `0 < z.im`
   * **`‖msc z‖ < 1`** 当 `0 < z.im`（由 `msc·(msc + z) = −1` 与 `|msc + z| > |msc|` 之类推）
3. Lemma 2.8 的构造：给定 `0 < Im z`，令
   `E := −2 · (msc z).re / ‖msc z‖`（**实数**）、`t := (msc z)^2 / (m^{(E)})^2`。
   要证：
   * `t = ‖msc z‖ ^ 2`，特别地 `t` 是**实的、正的、小于 1** 的。
     （因为 `m^{(E)} = msc z / ‖msc z‖`——这正是论文证明里那句
     「`m^{(E)} = m_sc(z)/|m_sc(z)|`」，先把这条证出来，后面全是它的推论。）
   * (2.38)：`msc z = Real.sqrt t * m^{(E)}`
   * (2.37)：`z = t^{−1/2} · z_t^{(E)}`。
     **`z_t^{(E)}` 的定义在 §2.4 里、(2.37) 之前**，去论文里把它照抄出来，
     不要从 Lemma 2.8 的证明里反推（证明里出现的是 `t^{−1/2}(E + m^{(E)}) − √t·m^{(E)}`，
     反推容易差一项）。

### 范围限制

论文 Lemma 2.8 还有 `|E| ≤ 2 − cκ`、`t ≥ c_κ`、`c_κ Im z ≤ Im z_t ≤ c_κ^{−1} Im z`（(2.40)）
这些**依赖 κ 的定量界**。那是实分析，且下游只在随机层用。
**这次只做上面的代数恒等式**，(2.40) 标为可选，做不出来不算没完成，
在文件末尾留一条注释说明它被推迟到哪个阶段即可（**不要写 `sorry`**，写注释）。

---

## T20 — Def 3.3：星图情形与 n=4 的三张图（依赖 T17）

新建 `RBM1D/Loop/Tree.lean`。论文 p.29–30（Def 3.3、Lemma 3.4 之后那个显式公式）。
**探索性工单，边界比前三条模糊，允许你判断后调整，但请把判断写进 `docs/STATUS.md`。**

论文的 `Γ_a^{(b)}(t,σ) = Π_{e ∈ E(Γ)} (f_t(e))_{e_i e_f}`，其中
`f_t(e) = Θ^{(B)}_{t m_k m_l} − 1(|k−l| ≠ 1 mod n)`，`R_k ∩ R_l = e`；
即**边界边**（一端在多边形上）取 `Θ`，**内部边**（两端都是内点）取 `Θ − 1`。
然后 `Γ_{t,σ,a} := Σ_{b ∈ Z_L^m} Γ_a^{(b)}(t,σ)`。

### 建议的做法

**不要**去构造树的顶点集与边集。走论文自己在 Lemma 3.2 证明里用的那条归纳：
`F = ∅` 时是星图；`{i,j} ∈ F` 时把多边形劈成两个小多边形，接缝上挂一条 `Θ_{t m_i m_j} − 1`。
也就是说，**把 `Γ` 的值直接按 `F` 递归定义**，跳过图论。

这次只要求两件事，足够把设计验证掉：

1. **星图**（`F = ∅`，对应 `TSP` 里的 `∅`）：
   `Γ^star_{t,σ,a} = Σ_{b ∈ Z_L} Π_{i=0}^{n−1} (Θ_{t·m_{i−1} m_i})_{a_i b}`（下标 mod n）。
   写出定义并证一条平凡但有用的性质：`n = 2` 时它等于 `(Θ_{t m₁m₂} · Θ_{t m₁m₂})_{a₁a₂}`……
   —— **先自己核对这一条对不对**，n=2 的多边形是退化的（二角形），
   论文的 Lemma 3.4 只声称 `n ≥ 2`，但 n=2 的 `T SP` 只有一个元素，
   而 Example 2.15 给的是 `W⁻¹m₁m₂Θ` 而不是 `Θ²`。
   **这两者不一致的话，说明 n=2 要特判**，把结论记进 `docs/paper-deltas.md`。
   （我的猜测：n=2 的多边形只有两条边、没有内点，`Γ` 应当是 `Θ` 而非 `Θ²`，
   星图公式在 m=0 个内点时求和是空的。请你算清楚，别信我的猜测。）
2. **n = 4 的显式公式**：论文在 Figure 6 之后给出
   ```
   Σ_{Γ ∈ TSP} Γ_a(t,σ) = Σ_{b₁b₂b₃b₄} (Π_{i=1}^{4} (Θ_{t m_{i−1} m_i})_{a_i b_i})
       × ( δ_{b₁b₂b₃b₄} + δ_{b₁b₂}δ_{b₃b₄}(Θ_{t m₁m₃} − 1)_{b₁b₃}
                        + δ_{b₁b₄}δ_{b₂b₃}(Θ_{t m₂m₄} − 1)_{b₁b₂} )
   ```
   三项正好对应 T17 里 `TSP 4` 的三个元素 `∅`、`{(0,2)}`、`{(1,3)}`。
   把它写成 Lean 里的一条 `def` 或 `theorem`（哪种由你定），
   **作为将来一般定义的验收标准**：一般定义写好之后，它在 n=4 必须化归到这个式子。

Lemma 3.4 本身（树表示成立，即这个和真的解原始方程）**这次不做**，
它需要 (2.48) 的解的唯一性（Grönwall），排在 T18 之后单独开工单。

---

## 给 Claude Code 的一句话（第二批）

> 读 `docs/TASKS.md` 的「第二批工单」，按 T18 → T17 → T19 → T20 的顺序做。
> 开工前先在表格里把 `认领` 改成 Claude Code 并单独提交这一行的改动。
> T18 的第一步是下标核对，核对完先提交一次再往下走。
> 规则照 `CLAUDE.md`：不留 sorry、不发明 Mathlib 引理名（先 grep 或 `#check`）、
> 每条主定理跑 `#print axioms`、`decide` 不用 `native_decide`、
> 偏离论文或建模决定记进 `docs/paper-deltas.md`、只 `git add` 自己的文件名。

---

# 第三批工单（2026-09-19，第二批全部完成后开出）

T17–T20 全部完成，218 条定理、0 sorry、`lake build exit=0`。
T20 的两个副产品值得表扬，也决定了这一批的排法：

* **论文 Figure 6 之后的 n=4 显式式有下标笔误**（边界因子应是 `Θ_{t m_i m_{i+1}}` 而非
  `Θ_{t m_{i−1} m_i}`），并且用有限差分做了数值判据（`1e−11` vs `1e−2`）——
  这正是 `CLAUDE.md` 说的「小错自行修改并记档」的标准做法。
* **n = 2 必须特判**：二角形的树是单条边，不是星图；`not_hasDerivAt_starK_two`
  用一条**否定性**定理把这件事钉死了，而不是含糊带过。

**建议顺序：T23 → T21 → T22 → T24。**
T23 放最前面，因为它是**第一次真正检验树表示**：n=2 退化（Example 2.15 已做），
n=4 只是核对了一个静态恒等式，只有 n=3 才第一次出现「星图 + 一个内点」并且
必须真的满足 (2.48)。如果 T23 过了，Lemma 3.4 的形状就基本确认了；如果不过，
现在发现比在一般定义写完之后发现便宜一个数量级。

---

## T23 — Example 2.16（n = 3）：第一个非平凡的树表示实例（**优先**）

新建 `RBM1D/Loop/Example3.lean`。论文 p.20–21（Example 2.16，紧接 Example 2.15）。

### 第一步：又一次下标核对（照 T18 的做法）

论文 (2.48) 在 n=3 时展开为三项（`(k,l) = (1,2), (2,3), (1,3)`）：

```
d/dt K_{t,σ,a} = W Σ_{b₁c₁} K_{t,(σ₁,σ₂),(a₁,b₁)} S_{b₁c₁} K_{t,σ,(c₁,a₂,a₃)}
               + W Σ_{b₂c₂} K_{t,(σ₂,σ₃),(a₂,b₂)} S_{b₂c₂} K_{t,σ,(a₁,c₂,a₃)}
               + W Σ_{b₃c₃} K_{t,(σ₃,σ₁),(a₃,b₃)} S_{b₃c₃} K_{t,σ,(a₁,a₂,c₃)}
```

用你的 `cutGlueL` / `cutGlueR` 展开一般式，证明它等于上式（就像 `primRhs_two` 那样）。
**注意第三项**：论文里它的短链是 `(σ₃,σ₁)`，即**跨过端点回绕**的那一对——
这是 `k=1, l=n` 的情形，也正是 `length_cutGlueR_one` 说右链长度 `= n` 的那一项。
如果只有它对不上，问题一定在回绕的约定上。对不上就改 `Loop/Index.lean` 并记 `paper-deltas.md`。

### 第二步：用 (2.57) 改写

论文接着用 Example 2.15 把三项里的短链 `K_{(σᵢ,σⱼ),(aᵢ,b)}` 换成 `W⁻¹mᵢmⱼ(Θ_{t mᵢmⱼ})_{aᵢb}`，
于是 `W · W⁻¹ = 1`，得到

```
d/dt K_{t,σ,a} = Σ_{c₁} (m₁m₂ Θ_{t m₁m₂} S^(B))_{a₁c₁} K_{t,σ,(c₁,a₂,a₃)} + （另两项同理）
```

把这一步也证出来（用你已有的 `kTwo`）。

### 第三步：树表示在 n=3 成立（**本工单的里程碑**）

`TSP 3 = {∅}`（`TSP_three` 已证），所以 Lemma 3.4 在 n=3 就是星图一项：

```
K_{t,σ,(a₁,a₂,a₃)} = m₁m₂m₃ · W⁻² · Σ_b (Θ_{t m₁m₂})_{a₁b} (Θ_{t m₂m₃})_{a₂b} (Θ_{t m₃m₁})_{a₃b}
```

（下标用 T20 里**更正过**的 `Θ_{t m_i m_{i+1}}` 约定，不要用论文 Figure 6 后那个笔误版。）

要证：它满足第二步得到的方程，且 `t = 0` 时等于 Def 2.12 的初值
`W⁻² m₁m₂m₃ · 1(a₁=a₂=a₃)`（`Θ_0 = 1`，三个 Θ 各给一个 δ）。

求导链条：对 `Σ_b` 里的三因子乘积用乘法法则，每个因子按 (2.51) 求导得
`mᵢmⱼ(Θ S Θ)`，正好凑出三项。用 `RBM.hasDerivAt_Theta_apply` + `HasDerivAt.mul`
（三项乘积要嵌套两次）。**这是整个项目里第一次出现「树的每条边各贡献一项求导」的结构**，
也是 Lemma 3.4 一般证明的缩影——把它做干净，一般证明就是同一段论证加一层归纳。

如果哪一步对不上，**先用数值验**（你已经写了 `scripts/tree_ode_check.py`），
确定是论文的问题还是我们的问题，再动手改，并记进 `docs/paper-deltas.md`。

---

## T21 — 一般树值 Γ 的递归定义（Def 3.3 完整版）

继续 `RBM1D/Loop/Tree.lean`（你自己的文件）。

按 T20 定下的路线：**不构造树的顶点集与边集**，直接对无交叉集合 `F` 递归定义 Γ 的值。

```
Γ(n, σ, a, F) :=
  | n ≤ 2            => 单边：(Θ_{t m₀ m₁})_{a₀ a₁}                （T20 的 kTwo_eq_edge）
  | F = ∅, n ≥ 3     => 星图：Σ_b Π_i (Θ_{t m_i m_{i+1}})_{a_i b}   （T20 的 starGamma）
  | {i,j} ∈ F        => Σ_{x,y} Γ(左多边形, F 左) · (Θ_{t m_i m_j} − 1)_{x y} · Γ(右多边形, F 右)
```

要点：

1. **递归下降**。`{i,j}` 非相邻 ⇒ 两个小多边形的边数分别是 `j−i+1` 和 `n−(j−i)+1`，
   **都 ≤ n−1**。所以 `termination_by n` 就够，不必对 `F.card` 做字典序。
   （相邻对不在 `diagonals` 里，这正是 `IsDiag` 排除相邻的原因——请在注释里写明这一点，
   它是终止性的全部依据。）
2. **`F` 的分裂**。`F \ {(i,j)}` 里的每个对角线，因为与 `(i,j)` 不交叉，必然整个落在
   左边或整个落在右边。这条「不交叉 ⇒ 可分」是递归良定义的关键，**要作为引理证出来**，
   不要 `decide` 糊过去（`n` 是变量）。
3. **良定义性**。选哪个 `{i,j}` 展开会影响结果吗？数学上不会，但 Lean 里若用
   「取 `F` 的某个元素」就得证明与选择无关。**建议避开这个坑**：按某个固定规则选
   （例如字典序最小的对角线），这样定义是确定的，「与选择无关」就不必证。
   代价是后面要用「换个顺序展开」时得补引理——先记在文件注释里，别现在做。
4. 用 `List` 承载 `(σ, a)`（与 `Loop/Index.lean` 一致），切片才方便。

**验收标准（已经现成）**：`gammaFour_eq`。一般定义在 `n = 4` 必须化归到 T20 已证的
那个三项和。做完第一件事就是把这条接上。

---

## T22 — (2.48) 解的唯一性

新建 `RBM1D/Loop/Unique.lean`。Def 2.12 说 K 是 (2.48) 的**唯一**解，我们目前只有谓词
`IsPrimitive`，没有唯一性。Lemma 3.4 的整个策略（把树和当定义、证它满足方程、用唯一性
得到它就是 K）就卡在这一条上。

### 先证这条结构引理（它决定了证明的形状）

由 `length_cutGlueL_add_length_cutGlueR`：(2.48) 右端每一项的两条链长度满足
`len_L + len_R = n + 2`，且都 `≥ 2`、都 `≤ n`。于是：

* **n = 2**：只有 `(2,2)`，方程对长度-2 的未知量是**二次**的（Riccati 型）；
* **n ≥ 3**：含长度-n 因子的项，另一个因子长度必为 2。所以固定住所有长度 `< n` 的解之后，
  长度-n 的方程是**线性**的（系数由长度-2 的解给出）+ 低阶源项。

**把这条写成引理**（对长度做分类即可，纯组合），它是下面一切的依据，也值得单独立个名字。

### 然后

1. **n = 2 的唯一性**：两个解之差满足 `d/dt D = 双线性项`，在解有界的时间区间上用 Grönwall。
   Mathlib 里找 `ODE_solution_unique` / `ODE_solution_unique_of_mem_Icc` / `norm_le_gronwallBound_of_norm_deriv_right_le`
   （**名字先 grep**，别猜）。有界性作为假设写进去即可，不要去证解的存在性。
2. **n ≥ 3 的唯一性**：对 `n` 归纳，用上面的线性结构 + 线性 ODE 的唯一性。

**不要**做存在性。论文的存在性是靠树公式给出的（Lemma 3.4），我们也走这条路。

---

## T24 — 公理审计、删 Probe、linter 清理

三件互不相干的收尾，凑一条工单，做完就把仓库的卫生拉到位。

1. **公理审计**。新建 `RBM1D/Test/Axioms.lean`，对每条主定理跑 `#print axioms`。
   `CLAUDE.md` 要求只出现 `propext / Classical.choice / Quot.sound`。
   但目前是靠人读 build.log——**请改成硬性的**：查一下 Lean 有没有
   `#guard_msgs in #print axioms foo` 这种写法能让「冒出新公理」直接编译失败
   （先 `#check` / grep `.lake/packages/` 确认语法存在再用；不存在就退回
   `#print axioms` 并在文件头写明需要人工核对）。这是整个项目最重要的一条回归防线。
2. **删 `RBM1D/Probe.lean`**（原 T7）。先把里面还有价值的 `#check` 结论
   （那些"这个引理在 Mathlib 里叫什么"的记录）转成 `docs/mathlib-api.md` 的条目，再删文件，
   同时从 `RBM1D.lean` 的 import 里摘掉。
3. **linter 清理**：`automatically included section variable(s) unused`、
   `if_neg/if_pos has been deprecated`、`This line exceeds the 100 character limit`。
   **只动你自己写的文件**：`Defs/{Block,Dist,Domination,Model,Semicircle}.lean`、
   `Loop/*.lean`、`Propagator/{Basic,Bounds,Deriv,Root,Support,Symbol}.lean`、
   `Delocalization.lean`、`Test/*.lean`。
   **`Propagator/Decay.lean` 是我的，别碰**（我在里面做 (2.52)）。

---

## 给 Claude Code 的一句话（第三批）

> 读 `docs/TASKS.md` 的「第三批工单」，按 T23 → T21 → T22 → T24 做。
> 开工前先把表格里的 `认领` 改成自己并单独提交这一行。
> T23 的第一步和 T18 一样是下标核对，核对完先提交再往下。
> 规则照 `CLAUDE.md`：不留 sorry、不发明 Mathlib 引理名、每条主定理跑 `#print axioms`、
> 不用 `native_decide`、偏离论文或建模决定记进 `docs/paper-deltas.md`、只 `git add` 自己的文件名。
> `Propagator/Decay.lean` 是 Cowork 侧在写的，不要碰。

---

# 永不停工规则（2026-09-19 起生效）

**队列空了不算理由。** 如果表格里没有一条「空闲 + 可开工」的工单，**不要停下来等我补**，
按下面的顺序自己找活，并在表格里补一行说明你在做什么：

1. **先做 T8–T11**（一般 Fourier 机器，`Propagator/SymbolBound.lean`）。
   它们从来没有被取消，只是排在第 3 节之后；队列一空，它们就是当前最高优先级。
   T8 是入口：`|1 − ξŜ(p)| ≍ |1−ξ| + |p|²` 的双边界，只依赖已完成的 `Propagator/Symbol.lean`。
2. **再看下面的储备工单 B1–B6**，从上往下挑第一条依赖已就绪的。
3. **都不可做时做常规维护**（这几件永远有得做）：
   * `leanblueprint checkdecls`：确认蓝图里每个 `\lean{}` 都解析到真实声明；
     新证的定理补进 `blueprint/src/content.tex` 的相应节点。
   * linter 清理（见 T24 的清单，别碰 `Propagator/Decay.lean`）。
   * `docs/mathlib-api.md`：把这一轮新查到的 Mathlib 名字记进去，下次少走弯路。
   * 给已有定理补数值回归（`Test/Numeric.lean`），特别是新加的组合定义。

唯一该停下来问我的情形，`CLAUDE.md` 里写着：**改动范围、发布/删除内容、不可逆操作**。
其余一律自行决定、自行动手、记档。

---

## 储备工单 B1–B6（依赖就绪即可开工，不必等我点名）

* **B1 — Corollary 3.5：纯 loop 的界**（`Loop/Cor35.lean`）。论文 p.30。
  σ = (+,…,+) 时 `|K_{t,σ,a}| ≤ C_n exp(−c_n max_{ij} ‖a_i − a_j‖)`。
  依赖：树表示（T21）+ (2.52)。**(2.52) 的实 ξ 版本已经证完**
  （`RBM.norm_Theta_apply_le_of_real`，`Propagator/Decay.lean`），而 σ 全 + 时
  `ξ = t m² `——先确认这个 ξ 是否落在实轴上；不在的话这条要等复 ξ 版本，跳过做 B2。
* **B2 — Lemma 3.4 的一般证明**：树和满足 (2.48)，再用 T22 的唯一性得到它就是 K。
  依赖 T21 + T22。这是第 3 节的主定理，做之前先把 T23（n=3）做扎实。
* **B3 — Lemma 3.6 的 Ward 恒等式**（`Loop/Ward.lean`）。论文的证法形式化友好：
  两边之差满足齐次线性 ODE 且初值为零。依赖 B2。
* **B4 — Def 2.9 的 G-loop 本身**（`Loop/GLoop.lean`）。
  对**给定的确定性 Hermite 矩阵 H** 定义 `L_{t,σ,a} = ⟨Π_i G(σ_i) E_{a_i}⟩`，
  证它的代数性质（转置、循环不变、与 `Eblk` 的关系、Ward 型恒等式 `G(z)−G(w) = (z−w)G(z)G(w)` 的 loop 版本）。
  **不碰任何概率**：随机性只在期望和 Itô 里，定义与代数是确定性的。
  这条与第 3 节完全正交，任何时候都能做。依赖：`Defs/Model.lean` + `Delocalization.lean`（均已完成）。
* **B5 — `Test/Numeric.lean` 扩展**：把 `scripts/tree_ode_check.py` 的有限差分核对
  搬一部分进 Lean（有理数、小 L、`norm_num`/`decide`），至少覆盖 n=3 的树和满足 (2.48)。
  数值脚本能防笔误，但它不进公理审计；进了 Lean 才算数。
* **B6 — Lemma 2.8 的定量部分 (2.40)**（`Defs/Semicircle.lean`）：
  `t ≥ c_κ`、`c_κ Im z ≤ Im z_t ≤ c_κ^{-1} Im z`、`|E| ≤ 2 − cκ`。T19 里被推迟的那部分。
  纯实分析，随机层才用得上，但现在做也不浪费。

---

# 第四批工单（2026-09-19，T21–T24 完成后开出）

第三批四条全部完成，一般 Fourier 机器也推进到 T10。树值 `treeVal`/`treeSum`、
唯一性 `Loop/Unique.lean`、n=3 实例 `Loop/Example3.lean` 都在了，
**Lemma 3.4 的所有前置条件因此齐备**——这一批的重心就是把它拿下。

**建议顺序：T25 → T26 → T27 → T28**（T11 仍然空着，队列再见底就回去做它）。

---

## T25 — Lemma 3.4：树表示（**第 3 节主定理，优先**）

新建 `RBM1D/Loop/TreeRep.lean`。论文 (3.5)：对 `n ≥ 2`，

```
K_{t,σ,a} = m_σ · W^{−n+1} · Σ_{Γ ∈ T_SP(P_a)} Γ_a(t,σ),     m_σ = Π_i m(σ_i)
```

前置全部就绪：`treeSum`（T21）、`IsPrimitive`（T18）、唯一性（T22）、
n=2（`kTwo_eq_treeSum`）、n=3（T23）、n=4（`treeSum_four`）。

**证明骨架**（论文自己的路子，别去证 ODE 存在性）：

1. 令 `Ktree t σ a := m_σ W^{−n+1} · treeSum …`，证 `IsPrimitive Ktree`，即
   * 求导：对 `treeSum` 逐项求导。每棵树的每条边是一个 `Θ`（或 `Θ−1`），
     按乘法法则，**求一条边的导数 = 在那条边上插一个 `S^(B)`**（这是 (2.51)）。
     论文的组合内容就是：「所有树的所有边各求一次导」之和
     = 「所有 (k,l) 的 cut-and-glue 项」之和。**这一步是本工单的全部难度。**
     建议先在 n=3、n=4 上把这个双射写出来（两边都已有显式表达式），
     看清楚「边 ↔ (k,l) 对」的对应，再写一般证明。
   * 初值：`t = 0` 时 `Θ_0 = 1`，所有边退化成 δ，树和塌缩成 `1(a_1=…=a_n)`。
2. 用 T22 的唯一性得到 `K = Ktree`。

**如果一般归纳一时做不出来**：退而求其次，把 n ≤ 4 的情形作为定理留下
（n=2、3 已有，补 n=4），并在 `docs/STATUS.md` 里写清楚卡在哪一步——
这比硬凑一个含糊的一般证明有价值。**但不要写 sorry。**

---

## T26 — Lemma 3.6：𝒦 的 Ward 恒等式

新建 `RBM1D/Loop/Ward.lean`。论文 §3 的 Lemma 3.6 + Cor 3.7。

论文的证法对形式化极友好：**两边之差 `D` 满足齐次线性 ODE 且初值为零**，故恒为零。
这正好复用 T22 的 Grönwall 机器。

步骤：先把 Lemma 3.6 的陈述照抄准确（注意它用到 `Σ_b Θ_ab = (1−ξ)^{-1}`，
即 `RBM.sum_Theta_row`，这条早就有了），再证 `D` 的 ODE 与初值，最后引用唯一性。

可以先做 n=2 的情形热身：那时两边都是 `kTwo` 的显式表达式，恒等式应当是代数可验的。

---

## T27 — Def 2.9 的 G-loop 本身（与第 3 节正交，随时可做）

新建 `RBM1D/Loop/GLoop.lean`。**不碰任何概率**：对**给定的确定性 Hermite 矩阵 H**
定义论文 (2.41) 的 loop

```
L_{t,σ,a} = ⟨ Π_i G(σ_i) E_{a_i} ⟩       G(+) = G(z), G(−) = conj
```

用 `Defs/Model.lean` 的 `Eblk` 和 `Delocalization.lean` 的 `green`。要证的都是代数性质：

* 循环不变性（迹的循环性）；
* 转置/共轭对称性，与 `σ` 翻转的关系；
* **Ward 型恒等式** `G(z) − G(w) = (z−w) G(z) G(w)` 的 loop 版本
  —— 这是论文后面所有 Ward 恒等式的源头，且完全确定性；
* `L` 与 `cutGlueL/R` 的相容性（长度、指标）。

期望与 Itô 才需要概率；定义与代数不需要。这条让第 2 节的 loop 层真正落地，
也是将来接随机层的接口。

---

## T28 — Corollary 3.5：纯 loop 的界（待 T25）

新建 `RBM1D/Loop/Cor35.lean`。论文 p.30：`σ = (+,…,+)` 时

```
|K_{t,σ,a}| ≤ C_n exp(−c_n max_{ij} ‖a_i − a_j‖)
```

依赖树表示（T25）与 (2.52)。**注意**：σ 全 + 时 `ξ = t m²` 是**复数**，
而 `Propagator/Decay.lean` 里证完的 (2.52) 只覆盖实 ξ。
先看 `Propagator/DecayComplex.lean` 里 Fourier 路线做到哪了——
如果复 ξ 的 (2.52) 还没落地，就先把 T28 写成「以复 ξ 的 (2.52) 为假设」的形式，
等那边补上再去掉假设。**不要为了绕开它而偷偷换成实 ξ**。

---

## T29 — (3.35)(3.36)：短边与长边（自查发现的缺口）

新建 `RBM1D/Propagator/Edges.lean`。论文 p.~(3.35)(3.36)（§3.3 开头）。

**背景**：蓝图里 `lem:Theta-bounds` 一度被标成「(3.35)(3.36)」，但它证的是**一致界**
`‖Θ_ξ‖ ≤ (1−‖ξ‖)⁻¹`，而论文那两条是**分短边/长边**的：

```
‖Θ_{tm²}‖_max ≺ 1,     ‖Θ_{t|m|²}‖_max ≺ 1/(ℓ_t η_t)      (3.35)
‖Θ_{tm²}‖_1   ≺ 1,     ‖Θ_{t|m|²}‖_1   ≺ 1/η_t            (3.36)
```

**短边那半根本没被覆盖**：`ξ = tm²` 时 `‖ξ‖ = t → 1`，一致界 `(1−t)⁻¹` 是发散的，
给不出 `≺ 1`。要的是 `|1 − tm²|` 的**下界**（`m` 非实、`|m| = 1` 时它是 O(1)）。

要做的：

1. **`|1 − tm²| ≥ c` 的下界**。`m = m^{(E)} = (−E + i√(4−E²))/2`，`|m| = 1`，
   `m² = e^{2iθ}`，`θ` 由 `E` 决定。`|1 − tm²|² = 1 − 2t cos 2θ + t²`，
   在 `|cos 2θ| ≤ 1 − c` 时下有界。论文的 `|E| ≤ 2 − κ` 正是保证这一点的条件——
   **先把这个条件如何转成 `θ` 的条件弄清楚**，用 `Defs/Semicircle.lean` 里已有的 `mE`。
2. **短边的 max 界**：由 1 + 复 ξ 的 (2.52)（`norm_Theta_apply_le_complex`，已完成）直接得到。
3. **短边的 ℓ¹ 界**：对闭式/Fourier 求和，或者用 `1/(1−‖ρ‖)` 配合 `rho_complex_bounds`。
4. **长边**：max 界来自实 ξ 的 (2.52)；ℓ¹ 界就是 `sum_norm_Theta_row_of_real` 的
   精确值 `(1−t)⁻¹`。但要写成论文的 `1/η_t` 还差**字典 `1−t ≍ η_t`**，
   那是 Lemma 2.8 的定量部分 (2.40)，目前推迟着（见 T19 的说明、储备工单 B6）。
   **所以这一条要么先做 B6，要么把 `η_t` 换成 `1−t` 并在 `docs/paper-deltas.md` 里注明。**

**这条工单的意义**：它是自查对账逮出来的，不是新数学。做之前先读
`docs/STATUS.md` 里「一次自查发现的缺口」那两节，理解为什么"看起来同量级"不够。

---

# 第五批工单（2026-09-19，Lemma 3.4 与 3.6 拿下后开出）

**Lemma 3.4（树表示，一般 n）与 Lemma 3.6（Ward 恒等式）都完成了**——第 3 节的两块地基到位。
这一批把战线推到 §3.3：sum-zero 性质。那是论文自己说的"key input"，也是整篇文章
最原创的部分之一。

**建议顺序：T31 → T32 → T33 → T34。** T31 是纯定义层，必须先做对，T34 全建在它上面。

---

## T31 — Def 3.8/3.9：按长边分层（**优先**）

新建 `RBM1D/Loop/Layer.lean`。论文 p.38（Definition 3.8）与紧接的 Definition 3.9。

**Definition 3.8**（论文原文照抄）：

* `F(Γ_a)` 已经有了——就是 `Loop/Crossing.lean` 里 `TSP n` 的元素本身
  （我们把 Lemma 3.2 当定义用，所以一个"树"就是一个无交叉对角线集合）。
* **长内部边**：`F_long(Γ_a, σ) := { {i,j} ∈ F(Γ_a) : {σ_i, σ_j} = {+,−} }`。
  即两端电荷相反的内部边。注意 `{σ_i,σ_j} = {+,−}` 就是 `σ_i ≠ σ_j`（Bool 上直接写 `σ i ≠ σ j`）。
* **按 π 分层**：对 `π ⊆ Z_n^off`（`Z_n^off` 就是我们的 `diagonals n`），
  `T_SP(P_a, σ, π) := { Γ_a ∈ T_SP(P_a) : F_long(Γ_a, σ) = π }`。
  显然这给出 `TSP n` 的一个**划分**（按 `F_long` 的取值分类）——把这条证出来
  （`Finset` 上就是"按 `F_long` 分组"，`Finset.filter` + 互不相交 + 并集是全体）。

**Definition 3.9** 在紧接着的一页，定义 `K^(π)`（把树和限制在 `T_SP(P_a,σ,π)` 上）
与它的自能 `Σ^(π)`。**照抄要非常小心**，尤其是 `Σ^(π)` 的归一化因子和指标。
`K^(π)` 的定义应当复用 `Loop/TreeRepGeneral.lean` 里已有的树和（`treeSum` 一族），
只是把求和范围从整个 `TSP n` 换成 `filter (F_long · σ = π)`。

**验收**：`∑_{π} K^(π) = K`（分层求和等于总和）——这条既是正确性检查，
也是后面所有估计的起点。`Finset.sum_fiberwise` 之类应该直接可用。

---

## T32 — Corollary 3.7

论文 p.~（Lemma 3.6 之后）。既然 Lemma 3.6 已经证完，这条应当是它的直接推论。
放进现有的 `Loop/Ward*.lean` 里合适的那个文件，不要新建。
**先把论文的陈述逐字抄下来再证**，别凭印象。

---

## T33 — (2.53)(2.54) 推到复 ξ（原 T11）

新建 `RBM1D/Propagator/DiffComplex.lean`。

实 ξ 的版本我（Cowork）已经做完并补强到论文形式
（`norm_Theta_sub_shift_le`、`norm_Theta_second_diff_le_inv_dist`，
见 `Propagator/Decay.lean` 的 `Differences2`/`SecondDiff`/`InvDist` 三节）。
复 ξ 的 (2.52) 你们也做完了（`norm_Theta_apply_le_complex`）。
现在把差分估计也推到复 ξ：

* 路线 A（推荐）：沿用 Fourier 表示。`(Θ_ξ)_{x,y} − (Θ_ξ)_{x,y+1}` 在 Fourier 侧是
  乘以 `(1 − ζ^{-p})`，模长 `≍ |p|`；配合 `SymbolBound.lean` 的 `|1 − ξŜ(p)| ≍ |1−ξ| + |p|²`
  就能出 `(2.53)`。二阶差分同理乘 `|1 − ζ^{-p}|² ≍ |p|²`。
* 路线 B：闭式解对复 ξ 也成立（`theta_apply_closed_form` 没有实性假设），
  `kern_succ_sub`/`kern_second_diff` 也都是对一般 ξ 的。缺的只是
  `‖A(1−ρ)‖`、`‖A(1−ρ)²‖` 在复 ξ 下的界——而 `RateComplex.lean` 的
  `rho_complex_bounds` 也许正好给得出。**先花十分钟看看路线 B 是不是几行就完了**，
  是的话别走 A。

**注意**：像我在 (2.54) 上踩过的那样，**别把衰减因子放缩掉**——
最终陈述必须真的蕴含论文的 `≺ 1/(‖x−y‖+1)`。见 `docs/STATUS.md` 的两节自查记录。

---

## T34 — Lemma 3.10：对称性与 sum-zero（待 T31）

新建 `RBM1D/Loop/SumZero.lean`。论文 p.40。

对 **偶数 `n ≥ 4`** 与**交替电荷** `σ^(alt)`（奇数位 `+`、偶数位 `−`），单分子树图（`π = ∅`）：

1. **平移不变 + 对称**：`Σ^(∅)(t, σ^(alt), d) = Σ^(∅)(t, σ^(alt), −d)`；
2. **sum zero**：`L^{-1} Σ_{d ∈ Z_L^n} Σ^(∅)(t, σ^(alt), d) = O(1−t) = O(η_t)`。

第 1 条应该是纯对称性（`Θ` 的对称与平移不变已有：`Theta_transpose`、`Theta_apply_add_right`），
先做它。第 2 条是真正的内容，论文 §3.4 有完整证明（p.41 起），**照着做，别自己发明**。

`O(1−t)` 与 `O(η_t)` 的互换由我做的字典保证
（`Propagator/Edges.lean` 的 `zt_im_le` / `le_zt_im`：`(1−t)√(2κ)/2 ≤ η_t ≤ 1−t`）。

---

## T38 — 下沉共用的求和工具（低优先级清理）

`RBM.Cor35.sum_pow_val_le` / `sum_pow_zdist_le`（`Loop/Cor35.lean`）与
`RBM.sum_pow_val_le` / `sum_pow_zdist_le`（`Propagator/Edges.lean`）是同一条引理的两份证明。
新建 `RBM1D/Defs/Sums.lean`，收拢环上的求和工具：

* `sum_zmod_val`（`∑_{u : ZMod L} f u.val = ∑_{v < L} f v`）
* `sum_pow_val_le`、`sum_pow_sub_val_le`、`sum_pow_zdist_le`
* `sum_exp_neg_zdist_le`、`one_sub_exp_neg_ge`、`mul_exp_neg_le_exp_neg_one`
* `two_mul_zdist_le`、`zdist_neg`

**保留 Claude Code 那份 `sum_pow_val_le` 的证明**（用 `ZMod (k+1) ≃ Fin (k+1)` 的 defeq，
比 Cowork 那份绕 `Finset.sum_image` 的短），然后让两边都 import 新文件、删掉各自的副本。
`Defs/Sums.lean` 只能依赖 `Defs/Dist.lean`（`zdist`），不能依赖 `Propagator/` 或 `Loop/`。

**动手前先确认两边都没在改这两个文件**（看 git log），这是一次跨两边文件的重构。

---

## T40 — Lemma 4.2：预解式的 minor 公式（论文 p.49）

新建 `RBM1D/Green/Minor.lean`。**纯线性代数，零概率成分，与 T37 完全不同的文件**，可以立刻开工。

设 `H : Matrix (Fin N) (Fin N) ℂ` Hermitian，`z : ℂ`，`Im z ≠ 0`（保证 `H − z` 可逆），
`G = (H − z)⁻¹`。对 `i : Fin N`，`H^(i)` 是去掉第 i 行第 i 列的 minor，`G^(i) = (H^(i) − z)⁻¹`。

要证的三条（论文 (4.7)(4.8)(4.9)）：

```
G i i   = (H i i − z − Σ_{k,l ≠ i} H i k * G^(i) k l * H l i)⁻¹          -- (4.7)
G i j   = − G i i * Σ_{k ≠ i} H i k * G^(i) k j        (j ≠ i)           -- (4.8)
G^(i) j k = G j k − G j i * G i k / G i i              (j, k ≠ i)        -- (4.9)
```

**注意符号**：论文 (4.8) 写成 `Gij = Gii Σ_k Hik G^(i)_kj`，但按 `G = (H−z)⁻¹` 的约定，
Schur 补给出的应该是带负号的。**先自己把两边算一遍确定符号**，若与论文不符，
按 `CLAUDE.md` 的规则记进 `docs/paper-deltas.md`（这类符号差是第 23 条候选）。

**建议的形式化路线**（不要直接做 `N × N` 的分块矩阵手术，Mathlib 里很痛）：

1. 索引类型用 `Option α`（`α = Fin (N−1)` 或直接 `{j // j ≠ i}`），`none` 扮演被去掉的第 i 行列。
   Mathlib 有 `Matrix.toBlocks₁₁` … `Matrix.toBlocks₂₂`、`Matrix.fromBlocks`、
   `Matrix.fromBlocks_inv…`、`Matrix.invOf_fromBlocks…`（先 grep 确认当前名字与签名）。
2. 核心是 Schur 补：`fromBlocks A B C D` 在 `D` 可逆时的逆的 `(1,1)` 块是 `(A − B D⁻¹ C)⁻¹`。
   Mathlib 应已有 `Matrix.fromBlocks_inverse_of_invertible…` 之类；若只有 `IsUnit` 版本，
   用 `Matrix.isUnit_iff_isUnit_det` 桥接。
3. (4.9) 是 `(2,2)` 块的对偶陈述，用同一条 Schur 恒等式反过来读。

**可逆性的前提怎么给**：`H` Hermitian 且 `Im z ≠ 0` ⇒ `H − z` 可逆，这条我们可能已经有了
（`Delocalization.lean` 里做 Thm 2.2 时用过谱定理）。**先 grep 仓库**，别重造
（`CLAUDE.md`「造轮子之前先查」）。`H^(i)` 也是 Hermitian，所以同一条引理复用。

**边界情形**：`G i i ≠ 0` 是 (4.9) 的前提。论文在用它时有 `1_Ω |G_ii| = O(1)` 撑着；
我们把 `G i i ≠ 0` 直接写进 (4.9) 的假设，不去证它。

**不要碰的部分**：§4 后面用的 [39] Lemma 3.3（大偏差估计）是外部文献里的概率引理，
本项目「只用这一篇论文」，所以它只能作为**假设**出现，不在本工单范围内。

---

## T41 — Def 2.1 的概率版 `≺`（论文 p.6）

新建 `RBM1D/Defs/StochDom.lean`。**纯定义 + 基本性质**，与 T37/T40 都不冲突。

`Defs/Domination.lean` 里已有确定性版 `DetDom`（Def 2.1 (ii)）。现在补 (i)(iii)(iv)。

```lean
variable {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω)   -- 每个 N 一个概率空间
-- 或者更省事：ξ ζ : ℕ → Ω → ℝ，P : Measure Ω 固定

def StochDom (ξ ζ : ℕ → Ω → ℝ) : Prop :=
  ∀ τ > 0, ∀ D > 0, ∀ᶠ N in Filter.atTop,
    (P N) {ω | ξ N ω > (N : ℝ) ^ τ * ζ N ω} ≤ (N : ℝ) ^ (-D)
```

要的性质（下游 §3–§5 到处在用，不证的话每次都要重来）：

1. 自反、传递
2. 对加法封闭：`ξ₁ ≺ ζ₁ → ξ₂ ≺ ζ₂ → ξ₁ + ξ₂ ≺ ζ₁ + ζ₂`
3. 对乘法封闭（同上）
4. 正常数倍不变；`DetDom → StochDom`（确定性的蕴含概率的）
5. **多项式多的事件取并**：若 `ξ_k ≺ ζ` 对 `k` 一致成立且 `k` 的个数 ≤ `N^C`，
   则 `max_k ξ_k ≺ ζ`。这一条是 (iv)「一致版」的实质内容，也是全篇用得最多的一条。
6. `overwhelming probability`（(iii)）：`∀ D > 0, ∀ᶠ N, P (Aᶜ) ≤ N^(-D)`，
   并证「多项式多个 w.o.p. 事件的交仍是 w.o.p.」

Mathlib 里要用的：`MeasureTheory.Measure`、`Filter.Eventually`、`Filter.atTop`、
`measure_union_le` / `measure_biUnion_finset_le`、`Finset.sup`。名字先 grep。

**设计上的一个选择**：概率空间要不要随 `N` 变。论文里 `H` 的维数随 `N` 变，所以严格说是变的。
最省事的做法是把 `Ω` 和 `P` 都固定、让 `ξ N : Ω → ℝ` 承担 N 的依赖（相当于取乘积空间）。
选哪个都行，但**选定后写进文件头的 docstring 并记进 `docs/STATUS.md`**，
因为随机层将来全建在这个签名上。

---

# 第二批工单（T42–T57）：随机层之外的全部剩余工作

**背景。** 已确认的范围决定：**暂不自建 Itô/随机积分**（自建最小切片约需 300–460 条定理，见与 Jun 的讨论）。
因此凡是依赖随机流的命题，一律写成 **Lean 的显式假设**（定理参数或 `structure` 字段），
**绝不写 `axiom`** —— 仓库有硬性公理审计 `#assert_rbm_axioms`，出现任何项目公理即构建失败。

下面 16 张工单**每张只碰一个新文件**，互不重叠，可以同时开工。
唯一的共享文件是根 `RBM1D.lean` 的 import 列表：**只在自己那一行做点插入，绝不整体重排**
（`sorted(set(lines))` 曾把 `#assert_rbm_axioms` 搅进 import 块）。

论文里被引用的**外部文献**（`[39]` Lemma 3.3 的大偏差估计、`[40]` (4.11) 的涨落平均）
按「只用这一篇论文」的约束，一律作为假设进入，不去证。

## 可以立刻开工（无未满足依赖）

### T42 — `RBM1D/Hierarchy/Kernel.lean` · 难度 M · **最高优先级，下游六张单都 import 它**

Def 5.2（p.53）的两个张量算子，作用在 `A : (Fin n → ZMod L) → ℂ` 上：

* **(5.16)** `(Θ_{t,σ} ∘ A)_a = Σ_i Σ_{b_i} (m_i m_{i+1} / (1 − t·m_i m_{i+1}·S^(B)))_{a_i b_i} · A_{a^{(i)}}`
  其中 `a^{(i)}` 是把 `a` 的第 `i` 个分量换成 `b_i`（Mathlib `Function.update`）。
* **(5.17)** `(U_{s,t,σ} ∘ A)_a = Σ_b ∏_i ((1 − s·ξ_i·S^(B)) / (1 − t·ξ_i·S^(B)))_{a_i b_i} · A_b`，`ξ_i = m(σ_i)m(σ_{i+1})`。

要证的：

1. **(5.18)** `(1 − sξS^(B))(1 − tξS^(B))⁻¹ = I − (s−t)·ξ·Θ^(B)_{tξ}·S^(B)`。
   直接从 `RBM.Theta` 的定义与 `eq_Theta_of_mul` 得到；这是整条线的地基。
2. 半群律 `U_{u,t,σ} ∘ U_{s,u,σ} = U_{s,t,σ}`、`U_{t,t,σ} = id`。
3. **Lemma 7.1 / (7.1)**：`‖U_{s,t,σ} ∘ A‖_max ≤ (1 + |1−s|·max_{‖ξ‖≤1}‖Θ^(B)_{tξ}‖_{max→max})^n · ‖A‖_max`，
   再由 (2.52) 得 `≺ ‖A‖_max·(η_s/η_t)^n`。**常数不求最优**。
4. Lemma 5.3 的确定性一半：`dA = Θ_{t,σ}∘A dt + D dt ⟹ A_t = U_{s,t,σ}∘A_s + ∫_s^t U_{u,t,σ}∘D_u du`。
   随机积分那一项**不在本工单范围**。

**已有可用**：`Propagator/Basic.lean`（`Theta`、`eq_Theta_of_mul`）、`Propagator/Bounds.lean`
（`norm_Theta_le`、`sum_norm_Theta_row_le`）、`Propagator/DecayComplex.lean`（(2.52) 复 ξ 版）。

**建议签名**（下游按这个写，改签名请先在本文件里改并提交）：
```lean
noncomputable def Uker (L n : ℕ) (m : Bool → ℂ) (s t : ℝ) (σ : Fin n → Bool) :
    ((Fin n → ZMod L) → ℂ) → ((Fin n → ZMod L) → ℂ)
```

**Mathlib**：`Function.update`、`Finset.sum_comm`、`Finset.prod_congr`、`Matrix.mulVec`、
`Finset.abs_sum_le_sum_abs`；Duhamel 用 `ODE_solution_unique` / `intervalIntegral`。

---

### T43 — `RBM1D/Analysis/StretchedExp.lean` · 难度 M · **完全自足，不需要任何 RBM 背景**

纯实分析。定义 (5.27) `T_{u,D}(ℓ) := (Wℓ_uη_u)^{-2}·exp(−(ℓ/ℓ_u)^{1/2}) + W^{-D}`
与 (5.28) `J_{u,D}(ℓ) := T^{(L−K)}_u(ℓ)/T_{u,D}(ℓ) + 1`，证：

1. `T_{u,D}` 关于 `ℓ` 非增；**(5.32)** `T_{u,D}(ℓ − C·ℓ*_u) ≺ T_{u,D}(ℓ)`，`ℓ*_u = (log W)^{3/2}ℓ_u`。
2. `∫_0^a exp(−√(a−x) − √x + √a) dx ≤ C`（论文说 `C ≈ 6.12`，我们只要一个显式常数）。
3. `∫_0^∞ exp(−√x) dx = 2`。
4. 半指数变体（(5.62) 用）。
5. **离散卷积界**（(5.50)(5.72) 的实质）：
   `Σ_{x : ZMod L} T_{u,D}(‖a₁−x‖)·T_{u,D}(‖a₂−x‖) ≺ η_u⁻¹(Wℓ_uη_u)⁻¹·T_{u,D}(‖a₁−a₂‖)`。
6. **(7.12)** `max_b (‖a₁−a₂‖^{1/2} − ‖b₁−b₂‖^{1/2}) ≤ C·(log W)^{3/4}·ℓ_t^{1/2}`
   在 `‖a_i−b_i‖ ≤ ¼ℓ*_t` 的限制下。

**Mathlib**：`Real.sqrt`、`Real.exp`、`Real.add_pow_le_pow_mul_pow_of_sq_le_sq` 一类，
`intervalIntegral`、`MeasureTheory.integral_comp_mul_left`、`Finset.sum_le_sum`，
和式↔积分比较用 `Finset.sum_le_integral_of_monotoneOn` 家族（**先 grep 确认当前名字**）。

---

### T44 — `RBM1D/Loop/Split.lean` · 难度 M

固定 Hermitian `H`、固定 `z`，**零概率成分**。

1. **(5.2)** `‖G_t‖_op ≤ 1/η_t`、`‖E_a‖_op ≤ W⁻¹` ⟹ `|L_{t,σ,a}| = O(W^{-n+1})`。
2. **(5.114)–(5.117)** 把 `2n+2`-loop 写成
   `W⁻² Σ_{i∈I_b, j∈I_{b'}} (C₁^{(n+1)})_{ij}(C₂^{(n+1)})_{ji}`，再按 `l₁=⌊(n+1)/2⌋`、`l₂=n+1−l₁` 劈开，
   得 `max|L^{(2n+2)}| ≤ max|L^{(2l₁)}|·max|L^{(2l₂)}|`。
3. **(5.118)** `Ξ^{(L)}_{u,2n+2} ≤ Ξ^{(L)}_{u,2l₁}·Ξ^{(L)}_{u,2l₂}·(Wℓ_uη_u)`。
4. **(6.4)** `(max|L^{(2m+1)}|)² ≤ max|L^{(2m)}|·max|L^{(2m+2)}|`。
5. **Lemma 6.1**（Gram 界）：`v, w₁…w_m` 属于有限维内积空间，`A_{ij} = ⟨w_i, w_j⟩`，则对任意 `p ≥ 1`
   `Σ_i |⟨v,w_i⟩|² ≤ ‖v‖²·(tr A^p)^{1/p}`。
   有限维下最省事的路线：`A` 是 PSD Gram 阵，`‖A‖_{ℓ²→ℓ²} = λ_max(A) ≤ (tr A^p)^{1/p}`，
   用 `Matrix.PosSemidef` + `Matrix.IsHermitian.eigenvalues` + `Finset.single_le_sum`。

**已有可用**：`Loop/Chain.lean`（`gchain`、`gchain_conjTranspose`、`trace_gchain_mul_Eblk`）、
`Loop/GLoop.lean`（`gloop`、`gloop_two_plus_minus_blocks`、`gloop_rotate`）、`Defs/Model.lean`（`Eblk`）。

---

### T45 — `RBM1D/Green/EntryBound.lean` · 难度 L · **下游用得最多**

Lemma 4.1（p.48–50）。**两条外部输入写成本文件定理的显式假设**：

```lean
-- [39, Lemma 3.3] 的形状：X 与 H 的第 i 行独立时的大偏差界
(hLDE : ∀ i j (X : _), Indep i X → ‖Σ_k H i k * X k‖ ≺ (Σ_k S i k * ‖X k‖^2)^(1/2))
-- (4.12) = [40, (4.11)] 的涨落平均
(hFA  : ∀ (c : _ → ℝ), (∀ k, |c k| ≤ W⁻¹) → Σ_k |c k| ≤ 1 →
          ‖Σ_k c k * (1 − E_k) (G k k − m)‖ ≺ max_a L_{t,(+,−),a})
```

在这两条之上确定性地推出：

* **(4.10)(4.11)** 的迭代，用 (4.8)(4.9) 去掉 `(i)` 上标 ⟹ **(4.2)**
  `1_Ω·max_{i∈I_a,j∈I_b}|G_{ij}|² ≺ Σ_{a'=a±1}Σ_{b'=b±1} L_{t,(+,−),(a',b')} + W⁻¹·1(‖a−b‖≤1)`。
* **(4.3)** `1_Ω·max_i |G_{ii} − m|² ≺ max_{a,b} L_{t,(+,−),(a,b)}`，
  用 (4.7) 在 `(−z−tm)⁻¹` 附近展开，配 `m = −(tm+z)⁻¹` 与 `‖(1−tm²S)⁻¹‖_{max→max} = O(1)`
  （后者就是我们的 `Θ^(B)`，已有）。
* **(4.5)** `max_a |⟨(G_t − m)E_a⟩| ≺ max_{a,b} L_{t,(+,−),(a,b)}`（由 `hFA` 加自洽求解）。

**已有可用**：`Green/Minor.lean`（(4.7)(4.8)(4.9)，刚落地）、`Loop/GLoop.lean`
（`gloop_two_plus_minus_blocks` 正是 (4.2) 右端的形状）、`Defs/StochDom.lean`、`Propagator/Bounds.lean`。

**注意符号**：我们证出的 (4.8) 带负号，论文写的没有；见 `docs/paper-deltas.md` 第 23 条。用我们的版本。

---

### T46 — `RBM1D/Propagator/ZeroMode.lean` · 难度 S/M · **干净、独立、马上能开**

§7.2 末尾（p.84）的确定性内容。令 `J` 为全 1 阵，`S̃^(B) := (1−ζ)S^(B) + (ζ/L)·J`。证：

```
[(1 − ξS̃^(B))⁻¹]_{ab} − [(1 − ξS̃^(B))⁻¹]_{a₀b₀}
  = [(1 − ξ(1−ζ)S^(B))⁻¹]_{ab} − [(1 − ξ(1−ζ)S^(B))⁻¹]_{a₀b₀}
```

以及 `‖ξ‖ ≤ 1`、`ζ` 小时的双边比较 `‖1−ξ‖ ≍ ‖1−ξ(1−ζ)‖`。
**为什么便宜**：`J` 只作用在常数模上，而 `Θ_ξ·𝟙 = (1−ξ)⁻¹·𝟙` 我们已经证过
（`Theta_mulVec_one` / `sum_Theta_row`），所以整个秩一修正是一个标量，
Sherman–Morrison 可以手搓，不必找 Mathlib 的秩一更新引理。

**推论**：(2.52)(2.53) 一类的界从 `Θ^(B)_{ξ(1−ζ)}` 原样搬到 `S̃^(B)` 上，只差一个常数零模。

---

### T47 — `RBM1D/Flow/Initial.lean` · 难度 S · **§2.7 里唯一无条件成立的一条**

**(2.67)**：`H_0 = 0`、`z_0 = E + m^{(E)}`、`m(m+E) = −1` ⟹ `G_0(σ) = m(σ)·I`；
再由 `E_a E_b = δ_{ab}W⁻¹E_a`（已证）与 `Tr E_a = 1` 得

```
L_{0,σ,a} = W^{-n+1}·∏_k m(σ_k)·1(a_1 = ⋯ = a_n) = K_{0,σ,a}
```

即 §2.7 归纳的基例，**一条假设都不用**。

**已有可用**：`Loop/GLoop.lean`（`Gsig`、`gloop`、`gloopProd`）、`Defs/Model.lean`（`Eblk` 及其乘法/迹）、
`Loop/Primitive.lean`（`primInit`）或 `Loop/TreeRepGeneral.lean`（`Kgen` 在 `t = 0`）、`Defs/Semicircle.lean`。

---

### T48 — `RBM1D/Flow/Scales.lean` · 难度 S/M

流的尺度层与时间网格：

1. `η_t = (1−t)·Im m^{(E)}`（已有 `zt_im`）、`ℓ_t = ℓ̂(t) = min((1−t)^{-1/2}, L)`（已有 `ellHat`）。
2. 关键恒等式 `A_t := W·ℓ_t·η_t = W·Im m^{(E)}·min((1−t)^{1/2}, L(1−t))`，
   两个分支都显然关于 `t` 反单调 ⟹ **`s ↦ W ℓ_s η_s` 在 `[0,1]` 上非增**（p.24 用）。
3. 几何网格 `1 − s_k = W^{−kτ'}`，`s_0 = 0`，`s_{n_0} = t`，并逐对核验 **(2.72)**
   `A_t⁻¹ ≤ ((1−t)/(1−s))^{30}`：因为 `((1−s_k)/(1−s_{k+1}))^{−30} = W^{−30τ'}`。
4. `η_t ≍ 1−t`、`ℓ(z_t) ≍ ℓ_t`、`ℓ(z) ≍ ℓ_t`（p.21）。

**风险提示**：`n_0` 依赖 `τ` 和 `W = W(N)`，所以「`1−t = W^{−n_0τ'}`」是逐 `N` 的存在性陈述。
Lean 里最干净的做法是**先固定 `τ, τ', n_0`，再对 `t ∈ [1 − W^{−n_0τ'}, …]` 全称量化**，
而不是从 `t` 反推 `n_0`。写之前先把这个定下来并记进 `docs/STATUS.md`。

---

### T49 — `RBM1D/Loop/ChainExpand.lean` · 难度 M/L

附录 A 的确定性核心（附录 A 开头自己声明「未用于主定理的证明」，所以它是**加分项不是关键路径**，
但完全可做，而且直接吃我们刚做完的 `Green/Minor.lean`）：

1. 双边 chain→loop：`L_{t,σ'',a''} = ⟨E_a · C_{t,σ,a} · E_b · C†_{t,σ,a}⟩`（`gchain_conjTranspose` + `trace_gchain_mul_Eblk` 的短扩展）。
2. **(A.5)(A.6)** 归一化比值 `Ξ^{(d)}_n`、`Ξ^{(o)}_n` 的定义。
3. **(A.8)(A.9)(A.10)** `C_n`、`C^{(i)}_n`、`C^{(ii)}_n`（用 `minorGreen`）。
4. **(A.18)** `(C^{(i)}_n)_{ij} = (G₁)_{ii}(H·C^{(ii)}_n)_{ij}` —— 这就是 (4.8)，直接用 `green_off_diag_paper`。
5. **(A.21)–(A.26)** 的**精确望远镜恒等式**（用 (4.9)），组合约束按论文写成 `Finset` 上带 `1(ℓ + Σn_i = n+k)` 指示函数的和。
6. **(A.15)** 对角劈分 `(C_nE_aC_n†)_{ii} = W⁻¹1(i∈I_a)|C_{n;ii}|² + Σ_{j≠i}C_{n;ij}E_a(j)C†_{n;ji}`。
7. p.85/p.88 的 Cauchy–Schwarz 梯子与 **(A.27)** 的三分法。

`1/G_{ii} = O(1)` 与 `[39] Lemma 3.3`（出现在 (A.16)(A.19)）**写成本文件定理的假设**。

---

### T50 — `RBM1D/Loop/Continuity.lean` · 难度 M

§6 的确定性骨架（**不含** (6.1) 的分布标度、也不含 (6.10)(6.11)(6.13) 的总装）：

* **(6.3)** 双参数预解式 `G = G̃ + (z − z̃)·G·G̃`。
* **(6.5)** 对称 loop 的范式 `L_{t,σ',a'} = ⟨E_{a₀}·C_{t,σ,a}·E_{a_m}·C†_{t,σ,a}⟩`。
* **(6.7)** 望远镜积恒等式 `∏(a_k+b_k) = ∏a_k + Σ_l (∏_{j<l}(a_j+b_j))·b_l·(∏_{j>l}a_j)`。
* **(6.8)(6.9)** chain 展开与逐项 Cauchy–Schwarz。
* **(6.12)** Ward 那一步 `W⁻¹Σ_{i∈I_{a₀}}‖v^{(l)}‖₂² = (2i Im z)⁻¹(L_{σ^{(1)}} − L_{σ^{(2)}})`。
* `z̃_{t₁} := (t₂/t₁)^{1/2}z_{t₁}` 的算术：`|z_{t₂} − z̃_{t₁}| ≤ C(1−t₁)`、
  `|z_{t₂} − z̃_{t₁}|² ≤ Cη_{t₁}²`、`|z_{t₂} − z̃_{t₁}|²/Im z̃_{t₁} ≤ Cη_{t₁}`、`Im z̃_{t₁} ≍ Im z_{t₁}`。

## 需要先等一个签名/前置（但可以先用 `variable` 假设占位并行开工）

### T51 — `RBM1D/Hierarchy/KernelDecay.lean` · 难度 L · 等 T42 的签名

**Lemma 7.2** (7.2)（`n=2`、`σ=(+,−)` 的尾估计）与 **Lemma 7.3** (7.13)–(7.24)：

* (7.13) `(u,τ,D)` 快衰减谓词；(7.14) 一般界；
* (7.15) sum-zero 谓词；**(7.16)** 在 Case 1（`∃k: σ_k = σ_{k−1}`）或 Case 2（sum-zero）下的改进界
  `≤ W^{C_nτ}‖A‖_max·(ℓ_sη_s/(ℓ_tη_t))^n + W^{−D+C_n}`。

**这条是 §5.4–§5.8 的硬依赖**：sum-zero 与「短边」带来的 `(ℓ_sη_s/ℓ_tη_t)^n` 增益全靠它。
(7.21) 用 (2.52)；Case 2 的 `|Ξ*_i| ≤ C(η_s/(ℓ_tη_t))(‖b_i−b_1‖/ℓ_t)` 用 **(2.53)**（`DiffComplex.lean` 已有）。
(7.19) 的容斥恒等式对 `n` 归纳即可。**六张单里最重的一张，预算给足。**

### T52 — `RBM1D/Hierarchy/SumZero.lean` · 难度 M · 等 T42

Def 5.12：`(P∘A)_{a₁} := Σ_{a₂…a_n}A_a`；`ϑ_{t,a} := (1−t)^{n−1}∏_{i=2}^n(Θ^(B)_t)_{a₁a_i}`；
`(Q_t∘A)_a := A_a − (P∘A)_{a₁}·ϑ_{t,a}`。由 `Σ_b(Θ^(B)_t)_{ab} = (1−t)⁻¹`（已有）得 `P∘ϑ_t = 1`、`P∘Q_t = 0`。

再证：**Lemma 5.13 (5.87)**（max 范数界 + 保持快衰减）；p.66 的行和恒等式
`Σ_{a_i}(m_im_{i+1}/(1−t m_im_{i+1}S^(B)))_{a_ib_i} = m_im_{i+1}/(1−t m_im_{i+1})`（与 `b_i` 无关）
⟹ **`P∘A = 0 ⟹ P∘(Θ_{t,σ}∘A) = 0`**；**(5.90)**；**(5.99)** 交换子界；
**(5.104)** 的 `Q⊗Q = I⊗I − (ϑP)⊗I − I⊗(ϑP) + (ϑP)⊗(ϑP)` 与 `(P⊗I)∘(Q⊗Q)∘A = 0`。

注意：`K` 层的 sum-zero 已经在 `Loop/SumZero.lean`（T34），**不是同一个文件，不要动它**。

### T53 — `RBM1D/Hierarchy/Step3.lean` · 难度 M · 等 T44 · **性价比最高的一张**

定义 (5.76) 的 `Ξ^{(L)}_{t,m}`、`Ξ^{(L−K)}_{t,m}` 与 (5.108) 的 `Ψ(n,k,s,u,t)` 及谓词 `S(n,k,s,u,t)`；
证 (5.107) 的互推；**把 Lemma 5.14 的 (5.92) 与 T44 的 (5.118) 当作假设**，证 **(5.109)** 的双重归纳
`{l=k, m≤n−1}` 或 `{l=k−1, m≤n+2}` ⟹ `S(n,k)`；跑完归纳得 **(2.77)**；证 (5.119)(5.120)。

**给定 (5.92) 作假设后，Step 3 是 100% 确定性的**，没有任何概率内容。

### T54 — `RBM1D/Flow/Hypotheses.lean` · 难度 M

随机层的假设接口。**全部是 `structure` 字段，一个 `axiom` 都不许有。**

* `Sample`（(2.34)(2.36) 的逐 `N` 数据：`H : ℝ → Ω → Matrix …`、Hermitian、`H 0 = 0`）；
* `Band`（`N = W·L`、(2.2) 的带宽条件、概率测度）；
* `Lval`（(2.41)，用现成的 `gloop`）、`Kval`（用现成的 `Kgen`）；
* `Bounds B s`：四个字段依次编码 (2.68)/(2.60)、(2.69)/(2.63)、(2.70)/(2.64)、(2.71)/(2.62)；
* `Thm221 B κ`：`Bounds B s → (2.72) → Bounds B t`；
* `Steps B s t`：八个字段依次是 (2.73)–(2.80)；
* `Transfer`：(2.39)/(2.65)/(2.66) 的分布相等，**写成「界的传递」而不是测度的相等**，避免动 pushforward。

顺手证两条免费的、用来校验接口没接错：
`Bounds_of_Steps`（`u := t`，并记下 p.25 的注记：Step 6 可以从 Thm 2.21 里摘掉）；
以及 `(2.61)` 由 `Bounds.LmK` 加已证的 (2.59) 一行得到。

### T55 — `RBM1D/Hierarchy/Step45.lean` · 难度 S · 等 T53

Step 4：由 (5.125) 对 `n` 归纳得 **(2.78)**；基例 `Ξ^{(L−K)}_{t,1} ≺ 1`（来自 (4.5)）与
`Ξ^{(L−K)}_{t,2} ≺ (Wℓ_tη_t)^{1/4}`（来自 (2.76)）作假设。
Step 5：两段劈分（`‖a₁−a₂‖ ≤ 6ℓ*_t` 用 Step 4；`> 6ℓ*_t` 用 (5.48)）得 **(2.79)**。
**六步里最小最干净的一张**，适合当第二个 agent 的热身。

### T56 — `RBM1D/Hierarchy/Step6.lean` · 难度 S/M · 等 T42、T53

把 Lemma 5.15 的 (5.126) 与「(5.20) 取期望后鞅项消失」作为假设，证：
(5.128) 的自洽求解（就是求 `Θ^(B)_{um²}` 的逆，已有）；(5.133)(5.134)(5.135) 的三角不等式劈分；
最后的时间积分 (5.136)，用 (7.14) 与单调性 `ℓ_t²η_t ≤ ℓ_u²η_u`，得 **(2.80)**。

### T57 — `RBM1D/Flow/Iteration.lean` · 难度 M · 等 T47、T48、T54

§2.7 p.24 的主定理：**Lemma 2.18、2.19、2.20 由 Theorem 2.21 推出**。
基例用 T47 的 (2.67)，网格与 (2.72) 用 T48，接口用 T54；沿 `k = 0,…,n_0−1` 归纳应用 `Thm221`，
把有限多次 `N^ε` 的损失并进 `≺`。得到 (2.60)(2.62)(2.63)(2.64)，再加 (2.59) 得 (2.61)。

## 认领方式

改表格里「认领」一栏 → `git add docs/TASKS.md` → 立刻 commit（别长时间持有）→ 开工。
**只按文件名 `git add` 自己那几个，绝不用 `git add -A`。**

---

# 第三批工单（T58–T66）：把随机层的假设往回收

第二批（T42–T57）之后，论文的**确定性骨架**基本齐了：传播子、第 3 节、§4、演化核、
sum-zero 算子、Step 3/4/5、§6 骨架、§7.1、§7.2 的零模、以及「Lemma 2.18–2.20 由 Thm 2.21 推出」。

但有一批结果是**以更强的假设成立的**：T53（Step 3）和 T55（Steps 4–5）都把 **Lemma 5.14 的 (5.92)** 当作假设，
而 (5.92) 本身只有鞅那一步是真随机的，其余全是确定性的。第三批的目标就是**把这些假设往回收**——
把「假设 (5.92)」换成「假设 Lemma 5.5 的二次变差界」，也就是把挂起点推到 Itô 的边界上，一步不多。

同样的规矩：每张单只碰一个新文件，随机成分一律写成 `structure` 字段或定理参数，**绝不用 `axiom`**。

## T58 — `RBM1D/Hierarchy/Dynamics.lean` · M · **先做这张，T59/T60/T61 都要它**

§5.2。把 (5.10) 的 loop 层级**作为假设**，确定性地推出：

* **(5.12)** 减去 (5.11) 的 `K` 方程（后者已有：`hasDerivAt_Kgen_all`），
* **(5.13)** `E^{((L−K)×(L−K))}` 与 **(5.14)** `[K∼(L−K)]^{l_K}` 的定义，
* **(5.15)** 把 `l_K = 2` 那一项单独拎出来的重组，
* **(5.19)** `Θ_{t,σ}∘(L−K) = [K∼(L−K)]^{l_K=2}`（用已证的 (2.57) `K_{t,σ,(a₁,a₂)} = W⁻¹m₁m₂(Θ^(B)_{tm₁m₂})_{a₁a₂}`），
* **Def 5.4 / (5.22)(5.23)** 的 `E⊗E`：**纯组合**，在 `LoopIdx` 上切第 k 条边再与共轭 loop 粘合（Figure 13），
* **(5.20)(5.21)** 的积分形式：漂移部分用 T42 的 Duhamel（`Hierarchy/Kernel.lean` 已有），
  随机积分那一项作为假设字段。

## T59 — `RBM1D/Hierarchy/Decay.lean` · M · 等 T58

§5.4。Def 5.8 的 `(u,τ,D)` 快衰减谓词 (5.74)；Lemma 5.9 (5.75)（链条：`K` 衰减 ⟹ `L_{(+,−)}` 衰减
⟹ 由 (4.2) 单个 G 元衰减 ⟹ 任意长度的 `L` 衰减；`K` 那一头由树表示 + (2.52) 给出，**已全部在库**）；
(5.76) 的 `Ξ` 记号；**Lemma 5.10 (5.77)** 的四条幂计数；**Lemma 5.11 (5.83)**（非交替 `σ`，用 T51 的 (7.16) Case 1）。

## T60 — `RBM1D/Hierarchy/SumZeroDyn.lean` · L · 等 T58、T52 · **⭐ 全队最高优先级**

> Jun 指定：**谁空出来就先做这张**，别的单往后排。T53、T55 现在都假设着 (5.92)，
> §5.3 Step 2 也要靠它收尾；不把它证出来，Theorem 2.21 的六步就一直挂在一条没证的引理上。
> 若 T59 还没落地，就把它的 (5.77) 先写成本文件的假设占位，等 T59 好了再换成真定理——**不要等**。

§5.5 的动力学半边，即 **Lemma 5.14 / (5.92)** —— T53 与 T55 现在假设的就是它。

已经在库的（T52，`Hierarchy/SumZero.lean`）：`P`、`ϑ_t`、`Q_t`、`P∘ϑ=1`、`P∘Q=0`、
p.66 的行和恒等式与锐化等式、(5.90)、(5.99) 的定量核、(5.104) 的两槽 `Q⊗Q`。**不要重做，import 即可。**

本单要做的：(5.88) 的 `Q_t∘(L−K)` 层级（多出 `−(P∘(L−K))·ϑ̇_t dt` 一项）、
(5.91) 的七项积分形式、(5.94) 的主不等式、(5.95)–(5.97) 的 `ϑ̇` 项
（**(5.96) 用 Ward 恒等式 Lemma 3.6，已在库**）、(5.98)–(5.100) 的交换子项（用 T52 的 (5.90)(5.99)）、
(5.101)，最后用 (5.93)=T51 的 (7.16) 与 T59 的 (5.77) 合成 (5.92)。
**只有 (5.103)(5.105) 的二次变差/BDG 是假设**，写成一个字段。

## T61 — `RBM1D/Hierarchy/Step2.lean` · L · 等 T58、T59

§5.3 Step 2。(5.26)–(5.29) 的 `T^{(L−K)}`、`T_{u,D}`、`J_{u,D}`、`J*`（`T_{u,D}` 与卷积界已由 T43 提供）；
**Lemma 5.6** (5.30)(5.31)(5.32)；**Lemma 5.7** (5.34)(5.35)(5.36)；
(5.39)–(5.42) 用 T42 的 Lemma 7.1 与 T51 的 (7.2) 组装；(5.47)(5.48)。
逻辑核心是一个**自改进不等式**（不是 Grönwall）：「设 `J*_{u,D} ≤ (η_s/η_t)⁴` 直到 `τ`，推出 `J*_{τ,D} ≺ (η_s/η_t)²`」。
停时 (5.43) 与鞅 (5.44)–(5.46) 作为假设。

## T62 — `RBM1D/Loop/ContinuityAssembly.lean` · M · 等 T44、T50

§6 的总装：(6.10) 用 T44 的 Lemma 6.1；(6.11)；(6.13) 的递推；
`m = 1` 的基例由 (5.6) 给出；`m > 1` 用 T44 的 (6.4) 闭合，最后一步是初等的
「`X ≺ A + A^{1/2}X^{1/2} ⟹ X ≺ A`」。(6.1) 的分布标度作为假设。结论是 **Lemma 5.1**。

## T63 — `RBM1D/Flow/Consequences.lean` · M · 等 T54

§2.6 p.22：**Theorem 2.3 与 2.4**。输入是 `Bounds`（T54 已有）与 `Transfer`（(2.39)/(2.65)/(2.66)）；
其余全部在库：Lemma 2.8 的定量部分、`ℓ(z) ≍ ℓ_t`、`K_{t,+,a} = m`、(2.57)(2.58)。
对应关系：(2.3)←(2.64)、(2.4)←(2.60)@n=1、(2.6)(2.7)←(2.60)@n=2、(2.8)(2.9)←(2.62)。

## T64 — `RBM1D/Loop/ChainBound.lean` · M · 等 T49

附录 A 的总装：(A.11)(A.12)(A.13)(A.14)(A.15)(A.17)(A.20) ⟹ **Lemma A.2** (A.3)(A.4)。
展开恒等式与 Cauchy–Schwarz 梯子 T49 已经做完，本单只做把它们串起来的归纳 (A.7)。
`1/G_{ii} = O(1)`（来自 Thm 2.3）与 `[39] Lemma 3.3` 作为假设。
注：附录 A 开头自己声明「未用于主定理的证明」，所以这是**加分项而非关键路径**。

## T65 — `RBM1D/Hierarchy/GUEPhase.lean` · L · 等 T58、T59

§7.2。(7.25) 的 `S̃ = (1−ζ_U)S + ζ_U/N`（零模部分 T46 已做）；(7.30) 的尺度算术；
**(7.33)–(7.36)** 的 Grönwall/连续性自举（**§7.2 里最可形式化的一块**：给定 GUE 相的流方程作假设后是纯 ODE 自举）；
(7.39)–(7.44) 把 `S^(B) → S^(B)_{GUE}` 之后的层级项重新记账；(7.45)(7.46) 闭合归纳得 (7.27)(7.28)。
(7.26) 的分布相等、(7.37)(7.38) 的 Duhamel/BDG、(7.47) 作为假设。

## T66 — 维护

蓝图 `blueprint/src/content.tex` 补上第二批（T42–T57）新增声明的 `\lean{}` 节点，跑 `leanblueprint checkdecls`
确认每个都解析得到真实声明；顺手清掉 `Green/Minor.lean` 与 `Hierarchy/Kernel.lean` 里的
`unusedSectionVars` 警告（用 `omit ... in`）。**改 `content.tex` 时改动要小、要立刻提交。**

---

# T67、T68：全文依赖图暴露出的两个缺口

画全文关系图（蓝图顶部那张，69 个节点）时发现，Theorem 2.21 的六步里
**Step 1（§5.1）从头到尾没有工单**，而论文的四个主结果里 **Theorem 2.5（QUE）与 2.6（普适性）**
也一张单都没有。前者在关键路径上，后者是论文的出口。补上。

## T67 — `RBM1D/Hierarchy/Step1.lean` · M · **在关键路径上**

§5.1（p.51），目标 **(2.73)** `L_{u,σ,a} ≺ (ℓ_u/ℓ_s)^{n−1}(Wℓ_uη_u)^{−n+1}` 与
**(2.74)** 弱 local law `‖G_u − m‖_max ≺ (Wℓ_uη_u)^{−1/4}`（注意指数是 1/4，不是 1/2）。

确定性部分（可以直接做）：

* **(5.2)** `‖G_t‖_op ≤ 1/η_t`、`‖E_a‖_op ≤ W⁻¹` ⟹ `L_{t,σ,a} = O(W^{−n+1})`，纯算子范数计算；
* 三情形分解（`s<t≤1/2`、`t>s≥1/2`、`t>1/2>s` 归约到第二种取 `s=1/2`），纯逻辑；
* **(5.4)** 由假设 (2.68) 加已证的 (2.59) 得到；
* **(5.8)** 由 (5.2)(5.4) 加 **Lemma 5.1**（T62 已完成）得到；
* **(5.9) 的禁区论证**：「若在 `{x ≤ b}` 上有 `x ≺ f` 且 `f ≪ a < b`，则 `x` 不落在 `[a,b]`」
  —— 这是个确定性蕴含，把它单独抽成一条引理，是本单最值钱的部分。

作为假设的：**(5.1)** 的时间连续性（高斯流 + 指数小事件）、以及把「对某个 `u`」提升到
「对所有 `u` 同时」的 `N^{−C}` 网 + 并集界（并集界那一层 `Defs/StochDom.lean` 已经有了）。

## T68 — `RBM1D/Flow/Universality.lean` · M · 论文的出口

§2.3 的 **Theorem 2.5（QUE）** 与 **Theorem 2.6（普适性）**。
输入：T65 的 §7.2 结论 (7.27)(7.28)(7.29)、(7.47)、以及 T46 已做的零模去除；
另外 (2.14)→(2.17) 那条路线在 §2 里，机器已经在库。

外部文献 **[51]**（Landon–Sosoe–Yau，DBM 的固定能量普适性）与 **[70]**（band matrix 的 QUE 比较策略）
按「只用这一篇论文」的约束作为假设进入，**不要去证**。

这两条是论文摘要里的 (iii)(iv)，所以哪怕只是把陈述和逻辑骨架搭出来、把外部输入写成假设，
主定理的四条就齐了——值得做。

---

# 第四批工单（T69–T76）：矩路线

完整路线、依赖图与风险见项目文档 `claude/moment-route-plan.md`。这里只列每张单要做什么。

**依赖**：`T70 → T71 → T72 → {T74, T75}`；`T69` 与 `T70` 可并行；`T73` 等 `T69`；`T76` 等 `T71`+`T73`。

## T70 — `RBM1D/Gauss/Stein.lean` · M · ⭐ **地基，先做**

1. 一维：`X ~ gaussianReal 0 v`（`v ≠ 0`）、`f` 可微且 `f`、`f′` 被多项式控制 ⟹
   **`E[X · f(X)] = v · E[f′(X)]`**。
   证法：`gaussianPDFReal 0 v x = (√(2πv))⁻¹ exp(−x²/(2v))`，直接算出
   `d/dx p_v(x) = −(x/v)·p_v(x)`，然后 ℝ 上分部积分（`MeasureTheory.integral_mul_deriv_eq_deriv_mul`
   一类，**名字先 grep**）。可积性由高斯尾 + 多项式控制给出。
2. 乘积：`Measure.pi` 上对第 `i` 个坐标的版本（其余坐标 Fubini 拿出去）。
3. 矩阵：`X` 是 Hermitian 带矩阵，实部虚部独立、方差 `S_ij`；给出
   `E[X_ij · F(X)] = S_ij · E[∂_ji F(X)]` 的形式（注意 Hermitian 约束下 `X_ji = conj X_ij`，
   所以对 `X_ij` 的导数要按实部/虚部拆，**这一步的记号要定死并写进文件头**）。

**Mathlib**：`ProbabilityTheory.gaussianReal`、`gaussianPDFReal_def`、`integrable_gaussianPDFReal`、
`MeasureTheory.Measure.pi`、`integral_integral_swap`、分部积分（先 grep 确认名字）。

## T69 — `RBM1D/Gauss/Model.lean` · M

固定的高斯带矩阵 `X`：Hermitian，`X_ij` 独立（`i ≤ j`），`E|X_ij|² = S_ij`。流 `H_u := √u • X`。要证：

* `Sample` 的三个字段：`hermitian`、`H_zero`（`√0 = 0`）、`measurable`；
* **确定性 Lipschitz**：`‖H_u − H_{u'}‖ = |√u − √u'| · ‖X‖`（这是 T73 降不可数并的全部依据）；
* `‖X‖ ≺ 1`（算子范数的高斯尾；若太贵，先写成假设，标注清楚）。

**与论文的偏差**：`H_u = √u·X` 不是布朗运动，增量不独立。**一时刻边缘完全一致**，
而层级方程只用一时刻边缘。这是重大 paper-delta，记进 `docs/paper-deltas.md`。

## T71 — `RBM1D/Gauss/Generator.lean` · L · **核心**

`∂_u E[Φ(H_u)] = ½ Σ_{ij} S_ij E[∂_ij ∂_ji Φ(H_u)]`。

路线：`E[Φ(√u·X)]` 对 `u` 求导 = 含参积分求导（`hasDerivAt_integral_of_dominated_loc_of_deriv_le`），
被积函数的导数是 `(1/(2√u)) Σ_ij X_ij ∂_ij Φ`，再对每个 `X_ij` 用 **T70 的 Stein**，
把 `X_ij` 换成 `S_ij ∂_ji`，`√u` 相消，得到上式。

**dominated 条件白送**：我们只对 `Φ = |F|^{2p}`、`F` 是 `G = (H−z)⁻¹` 的多项式用它，
而 `Im z ≥ η > 0` 给出 `‖G‖ ≤ η⁻¹` 在**全空间**成立，各阶导被 `k!·η^{-(k+1)}` 全局控制。
**把这条「全局控制」单独抽成一条引理**，后面每处都要用。

## T72 — `RBM1D/Gauss/MomentGronwall.lean` · L

取 `Φ = |F|^{2p}`，展开生成元恒等式的二阶导：

```
d/du E|X_u|^{2p} = 2p·Re E[ |X|^{2p−2} · X̄ · ∂_u F ]
                 + p(2p−1)· E[ |X|^{2p−2} · Σ_α S_α |∂_α F|² ]
```

**第二项必须被证明等于 (5.25) 里算出的二次变差**（即 `Σ_α Σ_k |U∘E^(M)(α,k)|²`）——
这是整条路线的支点，单独成一条定理，名字建议 `secondOrder_eq_quadVar`。
然后由 `φ′(u) ≤ a(u)φ(u) + b(u)` 用 Mathlib 的 `gronwallBound` 收尾。

## T73 — `RBM1D/Gauss/Domination.lean` · M

1. **矩 ⟹ `≺`**：Markov/Chebyshev。若 `∀p, E|Y_N|^{2p} ≤ C_p N^{εp}`，则 `Y ≺ 1`。
2. **`u` 一致的 `≺`**：取 `N^{-C}` 时间网 `u_k`，网上用 1. 加有限并；
   网间用 T69 的确定性 Lipschitz 把误差压到 `N^{-C'}`。
   **这条就是 Def 2.1(i) 不可数并的全部解法**，论文自己在 (5.46) 用的是同一个网。

## T74 / T75 / T76 — 卸载

* **T74**：把 `Flow/Hypotheses.lean` 里 BDG 那个字段换成 T72 的定理。
* **T75**：Step 2 的 bootstrap 原来用停时 (5.43)；`φ(u) := E[(J*_{u,D})^q]` 是确定性连续函数后，
  退化成「`φ` 连续 + 闭集取 sup」的连续归纳，不需要 optional stopping。
* **T76**：**不要去证 (2.45) 这条 SDE**。矩路线根本不需要它——只需要 `∂_u E[…]`。
  直接由 T71 推出层级的期望/矩版本。这是最大的一处 paper-delta，务必逐条记录。

---

## T77 — `RBM1D/Gauss/Envelope.lean` · M · **保持 `≺` 接口不变的关键**

T73（`Gauss/Domination.lean`）已经做了**正向**：`MomentDom ⟹ StochDom`（Markov）。
本单做**反向**，这样 `bdg` / `bdgQ` 这类「`≺` 进、`≺` 出」的接口就能在**签名不变**的前提下
被证明出来，而不是被改形状。

### 要证的

```
StochDom P Y Φ  →  (∀ N u ω, ‖Y N u ω‖ ≤ D N)  →  D 多项式增长  →  MomentDom P Y Φ
```

想法：把空间切成 `{|Y| ≤ N^τ Φ}` 与其补集。主部给出 `N^{2pτ} Φ^{2p}`；
补集的概率 `≤ N^{-D'}`（`≺` 的定义），在那里用确定性包络 `D N` 控住，
取 `D'` 足够大把 `D N ^{2p} · N^{-D'}` 压下去。**注意 T73 里量词的次序**
（`ε` 在 `p` 外面），反向桥要产出同样的次序，否则对接不上。

### 确定性包络从哪来

**白送的**：`z_t = E + (1−t)m^{(E)}`，`Im z_t = η_t > 0`，于是
`‖G_t‖_op ≤ η_t⁻¹` 在**全空间**成立（不是高概率，是处处）。
loop 是 `G` 与 `E_a` 的乘积的迹，所以任何 `n`-loop 都有确定性界 `≤ W^{-n+1} η_t^{-n}`；
`L − K`、`Ξ`、`J*` 同理。**把这条单独抽成一条引理**（建议名 `norm_gloop_le_det`），
T72 里每处 dominated 条件、T77 里每处包络都用它。

### 用在哪

- T72 的 Grönwall：输入是 `≺`，先用 T77 升成矩，跑完 Grönwall 再用 T73 降回 `≺`。
- T74 卸 `bdg`：**签名保持 `SumZeroDyn` 里现在那个样子**，只是把它从字段变成定理。

---

## T70 的剩余部分：卸掉 `Gauss/Generator.lean` 的 `MatrixStein` — ✅ **已完成 2026-09-20**

落地在 **`RBM1D/Gauss/SteinMatrix.lean`**（新文件，已进根 import，构建绿，公理审计通过）：

```lean
theorem RBM.Gauss.matrixStein (d : Dims) : RBM.Gauss.MatrixStein d
```

**下游怎么用**：所有带 `(hst : MatrixStein d)` 的定理（`Gauss/Hierarchy.lean` 的
`hasDerivAt_integral_gloop` 等、`Gauss/DischargeBDG.lean` 的 `momentDom_of_quadVar` 等）
**签名一个字都没改**，直接把 `hst` 填成 `RBM.Gauss.matrixStein d` 即可。
这正是「做不了的东西写成 `structure` 字段、日后原地换成定理」那条规矩兑现的地方。

**实际走的路线**（比原计划的 `Measure.pi` + Fubini 便宜很多，记下来给 d≥3 抄）：

1. `upd d c (ω, t)` = 把 `ω` 的第 `c` 个坐标换成 `t`。
2. **`P_map_update`**：`((P d) ⊗ γ_c).map (upd d c) = P d`
   —— 用自己那一维的独立样本重采样一个坐标，不改测度。
   证法是在可测长方体上验证，`Measure.eq_infinitePi` + `Measure.infinitePi_pi`，
   两种情形（`c ∈ s` / `c ∉ s`）各一行乘积重排。**独立性只在这一处用到。**
3. Stein 两边都沿这个映射推过去，乘积上 Fubini（`integral_prod`）把 `t` 分离出来，
   内层就是 `Gauss/Stein.lean` 的一维复值 Stein。
4. `integral_mul_gaussianReal_complex'` 连方差为 0 的退化情形一起覆盖
   （`gaussianReal 0 0 = dirac 0`，两边都是 0），所以 `MatrixStein` 不需要 `gvar ≠ 0` 假设。

**意外收获**：`MatrixStein` 的两条 `FinDep` 假设在这条路线上**根本用不到**
（重采样恒等式对整个无穷乘积成立，不需要先约化到有限坐标）。为了不动 T71 已在消费的接口，
它们照收不误、直接忽略。

**`Gauss/Stein.lean` 这一侧新增**（同批，已提交）：
`integral_mul_gaussianReal_complex`（复值一维 Stein，实虚部拆分）、
`integrable_of_bdd_gaussianReal`、`integrable_id_gaussianReal`、
`integrable_ofReal_mul_gaussianReal`。

---

# 第五批工单（T81–T83）：卸掉外部文献 [39]

**背景（2026-09-20，Jun 指定）**：「我希望这篇论文里不包含外部文献输入（因为也是我的工作，
错对的责任也在我身上）」。所以 `[39, Lemma 3.3]` 与 `[40, (4.11)]` 都要自己证。

**注意：不是重证 [39]/[40] 里的定理，只证我们需要的那一部分。**
仓库里这一部分早就切好了——`Green/EntryBound.lean` 的 `LDERow`/`LDECol`/`LDEQuad` 三条，
以及 `hIBP`。照着它们的**现有签名**做，**不要改签名**。

**关键红利**：论文自己在 §5.1 白纸黑字写着 *"the entries of `H_t` follow a Gaussian
distribution"*。[39] Lemma 3.3 之所以是篇幅可观的引理，是因为它要处理**任意分布**
（矩条件 + 矩方法）。**我们只要高斯**，线性那一半直接塌成恒等式。

`[40]` 的涨落平均 (4.12) 另开一批，方案待定（见 `docs/STATUS.md` 的可行性核查记录：
用 n=1 层级绕开的路线**已被否掉**，原因是 `E^{(G̃)}` 自耦合系数 `η_u^{-1}` 的积分是对数的，
Grönwall 因子是多项式量级，`≺` 吸不掉）。

## T81 — `RBM1D/Gauss/LDELinear.lean` · M · **最便宜的一张**

目标：对 `Gauss/Model.lean` 的高斯模型，证 `RBM.LDERow` / `RBM.LDECol` 的 `StochDom` 版本
（`Φ = N^τ`，对任意 `τ > 0`）。

```
ldeRowLHS H G i j = ‖∑_{k≠i} H_ik G^(i)_kj‖²   ≺   ∑_{k≠i} S_ik ‖G^(i)_kj‖² = ldeRowRHS
```

**为什么便宜**：`G^(i)` 只读第 `i` 行以外的坐标，与 `H_ik`（`k≠i`）**严格独立**。
条件在其余坐标上，`∑_{k≠i} H_ik X_k` 就是一个**中心复高斯**，方差恰为 `t·∑_k S_ik‖X_k‖²`。
于是矩形式是**恒等式**而非估计：

    E[ ‖∑_k H_ik X_k‖^{2p} | 其余坐标 ] = p! · ( t ∑_k S_ik ‖X_k‖² )^p

再用 T73 的 `stochDom_of_momentDom`（Markov）落地成 `≺`。

**需要的零件**：独立高斯的复线性组合仍是高斯（Mathlib 的 `isGaussian_map` 走 CLM）、
复中心高斯的绝对矩公式 `E‖Z‖^{2p} = p!σ^{2p}`、条件期望 = 乘积测度上的 Fubini
（`Model.lean` 的 `P_map_restrict` 已经有了）。

**坑**：`G^(i)` 的独立性要真的说清楚——写成「`G^(i)` 是 `FinDep` 且其见证集不含第 `i` 行的坐标」。
这条单独抽一个引理，T82 也要用。

## T82 — `RBM1D/Gauss/LDEQuad.lean` · L · **这一批的主要工作量**

目标：`RBM.LDEQuad` 的 `StochDom` 版本，即高斯情形的 Hanson–Wright：

```
‖∑_{k,l≠i} H_ik B_kl H_li − t ∑_k S_ik B_kk‖²  ≺  ∑_{k,l} S_ik ‖B_kl‖² S_li
```

`B = G^(i)`，与第 `i` 行独立。左边是**中心的二阶高斯混沌**。

**两条路，建议走 (b)**：

* **(a) Wick 展开 + 配对计数** —— 组合重，Lean 里贵。
* **(b) 用 `MatrixStein` 做矩递推** —— 对 `E‖Q‖^{2p}` 用一次分部积分，
  把一个 `H_ik` 换成 `S_ik ∂`，得到 `E‖Q‖^{2p} ≲ (2p−1)σ²E‖Q‖^{2p−2} + (交叉项)`，
  对 `p` 归纳。**复用我们已经有的机器**，而且天然是矩形式，正好接 T73。

**先做 (b) 的 `p=1`（方差）那一例把记号跑通**，再上归纳。

## T83 — `RBM1D/Gauss/IBP.lean` · S · 等 T70 矩阵版

卸掉 `Green/EntryBound.lean` 的 `hIBP`——论文 p.50 的那个显式式

    E_i(G_ii − m) = E_i[m(−H − tm)G]_ii = ∑_k E_i[m(G_kk − m)tS_ki G_ii] + O≺(Ψ²)

它**就是**高斯分部积分，也就是 T70 的矩阵版 Stein。T70 一落地这条基本是套用。
**注意**：它只是 (4.5) 证明里的一步，(4.5) 本身还要 (4.12)，那是第六批的事。

---

# 第六批工单（T84–T88）：自证涨落平均 (4.12)，卸掉 [40]

**推演结论（2026-09-20，已记入 STATUS）**：两条便宜路线都试过，**都不行**——

* **方差/正交性**：`E_k[Z_k]=0` 加 (4.9) 的替换只给到 `E|∑t_kZ_k|² ≲ Ψ³`，即 `≺ Ψ^{3/2}`，
  比 (4.12) 要的 `Ψ²` 差一个 `Ψ^{1/2}`。方差只看二阶，看不到「每个指标至少出现两次」。
* **高斯 Poincaré / Efron–Stein**：`∂_{H_jm}G_kk = −G_kjG_mk ≺ Ψ²` ⟹ `Var ≲ N·Ψ⁴`，
  差 `N` 倍。它完全没用上 `(1−E_k)` 的结构。

**所以走标准高阶矩展开，没有捷径。** 高斯让第 1、2 步变干净（精确 Fubini、严格独立，
而不是 [39] 那种一般分布的矩方法），但**第 5 步的计数不因高斯而简化**。

依赖：`T84 → T86 → T87 → T88`；`T85 → T86`。T84、T85 可并行开工。

## T84 — `RBM1D/Gauss/CondRow.lean` · M · **地基**

在 `Gauss/Model.lean` 的乘积模型里，`E_k[X] := E[X | H^{(k)}]` **就是对第 k 行的坐标积分**，
是精确的 Fubini，**不要用抽象 `condExp`**。要：

* `condRow d N k : (Ω d → ℂ) → (Ω d → ℂ)`，由 `P_map_restrict` + Fubini 定义；
* 幂等 `E_k ∘ E_k = E_k`；**`E_k ∘ (1 − E_k) = 0`**（消失引理的全部依据）；
* 不读第 k 行的因子可以提出：`E_k[X·Y] = X·E_k[Y]`（`X` 的 `FinDep` 见证集不含第 k 行）；
* `E[E_k X] = E[X]`；
* **`G^(k)` 与第 k 行严格独立**：写成「`G^(k)` 是 `FinDep` 且见证集不含第 k 行坐标」。
  这条 T81/T82 也要用，**抽成公共引理**。

## T85 — `RBM1D/Gauss/MinorReplace.lean` · S/M

`|G_ll − G^(k)_ll| ≺ Ψ²`，`l ≠ k`。**(4.9) 已经在 `Green/Minor.lean` 里证了**
（`RBM.inv_minorMat` / `green_diag_paper`），本单只是把它配上
`|G_lk| ≺ Ψ`（来自 Step 2 的 (2.75)）与 `|G_kk|` 下界，得到误差界。基本是套用，便宜。

## T86 — `RBM1D/Gauss/FlucVanish.lean` · M · 等 T84、T85

**消失引理**：设 `Z_k := (1−E_k)(G_kk − m)`。若在乘积 `Z_{k_1}···Z_{k_{2p}}` 中某个指标
（比如 `k_1`）**恰好出现一次**，则

    |E[∏_i Z_{k_i}]| ≲ (替换误差) × (其余因子的界)

做法：把每个 `Z_{k_i}`（`i ≠ 1`）换成 `Z^{(k_1)}_{k_i}`（用 `G^{(k_1)}` 造），
换完之后它们与第 `k_1` 行严格独立，于是 `E_{k_1}` 可以穿过去打在 `Z_{k_1}` 上，得 0（T84）；
替换误差由 T85 逐项估计。

## T87 — `RBM1D/Gauss/FlucCount.lean` · L · **大头**

把 `E|∑_k t_k Z_k|^{2p}` 展开成对 `(k_1,…,k_{2p})` 的求和，按 **不同指标的个数** 分层：

* 有指标只出现一次的那些层，用 T86 压掉；
* 其余层：每个指标至少出现两次 ⟹ 不同指标至多 `p` 个 ⟹ 权重求和给出额外的因子。

配上 `|Z_k| ≺ Ψ`、`∑_k|t_k| ≤ 1`、`|t_k| ≤ CW⁻¹`，得到 `E|∑t_kZ_k|^{2p} ≲ (N^ε Ψ²)^{2p}`。

**我们只需要两组系数**（`t_k = W⁻¹1(k∈I_a)` 与 `t_k = S_{ik}`，都是块上的均匀平均），
如果一般权重的记账太痛，**可以只对这两组做**——签名照 `EntryBound` 现有的来。

## T88 — `RBM1D/Gauss/FlucAvg.lean` · M · 等 T87

用 T73 的 `stochDom_of_momentDom` 把 T87 的矩界落成 `≺`，得到 **(4.12)**；
再配 `Green/EntryBound.lean` 已有的确定性部分（`norm_condExp_le`、`norm_sum_coef_green_sub_le`）
与 T83 的 `hIBP`，卸掉 `hFA`，得到 **(4.5)**。
**不要改 `EntryBound` 的签名。**

---

## T94 — `RBM1D/Gauss/FlucIter.lean` · L · **[40] 的最后一条，(4.12) 的真实缺口**

**背景**：T88 把 (4.12) 的其余部分全部证完了，`hFA` 已在原签名下卸掉、(4.5) 已得证，
但 (4.12) 本身还差一口气，缺口被隔离成单独一条假设 `hsmall`（见 `docs/STATUS.md`
「⚠⚠ (4.12) 尚未成为定理」一节）。**这不是记账问题，也不是截断问题。**

T87 现在给的是

    E|Σₖ tₖ Zₖ|^{2p} ≤ (2p−1)·ε·B^{2p−1} + c^p p^{2p} B^{2p}

(4.12) 要的是 `≲ N^{δp} Ψ^{4p}`。第二项没问题（`c = W⁻¹ ≤ Ψ²` 给出 `Ψ^{4p}`）。
**第一项**即便取到理想参数 `ε ≍ Ψ²`（T85）、`B ≍ Ψ`，也只有 `Ψ^{2p+1}`——
`p=1` 时是 `Ψ³`，要的是 `Ψ⁴`。差的正是第六批开头记下的那个 `Ψ^{1/2}` 亏空。

**根因**：T86 的小行替换**只迭代到一阶**（`Z_{kᵢ} ↦ Z^{(k_{i₀})}_{kᵢ}` 只换一次）。
标准证法要迭代到 `2p` 阶，残项才是 `Ψ^{4p}`。

**要做的**：把 `Gauss/FlucVanish.lean` 的消失引理 + `Gauss/MinorReplace.lean` 的替换误差
组织成一个**可迭代 `2p` 次**的归纳，每次替换换掉一个还只出现一次的指标，
残项按 T85 的 `ε` 级数累加。

**硬性约束（照抄，不要改）**：

* **不要改 `Green/EntryBound.lean` 的任何签名**，也不要改 T87 `Gauss/FlucCount.lean`
  与 T88 `Gauss/FlucAvg.lean` 的现有陈述——只把 `hsmall` 从假设变成定理。
* **不要用 `1_Ω` 记账**：T86 的消失性依赖 `E_k[(1−E_k)X] = 0`，而 `1_Ω·X` 破坏它，
  且 `1_Ω` 不是 `FinDepOffRow`、无法从 `E_k` 里提出来。STATUS 里已经确认
  **任何 ≺ / 指示函数记账都补不回这一项**。截断接缝要走 T88 已经打通的
  `flucBound_env`（`B = 2(η_t⁻¹+1)`、`ε = 4η_t⁻¹` 逐点一致）那条无条件方向。
* 复用而不是重证：`FinDepOffRow`（T84）、`condRow` 的幂等与 `E_k∘(1−E_k)=0`（T84）、
  `MinorReplace` 的三元组版与 Ψ-级版（T85）、`HasLoneSlot` 与分层矩界（T87）。

**不要重证 [40] 的定理，只证我们需要的那一部分**（Jun，第六批批注）。
这是 [40] 自证路线上最后一块；补上之后 (4.12) 与 (4.5) 全部是无假设定理。
