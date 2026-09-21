# 任务队列

> ## ⭐⭐⭐ 当前优先级：**T223**（`xi2` 漏共轭，原地改定义）‖ **T227**（Step 6 包络量词改到窗口，(2.71) 的门）> **T222**（`CutHyp.moment` 条件版生产者，钝版逐步自举）‖ **T225**（`Q` 版生成元恒等式）> T212 ‖ T219 ‖ T220 ‖ T218 > T224 > T226 > **T205**（第二遍 (2.71)）> T216 > T215 > T217 ‖ T221（文档/去重）> T159 > T58。**Theorem 2.6：等其余各块无高风险项后再开（Jun）**（2026-09-21 17:55，Cowork）
> **⚠ 更正（T176，2026-09-21）**：本表此前把 T58 的 ②③（`Lemma514`）记作「→ T146（完成）」，**是错的**——T146 交付的是 `hrhs`，`Lemma514` **现在无主**，且其唯一生产者 `SumZeroDyn.lemma514_flow'` 落在 T118 禁用的 fiat 路线上。另：**`Thm221.step` 只收裸 `Cond272` 而全链要带 `N^c` 增益的 `hregS`**，这条接口错配无人负责、挡在总装最后一米。见 STATUS「T176」。
>
> **⚠ paper-deltas 不要自己取数字号**（今天撞号五次）：`#` 栏写临时号 `T<工单号><字母>`（如 `T177a`），数字号由 Cowork 统一分配。见 `CLAUDE.md`「取号纪律」。
>
> **范围（Jun 2026-09-21）**：**Theorem 2.6（普适性、QUE、`StepTwoClaim`）暂缓，不开单**（**Jun 2026-09-21 12:20 补充：等其余各块都没有高风险项后再开启**）；T153（Theorem 2.2 的概率一半）排在六步之后。**当前目标 = 六步循环（Theorem 2.21 + Lemmas 2.18–2.20）正确无误**，终点核对是 T159。
>
> **T58 的四项交付物在矩路线下的归属**：① Step 2 路线 A → **放弃**，走路线 B（T132c）；②③ `Lemma514` → **T146**（矩 Duhamel 重新生产）；④ Step 6 层级 → **T152**。T58 只剩表示桥与 (5.19)（已由 T140 以更正形式证出），**降为清理单**。
>
> **T132 是随机层真正剩下的那堵墙**（T74/T76 判定逐路径 `duhamel`/`bdg` 在 `√u·X` 下不可卸，之后没人接手）。规格见下文「T132 规格」。T133、T134 是它的两块前置零件，可并行。
>
> **Jun 已裁 paper-deltas #72（原 #66）：论文不缺数学，走 (c) 收窄引用，(2.76) 陈述不改。**
> `(+,+)` 的来源是 **Lemma 5.11 在 `n = 2`**（非交错电荷，(7.16) 情形 1），p.70 只是把出处写成了 (2.76)。
> T115/T120 写进文件头的「旁证：Lemma 5.14 排除常值 σ」是**误读**，由 T122 顺手更正。
> **T122 是主定理总装路上唯一剩下的「论文侧」缺口**，下一个空出来的 agent 去接它；规格见下文「T122 规格」。
>
> ---
>
> ## ⚠ T58 的优先级已下调（2026-09-21，Cowork 据 T114 第 1 步的勘察改判）
>
> **Jun 当时把 T58 提到最高，依据的是我的判断「它是 Theorem 2.21 的唯一阻塞」。
> T114 第 1 步的勘察证明那个判断是错的**：Step 2 有两条路线，
> **路线 B（`Step2Moment.step2`，矩路线）不需要 T58**。
> 所以 **T58 不再是主定理的阻塞**，它仍然是论文 §5.2 的内容（(5.19)(5.21) 等），但可以排在后面。
>
> **新的最高优先级是 T115**（见下），它是纯确定性记账、**现在就能开工、且不依赖任何未完成的单**。
>
> ---
>
> ## （已作废）T58 是全队最高优先级（2026-09-21，Jun 指定）
>
> **下一个空出来的 agent（或你手上这张单做完时）无条件去接 T58。**
> 不要再挑「看起来边界更清晰」的小单——T58 是**待形式化那一条（Theorem 2.21 六步总装）的唯一阻塞**，
> 其余所有单做完，主定理仍然拼不起来。
>
> 它不难：**设计决定已由 Cowork 拍板**（保留 `LoopIdx` 为规范表示，把 T42 的十来条张量算子共轭过去，
> 走 `List.ofFn` / `List.get`），规格与**验收标准**都写在下文「T58 交接」，Mathlib 引理全是现成的。
> 接手不需要再做任何判断，只要照着做。
>
> ---
>
> ## 扩到 4 条并行车道（2026-09-20，Jun 指定）
>
> **给已经在跑的两个 agent 的指令（优先级高于你手上正在做的细节，读到就执行）**：
>
> > Jun 要把并行度从 2 提到 4，但他人不在那台机器旁边，**没法再开终端窗口**。
> > 所以：**你自己用 Task/Agent 工具扇出子 agent**，不要等新窗口。
> > 做法：你保留自己当前那张单，**另外挑一张待认领的单，改表格认领到「<你的名字> 子 agent」并提交**，
> > 然后派一个子 agent 去做它，把该单的「规格」段落整段贴给它当任务说明。
> > 一次最多扇出 **1 个**子 agent（连你自己两条车道），全队合计不要超过 4 条 —— 
> > **周额度是真会撞的**（T108 那个 agent 就是在读文档阶段撞上限直接中断的）。
> > 子 agent 同样守全部硬规则：只碰自己那个新文件、不留 `sorry`、不写 `axiom`、
> > 不改冻结签名、认领先提交、绿了就 commit + push。
> > 子 agent 做完或撞限中断，**由你负责把表格改回真实状态**，不要留假的「进行中」。
>
> **挑单顺序**：T58（表示桥，卡主定理，最值钱）> T110（`FlucGain` m≥2，最高风险）
> > T109（`TraceMomentBound` p≥2）> T111 > T1。四张的规格都已写好，在本文件下半部分。
>

> **给新开 agent 的一句话（照抄）**：
>
> > 读 `docs/TASKS.md`，挑一张**待认领**的单，**先改表格把认领改成自己的名字并单独提交**，再开工。
> > 每张单只碰它指定的那个新文件；唯一的共享文件是根 `RBM1D.lean` 的 import 列表，
> > **只做点插入，绝不整体重排**。硬规则：不留 `sorry`；做不了的写成 `structure` 字段或定理参数，
> > **绝不用 `axiom`**（仓库有硬性公理审计 `#assert_rbm_axioms`）；不许改被标为冻结的接口签名；
> > 偏离论文记进 `docs/paper-deltas.md`；只按文件名 `git add` 自己那几个；**跑完 `lake build` 绿了就 commit 并 push**。
> > 队列空了按「永不停工规则」自己挑活，并在表里补一行说明在做什么。
>
> **四条车道（互不依赖，可同时跑）**：
>
> | 车道 | 单 | 说明 |
> |---|---|---|
> | A | **T83** | p.50 的高斯分部积分，Cowork 已交接，规格在「T83 交接」（已被接） |
> | B | **T110** | `FlucGain` (m ≥ 2)，全队最高风险，**第 0 步先手算 m = 2 再决定往下建**，规格在「T110 规格」 |
> | C | **T109** | `TraceMomentBound` (p ≥ 2)，Wick + 闭走计数，标准但繁 |
> | D | **T58** | 表示桥，设计决定已由 Cowork 拍板，规格在「T58 交接」——**这条卡着主定理，优先级最高** |
>
> 备用：**T111**（两条分布相等）、**T1**（初等不等式，最轻）。
> **D 车道最值钱**：它一通，Theorem 2.21 的六步总装就从「阻塞」变成「排队」。
>
> ---
>
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
| T1 | `1 − ‖ρ(ξ)‖ ≍ \|1−ξ\|^{1/2}` 的定量估计 | `Propagator/Decay.lean` | Claude Code | **完成**（`Propagator/Rate.lean`；数学内容此前已由 T1c 齐备，本单补的是 `≍` 打包与 `ellHat` 的双边识别，并给出复 ξ (2.52) 的闭式路线） |
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
| T58 | §5.2：(5.10)–(5.15) 的 `L−K` 层级重组、Def 5.4 的 `E⊗E`、(5.19)、积分形式 (5.20)(5.21) | `Hierarchy/Dynamics.lean` | Claude Code | **T118 (iii) 完成**（`Hierarchy/DriftDef.lean`，473 行，全量绿、审计 8899）：`driftF` 是 **`def`**，`F = Ẽ + ∑_{l_K≥3}[K∼(L−K)]^{l_K} + E^{((L−K)×(L−K))}` 由 `Hyp.F_unique` **证出**（`eGterm 0` 精确抵消，无第三项）。补上两条**本来缺失的桥**：`eGterm_eq_eG`（此前 `Decay.eG` 与漂移里的 `Gauss.eGterm` 一直在说不同的函数）、`sum_couplingLen_erase_two`（`∑_{l_K≠2} = ∑_{l_K>2}` 且截到 `l_K ≤ n`，两侧都是定理）。`F_decay` 的确定性内核 `fastDecay_driftF` 已给。fiat 审计干净、可满足性已验。**(5.19) 与表示桥在 T140 已完成**；`F_le` 的 Ξ-记账留 T165。见 STATUS |
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
| T83 | 卸掉 `Green/EntryBound.lean` 的 `hIBP`（p.50 的高斯分部积分显式式） | `Gauss/IBP.lean` | Claude Code | **完成**（(a)(b)(c) 全部落地，`hIBP` 可在冻结签名下卸掉；余 `hprod`/`hminor` 两个输入，见 STATUS） |
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
| T94 | **把 `FlucVanish` 的机器迭代到 `2p` 阶**：卸掉 T88 隔离出来的 `hsmall`，让 (4.12) 真正成为定理 | `Gauss/FlucIter.lean`（新建） | Claude Code | **完成**（`hsmall` 按字面为假，改换 T87 的界本身；(4.12) 仅余接口 `FlucGain`，其 `m ≥ 2` 需迭代小行，见 STATUS） |
| T95 | **为高斯模型造 `RowChaos` 实例**（T82/T93 的 `LDEQuad.lean` 文件头「What is not done here」第 2 条）。关键：`B` 取**小方阵预解式** `(H^{(i)} − z)⁻¹` 而不是 `greenMinor`——它由 `norm_green_le` 全局有界 `η⁻¹`、连续、且只读 off-row 坐标（`Hflow_submatrix_congr_offRowCoord`），而 `greenMinor` 因 `G_ii` 无全局下界而无界；两者对**每个 ω** 相等，由 `inv_minor_resolvent` + T91 的 `green_diag_ne_zero`。`co`/`eps` 由 `Xentry` 的 `idxKey` 分支读出（同 T81）。**不碰 `Gauss/LDEQuad.lean`** | `Gauss/LDEQuadInst.lean`（新建） | **Claude Code #2** | 已完成 |
| T96 | **`hLquad` 的最后一段**：把 T95 的矩不等式 `E[ldeQuadLHS^p] ≤ C_p u^{2p} E[ldeQuadRHS^p]` 翻成 `diag_bound_stochDom` 要的 `StochDom P ldeQuadLHS ldeQuadRHS`。难点：控制 `ldeQuadRHS` 是**随机**的，`stochDom_of_momentDom`（T73）只接受确定性控制；走 `StochDom.of_det` 或先用好事件上的确定性控制夹住。**不碰 `Gauss/LDEQuad.lean`、`Green/EntryBound.lean`** | `Gauss/LDEQuadDom.lean`（新建） | **Claude Code #2** | 已完成 |
| T97 | **总装 (4.2)(4.3) 的高斯版**：把 T91/T92/T96 的四条 `StochDom`（`hLrow`/`hLcol`/`hLdiag`/`hLquad`）喂进 `entry_bound_stochDom` 与 `diag_bound_stochDom`，得到对高斯流无 LDE 假设的 Lemma 4.1。需核对 `zt E t` 的 `im ≠ 0`（由 `0 ≤ t < 1`）与各处 `Sblk` 参数一致。**不碰 `Green/EntryBound.lean`** | `Gauss/EntryBoundGauss.lean`（新建） | **Claude Code #2** | 已完成 |
| T98 | 维护：把 T91–T97 里核实过的 Mathlib API 记进 `docs/mathlib-api.md`；重跑全库重复引理扫描（T90 之后新增约 200 条声明），只下沉**自己文件里**的重复，别人的列进 STATUS | `docs/mathlib-api.md`、`docs/STATUS.md` | **Claude Code #2** | 已完成 |
| T99 | 审计：从 T97 的 (4.2)(4.3) 到 `Hierarchy/Step1.lean` 的 `Lemma41Flow` 还差什么？逐条核对时间一致性（`u ∈ [s_N,t_N]`）所需的输入，产出下一批工单 | `docs/STATUS.md`（审计记录） | **Claude Code #2** | 已完成 |
| T100 | **`‖X‖ ≺ 1`**：高斯带状矩阵的算子范数界，卸掉 `Gauss/Model.lean` 的 `OpNormBound` 字段（paper-deltas #49 的公开缺口）。迹/矩方法：`E‖X‖^{2p} ≤ E Tr(X^{2p})`。T101 之外的另一半时间一致性前提 | `Gauss/OpNorm.lean`（新建） | Claude Code | **完成（有条件）**（`opNormBound_of_traceMomentBound`；缺口收窄为 `TraceMomentBound`（p ≥ 2 的 Wick + 闭走计数），p = 1 已无条件，见 STATUS） |
| T101 | `stochDom_timeIcc_of_holder` 的变体：Hölder 模只在**高概率事件**上成立（或常数本身被 `≺` 控制）。与 T100 独立 | `Gauss/DominationHolder.lean`（新建） | Claude Code | **完成**（高概率版与 `≺`-常数版；后者可零胶水接 T100；严格强于 T73/T75） |
| T102 | `Lemma41Flow` 的接口对齐 + 界传递（T99 审计的 (A)(B) 两块，**不依赖时间一致性**）：`‖Lval (pmLoop a b)‖ = Lre`、`goodEv ↔ goodSet`、`llMax²` 由逐 `(i,j)` 的界合成、随机控制经假设传到确定性 `Φ` | `Gauss/Lemma41Glue.lean`（新建） | **Claude Code #2** | 已完成 |
| T103 | 审计：全库**仍被携带的假设**清点（`Flow/Hypotheses.lean` 的 structure 字段、各文件的 `Prop` 参数），逐条标注「已被高斯层卸掉 / 可卸但没人做 / 真缺口（缺什么）」，产出下一批工单 | `docs/STATUS.md`（审计记录） | **Claude Code #2** | 已完成 |
| T104 | **卸掉 `GaussIBP`**（`Gauss/LDEQuad.lean` 的两个字段，T103 审计出的唯一「可卸未卸」项）。`stein`：把 `SteinMatrix.matrixStein` 的逐坐标 Fubini 论证从「全局有界」换成「多项式增长」——一维的 `integral_mul_gaussianReal`（`Gauss/Stein.lean:94`）本来就只要三条可积性，**不需要光滑截断**；`polyInt`：初等高斯矩。卸掉后 T93/T95/T96/T97 全链无携带假设 | `Gauss/IBPPoly.lean`（新建） | **Claude Code #2** | 已完成 |
| T105 | 维护：`GaussIBP` 已由 T104 卸掉，把 `hG : GaussIBP d` 从**我自己那几个文件**的签名里删掉（`LDEQuadInst.lean`、`LDEQuadDom.lean`、`EntryBoundGauss.lean`、`Lemma41Glue.lean`），内部改填 `gaussIBP d`。**不碰 `Gauss/LDEQuad.lean`**（那是别人的，接口保持不变） | 上述五个文件 | **Claude Code #2** | 已完成 |
| T106 | **`u ↦ ‖G_u − m‖²_max` 的 Hölder 模**（T99 的 (C) 里唯一还没人做的一块，且**不依赖 T100**）：纯确定性。预解式恒等式 + `norm_Hflow_sub`（`‖H_u−H_u'‖ = \|√u−√u'\|·‖X‖`）+ `\|√u−√u'\| ≤ \|u−u'\|^{1/2}` + `z_u` 的 Lipschitz 性，给出 `\|llMax_u² − llMax_u'²\| ≤ C·η_t⁻²(‖X‖+1)·\|u−u'\|^{1/2}`。配 T101 的 `≺`-常数版与 T100 的 `‖X‖ ≺ 1` 即可关掉 `Lemma41Flow` | `Gauss/FlowHolder.lean`（新建） | **Claude Code #2** | 已完成 |
| T107 | **带时间指标的 Lemma 4.1**（T107 原计划的障碍一，纯接口重做）：用 `Green/EntryBound.lean` 的**确定性内核** `norm_sq_green_le_blk` / `norm_sq_green_diag_sub_le_blk` 加自己的 `StochDom.of_det` 调用，把 (4.2)(4.3) 的指标集扩成 `TimeIcc s t N × …`（时间与谱参数随指标走）。`δ N := (scale E N (t N))⁻¹^{1/6}`（`scale` 对 u 反单调，方向正确）。**不碰 `Green/EntryBound.lean`** | `Gauss/EntryBoundTime.lean`（新建） | Claude Code | **完成**（新建 `Gauss/EntryBoundTime.lean`，501 行，全量绿、审计 9206；`Lemma41FlowGauss.lean` 一字未动）：`entryBoundFlow_floor` 交付 `EntryBoundFlow'`（逐字不变、控制多一项地板），**地板代价为零**（与无条件的 `W⁻¹` 复合，`B := 1`）。**四条下游陈述用 `rfl` 探针验证确为 defeq**，旧签名一字未改。⚠ **row/col 侧也有 T166 说的指标加宽缺口**（`EntryBoundFloor.lean` 只有对角版），本单补了 `entry_bound_stochDom_floor_idx`，建议下沉到 `Green/EntryBoundFloor.lean` 并排。额外：`step1Hyp_gauss_of_scale'` 删掉 `hEntry`——**(4.2) 已从 `Step1.Hyp` 的假设表里彻底消失**，只剩 `DiagBoundFlow` |
| T108 | **`Lemma41Flow` 总装**（依赖 T107 + T100）。还要处理障碍二：`Lemma41Flow` 的控制 `Φ N u` 依赖时间，而 T101/T75 的时间网桥只吃 `Φ : ℕ → ℝ`；需给桥补一个 `Φ` 的缓变假设，或在本文件重做网论证 | `Gauss/Lemma41FlowGauss.lean`（新建） | Claude Code | **完成**（`lemma41Flow` 对任意 `Φ ≥ 0` 成立——**不需要时间网**，障碍二不成立；缓变桥仍已交付，见 STATUS） |
| T109 | **`TraceMomentBound` (p ≥ 2)**：`E Tr(X^{2p}) ≤ C·N`。**规格见下文「T109 规格」：建议用已证的 `gaussIBP` 跑矩递推绕开 Wick 与走计数，第 0 步先验因子**。卸掉 T100 收窄后剩的那条接口，进而 `‖X‖ ≺ 1` 无条件 | `Gauss/TraceMoment.lean`（新建） | Claude Code | **完成**（`‖X‖ ≺ 1` 无条件，`OpNormBound` 已卸，paper-deltas #49 关闭；收口改用对数凸性，见 STATUS） |
| T110 | **`FlucGain` (m ≥ 2)**：小行替换迭代到 `2p` 阶，卸掉 (4.12) 最后一条接口。承 T94（`m = 0`、`m = 1` 已证）。**规格见下文「T110 规格」，第 0 步先手算 m = 2** | `Gauss/FlucIterHigh.lean`（新建） | Claude Code | **完成**（第 0 步：增益**乘性**，且机制是恒等式；`FlucGain` 对所有 m 由 `MinorDiffGain` 得出，m=2 已无条件） |
| T111 | **两条分布相等**：(2.39) 与 (6.1)，外加 1-loop 的 `TransferLoop1`。**规格见下文「T111 规格」：先查是不是同一个 `X` 的确定性标度；真换律就走 `gaussianReal_map_const_mul` + `infinitePi_map_pi`** | `Gauss/DistEq.lean`（新建） | Claude Code | **完成**（三条全部为定理；全是逐点相等，不需要任何分布论证） |
| T112 | **`≺` 在条件期望下的保持** + T83 剩下的两个输入 `hprod`/`hminor`。**规格见下文「T112 规格」** | `Gauss/CondDom.lean`（新建） | Claude Code | **完成**（通用工具 `stochDom_condRow_of_envelope`；`hIBP` 已在冻结签名下卸掉并编译验证；**发现 `hminor` 对角处为假**，见 STATUS） |
| T113 | **`MinorDiffGain` (m ≥ 3)**：迭代小行差的大小，(4.12) 的最后一条输入。承 T110（`m ≤ 2` 已无条件，且已证增益是**乘性且由恒等式给出**）。**纯 Green 函数 + 局部律，概率那一半已卸干净** | `Gauss/MinorDiffGain.lean`（新建） | Claude Code | **完成（有界字长版）**（每阶估计已证，m=3 体检通过；`MinorDiffGain` 原定义因对 m 一致性不可能成立，见 STATUS） |
| T114 | **Theorem 2.21 的总装**：由六步产出 `Steps`，再经已有的 `Bounds_of_Steps` 得 `Thm221`。**规格见下文「T114 规格」。等 T58** | `Flow/Thm221.lean`（新建） | Claude Code | 第 1 步**完成**（八字段全部逐字对上，对账表见 STATUS；暴露 `0 ≤ s` vs `0 < s` 的不匹配与三处 T58 消费点）；Lean 总装仍等 T58 |
| T115 | **⭐⭐ 总装的确定性缺口**：`h0`/`h12`/`hs1`/`hs2` 全树无生产者，但按文档都可由 Steps 1–2 的产出推出。**纯确定性记账，不依赖 T58，现在就能开工**。规格见下文「T115 规格」 | `Hierarchy/StepGlue.lean`（新建） | Claude Code | **完成（条件）**（`h0`、`h12`@m=1 无条件；`h12`@m=2 与 `hs1`/`hs2` 条件于 `AprioriDecayAll`/`Eq45Flow`。**发现论文真缺口：(2.76) 只有 `(+,−)`，`(+,+)` 无来源**，见 STATUS） |
| T116 | **`Step1.Hyp` 的 `lift` 与 `cont`**：`NetLift`（把固定时刻的 `≺` 提升到时间网）与 `cont` 的高概率事件。注意 T108 已证「总装不需要时间网」，**先查 `lift` 是不是也可以整条绕开**（第 0 步） | `Gauss/Step1Hyp.lean`（新建） | Claude Code | **部分完成**（`cont` 无条件卸掉；`lift` **不可绕开**（`badSet` 把并放在概率里），已归约为放宽阈值的网引擎 + 四样待补，见 STATUS） |
| T117 | **Step 6 的七条随机层假设**在高斯实现下逐条落地（T114 勘察列为总装路上的一批）。**第 0 步：先把七条逐条列进 STATUS，标明哪几条已由现有定理供给**，再决定要不要拆单 | `Gauss/Step6Hyp.lean`（新建） | Claude Code | **勘察完成 + 部分落地**（七条表见 STATUS；`h527`(5.127) **精确恒等式**已证、`hint2` 已卸；余 6 条建议拆两张：A 归 T58，B（一阶矩反向桥）现在可开工） |
| T118 | **`SumZeroDyn.Lemma510` / `LKDecay` 与 T59 的形状不匹配**（`SumZeroDyn.lean:62` 自己记了「对不上」）。**第 0 步：说清楚是哪一侧该改**，不要两边硬凑；结论报 Cowork 裁 | `Hierarchy/SumZeroDyn.lean` 侧或新文件 | Claude Code | **完成（裁定）**：**两侧都不该改**——缺的是 wrapper（已写好 `DecayBridge.lean`）。唯一该动的是给 `LKDecay` 补 `\|L\|` 那一半（补强）。余下拆三张，见 STATUS |
| T119 | **`hIBP` 终定理的局部律侧输入**：`hstabP`/`hstabM`（`CondStable`）、`hrepl`、`hloc`、`hΩ`。这些是 `trace_green_sub_mul_Eblk_stochDom_of_localLaw` 现在带的假设，**目前不属于任何工单** | `Gauss/CondStableInst.lean`（新建） | Claude Code | **完成**（`hloc`/`hrepl`/`hstab*` 全卸，8→3 条假设；**发现固定 t 下 `L^max ≍ W⁻¹` 是确定性的**，T112 的判断被推翻，但时间依赖区制下失效，见 STATUS） |
| T120 | **`AprioriDecayAll`（四电荷版的 (2.76)）** —— T115 查出的**论文缺口**，`(+,+)` 无来源且便宜补法差一个 `A_u`。**不要硬证**：先把三条归约（循环性、共轭）落成定理，把缺口精确收缩到 `(+,+)` 一个电荷，写进 STATUS 等 Jun 裁 | `Hierarchy/ChargeReduce.lean`（新建） | Claude Code | **完成**（三条归约全通，缺口收缩为单一陈述 `AprioriDecayPP`；`K` 侧四电荷本就齐备，缺的只在 `L` 侧。**Jun 已裁（2026-09-21）：走 (c)，`(+,+)` 由 Lemma 5.11@n=2 供给 → T122**） |
| T121 | **`Eq45Flow`**：(4.5) 对 `u ∈ [s,t]` 一致。(4.5) 本身已证（`avg_bound_stochDom`），差 p.51 的一致化 | `Gauss/Eq45Flow.lean`（新建） | Claude Code | **完成**（是 T108 的情形：不需要时间网；`Eq45Flow` 已卸，条件为三个带时间指标的输入，见 STATUS） |
| T122 | **⭐⭐ 卸掉 `AprioriDecayPP`：Lemma 5.11 在 `n = 2` + 连续性自举**（Jun 裁 #72）。`(+,+)` 是非交错电荷，`SumZeroDyn.bound_nonAlt` 已覆盖；缺的只是 `n = 2` 自二次项的自举收口（`Step2Moment` 那一套）。**第 0 步：判定自举挂在 `≺` 层（前缀区间重新实例化）还是矩层（`MomentHypPP`）**，报告后再动手 | `Hierarchy/Step2PP.lean`（新建） | Claude Code | **完成**（#72 解决：(2.76) 不改，`(+,+)` 出自 Lemma 5.11@n=2；自举挂在**逐路径事件层**。`AprioriDecayPP` 本身卸不掉也不需要——消费者已全由带撇变体供给，见 STATUS） |
| T123 | **一阶矩反向桥**（T117 拆单 B，不依赖 T58）：`\|Y\| ≺ Φ` + 确定性包络 + 多项式下界 ⟹ `∫\|Y\| ≺ Φ`，卸 Step 6 的 `hq11`/`hq13`。**第 0 步：先看它是不是 `momentDom_of_stochDom`（p = 1）+ Jensen/Hölder 的两行推论**，是就别造新轮子 | `Gauss/Envelope.lean`（加定理）+ `Gauss/Step6Hyp.lean` | Claude Code | **完成**（通用工具进 `Gauss/Envelope.lean`；`hq11`/`hq13` 已卸且对任意 `Sample` 成立，`sharpExpect_step6` 只剩四条、全绑 T58） |
| T124 | **(4.5) 的三个带时间指标输入**（T121 余项）：`IBPFlow`/`FlucRowFlow`/`FlucBlkFlow` 的生产者。**照 T107 的做法**——固定时刻的证明若对 `(N, ω, u)` 逐点，就把 `StochDom.of_det` 在放大的指标集上重做，不用网。**第 0 步：逐条查 T119 `CondStableInst` 与 `Lemma41Glue.trace_green_sub_mul_Eblk_stochDom` 的证明是否逐点**；哪条不是就报告，别上网 | `Gauss/Eq45FlowInputs.lean`（新建） | Claude Code | **完成（到网为止）**（判定：生产支配必须用网，与 T121 的传递不矛盾；补了带随机时间依赖控制的网引擎；余 `hΩ`/三个 `hfix`/三个 `hHol`，见 STATUS） |
| T125 | **`Step1.Hyp.lift` 的余项**（T116 余项，paper-deltas #74）：四样里 (1)–(3) 是确定性的（`gloop` 对 u 的连续模、`aprioriRhs` 的缓变区制、多项式下界）；(4) Lemma 5.1 在阈值 `2 + o(1)` 处的版本。**第 0 步：看 `Loop/ContinuityAssembly.lean` 的 `lemma_5_1`/`lemma_5_1'` 里阈值 2 是不是写死的**；若只是证明里的常数，就加一个阈值参数 `C ≥ 2` 的推广版，旧定理作为特例保留，**不改旧签名** | `Gauss/Step1Hyp.lean` + `Loop/ContinuityAssembly.lean`（加推广版） | Claude Code | **完成**（阈值只是证明常数，(4) 不是新数学；四项全卸，`lift` 闭合，`Step1.Hyp` 在 `step1` 已有假设下完整，只余 T107） |
| T126 | **无条件的 `SumZeroDyn.LKDecay`**（T118 拆单 (i)）：把 `DecayBridge.lkDecay_of_highProb` 的输入——`LKDecayEvent` 对每个 `m, τ, D` 高概率——定量闭合。`Decay.lemma59` 是确定性内核、`loopDecay_lk_of_event` 已是纯重述，缺的只是**它的前提事件沿流高概率**。**第 0 步：把 `Decay.lemma59` 的前提逐条列出，逐条对到现有生产者**（`Steps.localLaw`/`aprioriDecay`、T108 `lemma41Flow`、T107 的带时间指标 Lemma 4.1），列不上的报告。**Cowork 裁：`LKDecay` 的定义不改**（19 条签名穿过它）；paper-deltas #78 的 `|L|` 那一半另立 `LDecay`（同文件、同证法顺手产出），不并进 `LKDecay` | `Hierarchy/DecayBridge.lean`（续） | Claude Code | **完成**（`LKDecay` 在 T130 输入之外无条件；`cKdecay` 的多项式上界是新造的分析输入；`LDecay` 同证顺出，见 STATUS） |
| T127 | **`Lemma510.EE_le` 由 `Decay.norm_eTens_le` 解锁**（T118 拆单 (ii)）：三块小管道——(a) `glueLoop = gloop (J k b b')`（T74 的遗留项）；(b) `Gauss.eeTens : LoopIdx → LoopIdx → ℂ` 与 `Hierarchy.EE : … → LoopArg L ((n+2)+(n+2)) → ℂ` 的类型适配；(c) `Band → Dims` 转换（全仓库没有；以后每次 `Gauss → Hierarchy` 交接都要用，**做成通用的**）。**只做 `EE` 这一半，不定义 `F`**（`F` 归 T58，见 T118 的 fiat 警告）| `Hierarchy/EEBridge.lean`（新建） | Claude Code | **完成**（三块管道全通，(a) 的共轭事实已证、T74 的约定升级为定理；`EE_le` 逐路径可得，`≺` 版缺一条控制的多项式下界——真缺口，见 STATUS） |
| T128 | **(4.5) 的三个 `hfix`（固定时刻）**（T124 余项 (2)）：`FlucRowFlow`/`FlucBlkFlow` 的固定时刻输入目前走 `stochDom_flucAvg_*`，带未卸的 `hsmall`。**第 0 步：改走 `FlucIter.stochDom_flucAvg_blockAvg_iter` 那条 `FlucGain` 路线**（T110：m ≤ 2 无条件；T113：有界字长版）——它**没有** `hsmall`，只要 `W⁻¹ ≤ ρ²`。逐条对：哪个 `hfix` 能由 `_iter` 供给、哪个不能、`Sblk` 权重是否也有 `_iter` 版。`IBPFlow` 那条的 `hfix` 走 `condExpDiag_stochDom_of_highProb`，其 `hΩ` 并入 T130。**不要去硬证 `hsmall`**（T87 已写明确定性包络给不出它） | `Gauss/Eq45FlowInputs.lean`（续） | Claude Code | **部分完成**（两条涨落输入已卸，走 T94 迭代路线；`hfixIBP` 未卸，缺环节已精确命名；另需按字长分级的 `FlucGain` 接口，见 STATUS） |
| T129 | **`condExpDiag` 对 u 的模**（T124 余项 (3) 里真正新的那半，paper-deltas #79）：Green 函数那半已有（T106 `norm_green_flow_sub_le`）；`condExpDiag` 那半的难点是随机常数 `‖X‖` 落在**行条件期望的积分内部**，不是逐点模的推论。**第 0 步：判定能否把模写成「随机常数 `C(ω) = E_i[‖X‖+1]` × `|u−v|^{1/2}`」并证 `C ≺ 1`**（`‖X‖ ≺ 1` 是 T109；条件期望下 `≺` 的保持是 T112 `CondDom` 的主题——**它不是自动的**），再看 T124 的 `stochDom_timeIcc_of_unifDom` 是否接受**随机**的 Hölder 常数；不接受就报告需要的引擎形状，别硬凑 | `Gauss/CondExpModulus.lean`（新建） | Claude Code | **完成**（模无条件；随机常数 `E_k[‖X‖] ≺ 1` 绕开 T112——靠「只重采一行」+ 锐的列范数界；引擎不需改，见 STATUS） |
| T130 | **`hΩ` 的 u-一致版**（T124 余项 (1) + T119 留下的 `hΩ`）：(4.4) 在**每个** `u ∈ [s,t]` 上成立的高概率事件。这是一条网命题，用 T124 刚补的网引擎（`UnifDomIcc`/`stochDom_timeIcc_of_unifDom`）+ T109 `‖X‖ ≺ 1`。**第 0 步：先写清 (4.4) 在 Lean 里的事件是什么、固定时刻由谁产出**；若事件含 `1(‖G_u‖_max ≤ 2)` 这类对 u 不连续的指示函数，照 T116 的**放宽阈值**做法（`netLift_of_relaxed`），并写 paper-delta | `Gauss/Eq45FlowInputs.lean` 或新文件 | Claude Code | **完成**（`hΩ` 的 u-一致版已有生产者，条件为弱局部律 + 两条区制边条件；`t_N → 1` 的坑不适用，见 STATUS） |
| T131 | **小单：T123 的 `hint` 尾巴**。`quad11_unifDetDom`/`quad13_unifDetDom` 仍带可积性假设 `hint`；现成的 `integrable_sample_lkErr_mul` 是 **ℂ 值乘积**，桥要 **ℝ 值** `lkErr · lkErr`。补一条 ℝ 值版的可积性（由 ℂ 版取范数，或直接由确定性包络 `‖G‖ ≤ η⁻¹`），**对一般 `Sample` 陈述**，保持 T123 的普适性 | `Gauss/Envelope.lean` 或 `Gauss/Step6Hyp.lean` | Claude Code | **完成**（ℝ 值可积性补上，高斯版 `quad11/13_unifDetDom_gauss` 不再带 `hint`；一般版保持不变） |
| T132 | **⭐⭐⭐ 矩 Duhamel**：`Φ(u,H) = (U_{u,t}∘(L−K)(H,z_u))_a`，对 `|Φ|^{2p}` 用**带显式时间的生成元恒等式**（只依赖一时刻律，故与模型无关）+ T72 的 QV 支点 ⟹ `‖(L−K)_t‖_{2p} ≤ ‖U(L−K)_s‖_{2p} + 2∫‖U∘F‖_{2p} + (C∫‖(U⊗U)∘(E⊗E)‖_p)^{1/2}`，即 (5.20)+(5.24) 的合体。替代全部 `Hierarchy.duhamel/bdg` 消费者（带撇变体）。**第 0 步只交消费者清单 + 接口草案，Cowork 审过再开工** | `Gauss/MomentDuhamel.lean`（新建） | Claude Code | **第 0 步已审（03:55）：拆成 T132a/b/c；修改 3 退回**，见规格下「Cowork 审查结论」 |
| T132a | **矩 Duhamel 的结构 + 收口 + 带撇 `Lemma514`**（不依赖 T133/T134）：`MomentDuhamel(Q)`（含逐点漂移字段钉死 `F`）、积分+取上确界的收口引理（**不是** `gronwallBound`）、`∂_u Uker`、重新生产 `Step3.Lemma514` | `Gauss/MomentDuhamel.lean` + `Analysis/` | Claude Code | **部分完成**（结构 + 收口 + `F_unique` 已证；**带撇 `Lemma514` 未做**，归约成具名 `hrhs`，需矩版的 `stochDom_of_logBound` 机器。另：`TimeIcc` 非 `Fintype`，时间一致性必须走 T124 网引擎，见 STATUS） |
| T132b | **矩 Duhamel 的高斯卸载**：带显式时间的生成元恒等式 + `(z,M)` 联合 `C²` ⟹ `MomentDuhamel` 实例。等 T133/T134；**规格见下文「T132b 规格」**（05:40）| `Gauss/MomentDuhamelGauss.lean` | Claude Code | **部分完成**（带时间的生成元恒等式 + `(z,M)` 联合 `C²` 全部证出，且**不需要二阶 `BddC1On`**；`integrable` 已证。**当时卡住的两处 `MomentDuhamel.lean` 缺陷（`genLK` 多一个 `W⁻¹`、`Hyp.integrable` 过度量化）已于同日修复**，`W_mul_genLK_eq` 改为 `genLK_eq`。余下：两条矩不等式本身，以及两个缺生产者——`u ↦ Kval` 的时间可微性、固定 Hermitian `M` 时 `u ↦ gloop` 的可微性。见 STATUS） |
| T132c | **`MomentHyp.step` 与 `(+,+)` 一步改进**：由矩 Duhamel + (5.39)–(5.41)(5.45) 的矩形式给出。等 T132a；**⚠ 规格已改（06:15）：`MomentHyp.step` 同阶形状很可能证不出（(5.40)–(5.42) 对 `J*` 超线性），先做可行性审查，建议光滑截断替代停时**，见下文「T132c 规格」| `Hierarchy/Step2Moment.lean` 追加或新文件 | Claude Code | **【已交付，勿再当「可开工」接手】**（原「实现可开工（Cowork 11:25）」）：T174 重算确认 **30 够**。实现按 T174 的三条建议：① **走 shape 2**（`eG_le_reduced`，(5.41) 主项 `β* = 5.5`）并**跳过** (5.36)→(5.42) 的 `−1/2 → −1/3` 吸收步（用 `ee_le` 的两项形，瓶颈 28.5 → 17.5）；`phi_arith′` 只需把 `hq : q ≤ R` 放松为 `q ≤ R²`（T174 已在 scratch 编译验证）；② 近场项**先积分后取 sup**（`∫η_u^{−1}(η_u/η_v)^4 r^5 du`），否则超预算 `R^{2.5}`；③ 光滑化的 `log N` 落在零余量行，须 `δ < c/9`（现有 `δ ≤ c/24` 已够）。(5.35) 左端取 T163 的 `eGpm`，(5.36) 左端取 T167 的 `EEpath`，截断取 T175 的具体 `χ`。交付含 (5.48) 与 `(+,+)` 的 `BootPP.step`  **三项里两项落地**（`Hierarchy/Step2MomentStep.lean`，1001 行，全量绿、审计 10077）：**`BootPP.step`** 化归到网点（`bootPP_of_net`/`_of_modulus` 直接造出整个 `BootPP`）、**(5.48)** 由 `flowEq548_of_near_far` 产出。指数账全部编译：瓶颈 `β* = 10`（(5.40)，沿用原样），远场 **5.5/4.5**，近场 `r³` 是 **4 且零余量**，**(2.72) 的指数没碰**；`integral_nearInt_le` 兑现「先乘后取 sup」、`R` 上零损失，`coarse_sq_ge` **证实粗算确超预算 `R^{5/2}`**。⚠ **`MomentHyp.step` 按冻结形状不可证，两条阻塞都编译成了定理**（`bnd_poly` 不许 `bnd` 带 `N` 的幂 vs `J*` 并集界每阶付 `L²`；矩层去截断的余项不小于门槛，压下去要把阶数乘 `(K+δ)/δ`）——**与规格第 0 步的结论一致**，替代路径（缺口穿越 + 网）已落地。`(+,+)` 的「免自举」捷径也被**证否**（`no_finite_pass`）。余：`hev` 与 `MomentHypCut` 都要**截断版矩 Duhamel** → **STATUS 的 D10 待裁定**；**`hfar` 是 (5.48) 唯一缺的**（`Step2.step_bound` 把三个指示函数全丢了）。记 paper-deltas #130 |
| T139 | **维护：paper-deltas 编号去重**。`61`–`65` 各有两行（T81/T91–T95 一组、T94/T101/T108/T83/T111 一组）。把**后一组**改编 `91`–`95`，再 grep 全仓库（`docs/`、`RBM1D/**/*.lean` 的 docstring）里的 `#61`–`#65` 引用，**按上下文**改到正确的号。以后新增条目前先 `grep -o '^| [0-9]* |' | sort -n | tail -1` 取号 | `docs/paper-deltas.md` 等 | Claude Code | **完成**（第二组改编为 95–99，`90` 的重复改 100——因 91–94 已被占用，未按工单原定的 91–95；STATUS 里 7 处引用已按上下文改正） |
| T140 | **`LoopIto.second`（冻结形式）+ (5.19) 的 `primBilLen 2 = ThetaOp`**（T134 余项，T132b 的前置）：`½ Σ S_ij ∂_ij∂_ji L_{σ,a}` = (2.45) 的 cut-and-glue dt 部分，**只需冻结 `z`、用 `G` 而非 `G̃`**（T134 已证 `G̃` 的 `−m` 减项是动 `z` 白送的）。纯确定性代数，用 T133 的 Fréchet 二阶乘积法则 | `Gauss/LoopIto.lean`（续） | Claude Code | **完成**（`LoopIto.second` 冻结形式已证，T76 该假设成为定理、Lemma 2.11 矩形式只剩 T70；**(5.19) 按字面为假：左端应为 `couplingLen`，且 (5.16) 漏了 `S^(B)`——论文笔误，两条佐证**，见 STATUS。**后续（Jun 2026-09-21 裁定）：`RBM.ThetaOp` 已按更正后的核重定义，31 处引用一并更新，全量构建绿、公理审计 8452；无一条定理被削弱，`Gauss.thetaGenOp` 与 `SumZeroDyn.genS` 现与 `ThetaOp` 按 `rfl` 相等**） |
| T141 | **`hjoint`：loop 导数界对 `z` 在球上一致**（T134 余项，T132b 的前置）：把 T133 的 `bdd₁`/`bdd₂` 加强成对 `z ∈ B(z_u, r)` 一致的版本（`‖G(z)‖ ≤ (Im z)⁻¹`，球取在 `Im z ≥ η_u/2` 内） | `Gauss/LoopC2.lean`（续） | Claude Code | **完成**（`z`-一致性免费，但真正要的是流×谱的联合导数；`hjoint` 已卸且不引入新假设，T134 余项只剩 `MatrixStein` 与 T140） |
| T142 | **(4.12) 做到论文尺寸 `Ψ²`**（T137 余项，paper-deltas #85/#90）：`MinorGood`（`MinorDiffGain.lean:436`）带 (4.1)(4.3) 但**不带 (4.2)**，所以空字分支只能用确定性包络，威力停在 `Ψ·η⁻¹`。给 `MinorGood` **加** `‖G^{(S)}_{aa} − m‖ ≤ Ψ` 字段（新增结构或带撇版，**旧结构不动**），在空字分支使用；顺手把 T137 探针里那 8 行桥（`flucGainUpTo_of_minorDiff`）落进 `Gauss/FlucIterHigh.lean` | `Gauss/MinorDiffGain.lean` + `Gauss/FlucIterHigh.lean` | Claude Code | **完成**（(4.12) 已达 `Ψ²`，控制中无 `η⁻¹`；`MinorGood` 未动、新增的 `MinorGood` 撇版生产者代价为负；分级桥按 import 方向拆成两半，见 STATUS） |
| T143 | **`LDEFlowDom`：(4.2) 的 LDE 对 u 一致**（T138 余项）。卡点：网引擎要控制的多项式下界，而 `ldeRowRHS` 可为零。**第 0 步：试用 T135 的吸收引理绕开**——对放宽的控制 `ζ + N^{−B}` 跑 T124/T130 的网（下界白送），再用 `StochDom.of_add_le` 把 `N^{−B}` 吸收回 `ζ`（若消费者只要 `≺ ζ + N^{−B}` 就更省事）；固定时刻生产者 `Gauss.stochDom_ldeRow`/`ldeCol` 已有 | `Gauss/LDEFlow.lean`（新建） | Claude Code | **完成（条件）**（改引擎去掉控制下界，旧引擎成特例；固定时刻输入已是无条件定理；余 `LDENetClose`，需小行 Green 的非对角衰减，见 STATUS） |
| T144 | **`eeDecayEvent` 与 `xiLowEvent` 的生产者**（T135 余项）：前者是粘合后 `(2m+2)`-loop 版的 `Decay.lemma59`（放 `LKDecayQuant.lean`，复用 T126/T138 的定量闭合）；后者是 `Ξ^{(L)}` 的高概率多项式下界，高斯侧由 `Im G_xx ≥ η/(‖H−E‖²+η²)` + T109 的 `‖X‖ ≺ 1` 给出（放 `Gauss/`，`Hierarchy` 不 import `Gauss`） | `Hierarchy/LKDecayQuant.lean` + `Gauss/XiLow.lean` | Claude Code | **完成**（(a) 无需新估计，是 T126 的实例；(b) 改走标号求和绕开 PSD 幂平均，除区制外无假设。`EE_le` 余 `FlowInputs` + T58，见 STATUS） |
| T145 | **⭐ 修补 T132a 的 `MomentDuhamel.Hyp`（Cowork 04:25 抽查的两处，提交时未落实）**：(1) `EE` 仍是无约束数据字段——它只在 `momentDuhamel` 右端出现，取随 `N` 增长的巨大值即令不等式空洞；**钉死为 T127 的 `eeField`**（直接定义，或加 `EE_eq`），T135 的 `stochDom_norm_eeField` 随即就是 `EE_le`。(2) `drift` 对**所有** `M : Matrix … ℂ` 量化——非 Hermitian `M` 处 `M − z_u` 可能不可逆，T132b 卸不掉；**改为只对 Hermitian `M`**，`genLK` 注明是沿 Hermitian 方向的二阶导。`Hyp` 刚建、无外部消费者，**可直接改结构**（不是冻结接口）；`F_unique` 与探针同步更新 | `Gauss/MomentDuhamel.lean` | Claude Code | **完成**（`EE` 字段**删除**改为定义、`drift` 限制到 Hermitian；fiat 审计：`F` 无自由参数、`cMD` 与消费者义务闭合，见 STATUS） |
| T146 | **`hrhs`：矩 Duhamel 右端三项的 `‖·‖_{2p}` 界**（T132a 余项；重新生产 `Step3.Lemma514` 的最后一环）。**第 0 步：先试「≺ ⟹ 矩」的桥，而不是把 `stochDom_of_logBound`/`term1F`/`termI1`/`QV1_stochDom` 整套做矩版**——那些定理在对时间积分**之前**已有逐时刻的 `≺` 界（(7.16) 核估计 + `Lemma510` 幂次计数），逐时刻 `|U∘F_u| ≺ Φ_u` + 确定性包络（T77 `norm_gloop_le_det`）经 T77 `momentDom_of_stochDom` 就给 `‖U∘F_u‖_{2p} ≤ N^ε Φ_u`；控制的多项式下界用 T135 的吸收引理。若中间 `≺` 结论在现有定理里没被单独陈述，就把它**抽出来**（不改旧签名）。时间一致性走 T124 网引擎（`TimeIcc` 非 `Fintype`，T132a 已确认） | `Gauss/MomentDuhamelRhs.lean`（新建） | Claude Code | **完成**（三项全卸，`≺⟹矩` 的桥走通、**不需要 T124 的网**（`MomentDom` 不要 `Fintype`）；`stochDom_of_logBound` 那套机器确实不必重做。留作假设的只有 `hEEmom` 缺的 **Lyapunov `‖·‖_p ≤ ‖·‖_{2p}`**（仓库里没有）与 `Ξ ≺ 1` 替换。**顺带查出 `MomentDuhamel.lean` 的括号错误 → paper-deltas #108**，等 T132b 落地再修） |
| T147 | **审计：总装还差什么（精确清单）**。从最顶层的定理（Theorem 2.2 / `Thm221` 经 Lemmas 2.18–2.20 的迭代）往下，列出**目前仍被携带的全部具名假设**，每条标：已有生产者（哪个定理）/ 在飞行中（哪张单）/ 无主（缺什么）。特别核对：矩路线接上后 `SumZeroDyn.Hierarchy`、`MomentHyp`、`BootPP`、`Step6.Hierarchy` 各自由谁替代；`hll`（u-一致弱局部律）是否就是 `Steps` 的字段。**只交清单，不写 Lean**；用于给 Jun 估算剩余工作量 | `docs/STATUS.md` | Claude Code | **完成**（七个编译探针；结论：拦路的头两项是**记账**——`Steps` 当假设用是循环打包、`0 < s` 未放宽；`T58` 有**四**项交付物且 Steps 2–6 全压在它上面；`BootPP.step`、`Step45.FlowEq548`、`StepTwoClaim`、Thm 2.2 的概率一半**无主无工单**；另有 9 处「已证但没接线」，见 STATUS） |
| T148 | **`LDENetClose`**（T143 余项，paper-deltas #104）：`ξ(u)/ζ(u) = u|⟨g, w(u)⟩|²` 对 `u` 一致，`g` 是第 `i` 行（高斯）、`w(u)` 是小行 Green 列的单位化。**第 0 步：试「条件化 + 不单位化 + 加地板」**——对其余各行条件化（T84 的坐标积分），`v(u)` 成为确定性曲线、与 `g` 独立；改证 `|⟨g, v(u)⟩| ≤ N^ε(‖v(u)‖ + N^{−D})`：网点上用高斯尾 + 并界，网点之间用 `v` 的确定性 Hölder 模（`‖v(u)−v(u')‖ ≤ η⁻²(‖X‖+1)|u−u'|^{1/2}`，T106）与 `‖g‖ ≤ N`；单位化在 `v(u) → 0` 处不 Lipschitz，**所以别单位化**，地板 `N^{−D}` 用 T135 的吸收引理收回。若消费者 `ldeFlowDom_of_close` 不容地板，报告需要的形状 | `Gauss/LDENetClose.lean`（新建） | Claude Code | **完成（负面结论）**：`LDENetClose` **按字面不可证**——`ldeNetClose_of_lower_bound` 证明它（在模已知下）**等价于**控制的多项式下界，而 `ζ` 对带距指数小，该下界**为假**。无条件交付的是**两侧的确定性 Hölder-1/2 模**与**带地板的时间一致 (4.2)**（`ldeFlowDom_floor`，不要好事件、不要局部律）。**地板去不掉**，消费者 `LKDecayQuant.LDEFlowDom` 需带 `+ N^{−B}` 重述。缺的**不是**高斯过程工具，是小方阵 Green 列的反集中下界（仓库与论文皆无）。见 STATUS、paper-deltas #111 |
| T149 | **⭐⭐⭐ 拆 `Steps` 包 + `0 ≤ s`**（T147 §0a/§0b，**杠杆最大、零新数学、最先做**）：约 8 条 glue 定理把整个 `RBM.Steps` 当假设收，而它们自己生产其中字段——打包上的循环（探针 P2/P5 已证实）。把这些签名里的 `hSteps : Steps X E s t` 换成**实际用到的字段**（全树只取 5 个投影：`apriori`、`localLaw`、`aprioriDecay`、`sharpLoop 2`、`sharpLmK 1/3`）。新增带撇版、旧签名保留（它们仍然正确，只是循环）；另把 `hs0 : 0 < s` 放宽成 `0 ≤ s`（`one_le_ellHat_of_nonneg`，探针 P4 五行）。**验收：一个探针把 1→2→3→4/5→6 按依赖序串起来，不再出现「先有 `Steps` 才能造 `Steps`」**；**Cowork 08:35 抽查**：T149 在 19 个文件里**就地**把 `hs0 : 0 < s` 放宽为 `0 ≤ s`（非带撇版）——**接受**：只放宽假设是单调加强，旧调用点经 `.le` 仍通过；但**只许放宽假设，不许动结论与任何 structure 字段**，提交前全量 `lake build` 必须绿（08:31 的构建有 4 个 WIP 错误）。| glue 文件（`StepGlue`/`Step2PP`/`Step6Hyp` 等）追加带撇版 | Claude Code | **完成**（15 条带撇版 + 5 条字段级 `def`；旧签名全部保留、改为一行推论，`Steps` 结构未动。验收探针两个都过：`steps_of_inputs`（1→2→3→4/5→6 串起来造出 `Steps`，假设里没有 `Steps`）与 `steps_of_inputs_nonneg`（同一条链在 `0 ≤ s` 下，Step 2 的两个输出当假设）。**`0 ≤ s` 只走到 Step 2 门口**：`Step2.step2`/`aprioriDecay`/`jS_stochDom`/`jS_highProb` 与整个 `SumZeroDyn`、`LKDecayQuant.lemma514_flow_of_flowInputs` 仍要 `0 < s`，底在 `norm_Uker_flow`/`norm_Theta_mul_sub_le` 这些只对 `0 < t` 证过的传播子估计上，见 STATUS） |
| T150 | **接线：已卸但没接的**（T147 §6(c)）：`hll`（`Steps.localLaw` + `Step3.Scales.le_A`，探针 P7）、Step 6 的 `hint1`（`integrable_sample_Lval`，P5b）、Thm 2.5 的 `hint_pp/hint_pm`、`eq45Flow_of_localLaw_gain` 的三个时间 Hölder 模 `hHolIBP/hHolRow/hHolBlk`（T129 + T106 组装）。**零新数学**，每条一个带撇定理 + 探针 | 各消费者所在文件（追加） | Claude Code | **完成**：四条全部落地、零新数学。`hll` 走 `unifDomIcc_of_stochDom_timeIcc` + `Step3.Scales.le_A`；`hint1` = `int1_gauss`；Thm 2.5 的两条可积性起了**新文件 `Gauss/Thm25Gauss.lean`**（全树没有同时 import `Flow/Universality` 与 `Gauss/Hierarchy` 的文件），顺带给出 **`theorem2_5_gauss`——唯一剩下的假设是 `Thm221`**；三个 Hölder 模按 T129 docstring 的组装方式原样可行，**无一处需要新估计**，唯一新假设 `HolConst` 是 regime 条件 |
| T151 | **`FlucGain` 分级接口的改接**（T147 §6(b)④⑤）：`eq45Flow_of_localLaw_gain` 要**不分级**的 `FlucGain`，而 T137/T142 产出的是分级 `FlucGainUpTo`；把该消费者搬到分级接口（只需 `M = 2p`），落地 T142 探针里的 `flucGainUpTo_of_minorDiff` 桥，按 `ρB ≍ Ψ²` 重算 `hΦW`/`hΨW` | `Gauss/Eq45FlowInputs.lean` + `Gauss/CondStableFlow.lean`（`FlucIterHigh.lean` 无需改动） | Claude Code | **完成**：分级生产者已落地（`M = 2p` 属实，另需 `Bp ≤ Kp·Bm` 的因子分解，在 T142 参数下取等、零代价）；**桥 `flucGainUpTo_of_minorDiff` T142 早已落地，T147 §6(b)⑤ 是过时记载**；**`hΦW` 整条消失**（由 `hΨW` 推出），两条 `hcρ` 合并——净删假设。**已全部完成**：带撇消费者 `eq45Flow_of_localLaw_gain'` 落在 `CondStableFlow.lean:1240`（纯新增，不带撇版一字节未动；证明体是裸应用，无 `convert`、无强制转换；结论 `StepGlue.Eq45Flow` 逐字相同） |
| T152 | **Step 6 的层级（`Step6.Hierarchy` + `FastDecayHyp` + `h5133` + `hG`）走矩路线**（T147 §5，原 T58 ④）：`Step6.Hierarchy` 是**期望形**的 (5.20)@长度 2（无 ω、无鞅、漂移拆成 `DLK + DG`），正是 T132b 的带时间生成元恒等式在**一阶**（线性，不取 `|·|^{2p}`）上的直接推论。`DLK`/`DG` 取 T134/T140 已钉死的漂移。等 T132b | `Gauss/Step6HierarchyGauss.lean`（新建） | Claude Code | **部分完成 + 决定性的负面发现**（`Gauss/Step6HierarchyGauss.lean`，557 行，全量绿、审计 8864）：补上了树里原先没有的 **`Uker` 常数变易演算**（`∂_v U_{v,t} = −U_{v,t}∘Θ_v`、`Uker_duhamel`），并给出**全树第一个 `hH` 生产者**。⚠ **fiat 审计：四个洞里 `hG` 与 `hFD` 的 `DG` 半边是空洞**（已编译成定理 `hG_zero_right`/`fastDecay_zero`），**`hH` 本身可 fiat**，有内容的只有 `hFD` 的 `DLK` 半边与 `h5133`。**`sharpExpect_step6_single`：`DLK`/`DG` 的拆分在 Lean 里毫无代价可省**（两条界相同），四个洞塌缩成单张量 `D` 上的三条义务。⚠ **另发现高斯漂移恒等式在 `v = 0` 不可满足**（链式法则全带 `0 < u`，而 Step 6 是唯一接受 `0 ≤ s` 的一步）——用 `_Ioo` 版。见 STATUS |
| T153 | **Theorem 2.2 的概率一半**（T147 §1，无主）：(2.10) 要在随机谱参数 `z = λ_k(ω) + iη` 处用局部律，而 `localSemicircleLaw_of_Thm221` 对确定性 `z : ℕ → ℂ` 陈述，`SpecSeq` 还把能量钉成与 `N` 无关。**第 0 步：查固定 `E` 的假设渗进多深**（`E : ℝ` 在 `Flow/`、`Hierarchy/` 里是否处处是参数）；方案候选：(i) 允许 `N` 依赖的能量 `E : ℕ → ℝ`（若只是参数化、证明一致，则 `≺` 对 `E` 自动一致）；(ii) 对能量取 `N^{−C}` 网 + `z` 的 Lipschitz。选哪条、改动多大，报告后再做 | `Delocalization.lean` 等 | Claude Code | **第 0 步完成**：`Flow/` 层固定 `E` **纯参数化**，换成 `E : ℕ → ℝ` 证明脚本一字不改（探针全绿）；**`SpecSeq` 的能量切片条件随之消失，直接销掉 paper-deltas #38 与 #5 的一半**。**(ii) 单独走不通**——网点能量本身就是 `N` 依赖的，(ii) 的输入恰是 (i) 的输出，故 **(i) 先做、(ii) 紧接**。一处真实非一致在 `Loop/SumZero.norm_Alayer_le` 的 `ι = (mE E).im`，由 `mE_im_ge` 机械修复、不在 `Bounds_of_Thm221` 路径上。建议 (i) 走新文件（骨架约 170 行、0 个现有签名改动）。见 STATUS　**（Cowork 14:10）实现拆到 T194**（D6 已定：(i) 走新文件；Theorem 2.2 的 (2.10) 原文就带 `1(λ_k ∈ [−2+κ, 2−κ])`）|
| T154 | **⭐ 修 `MomentDuhamel.Hyp` 的三处缺陷 + Lyapunov**（T132b/T146 查出）：(1) `genLK` 多了 `/ W`（`Sblk` 已含 `/W`；定理 `W_mul_genLK_eq` 已证 `genLK = W⁻¹𝓛`）——**删一个 token**，否则 `drift` 钉死的是 (5.15) 没命名的对象；(2) `Hyp.integrable` 对 `u ∈ ℝ` 量化，改为 `u ∈ [s N, t N]`（`u = 1` 处无包络）；(3) `momentDuhamel`/`momentDuhamelQ` 及 T146 `hrhs` 里 `∫` 向右延伸、(5.24) 第三项落进了时间积分——补括号（paper-deltas #108）；(4) 在 `momNorm` 旁补 **Lyapunov** `‖·‖_p ≤ ‖·‖_{2p}`（T146 唯一缺的引理）。**(1)(2)(3) 已于 2026-09-21 修复并推送**（`W_mul_genLK_eq` → `genLK_eq`，证明 `rfl`；`integrable` 按窗口量化，`hrhs_of_moment_inputs` 因此新增假设 `hvt : ∀ N, v N ≤ t N`；括号修好后 T146 的 `hnum` 掉了预测中的 `2(v−s)`；paper-deltas #108 已了结）。**(4) Lyapunov 亦已完成**：`momNorm_le_momNorm_of_exponent_le`（经桥 `momNorm_eq_eLpNorm_toReal` 走 Mathlib 的 `eLpNorm_le_eLpNorm_of_exponent_le`，该引理**本身不要可测性**；可测性从 `Integrable` 反推，故假设只有 `p ≠ 0`、`p ≤ q` 与**只对 `q` 阶**的可积性——消费者全能满足）。接线也通了：`hEEmom_of_momNorm_two_mul` 让 `hrhs_of_moment_inputs` 的 `hEEmom` 由 `2p` 阶界直接得出，常数与控制原样不变、调用方零额外代价 | `Gauss/MomentDuhamel.lean` + `Gauss/MomentDuhamelRhs.lean` | Claude Code | **完成** |
| T155 | **Lemma 5.7 (5.35) 立成定理**（今天只是 `Step2.Hyp.eG` 假设）：pp.59–61，(5.51)–(5.63) 的分情形论证，`T_{u,D}` 归一化。**交两个形状**：论文字面的（`A^{−1/3}(J*)³`）与 (2.73) 降幂版（T132c 第 0 步：`r^{3/2}A^{−1/2}J* + rA^{−1}(J*)^{3/2}`）。输入：(4.2)/(4.5)、(2.73)/(2.74)、(5.31)、(5.32) | `Hierarchy/Lemma57.lean`（新建） | Claude Code | **完成**（1066 行）：两个形状都证出（`eG_le_paper`/`eG_le_reduced`），**形状 2 的远场括号逐字落实 T132c 的预言**（`J*` 一次 + 3/2 次），(5.60) 从 3-loop 定义证出、无常数损失，(5.62) 的半指数求和核是新造的轮子。**Case 2 的 `(J*)^{3/2}` 不可降已确认**（`√T₁₂·√T₁₂ = T₁₂` 是全部理由）。留作假设：`hEG`（(5.51)/(5.52)——仓库里 `E^{(G)}` 无定义）、`h558a/h558b`（(5.58) 的 Schwarz 步，**最值得接的下一步**）。六处偏差记 paper-deltas #112，其中 **③ 形状 1 需要论文没写的 `J* ≤ A_u`** |
| T156 | **Lemma 5.7 (5.36) 立成独立的逐点估计**（T132c 缺口 1：今天它只经停时鞅假设 `Hyp.mart` 进入，矩路线不能用）：pp.61–63，(5.64)–(5.72)，`E⊗E` 带 `T_{u,D}²` 归一化与空间衰减；含内禀的 `(J*)²`（Case 2(1a)）、`(J*)³`（Case 2(1b)），都带 `A^{−1}` | `Hierarchy/Lemma57.lean`（续） | Claude Code | **完成**：`ee_le`/`ee_le_paper` 已是独立逐点估计，(5.72) 的卷积复用已有的 `sum_tailT_mul_tailT_le`（未造轮子）。⚠ **更正 T132c 审计**：内禀性确认，但 **Case 2(1a) 是 `A^{−1/2}` 不是 `A^{−1}`**（即 (5.36) 自己写的 `(Wη_uℓ_u)^{−1/2}`），指数表按「都带 `A^{−1}`」算会偏乐观半格。未卸：`hsym`（需 (5.22) 的 `k=2` 项）、`h566`（要 6-loop 展开）、`h572`。见 paper-deltas #113 |
| T157 | **`hinit`/`hFmom` 的随机控制替换**（T146 余项）：`Lemma510.F_le` 的控制是随机的 `xiRhs`；要 `‖U∘F_u‖_{2p} ≤ N^ε Φ_u`（确定性 `Φ`），走「`|U∘F| ≤ C·xiRhs` 逐路径 + `xiRhs ≺ Φ`（已有，`SumZeroDyn.F_stochDom` 的那一步）⟹ `|U∘F| ≺ Φ` ⟹（T77 + 包络）矩」；`hEEmom` 用 T154 的 Lyapunov | `Gauss/MomentDuhamelRhs.lean`（续） | Claude Code | **完成**：`hinit`/`hFmom`/`hEEmom` 三项输入全卸，`hrhs_of_moment_inputs` 一字未动。关键发现是**顺序**——`Lemma510` 的控制带时间而 `hrhs` 的不带，先过 T77 的桥再在**矩层面**放宽（`MomNormDom.control_mono`），于是不需要 `≺` 层面的控制单调性。`hinit` 的输入是 `BoundsCore.LmK` 逐字（(2.68) 本来就是确定性控制，这项从无随机控制问题）。⚠ **`hFmom` 链的最后一环仍在文件外**：生产 `hdom` 要一个 `SumZeroDyn.Hierarchy` 实例，而 T118 禁止实例化——未绕过、未伪造，`hdom` 留成与 `F_stochDom` 结论完全同形的假设，**指向 T58/T163**。见 STATUS |
| T158 | **截断方案的定量导数界**（T132c 缺口 2/3）：光滑 max 的链式法则与权重和界；`∂J`、`∂²J` 以 `T_{u,D}` 归一化（经 (5.36)，即 T156）；`∂_u T_{u,D}`（`−(ℓ/ℓ_u)^{1/2}` 项符号有利可丢，`W^{−D}` 地板区单独处理）；门槛的时间依赖项 `−χ'·Θ̇_u/Θ_u`（`= 4m/η_u`，工单原先漏了）。**收尾在概率层面做穿越论证 + 时间网**（`MomentHyp.holder` + `stochDom_timeIcc_of_holder`），不在矩层面用指示函数截断（那样阶数仍会升） | `Gauss/CutoffBounds.lean`（新建） | Claude Code | **完成**（`Gauss/CutoffBounds.lean`，734 行，全量绿、审计 8965）：光滑 max 的链式法则与权重和界全证（`(card ι)^{1/r} ≤ e`、Hölder 的 `∑wᵢ`，并带一条取等的锐性自检）；`∑S|∂J|²` 以 `T_{u,D}` 归一化；**`∂_u T` 的不一致项符号有利可丢，`W^{−D}` 地板区结论是「不需要单独处理」**；门槛时间依赖项 `4m/η_u` 已显式摆出；额外做掉二阶导——**光滑化的二阶代价恰好一个 `r−1 ≍ log N`**。边界：(5.36) 按形状接（`linarith` 级，待 T167）、二阶是方向导数非 Fréchet、未构造具体 `χ`（刻意不引入任何 `∀ ω` 量化）。⚠ **`β*` 表仍需按 T155/T156 的更正重算**。见 STATUS |
| T159 | **六步循环的端到端核对**（Jun 2026-09-21：「先确保 6 步循环部分正确无误」）。**（09:50 追加）可满足性审计是本单的必备项**：凡是链上携带的具名假设，除「不被 fiat」外还要「**可满足**」——逐点 `∀ ω` 的确定性不等式在高斯模型上按字面常常为假（T164：`MinorGood'`），此时下游全是空真；并入 T172 的扫描结果。在 T149 解开打包、Steps 1–6 各自有生产者之后做：(1) 一个探针按依赖序 1→2→3→4/5→6 串出 `Thm221.step`，再经 Lemmas 2.18–2.20 的迭代到 `Bounds`，`#print axioms` 只剩三条标准公理；(2) **逐条对照论文 (2.68)–(2.80) 与 Lean 陈述**（T114 做过字段对账，这次连同所有生产者的剩余假设一起列）；(3) **fiat 审计**：全链上每个数据字段（`F`、`EE`、漂移、鞅/残差）要么被恒等式钉死、要么是定义；(4) 列出全部 paper-delta 中影响六步的条目。**只交报告**；随后 Cowork 再派一个独立 agent 复核 | `docs/STATUS.md` | Claude Code | 已认领；T149 已完成（审计通过）；等 T161（`s = 0`）、T163（钉死漂移上的 (5.35)）与各步生产者 |
| T160 | **让消费者吃带地板的 (4.2)**（T148 余项；T148 已证 `LDENetClose` 按字面为假，交付了无条件的 `ldeFlowDom_floor`：`ldeRowLHS(u) ≺ ldeRowRHS(u) + N^{−B}`，对 `u` 与非对角对一致）。**判断：地板无害**——下游要的衰减本身就带 `W^{−D}` 地板（`T_{u,D}` 与 (5.75) 都是），取 `B ≥ 2D·log W/log N + 1` 即被吸收。所以：(1) 在 `Hierarchy/LKDecayQuant` 给 `LDEFlowDom` 加带地板的带撇版并把 `lkDecay_of_inputs` 改接到它，**删掉 `hlow`/`hΞ`/`hΞX` 这条替代假设**——`LKDecay` 应只剩 `hΩ`（T130）与 `hdecay`（Step 2）；(2) **T107 的 `EntryBoundFlow`/`DiagBoundFlow` 用的是同一个输入**（T147），同法改接；**先看 T107 是否早已停滞**（「进行中」已挂很久），若是，把它并入本单并在 T107 行注明。**只加带撇版，旧签名不动** | `Hierarchy/LKDecayQuant.lean` + T107 的文件 | Claude Code | **(1) 完成**：`LDEFlowDom'` + 一整条带地板的平行链（`lemma59_floor`、`FlowInputs'` 等，全部新增，`Green/EntryBound.lean`/`Hierarchy/Decay.lean` 未碰）。**探针验证 `LKDecay` 只剩 `hΩ` 与 `hdecay`**，`hlow`/`hΞ`/`hΞX` 与 `LDENetClose` 全部消失，且 **`LKDecay` 的陈述未变、下游零改动**。代价：多三条**确定性**区制条件（`hst`/`hK`/`hη`），别说成零代价。**(2) 只出了计划**：`EntryBoundFlow` 可同法接上且地板白送吸收（约 15 行），但 **`DiagBoundFlow` 缺 `ldeQuad` 的带地板时间一致版**，是独立一单的量。见 STATUS |
| T161 | **`Θ_t` 差分估计延拓到 `t = 0`**（T149 余项）：`0 ≤ s` 在总装层（Steps 1、3、4、5、6 + 全部 glue）已通，卡在 `Propagator/` 的 `Θ_t` 一阶/二阶差分估计整族只对 `0 < t` 证过（经 `ρ(t)` 闭式）——`norm_Theta_mul_sub_le`、`norm_Theta_sub_shift_le`、`norm_Theta_second_diff_le` 一族，`LongDiff.lean` 的 `ht0` 一族，`KernelDecay.lean` 的三条 `Uker` 引理，`norm_Uker_flow`。`t = 0` 处 `Θ_0 = I`，界平凡为真：**分情况补 `t = 0` 一支，就地把假设放宽成 `0 ≤ t`**（与 T149 同一纪律：只动假设、单调加强、不改结论；冻结签名则加带撇版）。**第 0 步**：先列出**矩路线**（T146 `MomentDuhamelRhs`、T132b `MomentDuhamelGauss`、`Step2Moment`）实际依赖的 `0 < t` 引理，优先放宽这些；旧路线（`Step2.step2`、`SumZeroDyn` 的 `termI*`/`termM`/`QV_Q_stochDom`/`lemma514_flow`、`LKDecayQuant.lemma514_flow_of_flowInputs`）顺带即可——它们带 fiat 风险的 `SumZeroDyn.Hierarchy`，终将被矩路线替换。另核对：矩 Duhamel 在 `s = 0` 处可用（`hasDerivAt_Psi_Hflow` 要 `0 < u` 是内禀的——`√u` 在 0 不可导——所以要的是「开区间 `(s,t)` 上可导 + 闭区间上连续」形式的 FTC，确认现有 `momentDuhamel` 已是这个形状，不是则报告）。**若某条估计在 `t = 0` 处按字面为假，停下报告，不要硬凑。** **验收**：T149 的探针 `steps_of_inputs_nonneg` 在 `hs0 : ∀ N, 0 ≤ s N` 下不再把 Step 2 的输出当假设收（经 `Step2.step2` 或 T132c 的矩替身）；全量 build 绿、公理干净 | `Propagator/Decay.lean`、`Propagator/LongDiff.lean`、`Propagator/KernelDecay.lean` + 消费者 | Claude Code | **已完成**（2026-09-21；全量 build exit=0、公理干净）。第 0 步结论：**矩路线一条都不需要**（`Step2Moment` 的 `jS_stochDom`/`aprioriDecay`/`step2` 签名本来就是 `0 ≤ s`）；卡的是旧逐路径链 `step2→aprioriDecay→jS_stochDom→jS_highProb→step_bound→norm_Uker_flow→…→norm_Theta_apply_le_of_real`。验收探针 `steps_of_inputs` 在 `0 ≤ s` 下由 `Step2.step2` 现场产出 Step 2 的两个输出，不再当假设收。**余留**：`SumZeroDyn` 流层那 22 条 `∀ N, 0 < s N` 未扫——终点 `lemma514_flow'` 的唯一外部调用者在**持有中**的 `Hierarchy/LKDecayQuant.lean:608`，按协议没动；两条底（`norm_Uker_sumZero_scale_le`、`integral_term_le`）已放宽。详见 `docs/STATUS.md` T161 节 |
| T162 | **(5.58) 的 Schwarz 步 + `inv_sq_le_tailT` 去重**（T155 余项）：`Lemma57` 的 `h558a`/`h558b`（逐字抄 (5.58)）从 `gloop_three_expand` + `gloop_two_plus_minus_blocks`（`∑_{x₁,x₂}\|G\|² = W²L_{(+,−)}`）+ AM–GM 证出（T155 已验证可行，常数 1/2），`case1_pointwise` 的两个对称分支改吃定理。顺手：`Lemma57.inv_sq_le_tailT`（`C = 1`）与 `Step45.inv_sq_le_tailT`（`C = 6`）是同一引理，**下沉到 `Analysis/StretchedExp.lean` 做成带参数 `C` 的一条**，两处改成推论（旧名保留）。**先 grep 再造轮子。** **验收**：`eG_le_reduced`/`eG_le_paper` 的假设表里不再有 `h558a/h558b`；全量绿 | `Hierarchy/Lemma57.lean` + `Analysis/StretchedExp.lean` + `Hierarchy/Step45.lean` | Claude Code | **完成**：(5.58) 已立成定理（从 `gloop` 定义打通到 `case1_pointwise`），**`eG_le_paper`/`eG_le_reduced` 的假设表里不再有 `h558a/b`**；`inv_sq_le_tailT` 已下沉到 `Analysis/StretchedExp.lean` 带参数 `C`，两处旧名旧陈述一字未改。副产品：`L_{(+,−),(a,b)}` 在非实对称 `H` 下**不对称**，`h558a/b` 的取向据此修正 |
| T163 | **⭐ 定义 `E^{(G)}` 并把 (5.35) 接到矩路线已钉死的漂移上**（T155 余项，fiat 关键）：T155 的 `hEG`（(5.51)/(5.52)：`EG ≤ κ₁(ℓ_uη_u)⁻¹∑_b L3 b`）是抽象假设，因为**仓库里 `E^{(G)}` 根本没有定义**，`Step2.Hyp.eG` 的左端 `H.F − eLL` 挂在带 fiat 风险的 `SumZeroDyn.Hierarchy` 上。矩路线里 `F` 已被漂移钉死（T134/T140/T145：`F` 无自由参数）。本单：(1) 按论文 p.59 (5.51) **把 `E^{(G)}` 定义成 `G`-loop 的具体表达式**（不是结构字段）；(2) 证**恒等式**：长度 2 处钉死的 `F` = (5.34) 所管的二次粘合项 + `E^{(G)}`（若还有别的项，逐项列出并对上论文）；(3) 证 (5.52)，即 `hEG` 对这个具体 `E^{(G)}` 成立，于是 `eG_le_reduced` 直接作用在钉死的对象上。**fiat 审计**：交付的定理里，(5.35) 左端的每个量都要能 `unfold` 到 `H_u = √u·X` 的 Green 函数，不许经过任何可自由赋值的结构字段。**不动** `Step2.Hyp`（旧路线，冻结）。T132c 实现时 (5.35) 从这里取 | `Hierarchy/Lemma57.lean`（续）或新文件 `Hierarchy/EGDef.lean` | Claude Code | **完成**（`Hierarchy/EGDef.lean`，734 行，全量绿、审计 8846）：`eGpm` 是**定义**逐字抄 (5.51) 并证 `= Gauss.eGterm`；恒等式 `F = eGpm + primBil(L−K,L−K)` **证出没有第三项**（长度 2 时耦合只有 `l_K = 2` 分量，`∑_{l_K>2}` 是空和）；(5.52) 过了，**(5.35) 形状 2 直接作用在 `‖eGpm‖` 上**。**fiat 审计干净**：左端每个量非定义即被恒等式钉死，全程无 `SumZeroDyn.Hierarchy` 实例。副产品：补上 `genLK_eq_split`（此前只有对 `loopObs` 的版本，与裸 `gloop` 不是同一函数）与 `hasDerivAt_Kval_two`。两条 paper-delta #116/#117（原编 #114/#115，撞号已改） |
| T164 | **`MinorGood'` 的生产者**（T142/T151 余项）：`MinorGood'`→`Eq45Flow` 的链已通（T151），唯一的开放项是 `MinorGood'` 本身——今天对**每个**样本点当假设收（例外集），需要「小行 Green 函数的定量局部律」。**第 0 步（交 Cowork 审）**：写清楚 `MinorGood'` 每个字段在论文里出自哪（§4，(4.1)–(4.3) 对小行矩阵），以及能否从本仓库已有的局部律（`LocalLawFlow` (2.75)、`Lemma41FlowGauss`、T130 的 `GoodEvent`）经 Schur 补 / 删行恒等式推出；列出推不出的部分和它们的最小形状。**只能用论文与本仓库，不引外部结果**（Jun 2026-09-21 永久规则）。之后再定实现单 | `docs/STATUS.md`（第 0 步）；实现另定 | Claude Code | **第 0 步完成，结论是驳回**：`MinorGood'` 按字面**是假命题**——`E = 0`、`ω = 0` 给出与 `N` 无关的缺口 `u/(1−u)`，配上链条自带的 `2Ψ ≤ 1` 得 `u ≤ 1/3`，而 Step 2 的区制是 `t > s ≥ 1/2`。`∀ᵐ ω` 同样假；**不带撇的 `MinorGood` 一样不可满足，故 T113 的包络版也悬空**。正面：层级 0 = `GoodEvent`（已证高概率）、`det` 是白送的定理、抬升归纳纯代数、穿过 `E_k` 的工具（`norm_condRow_le_split` + `meas_measure_rowSlice_ge`）仓库已有。建议 L1/L2/L3 三张单 + 两条顺手活，**待 Jun/Cowork 定**。见 STATUS |
| T165 | **⭐ Lemma 5.10 (5.77) 第 1–3 行对钉死的漂移立成定理**（T157 余项；原 T58 (iii) 拆出，fiat 关键）：T157 已卸 `hrhs` 的三项输入，唯一剩下的一环是 `hFmom` 的 `hdom`——它要 `SumZeroDyn.F_stochDom` 的结论，而后者经 `Lemma510.F_le` 这个**结构字段**（即 (5.77) 本身是假设）且要一个 `SumZeroDyn.Hierarchy` 实例，**T118 禁止实例化**。本单：(1) **恒等式**：`MomentDuhamel.Hyp.Fpath` = `Decay.couplingLen + Dynamics.primBil + Decay.eG`，其中 `X`、`Y` 取 `H_u = √u·X` 的**真实** loop（`(L−K)` 一圈与 `gloop`）——由 T134/T140 已证的逐点漂移恒等式 + `F_unique` 得出，不是按定义造 `F`；(2) 用 `Decay` 已有的逐项界（`norm_eG_le` 等）把 (5.77) 第 1–3 行的 `≺` 与 `F_decay` 证出来；(3) 交付 `hdom`，**形状与 `F_stochDom` 的结论逐字一致**。**不实例化 `Hierarchy`**：给 `F_stochDom` 加只收「函数 `F` + 这两条界」的带撇版，或直接产出 `hdom`。**与 T163 协调**：T163 的 `EGDef.eGpm`（(5.51)，`(+,−)` 长度 2）是本单 `eG` 在长度 2 的特例——证一条一致性引理把两者对上，**`E^{(G)}` 只许有一套定义**。**验收**：`hrhs_of_moment_inputs` 的调用链（探针）里不再有 `hdom` 或任何 `Lemma510` 字段；公理干净；fiat 审计同 T163（左端每个量都 unfold 到 `H_u` 的 Green 函数） | `Gauss/MomentDuhamelRhs.lean`（续）或新文件 `Gauss/Lemma510Pinned.lean` | Claude Code | **完成**（`Hierarchy/DriftBound.lean`，881 行，全量绿、审计 9074）：(5.77) 第 1–3 行对钉死的 `driftF` 立成定理，并一路打通到 **`hFmom_of_driftInputs`**——**调用链里不再有 T157 的 `hdom` 缺口、任何 `Lemma510` 字段或 `Hierarchy` 实例**。Ξ-记账的关键恒等式只有一条 `W(ℓ+1)/A ≤ (Krad+2)/η_u`（(5.77) 的所有 `η⁻¹` 都由它来）。⚠ 两个发现：**(5.77) 第 3 行短一个 `Ξ^{(L−K)}_{u,1}`**（paper-deltas #121，原编 #119）；**`Decay.norm_couplingLen_le` 的 `hD` 在长度 0 处会逼出 `Φ ≥ LW`**，本单用 `dTrunc` 绕过、未改 `Decay.lean`，收紧只需把 `hD` 改成 `2 ≤ J.length →`。余：`DriftInputs` 由 Lemma 5.9 与 Step 3 产出，是下一环。见 STATUS |
| T166 | **(4.7) 二次型 LDE 的带地板时间一致版 + `DiagBoundFlow`**（T160 余项）：`diag_bound_stochDom` 除 row/col 外还要 `hLquad`（(4.7) 的二次型 LDE）与 `hLdiag`，T148 只交付了 row/col 的带地板版，`Gauss/LDENetClose.lean` 里没有 `ldeQuad`。本单：`stochDom_ldeQuad_flow_floor`（同 T148 的「网点高斯尾 + 并界、网点之间确定性 Hölder、**不单位化**、地板 `N^{−B}`」配方）+ `norm_sq_green_diag_sub_le_blk` 的带地板版（放 `Green/EntryBoundFloor.lean`，与 T107 共用），然后把 `DiagBoundFlow` 接上。**先查** T148 的 row/col 证明能否按二次型直接复用（`⟨g, A g⟩ − E` 的高斯尾是 Hanson–Wright 型，仓库里 T91 的 `LDERow`/`LDECol` 用的是什么就用什么，**只用本仓库与论文**）。若按字面为假（同 T148 那样），报告并交带地板版 | `Gauss/LDENetClose.lean`（续）+ `Green/EntryBoundFloor.lean` | Claude Code | **完成**（`LDENetClose.lean` 992 → 1684、新建 `Green/EntryBoundFloor.lean` 794 行，全量绿、审计 9189）：`stochDom_ldeQuad_flow_floor` 的**假设表与 T148 的 row/col 版逐字相同**，无额外概率输入；**没有出现「目标本身为假」的情况**，二次型的模确实闭合、无因子短缺。关键观察：地板只经 `LDE*Floor` 进入，**多一条 `fl ≤ Λ` 即可让带地板陈述与无地板版形状完全相同、只是常数翻倍**。**`DiagBoundFlow` 的墙倒了**，剩下三件全在 `Gauss/` 侧、无新数学（`hLdiag` 的带时间版、地板吸收需 `DiagBoundFlow'`、`hδ`）。⚠ 因 `Green/` 不能 import `Hierarchy/`，被迫重证 T160 的六条——`LKDecayQuant` 的副本应删除改指到这里。记 paper-deltas #123（原编 #121，撞号已改）。见 STATUS |
| T167 | **Lemma 5.7 (5.36) 的余项 + 接到钉死的 `E⊗E`**（T156 余项）：T156 把 (5.36) 立成了独立逐点估计 `ee_le`/`ee_le_paper`，但留了三条假设与一处接线：(1) **`hsym`**——论文「by symmetry, we only consider the first case」是 (5.22) 的 `k = 1`/`k = 2` 两项之间的对称，不是 `k = 1` 项内部的重标号（另一半里 `(b,a₂)` 边是短的，(5.31) 不适用）。**先试**：证一条对称引理把 `k = 2` 项化成 `k = 1` 项在 `a₁ ↔ a₂`（必要时加共轭/转置）下的像——注意 T162 已查出 `L_{(+,−),(a,b)}` 对一般 Hermitian `H` **不对称**，取向要跟 loop 展开实际产出的走；若对称引理不成立，就对 `k = 2` 项重跑一遍论证。(2) **`h566`**（(5.65)/(5.66) 的 Cauchy–Schwarz 步）：需要 6-loop 的逐元展开（`gloop_three_expand` 的 6 元版）+ `G†E_bG` 的块结构——照 T162 打穿 3-loop 层的办法做。(3) **`h572`**（`(G†E_bG)_{x₁x₁'} ≤ max_{y∈I_b}\|G_{x₁y}\|\|G_{x₁'y}\|`）：`E_b` 是块平均，应为初等。(4) **接线**：(5.36) 左端取 `MomentDuhamel.eeFun`（已是定义、非字段，T145），证 `ee_le_reduced` 类结论直接作用在它上面——**不接 `Step2.Hyp.mart`**（旧路线，fiat）。**验收**：(5.36) 对 `eeFun` 的定理假设表里无 `hsym`/`h566`/`h572`；公理干净；fiat 审计同 T163 | `Hierarchy/Lemma57.lean`（续）或新文件 `Hierarchy/EEDef.lean`（若 `Lemma57.lean` 仍被占用） | Claude Code | **完成**（新建 `Hierarchy/EEDef.lean`，485 行，全量绿、审计 9091）：(5.36) 现在作用在**钉死的 `EEpath`** 上（`EEpath = eeField = eeFun∘X.H` 三者互为 `rfl`），`n = 0` 时连归一化的 `T_{u,D}(‖a₁−a₂‖)` 都不是自由选择。**⭐ 关键更正：(5.22) 的展开本来就在仓库里**（T74 的 `eeEdge_eq_sum_SB` 经 T127 的 `eeEdge_eq_sum_gloop`），`Lemma57.lean` 偏差表第 9 条「展开不在仓库里」是错的，已改；于是 `hEE` 不必是假设，`L^{(1)}` 成了**定义** `eeL6`。**可满足性在 Lean 里证出**（`ee_hyp_consistent`，显式见证），排除了「假设组自相矛盾 ⇒ 结论空洞」这一失效模式。仍是假设的六条：`h273`/`h564`/`h42sq`（别处输入）、`h566`（要 6-loop 展开）、`h572`（初等未做）、`hsym`（已证不可能从 `k=1` 推出）。见 STATUS |
| T168 | **Lemma 3.2（典范划分的分类）立成定理——组合模型**（Jun 2026-09-21 点名开工；今天蓝图里是唯一的「引用未证」节点：Lean 直接把它的结论当作 `TSP` 的**定义**（`Loop/Crossing.lean`），Lemma 3.4 的树表示对所有 `n ≥ 3` 已在该定义上证完，所以本单**不挡证明链**，是补论文保真度）。论文 pp.27–28，Definition 3.1 I–III + Lemma 3.2 + 其归纳证明。**建模（唯一的建模步，须在 blueprint 与文件头明写）**：Def 3.1 的几何对象用它的树 `Γ`（Part III）表示——**典范划分 := 带叶标的有限树** `Γ`（`SimpleGraph V`，`IsTree`），叶子恰为 `a : ZMod n ↪ V`（度 1），**内点度 ≥ 3**（等价类 II 的正规形：度 2 内点只是把一条边细分），**平面性条件：`Γ` 的每条边恰好落在两条区域路径上**，其中区域 `R_i` 的树内边界 := 唯一路径 `P_i = path(a_{i−1}, a_i)`（`R_i` 是 `e_i` 加 `P_i` 围成的多边形；「每个 `a_i` 恰属于 `R_i` 与 `R_{i+1}`」对叶子自动成立——**证一句**）。`R_i ∩ R_j ≠ ∅` := `P_i`、`P_j` 的顶点集相交；**paired** := `P_i`、`P_j` 共享一条边且 `\|i−j\| > 1 mod n`；`F(Γ)` 按 (3.1)。**要证的陈述**：(0) **「`R_i ∩ R_j ∈ E(Γ)`」**：两条区域路径若共享边则恰共享一条（用内点度 ≥ 3）；(1) `F(Γ)` 无交叉对（论文的「crossing」按 ℤ 上的序）；(2) **实现**：每个无交叉的 `F* ⊆ {{i,j} : \|i−j\| > 1 mod n}` 都等于某个 `F(Γ)`；(3) **唯一性**：`F(Γ) = F(Γ')` ⟹ `Γ ≅ Γ'`（保叶标的图同构）；(4) **等价 II**：两棵树的「`R_i ∩ R_j = ∅`」关系相同 ⟺ `F` 相同 ⟺ 同构——即 `SP(P_a) ↔ T_SP(P_a)` 良定且双射；(5) **接到现有定义**：`F` 的像在显式指标换算（论文 1..n ↔ `Fin n`，区域 ↔ 对偶多边形顶点）下**恰为 `RBM.TSP n`**，于是 `def:TSP` 从「由 Lemma 3.2 授权」变成定理。**证法**：按论文 p.28 的归纳（`F = ∅` ⇒ 星形；否则沿一个 paired 对把多边形切成两个小多边形、树在那条内边处切开/粘合）；**只用论文与本仓库，不引外部文献**（例如不引 Semple–Steel 的环序刻画）。**数值自检**：Fig. 4 的例子（`n = 6`，`F = {{1,4},{4,6}}`）与 `n = 3..6` 的计数（1、3、11、45，已有 `TSP_three`…`card_TSP_six`）各配一个 `decide`/具体实例。**验收**：新文件、`lake env lean` exit 0、公理干净；`content.tex` 的 `lem:3.2` 删掉「Cited, not proved」、加 `\lean{}` + `\leanok`、**明写建模步**（「平面划分 ↔ 每条边恰邻两个区域的叶标树」）。**不改** `Loop/Crossing.lean` 的任何现有声明（只在新文件里证它们与模型一致）。**若某条按字面为假**（例如等价 II 与同构不一致），停下报告 | `Loop/CanonicalPartition.lean`（新建） | Claude Code | **部分完成**（`Loop/CanonicalPartition.lean`，815 行，全量绿、审计 9309）：建模步已写进文件头与蓝图；**已证 (0)(1)**（`edge_unique_of_paired`、`FGamma_mem_TSP`），故 `F` 的像 `⊆ TSP`。**模型经 Lean 外穷举验证**：`n ≤ 7` 的树数 1/3/11/45/197 与 `|TSP n|` 完全对上，Figure 4 也对——（`decide` 放不进仓库：9 点树的无环性实测 85 秒）。**实现性/唯一性/像恰为 `TSP` 未证，故 `TSP` 仍是定义、#8 不能撤**；蓝图节点标为「部分形式化」、**未加 `\leanok`**。记 paper-deltas #124（原编 #122，撞号已改） |
| T169 | **`MinorGoodLe`：层级预算版小行好事件，由 `GoodEvent` 确定性推出 + 两条顺手活**（T164 建议 L1；纯确定性、今天能绿）：(1) 新文件定义 `MinorGoodLe X E N u Ψ M`（小行集 `S` 带预算 `S.card ≤ M`），证 `minorGoodLe_of_goodEvent : GoodEvent … Ψ ⟹ MinorGoodLe … (2Ψ) M`，在 `Ψ ≤ 1/4`、`8MΨ ≤ 1` 下经 `gEnt_insert`（(4.9) 的一般层级恒等式）归纳 `Ψ_{j+1} ≤ Ψ_j + 2Ψ_j²` ⟹ `Ψ_j ≤ 2Ψ`，`inv_le` 随归纳一起走。**这是以好事件为前提的逐点定理，不是对所有 `ω` 的假设**。依赖方向 `Green/EntryBound → FlucIterHigh → 新文件`，**`MinorDiffGain.lean` 一行不动**。(2) **`det` 立成定理**：`isUnit_det_sub_smul_one` + `(Hflow …).submatrix` 的 Hermitian 性，无需好事件——四处签名的 `hdet` 参数加带撇版删掉，旧签名保留为推论。(3) **(4.2)/(4.3) 标签更正**：`MinorDiffGain.lean:471`（`off_le` 应为 (4.2)）、`:517`（`diag_sub_le` 应为 (4.3)）、`diag_ne`/`inv_le` 不是 (4.1)（论文 (4.1) 是事件 `Ω(t,c)` 的定义，`\|G_ii\| = O(1)` 是其推论、未编号）；同步 paper-deltas #103 与 `content.tex:1935`——**只改注释与文档**。另记 paper-delta：论文只有层级 0 的 (4.2)(4.3) 与一步抬升 (4.9)，迭代到 `\|S\| ≤ M` 是 Lean 的构造（论文不需改） | 新文件 `Gauss/MinorGoodLe.lean` + 注释/文档 | Claude Code | **(1) 完成**（`Gauss/MinorGoodLe.lean`，335 行，全量绿、审计 8986）：可满足性先行检查通过，且**把「非空洞」证成了定理**（逆向 `MinorGoodLe.goodEvent`）。归纳的三条常数**原样够用且 `8MΨ ≤ 1` 是紧的**；一步 (4.9) 的代价正好等于不变量的增量。`det` 确是白送的定理。必须新证 `gEnt_insert_of_ne`——现有 `gEnt_insert` 吃整个 `MinorGood`，归纳步用不了。**(2)(3) 未做**（要改本文件之外的文件）。⚠ **T170 会遇到依赖成环**：本文件 import `MinorDiffGain` 以复用 `gEnt`，需先把 `gEnt` 下沉或让 T170 走新文件。记 paper-deltas #119（原编 #117，撞号已改）。见 STATUS |
| T170 | **`DiffBd` 加层级预算，消费点改吃 `MinorGoodLe`**（T164 建议 L2；机械，约 500 行，**需独占 `MinorDiffGain.lean`**）：障碍纯粹是 `DiffBd`（`MinorDiffGain.lean:243`）对 `S` **无界量化**；实际到达的层级 `card ≤ 字长 ≤ M = 2p`。给 `DiffBd` 及其归纳加 `S.card ≤ M`，所有 `MinorGood`/`MinorGood'` 的消费点换成 `MinorGoodLe`（T169）。**旧声明保留**（它们正确但前提不可满足），新链全部带撇。依赖 T169。**（10:28 Cowork 追加）T169 的 (2) `det` 立成定理、(3) (4.2)/(4.3) 标签更正没做（它们改别的文件），并入本单**——本单本来就独占 `MinorDiffGain.lean` | `Gauss/MinorDiffGain.lean` | Claude Code | **完成**（全量绿、审计 8986 → 9042）：`gEnt` 已下沉到 `FlucIterHigh.lean` 解环；`DiffBd` 加 `S.card + l.length ≤ M`，`delta`/`shift` 各花一格（**不用 ℕ 截断减法**）、`mul` 预算不变、`diffBd_atom` 的不变量 `B + T.card ≤ M` **和守恒**；13 个消费点全改吃 `MinorGoodLe`。**关键核对：字长预算与层级预算可以是同一个 `M`，没有多出第二个参数、没有消费点要求预算外的层级。**必需品 `iterDeltaFam_congr`/`DiffBd.congr`——预算内只有逐点等式，`funext` 全局族等式拿不到。顺手：删 `hdet`（实际**三处**不是四处）、(4.2)/(4.3) 标签全文对调、**删掉文件头那句关于拆积分的假话**。见 STATUS |
| T171 | **⭐ `MinorDiffGain` 事件条件化——真正的墙**（T164 建议 L3）：把逐点的 `MinorGoodLe` 换成「好事件外 + 行条件概率小」：`hgood : ∀ ω ∉ Bad, MinorGoodLe …` 加 `hslice`（行条件概率，`Gauss.meas_measure_rowSlice_ge`，`CondDom.lean:147`），穿过 `E_k` 用 `Gauss.norm_condRow_le_split`（`CondDom.lean:164`），用例见 `CondStableFlow.lean:285–320`。**先更正文件头的错误说法**：「`MinorDiffGain` 里已经没有条件期望，所以拆积分是合法的」不对——`flucDiagSet` 就是 `qRow`，`applyOps` 还会叠 `E_κ`。生产者消费 `goodSetFlow`（= 论文 (4.1) 的 `Ω(t,c)`，`highProb_goodSetFlow_of_localLaw` 已证），每次应用损一个 `N^τ`（`≺` 允许）。**验收**：一条探针链从 `LocalLawFlow` 出发、经本单与 T169/T170 到 `Eq45Flow`，**假设表里没有任何对所有 `ω` 量化的好事件假设**；公理干净。依赖 T169、T170。**（10:45 Cowork 追加，T172 反例 2）`FlucBound` 同病同方**：两点法已编译证明 `B ≥ 64/65`（`le_B_of_flucBound`），所以 `stochDom_flucAvg` 系列在 `Φ = Ψ²` 处的实例化不可满足、(4.12) 走不通那条接口——`B`、`ε` 同样要挂在事件上（`1_Ω` 进 `E_k`）。**本单一并处理**，并在交付时说明 `Eq45Flow` 的实际生产链走的是哪一条、它的每个假设是否可满足（抄 T172 的两个正面样板：`ContinuityAssembly:1117` 的指示函数门槛、`EntryBound.of_det` 的事件作前件） | `Gauss/MinorDiffGain.lean` 之后的新文件 | Claude Code | **完成**（新建 `Gauss/MinorDiffCond.lean`，726 行，全量绿、审计 9150）：主定理的假设表里**没有任何 `∀ω` 好事件假设**，概率输入只有 `goodSetFlow`（= (4.1)）。⚠ **T164 建议的单一 `hslice` 形状本身不可满足**（冻结另一行即得截面 = 全空间，Markov 循环救不了），正确形状是逐层的塔 `badTower`/`BadFamily`，每字母损 `(ε+#行)/ε`。⚠⚠ **另证出 `MinorDiffGainUpTo` 在 `B ≍ Ψ` 处不可满足**（其 `B` 支配 `Z_k` 的所有 `L^n` 范数，配 T172 的 `‖Z_k‖_∞ ≥ 64/65`）——与 `FlucBound` 是同一堵墙，根因是 **`ι` 没有基数预算**。修法已写清（加 `#ι ≤ n`，`2p` 阶矩展开里本来就成立）。记 paper-deltas #122（原编 #120，撞号已改）。见 STATUS |
| T172 | **⭐⭐ 全仓库「逐点 ∀ ω 假设」的可满足性扫描**（T164 的教训：`MinorGood`/`MinorGood'` 对所有样本点量化，在 `ω = 0` 就假，整支 `MinorDiffGain` 因此悬空，**编译器发现不了**）。只读审计，交 `docs/STATUS.md` 一张表：(1) grep 所有**结构字段与定理假设**中以样本点为参数、且不带事件限制（`ω ∈ Good`、`HighProb`、`StochDom`、`∀ᵐ`）的**确定性不等式**；(2) 对每条在**高斯模型**上做反例检验：`ω = 0`（`H = 0`，`G = −z⁻¹`）、大常数倍单位阵、单个坐标很大——按字面为假就标 ✗ 并给出反例量级；(3) 对每个 ✗，**沿依赖往下列出全部消费者**（哪些「定理」因此是空真的），并标它是否在六步循环的路径上（`Thm221` / Lemmas 2.18–2.20 / T159 的探针链）；(4) `∀ᵐ ω` 形式同样检验（逐点假的若在正测度集上假，`∀ᵐ` 也假——T164 的论证：`green` 对 `ω` 连续、level-`N` 只依赖有限多坐标）。另查**端点**型不可满足：闭区间上要求沿 `√u·X` 可导的假设在 `s N = 0` 时为假（T152 发现；应改用 `_Ioo` 版）。**不改 Lean**；修复另开单。结果并入 T159 的审计 | `docs/STATUS.md` | Claude Code | **完成**（145 个文件、六条检索、两条新编译反例）：**逐点 `∀ω` 全仓库只塌了 `MinorGood(')` 一处，且爆炸半径为 0**（那 8 条定理在本文件外无人 `apply`）。反例比 T164 强：`inv_le` **不提 `Ψ`，没有任何 `Ψ` 能救**。⚠ **新发现：`FlucBound` 的 `B ≥ 64/65`（两点法，已编译）——(4.12) 的 `B ≍ Ψ` 不是「还没证」而是不可能**，`stochDom_flucAvg` 系列在 `Φ = Ψ²` 处的实例化不可满足。其余 40 余处无恙；**`∀ᵐ ω` 形状仓库里根本不存在**。两个正面样板：`ContinuityAssembly` 把门槛写进指示函数、`EntryBound.of_det` 把事件当前件。见 STATUS |
| T173 | **Step 6 的单张量漂移钉死 + 其两条有内容的义务**（T152 余项）：T152 已证 `DLK`/`DG` 的拆分在 Lean 里无益（`sharpExpect_step6_single`），且 `hG`、`hFD` 的 `DG` 半边是空洞、`hH` 单独可 fiat。本单：(1) **把单张量钉死为 `D_v := E[Fpath_v]`**（`MomentDuhamel` 已钉死的漂移，长度 2 时 T163 已证 `F = eGpm + primBil(L−K,L−K)`，无第三项）——**是定义，不是字段**；(2) **期望形漂移恒等式** `∂_v E(L−K)_v = Θ_v∘E(L−K)_v + D_v` 在**开区间** `(s,t)` 上（`hasDerivAt_sample_ELval_hierarchy_gauss` 微分号下求导；逐路径 (5.15) 是 T140 的 `hasDerivAt_sub_prim_thetaGen`），经 T152 的 `Step6.hierarchy_of_hasDerivAt_Ioo` 交出 `hH`——**只用 `_Ioo` 版**：`0 < u` 对 `√u·X` 的链式法则是内禀的，闭区间版在 `s N = 0` 时不可满足；(3) `D` 的快衰减（`hFD` 的有内容半边）与 **(5.133)**（`h5133`）——`D = E[eGpm] + E[primBil(L−K,L−K)]`，前者走 T155/T163 的 (5.35)、后者走 (5.34)；二次项取期望后**不等于**期望的二次项，按论文的 `E E^{((L−K)×(L−K))}` 处理。**验收**：`sharpExpect_step6_single` 的一条探针调用，`D` 为本单的定义、无任何自由张量；fiat + 可满足性审计写进 STATUS | `Gauss/Step6HierarchyGauss.lean`（续） | Claude Code | **(1)(2) 完成，(3) 归约**（`Step6HierarchyGauss.lean` 557 → 905 行，单文件 exit=0）：`driftE` 是 **`def`**，与 `E[Fpath]` 的等价是**定理**；`sharpExpect_step6_driftE` 的陈述里**没有自由张量变量**，T152 警告的 fiat 路径被堵死。期望形漂移恒等式在**开区间**上给出，**二次半边 `E[primBil(L−K,L−K)]` 不与期望交换、原样留在 `driftF` 第三项**——即论文的 `E E^{((L−K)×(L−K))}`。(3) 已归约为「Lemma 5.9 的确定性输入」与「`F` 的一阶矩界」，**取期望不是障碍**；短的是 Ξ-记账（= T165 (2)）。**未为凑 `h5133` 改 `D` 的定义。** 见 STATUS |
| T174 | **T132c 指数表重算（第 0′ 步，只读）**：T132c 第 0 步的表有两处已知偏乐观——(a) T156：(5.36) Case 2(1a) 过完 (5.22) 的 `W∑_b` 后是 **`A^{−1/2}`**（`η_u^{−1}(ℓ_u/ℓ_s)^{3/2}A_u^{−1/2}(J*)²`），不是 `A^{−1}`；(b) T155：(5.35) 形状 2 的**近场项是 `r³` 不是 `r²`**。以 T155/T156/T162/T163 **已编译的**结论（`eG_le_reduced`、`ee_le_paper` 等的实际右端）为准，**(c) paper-deltas #113 ③：(5.36) 的陈述丢了 (2.73) 在 `n = 4` 产生的 `(ℓ_u/ℓ_s)^{3/2}`**（论文 (5.67) 后那行写了、到 (5.36) 陈述里没了；`ℓ_u ≥ ℓ_s`，所以这是 `≥ 1` 的真损失，约 `(η_s/η_u)^{3/4}`）——**表里必须带上它**，并单独回答：它能否被吸收（(2.72) 的余量 / `J*` 门槛）而不改 (5.36) 的陈述？**Jun 11:05 已裁定：论文 (5.36) 第二项补上这个因子**（论文改动，已记）——所以不再问「能否吸收」，**直接按补正后的 (5.36) 算表**，只核对 30 是否仍够；(d) T165：(5.77) 第 3 行多一个 `Ξ^{(L−K)}_{u,1}`（#121），由 (2.68) `≺ 1`，核对不影响指数。逐项重写 `A^{−α}(η_s/η_t)^{β}`（线性化后），核对在 (2.72)「`(η_s/η_t)^{30} ≤ A`，带增益 `N^c`」下每项仍 `≤ N^{−c′}`；**特别核对**：`A^{−1/2}` 那项在根号里还是根号外、Jun 的线性化 `(J*)² ≤ Θ·J*` 在截断支撑上作用后的净指数。**交付**：STATUS 一张新表 + 结论三选一：① 30 够；② 30 不够但 50 或 100 够（Jun 已预授权，写明取哪个、`Cond272`/`hregS` 带撇版的形状）；③ 都不够（停下报告，不改门槛）。**不改 Lean** | `docs/STATUS.md` | Claude Code | **完成**（只读重算，`β*` 全部从已编译陈述与论文原文重推）：**结论不变——30 够，50/100 不启用**。⚠ **但旧审计有两处算错**：(5.36)→(5.42) 的吸收步 `β*` 不是 6 而是 **28.5**（旧审计按 `A^{−1}` 算，实际只剩 `A^{−1/6}` 可花；**论文 (5.36) 自己写的就是 `A^{−1/2}`，是旧审计错不是论文错**），`BootPP` 那行是 5 不是 1。**三条有实现后果的建议**：不做论文那步 `−1/2 → −1/3` 的吸收可把瓶颈 28.5 → **17.5**（零成本）；生产 `Hyp.mart` 时近场项必须**先乘后取 sup**（粗算会超预算 `R^{2.5}`）；#113 ③ 的 `r^{3/2}` 在 (5.44) 的积分里**免费**，(5.36) 不用改。`phi_arith` 走 shape 1 **一字不改**（新增的 `hJA` 由 `hA` 免费推出）；走 shape 2 的改法已探针编译验证。见 STATUS |
| T175 | **具体的 `C²` 截断 `χ` + 实例化 T158 的全部假设**（T158 交付边界）：`CutoffBounds.lean` 对 `χ` 只收 `HasDerivAt` 与 `\|χ′\|`、`\|χ″\|` 的界作假设，**全仓库还没有一个具体的 `χ` 满足它们**——截断方案的前提从未被实例化，是可满足性缺口。用 Mathlib 的 `Real.smoothTransition`（`C^∞`、值在 `[0,1]`）拼出 `χ : ℝ → ℝ`：`[0,1]` 上为 1、`[2,∞)` 上为 0、单调不增，给出显式的 `‖χ′‖∞`、`‖χ″‖∞` 常数（数值不必最优），并逐条证它满足 `CutoffBounds` 的每个假设；**再给一个 `example`**：把这个 `χ` 代进 `CutoffBounds` 的主结论，得到不含任何 `χ` 假设的版本。**先 grep**（`smoothTransition`、`ContDiffBump`、仓库里已有的截断）。二阶导按 T158 的方向导数形式给，不需要 Fréchet | `Gauss/CutoffBounds.lean`（续）或新文件 `Gauss/CutoffChi.lean` | Claude Code | **完成**（新建 `Gauss/CutoffChi.lean`，416 行，全量绿、审计 9605）：⚠ **更正 T158 的记载——Mathlib 的 `ContDiffBump`/`smoothTransition` 不能作定量见证**（只有 `nonneg`/`le_one`/`ContDiff`，**无导数公式、无导数界**），故改用**五次 Hermite 截断**（恰好 `C²`），`C²` 由通用引理推出、不靠手工拼接。常数显式：`‖χ′‖∞ ≤ 15/8`（**紧的，取等已证**）、`‖χ″‖∞ ≤ 15`；`χ′` 支集恰是 T158 的 gap `[1,2]`。**T158 里关于 `χ` 的假设已全部关闭**（grep 确认只有两条，都已卸）。可满足性：`cutChi_spec` 把整包要求合成一条定理证明有居留，另有数值自检——**抄错系数会当场编译失败** |
| T176 | **⭐ 六步循环剩余假设的精确清单（T159 第 0 步，刷新 T147）**：T147（00:43）之后已落地 T149–T173，清单已过时。做一个**编译探针**：按 1→2→3→4/5→6 串到 `Thm221.step`，再经 Lemmas 2.18–2.20 到 `Bounds`，**每一环都调用目前最强的生产者**（矩路线：`Step2Moment`、`MomentDuhamelRhs`、`EGDef`/`DriftDef`、`Step6HierarchyGauss` 的 `driftE` 版、`LKDecayQuant` 的带地板版、`eq45Flow_of_localLaw_gain'` 等），把最终探针定理的**假设表逐条列出**，每条标：① 对应论文哪条、② 由哪张在飞/未认领的单负责（**没有单负责的，标红**）、③ fiat 与可满足性检查结果（沿用 T172 的方法）、④ 是否在旧的 fiat 路线（`SumZeroDyn.Hierarchy`、`Step2.Hyp`）上——在的要换成矩路线版本。**交付**：STATUS 一张表 + 探针源码放 scratch（不入库）+ 一句话「六步循环还差几条具名假设」。**不改 Lean**；标红的由 Cowork 开单 | `docs/STATUS.md` | Claude Code | **完成**（6 个编译探针）：**`Bounds → Steps` 现在只差 10 条具名假设**，探针链的假设里**没有 `Steps`、没有 `Hierarchy`、没有自由张量**，全程只收 `0 ≤ s`。⚠⚠ **查出 T147 没写的接口错配**：`Thm221.step` 只收裸 `Cond272`，全链却要带 `N^c` 增益的 `hregS`——**零新数学但无人负责，挡在总装最后一米**（探针 P3 已证网格能带任意增益）。⚠ **`FlucGainUpTo` 也在同一堵墙上且在活路径**（探针 P5），基数预算的单必须一并写进规格。⚠ **本表顶部「T58 ②③ → T146 完成」是错的**。fiat 审计：活路径只剩 `SumZeroDyn.Hierarchy` 一处冲突，而它是 `h514` 的唯一入口。见 STATUS |
| T177 | **⭐ `MinorDiffGainUpTo`/`FlucGainUpTo` 加基数预算 `#ι ≤ n`，打通 (4.12) 到 `Eq45Flow`**（T171 余项；与 T172 的 `FlucBound` 是同一堵墙）：T171 已编译证明 `MinorDiffGainUpTo` 在 `B ≍ Ψ` 处**不可满足**（取 `ι = Fin n`、空词，`B` 支配 `Z_k` 的全部 `L^n` 范数，而 `‖Z_k‖_∞ ≥ 64/65`），根因是 `ι` **没有基数预算**。修法（T171 STATUS 已写出算术）：给接口加 `#ι ≤ n`——`2p` 阶矩展开里 `#ι ≤ 2p` 本来就成立——并证加了预算后 T171 的条件化余项能被吸收。**带撇版**，旧声明保留（它们正确但在 `B ≍ Ψ` 前提不可满足，文件头注明）。**（11:40 Cowork 追加，T176 探针 P5）上层接口 `FlucGainUpTo` 同样塌**：`integral_pow_norm_flucDiag_le_of_flucGainUpTo` 已编译证明它自己的 `B` 支配 `Z_k` 的每个 `L^n` 范数，而它正是 `eq45Flow_of_localLaw_gain′` 的 `hg` 槽——**预算必须同时加到 `MinorDiffGainUpTo` 与 `FlucGainUpTo` 两层**，只修下层等于没修。另：T171/T172 的两条反例（`‖Z_k‖_∞ ≥ 64/65`）当时只在探针里，`L^n → L^∞` 需要 `ω ↦ Z_k(ω)` 的连续性，**本单顺手把这两条反例入库**（作为「旧接口不可满足」的编译证据，放文件末尾一节）。然后把 T151 的 `eq45Flow_of_localLaw_gain'` 链改吃新接口。**验收（端到端探针）**：从 `LocalLawFlow`（或 `goodSetFlow` = (4.1)）出发，经 T169/T170/T171/本单到 `StepGlue.Eq45Flow`，**打印最终探针的假设表，逐条给出可满足性见证**（仿 T167 的 `ee_hyp_consistent`：一组显式参数使全部数值假设同时成立），公理干净。**若加预算后仍有某条在 `B ≍ Ψ` 处不可满足，停下报告** | `Gauss/MinorDiffCond.lean`（续）或新文件 | Claude Code | **完成**（全量绿、审计 9309 → 9410；`CondStableFlow.lean`/`Eq45FlowInputs.lean` 一字未动）：**两层接口都加了预算**（`FlucGainUpTo'`/`MinorDiffGainUpTo'`，多一条 `#ι ≤ n`），旧声明一字未动、`.budget` 把旧推到新。**`#ι ≤ 2p` 那条 load-bearing 断言查过、成立**：`hg.gain` 全链**只用一次**，`ι = Fin p ⊕ Fin p`。**可满足性双向都验了**：退化脚本现在被预算挡住（证不出 `j ≤ n`，入库了带/不带预算的对照），并给出 `B ≍ Ψ` 的**正向数值见证**。端到端 `eq45Flow_of_goodSetFlow_budget` 从 (4.1) 走到 `Eq45Flow`。⚠ **`#ι = 0` 必须单独走**（余项档给 `1 + P(Bad) ≤ 1`，为假）。⚠ 余两件：`hsmall` 仍是端到端定理的**假设**（约 100–200 行 rpow/ENNReal，无数学悬念）；`‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步**仍未入库**。⚠ **旧的 `eq45Flow_of_localLaw_gain'` 仍在、仍站在不可满足的 `hg` 上**，退役它要动只读文件，待排期 |
| T178 | **(5.36) 余下三条假设：`h566`、`h572`、`hsym`**（T167 余项）：T167 已把 (5.36) 接到 `EEpath`（钉死）并给了可满足性见证，余三条：(1) **`h566`**——(5.65)/(5.66) 的 Cauchy–Schwarz 步，需 **6-loop 的逐元展开**（仿 T162 打穿 3-loop 层：`gloop_three_expand` 的 6 元版 + `G†E_bG` 的块结构 + AM–GM）；(2) **`h572`**——`(G†E_bG)_{x₁x₁′} ≤ max_{y∈I_b}\|G_{x₁y}\|\|G_{x₁′y}\|`，`E_b` 是块平均，初等；(3) **`hsym`**——论文「by symmetry」是 (5.22) 的 `k = 1`/`k = 2` 两项之间的对称（Figure 14）；T167 查明 (5.22) 两项**都在仓库里**（`eeTens` 是对 `k` 的和），所以要么证一条把 `k = 2` 项化成 `k = 1` 项在 `a ↔ a′` 或共轭/转置下的像的对称引理（注意 T162：`L_{(+,−)}` 对一般 Hermitian `H` **不对称**，取向按展开实际产出的走），要么对 `k = 2` 项把 (5.65)–(5.72) 重跑一遍。**验收**：(5.36) 对 `EEpath` 的定理假设表里只剩外部输入（(2.73)、(4.2)/(5.31)、远 `b` 余项），无 `h566`/`h572`/`hsym`；可满足性见证更新 | `Hierarchy/EEDef.lean`（续）或 `Hierarchy/Lemma57.lean` | Claude Code | **`h572` 完成；`h566` 机器落地但假设不可卸（精确否定发现）；`hsym` 按工单未试**（两文件 `lake env lean` exit=0）：⚠ **`h566` 与 `hsym` 不是两条独立假设**——`h566` 的右端是 `k=1` 的形状，而 `k=0` 项带的 `Gsq b a₁` 在该区制**完全没有衰减**，比 (5.36) 差整整 `A^{1/2}`；**`k=0` 正是 `hsym` 管的那一半**，要卸 `h566` 需要的就是 `hsym` 需要的 `k`-拆分。⚠ **另更正论文 (5.72) 的指标序**（`G(z)` 对复 Hermitian `H` 不对称）。记 paper-deltas #113 ⑦⑧。造轮子检查三处命中（删了一条重写的、一条因 import 方向改名、一条因不可见只能重写并注明） |
| T179 | **🔴 `Thm221` 收 `hregS`（带 `N^c` 增益的 (2.72)）而不是裸 `Cond272`**（T176 探针 P2/P3；纯记账、零新数学，挡在总装最后一米）：`Thm221.step` 只收 `Cond272`，而六步全链要的是 `hregS`（`N^c(η_s/η_t)^{30} ≤ A_t`）；`Cond272` 严格更弱，所以 **`Thm221` 按现在的陈述不可证**（paper-deltas #47/#54/#73 记过偏差，没人记这个后果）。`eventually_flow_grid` 也只产出裸 (2.72)。做法：(1) `eventually_flow_grid′`：网格带增益——T176 的 `gridT_step_2_72_gain`（探针 P3）已证网格步能带任意增益 `g`，`flow_grid_2_72` 的证明里本来就有 `g = Im m·W^{τ/2−30τ′}`（`60τ′ < τ`）；(2) `Thm221′`/`Cond272′`：结构加一个增益字段或带撇版（**冻结签名不动**，旧版保留为推论）；(3) Lemmas 2.18–2.20 的迭代与 `Bounds_of_Thm221` 改接带撇版。**验收**：T176 探针 P1 的链条从 `Bounds X E s` 走到 `Thm221′.step` 再回到 `Bounds`，假设里的 (2.72) 就是 `eventually_flow_grid′` 的产物，无人工插入的增益假设；公理干净。论文：**Cowork 已核，(2.72) 原文不带增益**——`(Wℓ_tη_t)^{−1} ≤ ((1−t)/(1−s))^{30}`。记 paper-delta（临时号 `T179a`）：Lean 的 `Thm221′` 多收一个 `N^c`，由 Lemmas 2.18–2.20 的网格自动给出，主定理不受影响；**另写明**：T174 表里唯一 `β* = 30`、R 余量为零的是 (5.41) 按论文字面 shape 1，**走 (2.73) 降幂的 shape 2 后所有行 `β* < 30` 严格成立，此时裸 (2.72) 其实也够**（`A_t ≥ N^c` 由区制给出）——**Jun 12:10 已选 (a)：论文 (2.72) 不改、(5.41) 补一句用 (2.73) 降幂**——所以本单照做（先打通总装），字面版由 **T186** 在 T132c 之后收回 | `Flow/Hypotheses.lean` + `Flow/Iteration.lean`（带撇版） | Claude Code | **完成**（全量绿、审计 9372）：新增 `Cond272'`（= `hregS` **逐字**）与 `Thm221'`（`c` 量化在 `step` 内部），旧签名一字未动。**T176 未编译的 `g ≥ N^c` 那一段现已编译，且比预估短**——直接用 (2.2) 的 `W ≥ N^{1/2+c_B}`，产出 `c = min(τ,1)/32`。下游带撇版在新文件 `Flow/Thm221Gain.lean`，**结论逐字不变（`rfl` 探针验证）**；`Thm221` 在整条装配里**只从 `SpecSeq.bounds` 一处进入**。⚠ **网格给的 `c` 有上界 ≈ `τ/16`**，故 `Thm221'` 必须对任意小 `c > 0` 成立（现有生产者满足，已验）。记 paper-deltas #125；STATUS 的 D1 已收窄到只剩论文措辞 |
| T180 | **🔴 `MomentDuhamel.Hyp` 的高斯模型生产者**（T176：`stochDom_of_momentDuhamel` 的 `Hyp` **无生产者**；T181 的前置）：把 T132a/b、T133、T134、T140、T141、T145、T154 已证的零件装成 `MomentDuhamel.Hyp X E s t n` 的一个实例——字段逐条来源：`drift`（T134/T140 的逐点漂移恒等式，Hermitian `M` 处）、`F_unique`、`momentDuhamel`/`momentDuhamelQ`（T132b 的带时间生成元恒等式 + T133 的 `C²` 界 + T154 的 Lyapunov 收口）、`cMD`、`integrable`。**只在开区间 `(s,t)` 上要导数**（`√u` 在 0 不可导，T152 的 `_Ioo` 教训）。**fiat + 可满足性**：`F` 由 `F_unique` 钉死、`EE` 是定义（T145）——交付时写一个 `example` 证明实例里没有任何可自由赋值的数据。若某字段在高斯模型上按字面不可满足，停下报告 | `Gauss/MomentDuhamelGauss.lean`（续） | Claude Code | **部分完成**（`Gauss/MomentDuhamelHyp.lean`，633 行，全量绿、审计 9409）：六个字段**已产四个**，产出 `hypOfMoments`/`gaussHypOfMoments`。**工单说 `drift` 是唯一障碍——这条已不成立**，T163+T58 之后 `drift` 免费。两条矩不等式的**收口那一半做完了**（`momentIneq_of_diffIneq`：整条由逐点 `hdu` 推出），**常数定死 `cMD p = 2p−1`**，与字段里的 `momNorm _ p` 指数正好对上。⚠ **余下的一句话卡在 `TestFunT` 对所有矩阵过度量化 → STATUS 的 D9（需裁定）**。可满足性逐字段编译验证：`drift` 含 `u = 0`（**这里没有 `0 < u` 接缝**，`√u` 根本不出现），矩不等式在 `v = s_N` 取等 |
| T181 | **🔴 `Lemma514` 走矩路线（时间一致版）并接进 Step 3**（T176：`h514` 无主，且唯一现有生产者 `lemma514_flow′` 经 T118 禁用的 `SumZeroDyn.Hierarchy`，还要 `0 < s`；**今天最大的一块**）：T146 交付的是 `hrhs`（矩 Duhamel 右端三项），`stochDom_of_momentDuhamel` 只给**固定终点**的 `≺`。本单：(1) 以 T180 的实例 + T146/T157/T165 的 `hrhs` 输入得到每个固定 `(t, a)` 的 `≺`；(2) **时间一致化**：`MomentHyp.holder` + `stochDom_timeIcc_of_holder`（T132c 已用的同一套时间网），所需的 `u`-Hölder 模从 `‖H_u − H_{u′}‖ = \|√u−√u′\|·‖X‖` + 确定性包络得出；(3) 产出 `Step3.Lemma514′`（带撇，陈述逐字等于 `Lemma514` 的内容），在 `hs0 : 0 ≤ s N` 下；(4) 把 T176 探针 P1 的 `h514` 换成它。**验收**：P1 链条里不再有 `h514`、不再有任何 `SumZeroDyn.Hierarchy` 或 `Lemma510` 字段；公理干净；可满足性见证。依赖 T180、**T187**（T180 余下的 `momentDuhamel`/`momentDuhamelQ` 两字段由 T187 补齐） | `Gauss/Lemma514Moment.lean`（新建） | Claude Code | **完成**（新建 `Gauss/Lemma514Moment.lean`，787 行，全量绿、审计 9660）：**端到端验收探针 `flow_sharpLmK_of_momentDuhamel` 通过**（bare application 填 `h514` 槽）。**文件里没有任何 `Hierarchy`/`Lemma510` 字段，全程只用 `0 ≤ s N`**——**六步链上最后一条 fiat 冲突消失，且没有重新撕开 T161 的缝**。方法性两点：量词交换 `unifDomIcc_of_forall_stochDom` **并证了逆向、两者等价**（交换没偷偷加强假设）；T124 引擎在常数控制下 `hζlow`/`hslow` 全免。⚠ **负面发现：量词交换对 `hrhs` 不适用**（`∃ C` 排在 `∀ᶠ N` 前），但 `hrhs` 侧**根本不需要**交换。余：A `Hyp` 的两字段（T187/T180）、**B `hHol` 唯一无主**（建议 `Gauss/FlowHolder.lean`）、C `hnum` 与 `edgeKer` 行和无主。可满足性六条全编译，含「`Lemma514Premises` 不能删」的反面论证 |
| T182 | **🔴 Step 6 收尾：`h5133` 的 Ξ-记账 + `hFD` 经 Lemma 5.9 + `hH` 余项**（T176：`h5133` 的 Ξ-记账无主；T173 余项）：T173 已把单张量钉死为 `driftE = E[Fpath]`，(3) 归约为「Lemma 5.9 的确定性输入」与「`F` 的一阶矩界」。本单：(1) **(5.133)**：`E[eGpm]` 走 (5.35)（T155/T163）、`E[primBil(L−K,L−K)]` 走 (5.34)，按 T165 的恒等式 `W(ℓ+1)/A ≤ (Krad+2)/η_u` 做 Ξ-记账，得到 `driftBound_of_5133` 要的形状；(2) `hFD`：`driftE` 的快衰减由 `fastDecay_driftF`（T58(iii)）+ Lemma 5.9 给出；(3) `hH` 的余项（T176 标「部分」）。**只用 `_Ioo` 版**。**验收**：`sharpExpect_step6_driftE` 的探针调用假设表里无 `h5133`/`hFD`/`hH`；可满足性见证 | `Gauss/Step6HierarchyGauss.lean`（续） | Claude Code | **完成**（新建 `Gauss/Step6DriftSplit.lean`，963 行，全量绿、审计 9422）：**`sharpExpect_step6_driftSplit` 把 `hH`/`hFD`/`h5133` 全部卸掉**，`hlow` **从假设变成定理**（T165 的同名假设也因此有了产出者）。⚠⚠ **推翻 T152 的单张量归约**：拆分「毫无代价可省」**只对恒等式成立，对 size estimate 不成立**——`eG` 那半逐路径比 (5.133) **恰好弱一个 `A`**，只能从期望的抵消 (5.134) 拿回，故按论文拆回两个张量（都是 `def`，和为定理）。⚠ 顺带更正 T165：多出来的那个 `A^{−1}` **长在 `Φ` 自己身上**，`norm_driftF_le` 并三行时把它丢了。余下全部不提漂移，其中 **`hG` = (5.134) 是唯一还约束 `E E^{(G)}` 的假设、且与 T152 的空洞版不同——这里是真约束**，无人认领 |
| T183 | **`DiagBoundFlow′`：(4.3) 的带地板时间一致版接进 `Step1.Hyp`**（T107/T166 余项；T176 清单第 2 条）：T166 已交 `ldeQuad` 的带地板时间一致版与 `diag_bound_stochDom_floor_idx`，T107 已把 (4.2) 从 `Step1.Hyp` 的假设表拿掉——**那里只剩 `DiagBoundFlow`**。本单：`hLdiag` 的带时间版（T166 说其生产者 `stochDom_normSq_Hflow_diag` 本来就无条件，查它是否已时间一致）+ `diagBoundFlow_floor : DiagBoundFlow′ … (N^{−B} 地板)`，地板对无条件的 `W⁻¹` 白送吸收（同 T107），再给 `step1Hyp_gauss_of_scale″` 删掉 `hDiag`。**`rfl` 探针验证下游陈述逐字不变**（仿 T107）。**验收**：`Step1.Hyp` 的高斯生产者假设表里无 (4.2)/(4.3) | `Gauss/EntryBoundTime.lean`（续） | Claude Code | **完成**（`Gauss/EntryBoundTime.lean` 纯新增 207 行，全量绿、审计 9372；`Step1Hyp.lean` 等一字未动）：`diagBoundFlow_floor` 交付 `DiagBoundFlow'`，三条 LDE 输入零改写 `exact` 直接过。**`step1Hyp_gauss_of_scale''` 与原版假设表逐字相同，只是同时删掉 `hEntry` 与 `hDiag`——(4.2)/(4.3) 已从 `Step1.Hyp` 彻底消失。**余项实情：`hLdiag` 带时间版白送但要 `of_subset_union` 换指标类型（~25 行，**没撞上 T107 在 row/col 侧的那种缺口**）；地板吸收**直接复用 T107 的引理、没写第二条**。一处形状差异（(4.3) 的内核带 `Kstab κ`）在 `Step1.Hyp` 层面代价为零，不构成 paper-delta。四条 `rfl` 探针全过 |
| T184 | **清理：地板内核归位 + `LKDecayQuant` 的八条重复副本**（T107/T160 的建议，低优先级）：(1) `Gauss.entry_bound_stochDom_floor_idx` 下沉到 `Green/EntryBoundFloor.lean` 与对角版并排；(2) `LKDecayQuant.lean` 里与 `Green/EntryBoundFloor.lean` 重复的八条声明改成一行推论或删除改指（**先 grep 全部使用点**；公开名保留为 `abbrev`/推论，不改签名）；(3) `Decay.norm_couplingLen_le` 的 `hD` 在长度 0 处过强（T165：要求 `\|J\| = 0` 时 `L_∅ = LW` 的界，逼 `Φ ≥ LW`）——加带撇版收 `2 ≤ J.length`，T165 的截断绕行即可删掉。**不改任何结论** | `Green/EntryBoundFloor.lean`、`Hierarchy/LKDecayQuant.lean`、`Hierarchy/Decay.lean` | Claude Code | **完成 (1)(2) + 新增项**（全量绿、审计 9401）：`entry_bound_stochDom_floor_idx` 已下沉、旧名 `export` 保留（`rfl` 验同一常量）；`LKDecayQuant` 的八条重复**删除改指**，逐条比对过语句与证明逐字相同，8 条 `rfl` 探针确认。⭐ **过时消费者 `eq45Flow_of_localLaw_gain(')` 已退役**：Lean 里无人依赖，但蓝图列了名字故保留，**加 `@[deprecated]` 作编译器级护栏**（docstring 挡不住下一个 agent，`MinorGood` 是证据），docstring 写明证据链与替代者。⚠ **`Eq45FlowInputs.lean` 的两个直接喂料仍站在同一堵墙上且无警告**，只读故留后续单。**(3) 未做**（要改 `Decay.lean`，= D8） |
| T185 | **Lemma 3.2 收尾：实现、唯一性、像 = `TSP`**（T168 余项；独立车道，不挡六步）：T168 已给出组合模型 `IsCanonicalTree`（平面性等价于「每条边的叶侧是循环区间」，全文的枢纽），并证了 (0)（`R_i ∩ R_j` 恰是一条边）与 (1)（`F(Γ)` 无交叉，故落在 `TSP`）；`n ≤ 7` 的穷举（树数 1、3、11、45、197 = `\|TSP n\|`）在 Lean 外跑过。余：(2) **实现**——每个无交叉的 `F*` 等于某个 `F(Γ)`（按论文 p.28 的归纳：`F = ∅` 给星形，否则沿一个 paired 对切开）；(3) **唯一性**——`F(Γ) = F(Γ′)` ⟹ 保叶标同构；(4) 等价 II ⟺ 同构；(5) 像恰为 `RBM.TSP n`，于是 `def:TSP` 变成定理、paper-deltas #8 可撤、蓝图节点加 `\leanok`。**用「叶侧是循环区间」这个枢纽做归纳**，避免在 Lean 里枚举树（T168：9 点树的无圈性 `decide` 就要 85 秒）。**只用论文与本仓库** | `Loop/CanonicalPartition.lean`（续） | Claude Code | **完成**（新建 `Loop/CanonicalRealize.lean`，1667 行、81 条定理，全量绿、审计 9868）：**实现、唯一性、像 = `TSP n` 三项全部落地** ⇒ **`RBM.TSP` 升级成定理，paper-deltas #8 撤销**（只剩 #128 的 `3 ≤ n`）；**蓝图 `lem:3.2` 已加 `\leanok`，「未形式化」节点归零**。实现复用 `TreeRepGeneral` 的 laminar 编码，**无环性用割证书 + `sep_of_cut` 而非 `decide`**（T168 实测 9 点树 `decide` 要 85 秒）；唯一性的枢纽仍是 `leafSide_eq_inArc`。锚点：两条 `example` 实例化到 Figure 4。命名检查手动逐个 grep（97 个名字，零冲突） |
| T186 | **`Thm221` 按论文字面：收裸 `Cond272`**（Jun 2026-09-21 12:10 选 (a)：论文 (2.72) 陈述不改，只在 (5.41) 补一句用 (2.73) 降幂；**依赖 T132c 实现与 T179**）：T179 让 `Thm221′` 多收一个 `N^c` 增益（由网格给出，零新数学），但与论文字面不一致。本单把它收回到字面：(1) `hregS` 加指数参数 `β`（带撇版，旧签名保留）；(2) 引理 `hregS_of_cond272 : Cond272 → (N^c ≤ A_t) → β < 30 → hregS_β`（`A^{−α}R^{β} ≤ A^{−α(1−β/30)}` 的算术；`N^c ≤ Wℓ_tη_t` 是 `step1` 自带的区制条件）；(3) 核对全链 `β* ≤ β`——按 T174 的表走 shape 2 且跳过 (5.36)→(5.42) 的吸收步后，最大约 17.5（若 T132c 实际落地的指数不同，以编译结果为准），取 `β = 29`；(4) 给出 `Thm221`（**无撇、逐字等于论文**）的证明，`Thm221′` 降为推论。**验收**：T176 探针 P1 的链条以 `Thm221` 结尾，假设里的 (2.72) 就是 `Cond272` 本身；公理干净。**若某行 `β* ≥ 29`，停下报告**（那时要么在该行用 (2.73) 再降幂，要么回到 T179 的增益版） | **新文件 `RBM1D/Flow/Thm221Bare.lean`**（`Flow/Hypotheses.lean`/`Iteration.lean`/`Scales.lean`/`Thm221Gain.lean` 一字未动；`Hierarchy/` 未碰） | Claude Code | **完成，但结论是裁定反转**（全量 `lake build RBM1D` exit=0、审计 10199）：**裸 `Cond272` 不够**。`β* < 30` 只解决 `R` 的幂；`hregS` 的 `N^c` 还有第二个用处——给 `A_t = Wℓ_tη_t` 多项式下界好吃掉 `≺` 的 `N^δ`——而裸 (2.72) 在 `s = t` 处逐字只是 `1 ≤ A_t`，且 `A_t = 1` **取得到**（已编译 `exists_flowScale_eq_one` / `exists_cond272_not_rpow_le_scale`）。可达的最强形是 `Cond272Reg` = (2.72) **逐字** + `∀ᶠ N, N^c ≤ A_t`（后者正是 Step 1 本来就带的 `hreg`，网格上白送），配 `Thm221Reg`；链 `Thm221 → Thm221Reg → Thm221'`、`Cond272' → Cond272Reg → Cond272`、`Bounds_of_Thm221Reg`（`rfl` 探针）全绿。算术桥 `rpow_mul_rpow_le_of_pow_thirty` 把判据换成 `e/c + b/30 ≤ a`；`hA_phi`（(5.40)，`β* = 10`，瓶颈）与 `hA_betaStar`（(5.41) 远场，`β* = 5.5`）对 `u ∈ [s,t]` 一致产出，**只要 `δ ≤ c/4`**（带增益路线要 `δ ≤ c/2`，代价就是 `δ` 预算减半）。scratchpad 探针已编译：`Step2MomentStep.side_conditions_of_reg` 的整个结论可从 `Cond272Reg` 重建。**paper-delta #132**：建议论文在 (2.72) 后补「`Wℓ_tη_t ≥ N^c`」。**未做**：`Hierarchy/` 侧的带撇版（`side_conditions_of_reg'` 等，文件被并行车道占用）、六步合拢、blueprint |
| T187 | **⭐ `TestFun`/`TestFunT` 只对 Hermitian 矩阵量化（带撇版）+ 补齐 `MomentDuhamel.Hyp` 的最后两字段**（T180 余项；D9 由 Cowork 定为 (i)）：T180 已产出 `Hyp` 六字段中的四个（`F` 经 `rfl` 钉到 `DriftDef.driftF`、`drift`、`integrable`、`cMD p = 2p−1`），并把 `momentDuhamel`/`momentDuhamelQ` 归约成一条关于 `ψ′` 的逐点微分不等式（`momentIneq_of_diffIneq`）。卡点是**过度量化**：`hasDerivAt_integral_Psi_pairs` 收 `Gauss.TestFunT`，而 `TestFun`/`TestFunT` 的 `bdd₀/₁/₂` 与 `slice` 对**所有**矩阵量化，`Ψ = \|U∘(L−K)\|^{2p}` 只在 Hermitian 集上合格（`(M−z_u)⁻¹` 在非 Hermitian `M` 上无界、奇异处不连续）。本单：(1) `TestFun′`/`TestFunT′`：`∀ M, M.IsHermitian → …`（`slice` 的 `ContDiff` 改为沿 Hermitian 线段，流与流值之间的线段都在 Hermitian 集内）；(2) `hasDerivAt_integral_Psi′`/`…_pairs′`：控制收敛在流上重证（T141 的常数控制函数思路可复用）；(3) 证 `Ψ ∈ TestFunT′`（T133 的 `C²` 界本来就是在 Hermitian 处给的）；(4) 由此补齐 `Hyp.momentDuhamel`/`momentDuhamelQ`，交出完整实例 `momentDuhamelHyp_gauss`。**旧的 `TestFun`/`TestFunT` 一字不改**。**验收**：完整 `Hyp` 实例编译，`example` 证明实例里无可自由赋值数据；可满足性见证（T180 已有的「`v = s_N` 处取等」）保留 | `Gauss/MomentDuhamelHyp.lean`（续）+ `Gauss/LoopC2.lean`/`MomentDuhamelGauss.lean` 带撇版 | Claude Code | **带撇类完成；两条 `Hyp` 字段未闭合**（新建 `Gauss/TestFunHerm.lean`，756 行，全量绿、审计 9561）：`TestFun'`/`TestFunT'` 落地，旧类一字未改并可装进新类。⭐ **工单预估的大头（把控制收敛改写到流上）根本不需要**——正则化 `Φ∘hermCLM` 是**货真价实的旧类、常数相同**，四条生成元恒等式全是旧恒等式的推论，**一行都没重证**。顺带把 `Generator.lean`「The Hermitian projection」一节**只写了散文、从未证明**的断言补成定理；T180 的第二条接缝（`genMomentPt_le` 要全局 `ContDiff`）已闭合。⚠ **比 D9 更细的一条**：带撇类对**原始** `Ψ` 仍给不出来（`bdd₁/₂` 要全方向算子范数，正则化只给投影后的，反向不成立）——**这是本单唯一被证伪的猜测，Lean 第一次编译就拦下了**；可用形状是 `_of_herm` 版，两条前提对原始对象都现成。**`momentDuhamel`/`momentDuhamelQ` 仍未闭合**：还差含时可容许性（`(u,M)` 联合 `C²`、`edgeKer`/`Kval` 对 `u` 的二阶、以及圈对 **`z`** 的导数界——**T141 给的是「`M`-导数界对 `z` 一致」，不是 `z`-导数界**）与 drift+Hölder 链 |
| T188 | **(4.12)→`Eq45Flow` 预算版收尾：`hsmall` 由高概率推出 + 接进六步探针**（T177 余项）：T177 已给两层接口加基数预算，并在 `MinorDiffCond.lean` 按预算版重建 (4.12)→`Eq45Flow` 整条链，正反两向可满足性都查过。余：(1) **`hsmall`** 仍是端到端定理的假设——由 `HighProb (goodSetFlow …)` 推出（T177 估 100–200 行 rpow/ENNReal 记账，无数学内容）；(2) 把预算版端到端定理接进 T176 探针 P1，**替换 P1 里的 `Eq45Flow` 假设**；(3) 旧的 `eq45Flow_of_localLaw_gain′` 站在不可满足的 `hg` 上——**不删**（签名冻结），在 docstring 里注明「前提在 `B ≍ Ψ` 处不可满足，见 T171/T177，用预算版」；**(3′)（T184 余项）**：`Eq45FlowInputs.lean` 里还有两个站在同一个不可满足 `hg` 上的 feeder，**没有任何警告**——同样加 `@[deprecated]` 指向预算版（T184 的做法：编译器级护栏，比 docstring 管用）；(4) 可选：`‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步（需 `ω ↦ Z_k(ω)` 连续性）入库，把那堵墙从「半编译」变成定论。**验收**：P1 的假设表里不再有 `Eq45Flow`；公理干净 | `Gauss/MinorDiffCond.lean`（续）+ `Gauss/Eq45Small.lean`（新）+ P1 探针 | Claude Code | **完成**（`lake build RBM1D` exit=0，审计 **9475** 条全清；只读文件一字未动）：(1) **`hsmall` 已由 `HighProb` 推出**（`hsmall_of_highProb`，新文件 `Gauss/Eq45Small.lean`），端到端 `eq45Flow_of_goodSetFlow_highProb` 的假设表里**没有 `hsmall`**；实际用到的区制界只有两条，且**都是原本就在的假设**：`hδnet`（→`PolyLo δ`）与 `hEnv`（→`PolyHi (η⁻¹+1)`），没有新增任何假设。(2) P1 的 (4.5) 槽已换掉：探针 `steps45_glue_no_eq45Flow`（scratchpad）把 `flow_steps45_glue_flowAs` 的 `h45 : Eq45Flow` 现场产出，公理干净。(3) 已由 T184 的护栏办掉，本单未动只读文件。(4) 未做（可选项）。⚠ **顺带查出并修掉一处真正的空洞**：T177 的 `hMδ : ∀ p N, 8(2p)δ_N ≤ 1` 与 `hδC : ∀ p N, …` 配 `hδpos : ∀ N, 0 < δ N` **不可满足**（固定 `N`、`p→∞`），即 `eq45Flow_of_goodSetFlow_budget` 原本是**空真**的。已改成论文的量词次序 `∀ p, ∀ᶠ N`；反例 `not_forall_mul_le_one` 与正向显式见证 `eq45Flow_delta_hyps_consistent`（`K=12`、`δ_N=(N+4)^{-28}`，`hδnet` 与 `hfine` 同时成立）都已入库 |
| T189 | **Step 6 的 (5.134)–(5.135)：`E E^{(G̃)}` 靠期望内的抵消多拿一个 `A^{−1}`**（T182 余项；Step 6 最后一条有内容的假设 `hG`）：T182 证明单张量路线在 `eG` 半边**逐路径**比 (5.133) 差一个 `A = Wℓ_uη_u`，且逐路径拿不回来（`Ξ^{(L)}_{u,3}`、`Ξ^{(L−K)}_{u,1}` 已花掉），故把漂移拆回 `driftELK + driftEG`（都是定义，和为 `driftE` 是定理），消费者换成双张量的 `sharpExpect_step6`，其 `hG` 正是 (5.134)–(5.135)。**`driftEG` 已钉死，所以这条 `hG` 有内容**（不同于 T152 那个取 `DG = 0` 即满足的空洞版）。按论文 (5.134)：在 `E^{(G̃)}` 的 3-loop 里写 `L = K + (L−K)`——**`K` 部分是确定性的，期望直接作用在 1-loop 上**，用 **(5.126)** 的 `E⟨(G−m)E_a⟩` 界（期望内的抵消就在这里）乘 (2.59) 的 `\|K\|`；**`(L−K)` 部分**逐路径用两次 (2.78)（`(L−K)_{(+),(a)}` 与长度 3 的 `L−K`）。得 (5.135)：`E E^{(G̃)} ≺ η_u^{−1}(Wℓ_uη_u)^{−3}`。**先查** (5.126) 在仓库里的形状（Step 6 那一节）与 (2.59)/(2.78) 的现有生产者；fast decay 部分 T182 已给。**验收**：双张量 `sharpExpect_step6` 的探针调用假设表里无 `hG`；公理干净；可满足性见证 | `Gauss/Step6DriftSplit.lean`（续） | Claude Code | **完成**（新建 `Gauss/Step6DriftEG.lean`，895 行，全量绿、审计 9632）：(5.134)/(5.135) 已证，**`sharpExpect_step6_driftEG` 的假设表里没有 `hG`**（连带少掉 T182 的 `hq13` 与 `hint2`）。⚠ **更正 T182 的归因**：两半**各**多一个 `A^{−1}`，**只有 `K` 半是期望里的抵消**（(5.126)）；`L−K` 半是**纯逐路径**的，来自「3-loop 取 `L−K` 而不是 `L`」——(5.77) 第 3 行短一个 `A` 正因为取成了 `L`。⚠ **否定发现**：`Step6.sharpExpect_step6` 的 `hG` **按字面推不出来**（只给一致界却要 `W·ℓ_u·Λ`，而一致界只能给 `W·L·Λ`；论文的 `ℓ_u` 来自 3-loop 的**衰减**，`hG` 的前提不含衰减信息）——故本单不证 `hG`，直接证它的结论 (5.135)。记 paper-deltas #127。另证出 Lemma 5.15 只在 `+` 处陈述但**覆盖两个电荷**（`G(σ)ᴴ = G(−σ)`），否则 (5.134) 只覆盖四种里的一种 |
| T190 | **(5.36) 的 `h566` 与 `hsym` 一并卸掉：对 (5.22) 的另一项镜像重跑 (5.65)–(5.72)**（T178 余项）：T178 查明二者是同一件事——`eeL6` 是对 `k` 的和，`h566` 的右端是 `k = 1` 的形状；在 `case2a_pointwise` 实际使用的区制里，`k = 0` 项带的 `Gsq b a₁` **完全无衰减**，`b`-求和后比 (5.36) 差整整 `A^{1/2}`。所以要做的是论文「by symmetry」的真实内容：对 `k = 0` 项（Figure 14 右图）在**区域 (2)**（`\|b−a₁\| ≥ \|b−a₂\|`）里按 `a₁ ↔ a₂`（连同 `a′`）互换角色重跑 (5.65)–(5.72)，再把两个区域拼起来。T178 已备好的零件可全用：(5.65) 展开、四边逐元界、`G(σ)E_bG(−σ)` 块平方质量 = 4-loop、Schwarz 收口、`glueIdx_two_{zero,one}`（`n = 0` 的两个显式 6-loop）。**注意**：复 Hermitian 下 `G` 不对称（T162、T178），镜像时下标次序按展开实际产出的走，**不要假设 `\|G_{xy}\| = \|G_{yx}\|`**。**验收**：(5.36) 对 `EEpath` 的定理假设表里无 `h566`、`hsym`；可满足性见证更新 | `Hierarchy/EEDef.lean` + `Hierarchy/Lemma57.lean`（续） | Claude Code | **完成——两条假设同时卸掉**（`Lemma57.lean` +421、`EEDef.lean` +699，全量绿）：`ee_le_EEpath_sym` 的假设表里既无 `h566` 也无 `hsym`。**关键不是拆 `k` 而是换割点**：6-loop 有两个黏合标号，`k=1` 时 `b` 只碰 `a₁` 块、`b'` 只碰 `a₂` 块，`k=0` 反过来——**这才是 Figure 14 对称的实质**。**T178 说的「`k=0` 差整整 `A^{1/2}`」是割点选错造成的，换割点后消失**。代价只是记账（`hrow` = 论文 "treat `b=b′`" 的显式化，记 paper-deltas #129）。可满足性见证**同时**覆盖两条定理，并补上旧见证漏掉的 `hA`/`hr` |
| T191 | **⭐ `MomentDuhamel.Hyp` 最后两字段 `momentDuhamel`/`momentDuhamelQ`**（T180/T187 余项；T181 的前置）：T187 已交 `TestFun′`/`TestFunT′`（只对 Hermitian 量化，`Φ ∘ hermCLM` 是旧类的真实例，四条生成元恒等式无需重证）与 `_of_herm` 形式。余下是**时间相关的可容许性**：`(u,M)` 联合 `C²`、`edgeKer`/`Kval` 对 `u` 的二阶依赖（仓库只有一阶）、对 `z` 的导数界（T141 给的是对 `M` 的导数关于 `z` 一致，不是对 `z` 求导），外加漂移 + Hölder 链。**第 0 步（先做，交 STATUS）**：核对生成元恒等式 `d/du E[Ψ(u,H_u)] = E[∂₁Ψ] + ½ΣS E[∂∂Ψ]` 的证明**实际**要 `Ψ` 对 `u` 几阶——若只要 `C¹`（对 `M` 才要 `C²`），那么 `TestFunT` 对时间的 `C²` 要求就是又一处**过度要求**（今天第七次），加带撇版放宽，`edgeKer`/`Kval` 的二阶 `u`-依赖就不用做了。然后补齐两字段，交完整实例 `momentDuhamelHyp_gauss`。**只在开区间 `(s,t)` 上要导数**。**验收**：完整 `Hyp` 实例编译，`example` 证明无自由数据；可满足性见证 | `Gauss/MomentDuhamelHyp.lean` + `Gauss/TestFunHerm.lean`（续） | Claude Code | **分析链全部打通，两字段仍未闭合**（新建 `Gauss/MomentDuhamelTime.lean`，1421 行，全量绿、审计 10016）：⚠ **第 0 步答案——`TestFunT` 对时间的 `C²` 是过度要求（今天第七次）**，联合 `contDiffAt` 只被用了两处；`TestFunT₁` 结论逐字不变，**严格性用 `not_testFunT_kinkT` 证出来**。**后果：`edgeKer`/`Kval` 对 `u` 的二阶依赖不用做了**，短的是联合正则性不是第二个时间导数。Hölder/除以 `pψ^{p−1}`/总装三块全落地（⚠ **`p = 1` 必须单独走**；`ψ=0` 的极限是初等的、不需控制收敛）。⚠ **真陷阱：`cMD p = 2p−1` 在 `p=0` 为负、装不进 `cMD_nonneg`**，改 `max 0 (2p−1)`——T180 的记载要按这个读。**唯一真缺口是 `bddT` 要圈对 `z` 的导数界**（T187 的判断成立） |
| T192 | **`Lemma514` 矩路线的余项：`hHol`（`u` 方向的确定性 Hölder 模）+ `hnum` + `edgeKer` 行和**（T181 余项；T181 标「唯一真正无主的一块」）：T181 的 `flow_sharpLmK_of_momentDuhamel` 已按裸应用填进 `Step45.flow_sharpLmK` 的 `h514` 槽，文件内无 `SumZeroDyn.Hierarchy`/`Lemma510`、全程 `0 ≤ s`；常数控制下 T124 的网引擎只剩 `hHol`。本单：(1) **`hHol`**——`u ↦ (U_{u,t}∘(L−K)_u)_a` 在 `[s,t]` 上的确定性 Hölder 模：`‖H_u − H_{u′}‖ = \|√u−√u′\|·‖X‖ ≤ \|u−u′\|^{1/2}·‖X‖`，配 `‖G‖ ≤ η⁻¹` 的预解式 Lipschitz、`z_u` 与 `U_{u,t}` 对 `u` 的 Lipschitz（`hasDerivAt_Uker_thetaOp`，T152），`‖X‖` 用 T109/T129 的 `‖X‖ ≺ 1` + 确定性包络；**注意 `u` 在 0 附近 `√u` 只 1/2-Hölder**，模写成 `\|u−u′\|^{1/2}`（T106 的做法）；(2) `hnum` 与 `edgeKer` 行和（T181 列为有主但尚未落地的小项，查清归属，能顺手做就做）。**新文件 `Gauss/FlowHolder.lean`**（T181 的建议）。**验收**：T181 的端到端探针 `flow_sharpLmK_of_momentDuhamel` 的假设表里只剩 `Hyp` 的两字段（T191）；可满足性见证 | `Gauss/FlowHolder.lean`（新建） | Claude Code | **三块全部落地**（新建 `Gauss/Lemma514Holder.lean`，1071 行，全量绿、审计 9941；**不叫 `FlowHolder.lean`——那个名字已被 T106 占用**）：`hHol_flow`（`γ = 1/2`，常数全显式，**全程只用 `0 ≤ s N`**），验收探针裸应用喂进 `h514`/`hHol` 槽。⚠ **更正 T181**：它列的三块缺口里**第一块早就存在**（T116）；且 **`lemma514_forall_of_momentDuhamel` 的 `(K,γ)` 排在 `∀ m` 前面，要不到**（模必带 `η^{−(m+1)}`，常数按 `m` 几何增长）——正确接口是单 `m` 版，已另给 `lemma514_forall_of_hHol_flow`。⚠ **`edgeKer` 行和不全是记账**：`hkerC`/`hker2C` 的常数**存在当且仅当短窗口 `t_N − s_N ≤ κ(1−t_N)`**，固定窗长而 `t_N ↑ 1` 时不可满足——**这是真假设**。可满足性两条编译（`‖X‖ ≺ 1` 真造出 `Ξ`，否则 `hXΞ` 会空真；长度 2 处 `hKb` 是定理）。余：`hKb` 在长度 ≥ 3 未装配、短窗口条件未从六步导出 |
| T193 | **蓝图同步：T163–T192 的节点**（只改 `blueprint/src/content.tex`，不改 Lean）：今天落地的一批关键声明大多没有蓝图节点或节点过时——`EGDef`/`DriftDef`/`DriftBound`（钉死的漂移与 (5.77)）、`EEDef`（(5.36) 接 `EEpath`）、`MomentDuhamelHyp`/`TestFunHerm`、`Lemma514Moment`（Lemma 5.14 矩路线）、`Step6DriftSplit`/`Step6DriftEG`（(5.133)–(5.135)）、`MinorGoodLe`/`MinorDiffCond`/`Eq45Small`（(4.12)→`Eq45Flow` 预算版）、`EntryBoundTime`（(4.2)/(4.3) 带地板时间一致）、`Thm221Gain`、`CutoffBounds`/`CutoffChi`。每个节点：`\lean{}` 列关键声明、`\uses{}` 连到论文编号节点、**仍带假设的写明剩几条、归哪张单**（不加 `\leanok` 除非无条件）；被取代的旧节点（`MinorGood` 一支、`eq45Flow_of_localLaw_gain`）注明「已被 … 取代（前提不可满足）」。`leanblueprint checkdecls` 通过（名字全部能解析）。**不要**为了变绿改 `\leanok` 的判定标准 | `blueprint/src/content.tex` | Claude Code | **完成**（`content.tex` only；**176 节点 / 173 已形式化 / 2694 名字 / 0 statement-only / 0 not-yet**）：新增 6 个节点（(4.12) 的塔与基数预算、其余项与量词序、Step 2 的一步改进、截断机器、`EntryBoundTime`、`Thm221Gain`），扩写 10 个。**否定结论全部写进了蓝图而不只是 STATUS**。`lem:5.14` 已按 T195 重写（「真假设」→「在会用到的地方为假」）。⭐ **主动收紧了一处诚实性**：查出 **T195 是 docs-only 提交、那 7 条定理没入库**，因此拒绝给它们挂 `\lean{}` 并在正文写明——这条我已回写进 STATUS。另自跑依赖图 DFS（无环）与 `xelatex` 构建（exit=0） |
| T194 | **Theorem 2.2 的概率一半：(i) 能量一致的 `Thm221`（新文件）**（T153 第 0 步已完成、D6 已定；**低优先级车道**，六步主线优先）：T153 探针已证 `Flow/` 层固定 `E` 纯参数化——换成 `E : ℕ → ℝ` 证明脚本一字不改，`SpecSeq` 的能量切片条件随之消失（销 paper-deltas #38 与 #5 的一半）。本单：新文件（骨架约 170 行、**0 个现有签名改动**）给出 `E : ℕ → ℝ` 版的 `BoundsCore`/`Bounds`/`Cond272`/`Thm221` 与四条迭代引理（照抄证明脚本），并顺手修 `Loop/SumZero.norm_Alayer_le` 里 `ι = (mE E).im` 的非一致（经 `mE_im_ge`）。(ii)（能量网 + Lipschitz 到随机 `λ_k(ω)`）紧接着另开。**Theorem 2.2 的措辞按原文**：(2.10) 带 `1(λ_k ∈ [−2+κ, 2−κ])` | `Flow/EnergyUniform.lean`（新建） | Claude Code | **完成**（新建 `Flow/EnergyUniform.lean`，685 行，全量绿、审计 10168；**0 个现有签名改动**）：`E : ℕ → ℝ` 版结构 + 四条迭代引理（**脚本逐字照抄**）+ `SpecSeqN` + Theorem 2.3 整条；**`localSemicircleLaw_of_Thm221N_of_z` 的陈述里已无能量参数 ⇒ paper-deltas #38 的局部律那一半撤销**。镜像**带撇（加成）主干**——理由是「`N` 依赖能量与 `N^c` 加成正交」，**T186 若改未加成路线只影响不带撇那一支**。**路线 (ii) 的网输入齐备**。T153 的 `∀E ∃C` 盲区扫出 **40 条（不是 34）**，**没有一条在本单路径上——是编译事实不是抽查**。未做：Thm 2.4 的 `N` 版、`norm_Alayer_le` 的非一致（协议限制，建议单开小单） |
| T195 | **⭐ `Lemma514` 矩路线里 `edgeKer` 行和的常数：短窗口假设 vs 论文 (5.92)「无 `(η_s/η_t)` 前因子」**（T192 余项；**可能是空真/可满足性问题**）：T192 查明 `hkerC`/`hker2C` 的左端恰为 `1 + (w−u)/(1−w) = (1−u)/(1−w)`，**常数存在当且仅当短窗口** `t_N − s_N ≤ κ(1−t_N)`；而 Theorem 2.21 的窗口只受 (2.72) 约束（`R = (1−s)/(1−t)` 可到 `A_t^{1/30}`），**固定常数的 `hkerC` 在 `R → ∞` 时不可满足**——若按现在的形状接进总装，Step 3 就是空真的。论文 (5.92) 明言「there is no prefactor depending on `(η_s/η_t)`」，靠的是 §5.5 的**求和为零算子 `Q_t`** 与快衰减（sum-zero 张量上 `U` 的界不随 `R` 长）。**第 0 步（只读，交 STATUS）**：对照论文 §5.5–5.6 与 (7.14)，查清矩路线（T146 `hrhs`、T181、T192）在哪一步用了**不带 sum-zero 的**裸行和；回答二选一：(a) 该步只作用在 sum-zero/快衰减张量上，换用 `Q_t` 的 `R`-无关界（仓库里旧路线有 `norm_Uker_sumZero_scale_le`、`norm_Uker_fastDecay_le_sumZero`，T161 已放宽到 `0 ≤ t`）即可去掉短窗口假设；(b) 不能，则常数取 `C·R^k`（写出 `k`），并按 T174 的方法核对 Step 3 的归纳（(5.92) 对 `n` 迭代有限次）在 (2.72) 的 30 下仍闭合——**若 (b) 且不闭合，停下报告，这会是论文层面的问题，要转 Jun**。之后按结论实现（带撇版，不改冻结签名）。**验收**：`lemma514_forall_of_hHol_flow` 的探针在 Theorem 2.21 的一般窗口（只假设 (2.72)）下可满足性见证成立 | `Gauss/Lemma514Holder.lean`（续）+ `docs/STATUS.md` | Claude Code | **完成（重要否定结论）**（只读审计 + 7 条编译定理）：**短窗口条件在论文自己的网格上是假的**（`gridS_window_len` 给出 `(t−s)/(1−t) = W^{τ'} − 1` 恰好相等，`no_const_Ck` 由 `W_N → ∞` 反证）。⭐ **根因：`hkerC` 的左端逐字就是 Lemma 7.1，而 (5.92) 的「无前因子」正是「不许用 7.1」**——Lemma 5.14 的每一项都经 `Q_u` 后用 **(7.16)**，仓库三档齐备而**矩路线用的是最弱那一档**，多付 `R^{n+2}`。「常数取 `C·R^k`」不闭合（`prefactor_not_absorbable_in_Scales`；**且 `R` 幂乘在 `Λ^{1/2}` 上，加大 `k` 救不了**）。**论文自洽，缺口在 Lean 这一侧**（paper-deltas #131）。⚠ **立即风险：`hkerC_flow`/`hker2C_flow` 的 `hwin` 槽在总装窗口不可满足，用它填 `hrhs` 会让 Step 3 空真**——建议加 T184 式护栏。要补：(7.16) 的矩形式、`momentDuhamelQ` 的消费者（该字段至今无消费者） |
| T196 | **`bddT`：loop 观测量对谱参数 `z` 的导数界**（T191 余项；`MomentDuhamel.Hyp` 最后一个缺口）：**⚠ Cowork 15:58 更正（滞留审计 B.4）：T191 的余项是四项——`diffJoint`、`contT`、`bddT`、`φ′` 的识别与边条件，本单全部负责，不只 `bddT`**（转派前没重读 T191 全文，是 Cowork 的疏漏）。T191 已证 `TestFunT` 对时间的 `C²` 是过度要求（放宽严格，`(u−½)\|u−½\|` 为证），两字段的 Hölder、除以 `pψ^{p−1}`、组装全部落地，**只差 `bddT`**——要 `∂_z` 的界，而 T141 给的是「对 `M` 的导数关于 `z` 一致」，不是对 `z` 求导。做法：`∂_z G(z) = G(z)²`，故 `‖∂_z G‖ ≤ η^{−2}`（`η = Im z`）；loop `L_{σ,a}` 是 `G` 的多线性函数，`∂_z L` 由乘积法则给出、每项多一个 `G`，界多一个 `η^{−1}`；`z_u` 对 `u` 的导数有界（`z_u` 显式）；在窗口上 `η_u ≥ η_t > 0` 一致，故 `∂_u Ψ` 一致有界。**先 grep**（仓库里多半已有 `hasDerivAt` 的预解式版本）。**验收**：`momentDuhamelHyp_gauss` 完整实例编译，`example` 证明无自由数据；可满足性见证 | `Gauss/MomentDuhamelTime.lean`（续） | Claude Code | **`TestFunT₁` 七个字段全部闭合；`Hyp` 两字段仍未闭合**（新建 `Gauss/MomentDuhamelBddT.lean`，1000 行、56 条，全量绿、审计 10411）：⚠ **更正诊断——缺的不是 `∂_z G = G²`**（`hasDerivAt_gloop_zt` + T134 的包络早就有），**真正要做的是组装**（`u` 同时出现在 `z_u`、传播子运行时间、`K_u` 三处；落地 `hasDerivAt_Uker_arg` 的 Leibniz 版 + 沿实路径的 `(f·conj f)^p` 求导）。⚠ **另查出 `bdd₀/₁/₂` 的窗口一致版原本也短、T191 没点名**（T133 给的是固定 `u`，`∃ C` 穿不过 `∀ u`），已补。**可满足性做了 T180 那次事故的同形检查**：显式造出非 Hermitian 且奇异的 `M`（原始预解式坍塌为 0），并证明一致界**确实在该点取值**——`∀ M` 不是伪装的 `∀ M, IsHermitian →`，且写明界讲的是经 `hermCLM` 分解后的对象、**没有绕过 T187 关于 `bdd₁/₂` 的结论**。未做：φ′ 的识别、边条件、`momentObsT ↔ Uker∘lkT` 的逐字对齐 |
| T197 | **截断版矩 Duhamel 接口 + `MomentHypCut`**（D10 → (a)；T132c 余项）：T132c 已交 `BootPP.step`（连续时间的量化降到有限网点）、`bootPP_of_net`、`flowEq548_of_near_far`，指数全过（瓶颈 `β* = 10`，近场 `r³` 为 4、零余量，`δ ≤ c/24` 有一个量级的余裕）；并编译证明 **`MomentHyp.step` 按冻结形状不可证**（`bnd_poly` 不许 `bnd` 带 `N` 的幂，而 `J*` 的并集界每阶付 `L² ≍ N²`；矩层去截断余项不小于门槛本身）——**冻结不动**。本单：(1) 新建 `Gauss/MomentDuhamelCut.lean`：`χ(Ξ₂/Θ)`（T175 的 `cutChi`）截断后的矩 Duhamel 接口，在 `χ` 的支撑上自二次项线性化，**在前缀事件上截断与未截断的 loop 重合**；**现有 `MomentDuhamel*.lean` 一字不动**；(2) `MomentHypCut`：前缀条件下网上的穿越论证（T132c 已放好的替代路径）；(3) 用它补齐 `BootPP.step` 与 (5.48) 的余项。**可满足性**：截断版字段在高斯模型上给见证；注意 `(+,+)` 用 (2.73) 的先验跳过自举**已被证伪**（自二次项在 `θ ≥ A_t` 不是压缩）。**验收**：T176 探针 P1 里的 `MomentHyp`/`hΘ` 两条被本单的生产者替换 | `Gauss/MomentDuhamelCut.lean`（新建）+ `Hierarchy/Step2MomentStep.lean`（续） | Claude Code | **完成**（新建 `Gauss/MomentDuhamelCut.lean`，1021 行，全量绿、审计 10312）：**`step2_cut`/`aprioriDecay_cut` 的结论与 `Step2Moment` 版逐字相同——整个 Step 2 绕开了已证不可证的 `MomentHyp.step`，只剩一条具名假设 `CutHyp.moment`**。截断自带确定性包络 `2Θ`，故 `env`/`env_le`/`cont` 三个字段直接消失；`cut_contraction` 正是 T132c `no_finite_pass` 的对照面（截断把映射拉回收缩半径内）；**去截断在概率层、余项为零**。可满足性给出**完整实例**且取在**临界标度 `J ≡ Θ`**，`mesh_fine` 与 `card_le` 这对反向条件由同一见证满足、且前者取等。⚠ **新的无主项：`hnear` 要锐化到 `(η_s/η_u)²` 而仓库只给 `(η_s/η_u)^4`**，T198 的规格未覆盖 |
| T198 | **`hfar`：矩路线上带三个指示函数的 one-step bound**（D11；T132c 余项；(5.48) 唯一缺的东西）：(5.39)/(5.41)/(5.44) 的三个指示函数必须**带过** one-step bound，而旧的 `Step2.step_bound` 把它们全丢了——**不改它**（旧路线、挂在 fiat 的 `Step2.Hyp` 上）。在矩路线上重做：以 T197 的截断版接口 + T163/T167 的钉死漂移与 `EEpath` + T155/T156/T190 的 (5.35)/(5.36)，写出保留指示函数的一步界，喂给 `flowEq548_of_near_far`。**验收**：`Step45.FlowEq548` 的生产者假设表里无 `hfar`；可满足性见证 | `Hierarchy/Step2MomentStep.lean`（续） | Claude Code | **完成**（`Step2MomentStep.lean` 新增 §11，全量绿、审计 10411）：`flowEq548_of_near_farInputs` 的**假设表里没有 `hfar`**，取而代之的 `FarInputs` **正是近场那一半本来就要的四条**——但 **(5.48) 仍是化归不是定理**，已写进文件头。两条新数学：**支撑估计**（住在对角带上的张量做不出远场，是论文那句「exponentially small」的定量版）与 **(7.2) 的锐化远场**（`ℓ*_v` 以外根本没有膨胀因子——**这才是远场为 `O(1)` 的真正原因**）。⭐ **指示函数的代价在 `R` 上是零**：(7.2) 已把 `R²` 从其余各项剥掉，唯一剥不掉的近场 `q` 只能靠支撑估计杀；`R²` 只落在 `FarResidue` 的自由大参数上，**不进 `phi_arith'` 的预算，T132c 的 `β* = 4` 零余量原封不动**。可满足性见证同时说明**真正的内容是 `cFarStep ≺ 1` 而非可实现性**。按 D11 未动 `Step2.lean` |
| T199 | **Theorem 2.2 的概率一半 (ii)：能量网 + 到随机特征值 `λ_k(ω)` 的 Lipschitz**（T153/T194 的后续；**低优先级车道，排在 T194 之后**）：T153 第 0 步已定 (i) → (ii) 的顺序，(ii) 的输入恰是 (i) 的输出（能量一致的 `Thm221`）。本单：(1) 把能量放进 `StochDom` 的指标集——用 T124 的网引擎（`TimeIcc s t N` 就是 `Set.Icc`，取 `s ≡ −2+κ`、`t ≡ 2−κ` 即能量区间），网点 `E_j(N)` 是 `N` 依赖的能量；(2) 网点之间用 `G` 对 `E` 的确定性 Lipschitz（`‖∂_E G‖ ≤ η^{−2}`）；(3) 在随机谱参数 `z = λ_k(ω) + iη` 处取局部律，推出 (2.10)：`max_k ‖ψ_k‖²_∞ · 1(λ_k ∈ [−2+κ, 2−κ]) ≤ N^{−1+τ}` w.h.p.（**措辞按原文，带体内指示函数**）。T153 的探针已编译「网」与「到随机 `λ_k` 的 Lipschitz 一步」，不需要概率连续模。**验收**：Theorem 2.2 在 Lean 里是无条件定理（只依赖 `Thm221` 与模型假设 (2.2)）；可满足性见证 | `Flow/EnergyUniform.lean`（续）+ `Delocalization.lean` | Claude Code | **完成——Theorem 2.2 落地**（`Flow/EnergyUniform.lean` +13、`Delocalization.lean` +4，全量绿、审计 10744）：能量网 + `|Im G_xx(E+iη) − Im G_xx(E′+iη)| ≤ |E−E′|η⁻²`（`im_green_lipschitz_energy`，只用谱分解），(2.10) 逐字、**指示函数写在体内**。⚠ **更正工单**：Theorem 2.2 **不能**放 `Delocalization.lean`——`Loop/GLoop.lean:7` import 了它，`Delocalization` 在 `Flow/` **上游**，import `Flow/EnergyUniform` 成环；概率版放 `Flow/EnergyUniform.lean`。假设表：`Band`（含 (2.2)）、`Sample`、`Transfer`（(2.39)）、`κ/τ/D > 0`、`Thm221N′`——**没有别的**（不需 `TransferLoop1`，不需 `κ ≤ 2`），量词次序 = 论文 `∀ κ τ D, ∀ᶠ N in atTop`。见证两条：网的粗细三条联立**都是定理不是假设**（工单担心的风险结构上不存在）；`1×1` 零矩阵处指示函数**会亮且界会失败**，说明结论事件既不恒真也不恒假。⚠ **更正工单 ⑦**：T204 交的是 `Thm221NoEL`/`BoundsCore`（无 `Bounds″`），要改的只有 `EnergyUniform.lean` 里三处，`Delocalization.lean` 的四条 Lipschitz 不受影响。⚠ 无主：`StochDom.of_forall_seq` 与 `Gauss.stochDom_reindex_of_forall_seq` 同一论证、`Gauss/` 在下游不能复用，按 CLAUDE.md 该下沉 `Defs/StochDom.lean`（纯机械）。paper-deltas T199a/T199b/T199c |
| T200 | **最终 Lean 报告的骨架 `docs/REPORT.md`（活文档，低优先级）**：现在就起草、随进度更新，避免最后一天赶工。内容：(1) **主定理清单**（Theorems 2.2–2.5、2.21、Lemmas 2.18–2.20）各自的 Lean 名与**完整假设表**；(2) **外部输入声明**（Jun 永久规则）：「全项目唯一的外部输入是 Theorem 2.6 Step 1 所用的 [51]（Landon–Sosoe–Yau）Theorem 2.2 的复 Hermitian 形式；[51] 正文陈述 β = 1，此处用其摘要所声称的 β = 2 版本；其余全部是独立完整的 Lean」——Theorem 2.6 未完成前写「待定」；(3) `#print axioms` 的汇总（只有三条标准公理）；(4) 建模选择：`H_u = √u·X`（一时刻律对齐布朗模型，Jun 选 (a)）、矩路线替代 Itô/BDG、Lemma 3.2 的组合模型；(5) **论文改动清单**（第 6–15 条，引项目文档）与 paper-deltas 的分类摘要；(6) 今天记录的**可满足性/fiat 教训**作为方法学附录。**不改 Lean**；数字从编译结果取，不手填 | `docs/REPORT.md`（新建） | Claude Code | **完成**（新建 `docs/REPORT.md`，537 行，活文档）：九节——主定理清单（Lean 名 + 完整假设表 + ①无条件/②化归/③空着）、六步链现状、外部输入声明、公理审计、**无生产者的具名假设（点名到字段级）**、空真与 fiat 两张风险清单、paper-deltas 索引、探针清单、待定夺 R1–R5（已转进 STATUS）。**每条都是编译探针打印出来的**，没有从 STATUS/TASKS 的叙述里抄。⚠ 方法学发现：按结论头常量找生产者对 **`def` 形状**的假设有**假阴性**（五条 `*Flow` 被误报），`def` 一律要用**裸 `:=` 探针**核。⚠ 快照 `HEAD = 2bde09d` 早于 T202/T203/T204，文件头已由协调者补记（`Dims` 的循环已解除等） |
| T201 | **⭐⭐ Lemma 5.14 的矩路线改走 `Q_u` + (7.16)，去掉 (7.1) 的 `(η_s/η_t)` 前因子**（T195 余项；**否则 Step 3 空真**）：T195 已编译证明：`hkerC` 的左端 `‖ξ‖ = 1` 时恒等于 `η_u/η_w`，所以 `Ck^{n+2} = (η_s/η_t)^{n+2}`——**正是 Lemma 7.1**；在论文自己的网格 `1 − s_k = W^{−kτ′}` 上 `(t−s)/(1−t) = W^{τ′} − 1`，**常数 `Ck` 不存在**（`no_const_Ck`）；吸收成 `C·R^k` 也不行（`(As,R,A) = (256,2,256)` 反例，且 `R` 幂乘在 `Λ^{1/2}` 上、`Ψ(n,k)` 的地板 `A_s^{1/2}` 与 `k` 无关）。论文 (5.92) 的「no prefactor depending on `(η_s/η_t)`」正是「每一项先经 `Q_u` 投影再用 **(7.16)**（前因子 `r^n` 与 `A^{−n}` 归一化相消）」。本单：(1) 把 T146/T181/T192 的矩路线里用 `edgeKer` 裸行和（(7.1) 档）的地方，逐处换成 `Q_u` 投影后的 (7.16) 档——**仓库三档齐备**（(7.1) 付 `ρ^n`、(7.14) 付 `R·r^n`、(7.16) 付 `r^n`；旧路线的 `norm_Uker_sumZero_scale_le`/`norm_Uker_fastDecay_le_sumZero`，T161 已放宽到 `0 ≤ t`）；(2) 需要的 sum-zero/快衰减性质：漂移 `F` 与 `E⊗E` 都已钉死（T58/T163/T167），逐项证它们经 `Q_u` 后满足 (7.16) 的前提（论文 §5.5 pp.67–69 逐项对照）；(3) **给 `hkerC_flow`/`hker2C_flow` 加 `@[deprecated]`**（T184 的编译器级护栏：它们是真定理，但 `hwin` 槽在 Theorem 2.21 的窗口上不可满足）。**验收**：`lemma514_forall_of_hHol_flow` 的探针在**论文网格窗口**上给出可满足性见证（不带短窗口假设）；公理干净 | `Gauss/Lemma514Moment.lean` + `Gauss/Lemma514Holder.lean`（续）或新文件 | Claude Code | **(7.16) 矩形式落地；但工单那一步在原地做不到**（新建 `Gauss/Lemma514Q716.lean`，917 行、31 条，全量绿、审计 10744）：⚠⚠ **更正工单本身**——`hrhs_of_moment_inputs` 里 `U` 下面的 `lkT`/`H.F`/`eeFun` **本身不是 sum-zero 的**，(7.16) 对它们不适用；`Q_u` 投影过的版本是**另一条陈述**，就是 `Hyp.momentDuhamelQ`。**所以带撇的 `hrhs_of_moment_inputs` 做不出来**，正确路线是矩路线改以 `momentDuhamelQ` 为接口 → **D14 待裁定**。落地：**(7.1) 档的否定结论入库**（T195 的 7 条探针 T193 查出从未入库，现补：`one_add_norm_edge_eq` 逐字 Lemma 7.1、`gridS_window_len` 是**等式**、`no_const_hkerC_on_gridS`/`no_const_hker2C_on_gridS` 的假设是槽的**逐字原形**）、真 Minkowski `momNorm_le_affine`（T146 那条**是 Jensen**，主项随机+误差确定时不够）、(7.16) 矩形式、**`momentDuhamelQ` 五项的界**（sum-zero 前提全是定理）、好事件拆分。见证 `gridS_Q716_witness` 在**论文自己的 p.24 网格**上、**不带短窗口假设**，证 `Q_u` 后对象非零且常数与 `N` 无关；与 T195 的反证互为对照一并入库。已接线：`Lemma514Holder` 的 `one_add_norm_mul_le`/`hkerC_flow`/`hker2C_flow` 加 `@[deprecated]`，:1150 那段**事实错误的 docstring** 已改写。paper-deltas T201a/T201b |
| T202 | **⭐⭐ `Gauss.Dims` 的居民（全高斯层的可满足性第 0 条）**（滞留审计 B.2；`Gauss/Model.lean:110–113` 自己写着没做）：`Gauss.band d`、`Gauss.sample d` 全部量化在 `d : Dims` 上——**若 `Dims` 无居民，整条矩路线都是空真的**。给出 `Dims.example : Dims`：`L N = 3`、`W N = max 1 (N / 3)`、`c = 1/4`，证 `W_pos`、`three_le_L`、`dim`（`∀ᶠ N, W L ≤ N ≤ 2WL`）、`bandwidth`（`∀ᶠ N, N^{3/4} ≤ W N`）。再给一个 `example : Nonempty Dims`。**顺手**：(a) 检查 `RBM.Band` 与 `Gauss.OpNormBound`（`‖X‖ ≺ 1`，Model.lean 说「未证、作假设」——核对 T109/T129 是否已卸，已卸则在文件头更正，未卸则报告）；(b) 给 `condExpDiag_stochDom_of_pieces`（`Gauss/IBP.lean:1214`，`hminor` 在对角为假，T112）加 `@[deprecated]`。**验收**：`#check (Dims.example : Dims)` 编译；文件头的「not done」段更正 | `Gauss/Model.lean`（追加）或 `Gauss/DimsExample.lean` | Claude Code | **完成**（新建 `Gauss/DimsExample.lean`，全量绿、审计 10493）：**`Gauss.Dims` 有居民了**——`Dims.example`（工单建议值 `L ≡ 3` **原样可行**，工单 ⚠ 担心的联立不可满足不成立：`N^{3/4} ≤ ⌊N/3⌋` 等价于 `N³ ≤ ⌊N/3⌋⁴`，`N ≥ 100` 起成立）与**非退化见证 `Dims.exampleGrow`**（`L ≈ N^{1/4}`、`W ≈ N^{3/4}`，两者都 `→ ∞`）。**四个字段一个没削弱**。往下挪一层也查了：`nonempty_Idx`（指标型非空）、**`exists_Sblk_pos`（`S` 不恒为零——挡 `ω = 0` 型事故）**、`band`/`sample` 是定义故自动有居民；`GaussIBP`/`TraceMomentBound` 确认是对每个 `d` 的定理。顺手 (a)：**`OpNormBound` 已卸**（`opNormBound_gauss` 无条件），`Model.lean` 文件头「not done」段已按事实改写（只改注释）；(b) `condExpDiag_stochDom_of_pieces` 加了 `@[deprecated]`。⚠ 查出 **`RBM.Bounds` 在 `s > 0` 处仍无居民**（只有 `Bounds_zero`）→ 归 T204/T205 |
| T203 | **`hKb`：(2.59) 在所有环长上的装配**（滞留审计 B.3；T192 标「接缝没缝」）：`Flow/Iteration.lean:598 norm_Kval_le` 是对一般 `n` 的 `K` 界，看上去只差一层接线。把它接进 `Lemma514Holder`/`Lemma514Moment` 的 `hKb` 槽；若形状不对（归一化、`η` 的幂、`σ` 的范围），写清差在哪、补一条桥引理。**先 grep** `norm_Kval_le` 的全部变体。**验收**：T181/T192 的端到端探针假设表里无 `hKb` | `Gauss/Lemma514Holder.lean`（续） | Claude Code | **完成**（`Gauss/Lemma514Holder.lean` 1071 → 1321 行，全量绿）：**`hKb` 从假设变成定理**（`hKb_flow`），端到端探针 `lemma514_forall_of_hHol_flow` 与新的 `flow_sharpLmK_of_hHol_flow` 假设表里**无 `hKb`**（后者连 `hHol` 也无）。工单猜测成立——`norm_Kval_le` 只差接线、**无数学缺口**，但归一化有**真差额**：压成 `N^c` 要付 `(Wℓη)^{−1} → η^{−1} → η_{t_N}^{−1}`，**指数 `c → c·m + 1`**；因 `hreg`/`hXΞ` 对 `c` 单调变弱，探针内部抬到 `c(n+2)+1`，**对外签名不变**。每长度各有 `C_n`，故先 `exists_norm_Kval_le_upto` 取 max。`lemma514_of_hHol_flow`/`_forall_` 的 `hKb` 参数已删（全仓无外部消费者，未留带撇版）。**全程未用短窗口条件**，与 T201 无冲突。见证 `exists_hHol_flow_inputs` 取**临界标度** `η_{t_N} = N^{−1}·Im m`（窗口不塌缩）。余 `hrhs`（`hnum` + `edgeKer` 行和）→ T201；`hkerC_flow`/`hker2C_flow` 的 `@[deprecated]` 等 T201 文案 |
| T204 | **第一遍：不含 (2.71) 的 Theorem 2.21 变体（D12 → (a)）**：论文 p.25 在 Step 6 之后原话「(2.71) will not be needed for Steps 1–5, i.e., Theorem 2.21 holds if (2.71) were removed from both the assumption and statement」。本单：(1) 带撇的 `BoundsCore″`/`Bounds″`/`Thm221″`：**假设与结论都去掉 (2.71)**（`expect` 字段）；(2) Steps 1–5 的现有生产者串成 `Thm221″.step`（不需要 Step 6）；(3) Lemmas 2.18–2.20 的迭代对 `Bounds″` 重跑（证明脚本应几乎照抄）；(4) 下游：Theorem 2.2、Theorem 2.3、**Theorem 2.4 的 (2.6)(2.7)** 改吃 `Bounds″`——**(2.8)(2.9) 与 Theorem 2.5 要 (2.71)，留给 T205**，不许为了过编译把它们挂在空假设上。**（D13 裁定后）(2.72) 一侧用 `Cond272Reg`**（(2.72) 逐字 + `t ≤ 1 − N^{−1+τ}`，T186 的 `Thm221Bare.lean`），与补正后的论文 Theorem 2.21 逐字一致；与 T194（能量一致）组合时用带撇版，不改冻结签名。**验收**：探针从 `Bounds″ X E s` 经 `Thm221″` 迭代到 `Bounds″ X E t`，假设里无 `expect`/(2.71)、无 Step 6 的任何字段；公理干净；可满足性见证（T202 的 `Dims` 居民） | `Flow/Thm221NoEL.lean`（新建） | Claude Code | **完成**（新建 `Flow/Thm221NoEL.lean`，747 行、30 条，全量绿、审计 10542）：**没有造 `BoundsCore″`**——`Flow/Hypotheses.lean` 的 `BoundsCore` 就是「(2.71) 删掉」的那个包，`BoundsCore_of_Steps` 也已是「不用 Step 6」的那一半，缺的只是定理和迭代。落地 `Thm221NoEL`（收 `Cond272Reg`）/`Thm221NoEL'`（收 `Cond272'`）、Lemmas 2.18–2.20 去掉 (2.62) 的重跑、(2.61)、Thm 2.3 全条、**Thm 2.4 的 (2.6)(2.7)**；结论**一字未改**（8 条 `rfl` 探针对照 `Bounds` 版），(2.8)(2.9) 与 Thm 2.5 **没有挂到空假设上**。见证 `boundsCore_gauss_witness` 用 T202 的 `exampleGrow`，证右端真是 `≺ N^{−n/2}` 而非 `≺ 1`；`cond272Reg_grid` 把「论文网格 × D13 窗口」的联立编译了（**T195 挂掉的正是这类**）。⚠ **更正工单**：树里 `Cond272Reg` 的第二项是**尺度下界**不是时间窗，已按实际定义收口并补 `eventually_rpow_le_scale`。⚠ **更正 T176**：Steps 1–5 这半边剩 **6 条**具名假设。⚠ **Theorem 2.2 全仓没有组装**，下游无事可改吃 `Bounds″`（归 T199）。⚠ **`Thm221NoEL`（`Cond272Reg` 形）产不出来**，只产得出 `Thm221NoEL'`——Step 2–5 逐字吃 `Cond272'`，桥在 `(a,b)=(1,30)` 处零增益（T186 的缺口，**无主**，见 STATUS）。paper-deltas T204a/T204b |
| T205 | **第二遍：(2.71) 的归纳 + Step 6 样本侧收口**（D12 更正后的方案；**T204 之后，不推迟到 Theorem 2.6**）：(2.71) 经 (2.62) 给 **Theorem 2.4 的 (2.8)(2.9)**，而 **Theorem 2.5 (QUE) 直接用 (2.8)(2.9)**（`Flow/Consequences.lean` 的 `expect_loop2_of_bounds` 吃 `hB.expect`）。本单在 T204 的结论之上**单独**对 (2.71) 做一次迭代：每步用第一遍的 (2.68)–(2.70) + 上一步的 (2.71) 经 Step 6 得到下一步的 (2.71)。Step 6 的漂移侧已全部落地（T182/T189：`sharpExpect_step6_driftEG` 无 `hG`），**余样本侧（滞留审计 B.1，逐个点名）**：`FDInputs`/`QuadInputs`/`EGInputs`/`DriftInputs` 四个好集的生产者（原料：T126 的 `LKDecay`/`LDecay`、`Decay.lemma59`、Step 3 的计数）；`henv*`/`hEnvpoly`/`hmeas*`（包络、可测性）；`hcont`/`hintU*`/`hintL*`/`hintQ`/`hintG`（连续性、可积性）；`hEL`（`LoopC2.differentiableAt_integral_gloop_flow` 已在树里，只差接线）。**可拆成 2–3 张子单**，开工时先交一张字段清单。**验收**：`Bounds X E t`（含 `expect`）由 `Bounds″` + 本单产出；Theorem 2.4 的 (2.8)(2.9) 与 Theorem 2.5 的探针无 (2.71) 假设 | `Gauss/Step6Sample.lean`（新建）+ `Flow/Thm221NoEL.lean`（续） | Claude Code | **第 0 步完成；(2.71) 的步进定理没写，因为写出来就是空真**（新建 `Gauss/Step6Sample.lean`，465 行、23 条，全量绿、审计 11100）：⚠⚠ **空真第九例，而且是量词写错**——`sharpExpect_step6_driftEG` 的 `henvQ`/`henvG`/`henvLK`/`hmeasQ/G/LK`/`hintL1` 把时间 `v` 量化在**整个 `ℝ`** 而不是窗口。**`not_exists_env_eG` 已编译**：`E=0`、`ω=0`、`v=1−w` 处 (5.131) 的被积量有**闭式** `2(w⁻¹−1)w⁻³/W`，`w ↓ 0` 无界，双和经 `sum_SB_col` 坍缩**无抵消**，故**不存在任何 `Env`**；Thm 2.4/2.5 量化在所有 `|E| ≤ 2−κ` 上，`E=0` 处不可满足即整条 (2.71) 归纳被封死。**是量词错不是数学缺口**，三条证据：两文件内部只在 `TimeIcc` 上用它；T150 的 `int1_gauss` 早就是窗口版、**形状对不上**；两条 `sharpExpect_step6_*` 全仓**零消费者**故没人撞上。交付：总装桥 `bounds_of_boundsCore_of_sharpExpect`（配 `rfl` 对照 `Bounds_of_Steps`）+ `hEL_gauss`（**零新假设**）+ `hintL2_gauss`；见证 `bounds_witness_zero` 是**退化见证**（文件里明写），非退化见证正是被封死的那一步。**没有把 (2.8)(2.9) 挂到空假设上**。第 0 步字段清单见 STATUS。⚠ **无主**：①**包络量词修复（零数学的一行改动）**，修完 `hintL1`/`hmeas*`/`henv*` 立刻有生产者；②四个好集的 `HighProb` 生产者；③`hKd` 的量化形；④`hcont`/`hintQ`/`hintG`/`hintU*`/`hlk`。本单**不产生 paper-delta**（是 Lean 内部量词错，不是与论文的偏差） |
| T206 | **`MomentDuhamel.Hyp` 两字段的最后三步**（T196 余项）：T196 已让 `TestFunT₁` 七个字段全部有实例（`u` 同时出现在谱参数、传播子运行时间、`K_u` 三处，`bdd₀/₁/₂` 做成窗口一致版；可满足性见证用的是非 Hermitian 奇异 `M` 处界取等），生成元恒等式对 `Ψ` 无假设。余三步：(1) **`φ′` 与 `Hyp.drift` 的对应**——生成元给出的 `φ′` 要逐字识别成 `(∂_u + 𝓛)(L−K) = Θ∘(L−K) + F` 里的 `F`（钉死的 `driftF`，T58）；(2) **边界可积性条件**（窗口端点处的 `ψ`、`φ′` 可积与 `ψ` 的一致上界；只在开区间要导数）；(3) **`momentObsT` 与 `Uker ∘ lkT` 的逐字桥**（`rfl` 或一条等式引理）。交完整实例 `momentDuhamelHyp_gauss`。**先读 T196 的 STATUS 节与 `MomentDuhamelBddT.lean` 文件头**。**验收**：完整 `Hyp` 实例编译，`example` 证明无自由数据；可满足性见证 | `Gauss/MomentDuhamelBddT.lean`（续）或新文件 | Claude Code | **第 (1)(3) 步完成，实例仍不存在**（新建 `Gauss/MomentDuhamelHypGauss.lean`，741 行、19 条，全量绿、审计 10661）：`hasDerivAt_ukerObsT_drift` 把 `(∂_u + 𝓛)(U∘(L−K)) = U∘F` 证了，**`F` 逐字是钉死的 `DriftDef.driftF`**，`K`/`∂_uK` 也被钉死（`Kprim = primRhs`），**两侧无可选数据**；`momentObsT ↔ Uker∘lkT` 是**等式定理**。⚠ **一处防 fiat 的数学要点**：`genMomentPt_le` 把 `Re(F̄𝓛F)` 放成 `‖F‖‖𝓛F‖` **对矩路线早了一步**——`Re(F̄∂_uF)` 必须与它**先相加再取模**，那正是 `Θ` 与 `genS` 相消处（分开放缩会留下不小的 `U∘Θ(L−K)`），故新证 `genMomentPt_le_re`。见证取全开区间 `u,v < 1`；`hasDerivAt_ukerObsT_drift_at_zero` 做了 `ω = 0` 同形检查。⚠⚠ **更正工单：它少点名了两项，`momentDuhamelHyp_gauss` 仍不存在**——(2) 边界可积性八件里只给了一件（同线续做）；**(新) 二次变差还不是接口的 `E⊗E`**，缺 (5.22) 的 **`U` 共轭双线性版**（`EEBridge.lean` 里一个 `Uker` 都没有，**无主**）；**(新) `Q_t` 路线 `MomentIneqQ` 完全没碰**，仓库无 `∂_u Q_u`（**无主**，与 T201 的 `Q_u` 同一个 `Q`，应合看）。见 STATUS |
| T207 | **`hnear`：Lean 的 (5.47) 要达到论文的 `(η_s/η_t)²`**（T197 余项；T198 的规格只点名了 `hfar`）：T197 的截断版 Step 2 需要 `hnear` 的形状 `(η_s/η_u)²`，而仓库里的 (5.47) 只给到 `(η_s/η_u)⁴`。**论文 (5.47) 原文是 `J*_{τ,D} ≺ (η_s/η_t)²`**（由 (5.45)(5.46) 的 `(η_s/η_t)²` 鞅界 + 初值 `J_{s,D} ≺ 1`）。**第 0 步**：查清 Lean 在哪一步多丢了两次幂——候选：近场 `r⁵` 的「先乘后取 sup」（T174 建议②、T132c 的 `integral_nearInt_le` 已实现，是否接上了）、(5.36) 补的 `(ℓ_u/ℓ_s)^{3/2}`（T174：在 (5.44) 的积分里免费）、或 `(η_s/η_t)` 与 `(η_s/η_u)` 的混用。然后补齐到 `²`。**若确实只能到 `⁴`**：核对 `hnear` 的消费者能否接受 `⁴`（按 T174 的指数表），能则改消费者，不能则停下报告 | `Hierarchy/Step2MomentStep.lean`（续） | Claude Code | **完成，`²` 可达、不需弱化结论**（新建 `Hierarchy/Step2Near47.lean`，939 行、38 条，全量绿、审计 10635）：**第 0 步答案——两次幂不是丢了，是从来没取出来过**。`⁴` 是 bootstrap 的归一化（`Step2Moment.lean:150` 的 `jSnorm := jS / ratR^4`），论文 (5.47) 是**同一条一步界的第二次读法**（p.58），仓库从没做这第二次读。记账层唯一真是 `R⁴` 的是 `phi_arith'` 的 `t4`（把 (5.41) drift 近场的 `(η_u/η_t)²` 与 `(ℓ_u/ℓ_s)³` **分开各取 sup**）。⚠ **更正工单候选 ①**：`integral_nearInt_le` 积的是 **(5.44) 二次变差**那条（预算本来就对），**(5.41) 的 drift 被积函数从来没被积过**；且 `phi_arith'` 与它**全仓无消费者**，记账层与 `CutHyp.moment` 是断开的。候选 ②③ 也都不是。补法：drift 近场**联合积分**，机制与 (5.44) **相反**（被积函数单减，sup×长度只到 `R^{5/2}`，必须真做原函数）。**核心：`phi_arith_second_pass` 证出只改 `t4`、`J*` 仍停在 `x⁸R⁴` 先验水平，输出已是 `R²`——不需要第二次 bootstrap**；代价只是远场边条件 `β* = 5.5/4.5 → 9.5/6.5`，由**同一个 `4δ ≤ 2c`** 给出，**指数预算零成本**，近场那行反从 `β* = 4`（零余量）降到 `2`。见证 `phi_arith_sharp_flow` 把 `qI` 取成**真实积分**（不是假设 `R²` 而是算出 `R²`）；`crude_exceeds_budget` 把「分开取 sup 超预算」编译成定理。`flowEq548_of_near_far` 一字不用改。余 `MomentHypCutSharp.cut` 与 `MomentHypCut.cut` **同级**（证了不比钝版要求更多）。⚠ **无主**：`CutHyp` 的 `Θ : ℕ → ℝ` 要推广成 `ℕ → ℝ → ℝ` 才表达得出真正的第二遍接口（见 STATUS）。paper-deltas T207a/T207b |
| T208 | **(5.48) 从化归变成定理：`FarInputs`/近场四个一步输入由钉死的漂移产出，并证 `cFarStep ≺ 1`**（T198 余项；**fiat 风险**）：T198 让 `flowEq548_of_near_farInputs` 不再收 `hfar`，但换上的 `FarInputs`（与近场同样的四个一步输入）的可满足性见证是**把漂移取成 0** 得到的——这正是 fiat 形状：若漂移是 `FarInputs` 里的自由数据，(5.48) 就是空洞的。T198 自己也写明「真正的内容是 `cFarStep ≺ 1`，见证没有提供」。本单：(1) **核查 `FarInputs` 与近场输入里的漂移是不是自由字段**——若是，改成吃钉死的 `driftF`（T58）/`EEpath`（T167）的带撇版，**不许留可自由赋值的张量**；(2) 由 (5.34)（二次项）、(5.35)（`eGpm`，T163）、(5.36)（`EEpath`，T167/T190）与 T198 新证的支撑估计 + 锐化远场 (7.2) 产出四个一步输入；(3) 证 `cFarStep ≺ 1`。**验收**：`Step45.FlowEq548` 的生产者探针假设表里无 `FarInputs`/近场输入的自由形式；fiat 审计写进 STATUS（仿 T163：左端每个量 unfold 到 `H_u` 的 Green 函数）；可满足性见证用**非零**漂移 | `Hierarchy/Step2MomentStep.lean`（续） | Claude Code | **完成，但结论是修正 T198**（新建 `Hierarchy/Step2FarInputs.lean`，917 行；单文件 exit=0、`lake build RBM1D` exit=0、20 条声明 `#print axioms` 干净；**`Step2MomentStep.lean` 一字未动**）：① **fiat 核查坐实**：`FarInputs` 的 `F`/`Fn`/`Mrt` 三个都是自由张量。`FarInputs'` **无任何存在量词**——漂移钉成 `DriftDef.driftF`（`= eGpm + primBil(L−K,L−K)`，且 `= Hyp.Fpath`），近场部分是它在 `‖b₁−b₂‖ ≤ ℓ*_u` 上的限制，鞅是 Duhamel **亏量的定义**。反 fiat 证书 `farDrift_eq_zero_of_farInputs'_zero`：`M_n = M_f = 0` 迫使模型漂移恒为 0（T198 的包对任意样本都能取 0）。② ⚠ **`cFarStep ≺ 1` 按 T198 的形状为假**——`M_f` 是 (5.35) 前因子 `η_u^{-1}(…)` 的 `sup_u`，`η_s^{-1}` 最大到 `N^{1−τ}`；`step_bound_far` 把 `|v−s| ≤ 1` 扔掉的那一步正是丢失点（`η_s^{-1}(1−s) = (Im m)^{-1}`）。修正形 **`cFarStep' = Ξ(M_i+M_f(1−s))+M_m+1`，`detDom_cFarStep'` 证出 `≺ 1`**，其中 **`Ξ ≺ 1` 是定理**（`eventually_xiK_le`，只用 `WL ≤ N` 与 (2.2)）。临界标度上两条对照都编译：`cFarStep'_detDom_critical` 成立 / `cFarStep_not_detDom` 为假；`s = 0` 时两者逐字相等。③ `flowEq548_of_farInputs'` / `flowEq548_of_farInputs'_detDom` 产出 `Step45.FlowEq548`，假设表里**无自由张量、无 `hpoly`**。④ `farInputs'_of_eG_of_quad` 把两条漂移输入化归到 (5.35)(`eGpm`) + (5.34)(`primBil`) 逐项。**未做**：`M_m ≺ 1`（(5.45) 远场鞅界，BDG，随机层，**无主**）；把 `eGpm_le_reduced` 的右端整理成 `M_gf·T` 并核 `M_gf(1−s) ≺ 1` 的显式指数账（建议新单）；带 `L¹` 权的积分形一步界（可彻底去掉 `1−s`）。记 paper-deltas **T208a/T208b** |
| T209 | **⭐⭐ Steps 2–5 改吃 `Cond272Reg`，产出 `Cond272Reg` 形的 `Thm221NoEL`（D13 收口）**（T204 无主项 1；T186 的缺口）：D13 定了 Lean 最终 `Thm221` 收 `Cond272Reg`，但 Step 2–5 **逐字**吃 `hregS = Cond272'`——三个消费者 `Gauss/MomentDuhamelCut.step2_cut`、`Hierarchy/Step2PP.flow_sharpLoop_glue_flowAs'`、`flow_steps45_glue_flowAs'`；`rpow_mul_rpow_le_of_pow_thirty` 在 `(a,b)=(1,30)` 处零增益，所以桥 `Cond272Reg → Cond272'` 不存在。**做法**：三个消费者各加**带撇版**（不改冻结签名），把 `N^c R^{30} ≤ A_u` 换成它真正用到的那几条——`Cond272Reg.hA_phi`（`x^{17}R^{10} ≤ A`，(5.40)）与 `hA_betaStar`（`x^{32}R^{11} ≤ A²`，(5.41) 远场）；T186 的 scratchpad 探针 `side_conditions_of_reg` 已证三条侧条件可从 `Cond272Reg` 重建，是模板。**第 0 步**：把 T207 的 `phi_arith_second_pass`（远场 `β*` 9.5/6.5、近场 2）逐条放进判据 `e/c + b/30 ≤ a`，确认 `δ ≤ c/4` 仍够；不够就停下报 Cowork，**不许**回退到 `Cond272'`。然后在 `Flow/Thm221NoEL.lean` 组装 `Thm221NoEL`（`Cond272Reg` 形）。**验收**：`Thm221NoEL` 的假设表里没有 `Cond272'`/`hregS`；可满足性见证走 `Band.cond272Reg_grid`（网格每一步 + D13 窗口联立）；`#print axioms` 干净 | `Gauss/MomentDuhamelCut.lean`、`Hierarchy/Step2PP.lean`、`Hierarchy/StepGlue.lean`（加撇版）+ `Flow/Thm221NoEL.lean`（续） | Claude Code | **完成——`Thm221NoEL`（不带撇、收 `Cond272Reg`）产出来了，D13 收口**（15 条 + 1 条 `rfl` 探针，追加进 `StepGlue`/`Step2PP`/`MomentDuhamelCut`/`Thm221NoEL`，旧签名一字未动，四文件各 exit=0）：生产者 `thm221NoEL_of_inputs`，`#check` 打印的类型里 `Cond272'` **出现 0 次**、`Cond272Reg` 7 次，具名假设与 T204 完全相同。⚠⚠ **更正工单：桥根本不需要，`hA_phi`/`hA_betaStar` 一次也没用到**——那两条是**矩路线内部**的侧条件（`MomentHypCut` 里面的事），Steps 1–5 的装配把它当黑箱，**所以 T209 不消耗 `δ` 预算**。实际做法是把 `hregS` 的真实用途逐个拆开，**一处都不需要增益**：Step 1 本来就吃 `Cond272Reg`；(2.76) 只经 `cond272_of_strict` 取 `Cond272`；弱律 (2.74) 本来就吃 `Cond272Reg`；(2.75) 只要 `(η_s/η_u)^4 ≤ A_u` 与 `N^c ≤ A_u`（**指数是 4 不是 30**）；Steps 3–5 的胶水只要 `Cond272`，唯一真消费者 `harith_flowAs` 要的两条都是 `Cond272Reg` 的分量。⚠ **这更正了 paper-deltas #125 的「六步全链要 `N^c` 增益」半句**，记 `T209a`。见证 `cond272Reg_grid_step_domain` 在**论文网格**上把一个 step 的四条域条件同时证出，`τ′,c,n₀` 先于 `E,t` 选定、`gridT n₀ = t`（窗口不塌缩）；三档 `Cond272'/Reg/裸` 的严格强弱都有定理，没有一档塌成同一个。余：`Step2.localLaw`/`Step2Moment.aprioriDecay_of_jS` 的原版该改成一行推论（纯机械，**无主**）；`EnergyUniform` 的 `Cond272N` 无 `Reg` 形（归 T199 续单，**无主**） |
| T210 | **`CutHyp.moment` 的生产者 + `CutHyp.Θ` 推广成 `ℕ → ℝ → ℝ`**（T207 无主项；T197/T198 余项；**Step 2 只剩这一条具名假设**）：(1) `MomentDuhamelCut.CutHyp` 的 `Θ : ℕ → ℝ` 表达不出第二遍接口——钝版水平换算到 `jSnorm2` 单位是 `N^{2δ}(η_s/η_u)²`，带 `u`。推广成 `Θ : ℕ → ℝ → ℝ`（新结构带撇，旧的由新的特化推出），并用它**删掉** T207 §3 那条假设（数学上已证完）。(2) 从 `MomentDuhamel.Hyp`（T206/T212–T214 那条线）+ 截断 `χ`（`cutChi`，`‖χ′‖ ≤ 15/8`）产出 `CutHyp.moment`，从而 `MomentHypCut.cut`、`MomentHypCutSharp.cut`（T207 已证二者同级）。(3) **记账层接线**：STATUS 记 `phi_arith'` 与 `integral_nearInt_le` **全仓无消费者**、记账层与 `CutHyp.moment` 断开——把它们接到 (2) 的产出上；T207 在 `Step2MomentStep.lean` 的文档指针（T208 已落地后）一并补。**依赖**：`momentDuhamelHyp_gauss` 未存在前，(2) 先做成「由 `MomentDuhamel.Hyp` 推出」的化归定理，不许加新的自由字段。**验收**：`step2_cut` 的假设表里没有 `CutHyp.moment`（或它只经 `MomentDuhamel.Hyp` 出现）；`Θ` 推广后的可满足性见证在 `u ↑ 1` 上非退化；公理干净 | `Gauss/MomentDuhamelCut.lean`（续）+ `Hierarchy/Step2Near47.lean`、`Hierarchy/Step2MomentStep.lean`（文档指针） | Claude Code | **完成（障碍精确定位 + 化归编译）**（新建 `Gauss/CutHypTheta.lean`，1062 行、39 条，全量绿、审计 10990）：⭐ **第 0 步的核心发现——`CutHyp.moment` 是无条件的，而 Duhamel 只在「前缀事件」上成立**（截断 `χ(J_{ws}/θ)` 只约束**端点**，对中间时刻 `u ∈ [s,ws]` 的 loop hierarchy 毫无约束，而 (5.39)–(5.44) 每一项都要中间时刻的先验界），**所以该字段不能直接从 Duhamel 产出**。化归 `moment_of_conditional` 已编译（无条件 `moment` ⟸ 前缀事件上的**条件**矩界 + `HighProb` + 水平多项式有界；前缀外由截断包络 `2θ` 付账，`D` 在 `∀ p` 内选）。**第二遍这条前缀免费**（就是第一遍的结论，`prefix_of_stochDom`）；**第一遍这条前缀正是自举要证的东西**。⚠ 这是**结构性障碍的定位，不是不可证性证明**，勿当否定定理引用。⚠⚠ **更正工单：推广 `Θ` 并不能「彻底去掉」T207 §3 的假设，方向还相反**——`cutTrunc` 对水平**单增**（`cutTrunc_mono_level`，严格性 `sat_level_strict`），抬水平是**加强**。真实结果：`MomentHypCutSharp` 不再独立（由 `momentHypCutSharp_of_cut2` 导出），但 Step 2 仍是**两条**具名假设，二者之差恰是 `R^{−4p}` 即 (5.47) 的全部数学内容；买到的是 (i) 假设写在数学真正支持的水平上、(ii) 第二遍**不需要第二次 bootstrap 也不需要第二个初值条件**。见证 `satCutHyp'` 取临界标度、水平真带 `u`；⚠ `lev_ge` **必须限制在窗口**（`u > 1` 时按字面为假）。paper-delta T210a |
| T211 | **`Flow/Consequences.lean` 改吃 `BoundsCore`（机械）**（T204 无主项 2）：给下列定理各加 `*_of_boundsCore` 新名（**不改旧签名**；旧名由新名一行推出），证明脚本一字不动（T204 文件里已有逐字副本 + `rfl` 探针作模板）：`localLaw_of_bounds`、`loop1_of_bounds`、`partialTrace_of_bounds`、`trace_of_bounds`、`loop2_of_bounds`、`quantumDiffusion_pm/pp_of_bounds`、四条 `*_prob_of_bounds`、`localSemicircleLaw_of_Thm221` 整条；把 `quantumDiffusion_of_Thm221` 的前两个合取拆成独立定理。**不许动**（要 (2.71)，归 T205）：`expect_loop2_of_bounds`、`expect_quantumDiffusion_*`、`QDExpect.of_Thm221*`、`theorem2_5_of_Thm221*`。**验收**：新名的假设表里只有 `BoundsCore`；旧名 `rfl`/一行推出；全量绿 | `Flow/Consequences.lean` | Claude Code | **完成**（`Flow/Consequences.lean`，13 条新名 + 15 条 `rfl` 探针；单文件 exit=0）：⚠ **更正工单**——`Flow/Thm221NoEL.lean` 是 `Consequences.lean` 的**下游**不是上游，所以「改成一行推论指向 T204」不可行，七条核心定理放进 `namespace Core` 与 T204 的裸名并存（**唯一的重复劳动，只写一个文件消除不掉**，合并动作归 T209 之后的 `Thm221NoEL.lean` 持有者）。`Core` 七条证明脚本**一字不动**；新增四条 `*_prob_of_boundsCore`、**`localSemicircleLaw_of_boundsCore`（Theorem 2.3 整条）**、`quantumDiffusion_pm_pp_of_boundsCore`（前两个合取拆出）。**13 条旧名签名一字未改**，全部降为一行推论。越界检查：全仓 `grep "\.expect"` 只命中一处，沿链保持 `Bounds` 的是六条（含 (2.8)(2.9)），**另加两条反向 `rfl` 探针钉死它们仍吃 (2.71)**，没有挂空假设。paper-delta 不需新号（已由 #134 覆盖） |
| T212 | **`momentIneq_of_derivBound` 的五件边界可积性**（T206 第 (2) 步；T206 只给了八件里的逐点不等式与桥）：每个 `(p,N,σ,v,a)` 还缺——`ψ` 的窗口界、`u ↦ E|Ψ₁|^{2p}` 的 `ContinuousOn`、`φ′` 的区间可积、`u ↦ ‖U∘F_u‖_{2p}` 与 `u ↦ ‖(U⊗U)∘(E⊗E)‖_p` 的区间可积、乘积 `ψ·f` 的可积。机制：确定性包络 `‖G‖ ≤ (Im z_u)^{−1}` + 控制收敛，仿 `integrable_lkT_pow` 的定时版。**可满足性**：窗口取 T206 的全开区间 `0 ≤ u < 1`、`0 ≤ v < 1`，不许靠 `v` 远离 1 的短窗口常数（T195 事故）。若 T206 的 agent 仍在续做第 (2) 步，由它认领 | `Gauss/MomentDuhamelHypGauss.lean`（续） | Claude Code | **进行中**（Claude Code 子 agent，心跳 10:15 派出） |
| T213 | **二次变差的 `E⊗E` 形：(5.22) 的 `U` 共轭双线性版**（T206 查出，**无主**）：`MomentIneq` 右端要 `‖(U⊗U)∘(E⊗E)_{a,a}‖_p`（`Uker` 在 `SumZeroDyn.xi2` 上作用于 `eeFun`），仓库只有 `quadVarPairs_Uker`（`quadVar(Ψ₁) = ∑_{ij}‖(U∘E^{(M)}(i,j))_a‖²`）与**单条 loop** 的 `eeRaw_self_eq_quadVarPairs` + (5.22) `eeEdge_eq_sum_SB`。要证 `∑_{ij}(U∘E^{(M)}(i,j))_a·conj((U∘E^{(M)}(i,j))_{a′}) = ((U⊗U)∘eeArg)_{a,a′}`，其中 `E⊗E` 是**钉死的** `EEpath`/`eeFun`（定义，不是字段）。`Hierarchy/EEBridge.lean` 里目前一个 `RBM.Uker` 都没有。**验收**：`quadVar(Ψ₁)` 等于接口右端的等式定理；`ω = 0` 同形检查（T164 规则）；公理干净 | `Hierarchy/EEBridge.lean`（续）或 `Gauss/EEUker.lean`（新建） | Claude Code | **完成——⚠⚠ 查出 `SumZeroDyn.xi2` 按字面不是论文那个量**（新建 `Gauss/EEUker.lean`，744 行、44 条，全量绿）：**第 0 步答案是「对不上」**——论文 Lemma 5.5（p.55）写的是 `U_{u,t,σ} ⊗ U_{u,t,σ̄}`，"where σ̄ is the conjugate sign vector of σ"，(5.23) 的后半段全带杠；仓库的 `xi2 = Fin.append (xiOf σ) (xiOf σ)` **重复了未共轭的 ξ**。差的就是第二半那 `n+2` 个边参数上的**一次 `starRingEnd ℂ`**。**此前没人发现是因为 `‖ξ_i‖ = 1`**——所有经 `xi2` 的**估计**看不见这个差别（`norm_xi2bar` 证逐项模相同，故下游一字不用动），但**等式**对 `xi2` 为假（`xi2bar_ne_xi2` 给出 `E=1`、`σ≡+` 的反例）。交付 `sum_Uker_mul_conj_Uker`（核心代数等式）、`quadVarPairs_Uker_eq_norm_eeRawArg`（**等式**）、`quadVarPairs_Uker_le_norm_eeArg`（**(5.25)**）、Band 版逐字对上 `eeFun`。**数值自洽检查**：`L=3`、`ξ=i`、`t=0`，`a≠a'` 与 `a=a'` 两处两侧**各自独立**算出 `8/9−(4/3)i` 与 `26/9`（都非零、求值不用本文件任何定理）；**判别性 `sanity_rhs_xi2_wrong`** 证明用 `ξ` 在同一点给出**不同的数**。余：`hsplit`/`hdiff` 仍是假设（与 `DischargeBDG` 同一缺口，**无主**）；`xi2` 的定义修正涉及 **11 个文件、机械替换**（**无主**，见 STATUS）。paper-delta T213a |
| T214 | **`Q_t` 路线 `MomentIneqQ`：`∂_u Q_u` 与 (5.91) 的 `commS`、`varthetaDot` 两项**（T206 查出；**D14 之后是关键路径**：`momentDuhamelQ` 的生产者要它，T219 等它）：`MomentIneqQ` 的漂移恒等式要 `∂_u Q_u`，由此才生出 (5.91) 的 `SumZeroDyn.commS` 与 `varthetaDot`；仓库里没有对 `Qop` 求时间导数的任何东西。**与 T201 是同一个 `Q`**（Lemma 5.14 改走 `Q_u` + (7.16)）：开工前先读 T201 的 `Gauss/Lemma514Q716.lean`，`Q_u` 的定义只许有一个；若 T201 的 agent 空出来，优先由它认领。仿 T206 的 `hasDerivAt_ukerObsT_drift`：漂移逐字是钉死的定义，两侧无可选数据。**验收**：`MomentIneqQ` 的逐点被积式定理（`Q` 版 `timeD1_add_genMomentPt_le_driftF`）；`ω = 0` 同形检查；公理干净 | `Gauss/MomentDuhamelHypGauss.lean`（续）或 `Gauss/MomentDuhamelQ.lean`（新建） | Claude Code | **完成——`stochDom_of_momentDuhamelQ` 总装起来了**（新建 `Gauss/MomentDuhamelQ.lean`，884 行、27 条，全量绿）：⚠⚠ **更正工单（两句都错）**——`SumZeroDyn.hasDerivAt_Qop`（:1157）**逐字就是 `∂_u Q_u`**，`hasDerivAt_Qop_hierarchy`（:1174）**就是 (5.88)**、`commS` 与 `varthetaDot` 已显式出现。真正缺的是**传播子共轭 + 矩阵生成元**那一版（T206 `hasDerivAt_ukerObsT_drift` 的 `Q` 孪生），本单补的是它：`(∂_u+𝓛)(U∘Q_u(L−K)) = U∘Q_uF + U∘[Q_u,Θ](L−K) − U∘(P(L−K))ϑ̇`，三项与 `MomentIneqQ` 的三个漂移被积式**逐字同形**；`commS` 恰是 `Q_uΘ−ΘQ_u` 的亏量、与传播子的 `Θ` 相消。漂移全钉死（`driftF`/`commS`/`varthetaDot` 都是定义），无自由张量。**对 D14 的输入：消费者端不再是缺口**，代价只多一条 `QIntegrable`（高斯模型上是定理 `qIntegrable_gauss`）。但 **`MomentIneqQ` 本身仍未产出**，还差三件：**`Q` 版 `TestFunT₁`/生成元恒等式（最大一块，≈T196 体量，无主）**、`Q` 版五件可积性（归 T212 线）、`Q` 版二次变差桥（归 T213 线）；且 **T201 的五条核估计至今无消费者**（其 `hGd` 即 (7.13) 沿流快衰减没产出）——**D14 裁定时请计入**。⚠ 本机无 pdftotext，(5.91)/(5.99)/(5.100)/(5.103) 的印刷文本**未逐字核对**，请 Cowork 用会话里的 PDF 复核一次。paper-delta T214a |
| T215 | **`M_gf(1−s) ≺ 1` 的显式指数账**（T208 建议的新单）：`farInputs'_of_eG_of_quad` 已把远场输入化归到「`‖eGpm‖ ≤ M_gf·T` 且 `‖primBil‖ ≤ M_qf·T`」。本单把 `EGDef.eGpm_le_reduced` 的右端（含指示函数项与 `(r/(ℓ_uη_u))·L·ρ` 余项）整理成这个形状，并核出 `M_gf(1−s) ≺ 1`，输入只许用 (2.72)/(2.73)（`Cond272Reg` 形，T209）与 T207 的 `J* ≺ (η_s/η_u)²`。**可选第二步**：带 `L¹` 权的积分形一步界（`∫_s^v η_u^{-1}du = (Im m)^{-1}log R`），彻底去掉 `1−s`，与论文字面一致（T208a）。**验收**：`FarInputs'` 的前三条由钉死的漂移产出、只剩第四条 `M_m`（T216）；公理干净 | `Hierarchy/Step2FarInputs.lean`（续） | Claude Code | **进行中**（Claude Code 子 agent，心跳 10:15 派出） |
| T216 | **`M_m ≺ 1`：(5.45) 的远场鞅界，走矩路线而不是 BDG**（T208 无主项；`FarInputs'` 第四条，左端是钉死的 `farMart`）：T74 已证 `bdg`/`bdgQ` 在现有签名下不可卸，T197 让 Step 2 用截断矩 Duhamel 绕开了 `MomentHyp.step`。**第 0 步（先交判断）**：`farMart` 定义为亏量，其小性是 (5.20)+(5.45) 合成的一条——判定它能否由 `MomentIneq`/`CutHyp.moment` 的二次变差项（T213 的 `E⊗E` 形 + (5.44) 的 `R⁴` 预算、`integral_nearInt_le`）直接给出。能，就接线；不能，写明卡在哪一步交 Cowork，**不许**把 `M_m` 换个名字留作新字段。另核 T208b：鞅界只在用到的那个远场 `a` 上要求（`step_bound_far'`）。**验收**：`flowEq548` 的假设表里没有 `M_m`（或只经 T210 的 `CutHyp.moment` 出现）；公理干净 | `Hierarchy/Step2FarInputs.lean`（续） | Claude Code | **进行中**（Claude Code 子 agent，心跳 10:15 派出） |
| T217 | **`docs/REPORT.md` 按 R1/R5 裁定改写**（Jun 17:15 同意，裁定全文见 REPORT §9）：(1) §1 把 Theorems 2.2–2.5 **并列为主定理**，每条附完整假设表（编译探针打印，不抄叙述），状态栏写「以 Theorem 2.21 为前提」或「无条件」；Theorem 2.21 与 Lemmas 2.18–2.20 作为关键中间结果单列；Theorem 2.6 单列并标「③ 空着」（`theorem2_6_of_steps` 在 `OUFlow` 钉死之前**不**算形式化）。Theorem 2.2 用 T199 刚落地的 `delocalization_of_Thm221N′`（假设表只有 `Band`、`Sample`、`Transfer`、`κ/τ/D > 0`、`Thm221N′`；`Transfer` 在高斯模型上有实例 `Gauss.transfer_gauss`）。(2) 否定结论**单列一节，分两小节**：(a) 论文层面的修正（对 paper-deltas 与论文改动预算第 8/13/16 条等，全部零重新编号）；(b) 形式化中被证伪的**自设接口**（`MinorGood`、冻结形 `MomentHyp.step`、`LDENetClose`、T198 形 `cFarStep ≺ 1`、(7.1) 档的 `hkerC`（T201 入库的 `no_const_hkerC_on_gridS`）等），写明**不是论文错误**。(3) §3 外部输入改写为「[51] Theorem 2.2 的复 Hermitian 形式（逐字，量化在所有满足前提的模型上）；Lean 实现在 Theorem 2.6 阶段」，删掉「待定」。**验收**：§1 每条的假设表都有对应的探针名；§9 的 R1–R5 状态与正文一致 | `docs/REPORT.md` | Claude Code | 未认领 |
| T218 | **D14 ①：`P∘(L−K)` 半边接到矩路线**（T201 → D14，Cowork 17:25 裁定「改」）：矩路线改以 `Hyp.momentDuhamelQ` 为接口后，结论只控制 `‖Q_v∘(L−K)_v‖`；要回到 `‖(L−K)_v‖`，用 `A = Q_t A + (P·A)ϑ_t`，其中 `Psum` 那一项的界。现成的 `SumZeroDyn.norm_le_norm_Qop_add` 与 `norm_Psum_lkT_le` 都有，但**没接到矩路线**（矩范数版、沿流、在 T201 的好事件拆分 `momNorm_le_affine_on_event` 之下）。**验收**：`‖(L−K)_v‖` 的矩界由 `Q` 半边 + `P` 半边合成的定理；`P` 半边的输入是已证的定理，不是新字段；可满足性见证沿用 `gridS_Q716_witness` 的网格窗口 | `Gauss/Lemma514Q716.lean`（续）或 `Gauss/Lemma514QRoute.lean`（新建） | Claude Code | 未认领 |
| T219 | **D14 ②：`stochDom_of_momentDuhamelQ` 总装，Lemma 5.14 的矩路线改走 `Q` 接口**（T201 → D14）：`stochDom_of_momentDuhamel` 的 `Q` 类比。T201 已交付它要的五个核估计（`momNorm_Uker_Qop_le`、`momNorm_Uker_commS_le` (5.99)、`momNorm_Uker_PsumVarthetaDot_le` (5.100)、`momNorm_Uker_QQ_le` (5.103)，每条的 sum-zero 前提都是定理），总装定理没写。然后把 `Lemma514` 的矩路线（`lemma514_forall_of_hHol_flow` 那条）改成吃 `momentDuhamelQ` + T218，**不再经过**已退役的 `hkerC`/`hker2C`。**依赖**：`momentDuhamelQ` 的生产者要 `∂_u Q_u`，即 **T214**（关键路径）；本单可先以 `Hyp.momentDuhamelQ` 为具名输入写总装，等 T214 接上。**验收**：Lemma 5.14 的端到端探针在论文网格窗口上有可满足性见证（不带短窗口假设），假设表里没有 `hkerC`；公理干净 | `Gauss/Lemma514Q716.lean`（续）+ `Gauss/Lemma514Moment.lean`（带撇版） | Claude Code | 未认领（总装可先做；接线等 T214、T218） |
| T220 | **(7.13) 的前提 `FastDecay`：沿流的生产者**（T201 另附的第三块，**无主**）：`momentDuhamelQ` 各项张量沿流的 `FastDecay` 是 (7.13) 的前提，也是**唯一一个关于模型而不是关于核的前提**。`SumZeroDyn.lean:3093/3549` 有 `fastDecay_Qop_le` 的用法，但都在好事件上、没接到矩路线。**第 0 步（先交判断）**：列出需要 `FastDecay` 的张量清单（逐项对到 `momentDuhamelQ` 的五项），并判定来源——应是 Step 2 的 (2.75)(2.76) 衰减（`aprioriDecay_cut`）与 (5.35)(5.36) 钉死对象上的衰减，在高概率事件上成立，损失由 `momNorm_le_affine_on_event` 吸收。能接就接；接不上写明卡在哪一步。**不许**把 `FastDecay` 挂成新的自由字段。**验收**：T219 的总装里 `FastDecay` 由定理产出；公理干净 | `Gauss/Lemma514Q716.lean`（续）或新文件 | Claude Code | 未认领（第 0 步可先做） |
| T221 | **去重：`BoundsCore` 下游的三份同一证明脚本**（T211 交出的两条无主项；**低优先级，T209 之后**）：(1) T209 交还 `Flow/Thm221NoEL.lean` 后，删掉它 §6 里与 `RBM.Core.*_of_boundsCore` 逐字相同的七条，去掉 Consequences 的 `Core.` 前缀；`localSemicircleLaw_of_Thm221NoEL'`、`quantumDiffusion_pm_pp_of_Thm221NoEL'` 改成一行推论，指向 `RBM.localSemicircleLaw_of_boundsCore`、`RBM.quantumDiffusion_pm_pp_of_boundsCore`。(1′) T209 余项：`Step2.localLaw` / `Step2Moment.aprioriDecay_of_jS` 的原版改成一行推论（`StepGlue` 里已有严格更一般的重述）。(1″) 下沉到 `RBM1D/Defs/`：`EEUker.mSigma_not` ≡ `Gauss/Step6DriftEG.lean:192` 的 `RBM.mSigma_not`；`EEBridge.leftArg`/`rightArg` ≡ `SumZeroDyn.spl1`/`spl2`（定义相等）。(2) `Flow/EnergyUniform.lean` 的 `SpecSeqN` 一套（:506/:521/:542/:552/:568）是第三份同样的脚本：让固定能量版与能量依赖版一个由另一个特化推出（常值能量序列），择一。**纪律**：被删的名字若有外部消费者，就保留名字、改成一行推论，**签名一字不改**；全量绿。**验收**：`grep` 同一证明脚本只剩一份；`rfl` 探针（T211 的 15 条）全过 | `Flow/Thm221NoEL.lean`、`Flow/Consequences.lean`、`Flow/EnergyUniform.lean` | Claude Code | 未认领（等 T209 交还 `Thm221NoEL.lean`） |
| T222 | **⭐⭐ `CutHyp.moment` 的条件版生产者：钝版改成沿网格逐步自举**（T210 无主项 1+2；**Step 2 余下的两条具名假设 `MomentHypCut.cut`/`MomentHypCut2.cut` 都卡在这里**）：T210 已编译化归 `moment_of_conditional`——无条件 `moment` ⟸ 前缀事件 `A N ws` 上的**条件**矩界 `hcond` + `A` 以 `HighProb` 成立 + 截断水平多项式有界。锐版（第二遍）的前缀是第一遍的结论，免费；**钝版（第一遍）的前缀正是自举要证的东西**，在「一次性对所有网点、无条件」的形状下拿不到。**做法**：第一遍改成**沿网格逐步**的自举——第 `k` 个网点的前缀 = 前 `k−1` 个网点的结论，由归纳假设供给（`BootPP.step` 已把连续时间量化降到有限网点，是现成的骨架）；接口用带撇版，不改冻结签名。然后交 `hcond`：前缀事件上的截断 Duhamel 矩界，输入是 `momentDuhamelHyp_gauss` 那条线（T212/T213/T214）与 (5.34)/(5.35)/(5.36) 三项的界（钉死对象上已证）；`phi_arith'`、`integral_nearInt_le`、`phi_arith_second_pass` 这三条**全仓无消费者**的记账层接到这里。前缀事件可测性：改用 `integral_add_compl₀` 并补「连续路径的一致上界事件是零可测集」。**纪律**：T210 明说硬接会变成 fiat——(5.34)–(5.36) 的界缺哪条就停下报，**不许**当新字段收。**验收**：`step2_cut` 的假设表里 `MomentHypCut.cut`/`MomentHypCut2.cut` 只经 `MomentDuhamel.Hyp` 出现；可满足性见证沿用 `satCutHyp'`（临界标度、水平真带 `u`）；公理干净 | `Gauss/MomentDuhamelCut.lean`、`Gauss/CutHypTheta.lean`（续） | Claude Code | 未认领 |
| T223 | **⭐⭐⭐ 修正 `SumZeroDyn.xi2` 的定义：第二半改成 `σ̄`**（T213 查出；**Cowork 17:55 裁定：原地改定义**，理由见 STATUS）：`Hierarchy/SumZeroDyn.lean:1445` 改成 `Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) (fun i => !(σ i)))`，即论文 Lemma 5.5 的 `U_{σ} ⊗ U_{σ̄}`（p.55，「σ̄ is the conjugate sign vector of σ」）。证 `xi2_eq_xi2bar : xi2 E σ = EEUker.xi2bar E σ`，`xi2bar` 改成它的别名或 `@[deprecated]`。`xi2_ne_zero`(:3650)、`norm_xi2_le`(:3657) 在第二半多一步 `xiOf_not` + `Complex.norm_conj`。**消费者 11 个文件**（`SumZeroDyn` 18 处含 `Hierarchy.bdg`/`bdgQ`、`Gauss/MomentDuhamel` 3 处含 `Hyp.momentDuhamel(Q)` 与 `stochDom_of_momentDuhamel` 的 `hrhs`、`Lemma514Holder` 4 处、`Lemma514Moment`、`Lemma514Q716`、`MomentDuhamelHyp`、`MomentDuhamelHypGauss`、`MomentDuhamelQ`、`MomentDuhamelRhs`、`MomentDuhamelTime`），T213 核过全部只用 `‖xi2‖ = 1`/`≠ 0`。**并行纪律**：这 11 个文件里有正在被 T212/T219/T222 改的；开工前在本单状态栏写明锁定的文件，每个文件只在 `git status` 显示它干净时改、改完立刻提交；**声明类型一字不变**（只改定义体）。**验收**：全量绿；`sanity_rhs_xi2_wrong`（T213 的判别性数值检查）改为对 `xi2` 本身成立的正向检查；`#print axioms` 干净；paper-delta 记一条（Lean 侧定义修正，论文不改） | `Hierarchy/SumZeroDyn.lean` + 上列 10 个文件 | Claude Code | 未认领（**优先**：`momentDuhamelHyp_gauss` 必须在正确的 `xi2` 上产出） |
| T224 | **`hsplit` 与 `hdiff`：`E^{(M)}(α) = ∑_k E^{(M)}(α,k)` 的链式法则（预解式乘积的 Leibniz）**（T213 查出，**全仓无人负责**；`DischargeBDG.lean` 文件头早已承认）：与 `Gauss.quadVarPairs_le_of_split`、`quadVarPairs_Uker` 是同一条缺口——需要 `List.foldr` 形式的预解式乘积对矩阵元的求导 Leibniz 法则（逐因子求导再求和）。先证一般的 `List.foldr` 乘积 Leibniz（任意赋范代数上的可微族），再特化到 loop 的 `G_{σ_1}E_{a_1}⋯` 乘积。**验收**：`hsplit`/`hdiff` 从 T213 的假设表里消失；`ω = 0` 同形检查；公理干净 | `Gauss/EEUker.lean`（续）或 `Gauss/LoopLeibniz.lean`（新建） | Claude Code | 未认领 |
| T225 | **⭐ `Q` 版 `TestFunT₁`/生成元恒等式：把五条 `momentObsT` 专用引理泛化一次，两条路线共用**（T214 交出，`MomentIneqQ` **唯一的大缺口**，约 T196 的体量）：`momentIneqQ_of_derivBound` 的 `hbound` 要 `∂_u E[·]` 的**期望**形式，T214 只给了逐点被积式；桥是 `testFunT₁_qMomentObsT` + `hasDerivAt_integral_qMomentObsT`。而 `testFunT₁_momentObsT`、`exists_bddC2C_momentObsT`、`bddT_momentObsT`、`differentiableAt_momentObsT_pair`、`continuous_timeD1_momentObsT` 全对 `momentObsT` 写死。**做法**：按「确定性系数的 loopObs 有限线性组合，系数族对 `u` 是 `C¹` 且有界」泛化成一套（`qUkerObsT` 与 `ukerObsT` 都属这一类），旧名改成一行特化（签名不变），`Q` 版直接实例化。**可满足性**：系数族取 `Q_u`（论文网格上非退化，沿用 `gridS_Q716_witness`）；T191 的教训——时间方向只要 `C¹`，不要 `C²`。**验收**：`MomentIneqQ` 的期望形式导数界是定理；公理干净 | `Gauss/MomentDuhamelBddT.lean`、`Gauss/MomentDuhamelQ.lean`（续） | Claude Code | 未认领 |
| T226 | **`Q` 版的两条孪生缺口：五件区间可积性 + 二次变差桥**（T214 交出）：(1) T212（plain 版五件边界可积性）的 `Q` 孪生——同一确定性包络 `‖G‖ ≤ (Im z_u)^{−1}` + 控制收敛，`QIntegrable` 已有 `qIntegrable_gauss` 可复用；(2) T213 的 `Q` 孪生：`∑_{ij}(U∘Q_u∘E^{(M)}(i,j))_a·conj(…)_{a′} = ((U⊗U)∘QQ(eeArg))_{a,a′}`，在**修正后的 `xi2`**（T223）上陈述，复用 `sum_Uker_mul_conj_Uker`。**认领优先**：T212 / T213 的 agent 做完本线后续做各自的孪生，避免两份包络论证。**验收**：`MomentIneqQ` 的可积性与二次变差两类前提由定理产出；公理干净 | `Gauss/MomentDuhamelQ.lean`（续） | Claude Code | 未认领（(2) 等 T223） |
| T227 | **⭐⭐ T205 续：Step 6 包络假设的量词改到窗口上，然后写 (2.71) 的步进定理**（T205 查出**空真第九例**，无主）：`not_exists_env_eG` 已编译——`henvG` 等包络假设写成 `∀ v : ℝ`，在 `E = 0`、`ω = 0`、`v = 1 − w` 处被积量 `2(w⁻¹−1)w⁻³/W` 无界，没有任何 `Env` 满足它；而两个文件内部只在 `TimeIcc s t N` 上用它。**做法**：`sharpExpect_step6_*` 等含该假设的声明加**带撇版**，量词改成 `∀ v : TimeIcc s t N`（冻结签名不动；旧版全仓零消费者，加 `@[deprecated]` 护栏并附 `not_exists_env_eG` 的指针）。然后按 T205 点名的来源补槽：`hintL1` ← `int1_gauss`，`hmeas*` ← `continuous_gloop_Hflow`，`henv*` ← `norm_gloop_le_rpow` + `norm_Kval_le` + `hη`。最后写 (2.71) 的步进定理（(2.80) 生产者）与 `Bounds X E t`（含 `expect`）的产出，交给 T205 的总装桥 `bounds_of_boundsCore_of_sharpExpect`。**验收**：**非退化**见证（不是 `s = t = 0`，窗口在论文网格上）；Theorem 2.4 (2.8)(2.9) 与 Theorem 2.5 的探针里没有 (2.71) 作为假设；公理干净 | `Gauss/Step6Sample.lean`（续）+ 含 `sharpExpect_step6_*` 的文件（加撇版） | Claude Code | 未认领 |
| T133 | **loop 观测量的 `C²` 界**（T76 `TestFun` 缺口）：`L_{σ,a}` 与 `(U∘(L−K))_a` 对 `H` 为 `C²`，一二阶导有确定性 `η` 幂界。T132 的前置 | `Gauss/LoopC2.lean`（新建） | Claude Code | **完成**（`BddC2` 对乘积封闭——缺的只有 Leibniz 一步；loop 与 `U∘(L−K)` 的 `TestFun` 均已拿到，探针验证端到端） |
| T134 | **逐点漂移恒等式 + 动 `z_u`**（T76 `LoopIto` 与未做项）：`(∂_u + 𝓛)(L−K) = Θ∘(L−K) + F` 逐点成立；联合可微走 `ContDiff.comp`，绕开「偏导连续 ⟹ 可微」。T132 的前置 | `Gauss/LoopIto.lean`（新建） | Claude Code | **完成**（动 `z_u` 闭合、`ContDiff.comp` 够用；**(2.47) 的 `−m` 减项证明为动 `z` 的产物**，`LoopIto.second` 今后只需冻结形式；余 `hjoint`，见 STATUS） |
| T135 | **`≺` 的可加余量吸收引理**（T127 余项）：界形如 `N^τ·Φ + m·W·L·N^{−D}` ⟹ `≺ Φ`，前提是控制 `Φ` 有**多项式下界** `N^{−B} ≤ Φ`。放 `Defs/StochDom.lean`（通用，**先 grep**：T123 `rpow_neg_le_aprioriRhs`、T125 同形引理可能已近似）。然后用它把 `EEBridge.norm_eeField_le` 升成 `Lemma510.EE_le` 的 `≺` 版，并给出该控制的多项式下界 | `Defs/StochDom.lean` + `Hierarchy/EEBridge.lean` | Claude Code | **完成**（吸收引理进 `Defs/StochDom.lean`（高概率型，下界本身是事件）；`EE_le` 已由裸 `:=` 闭合，余 `eeDecayEvent`/`xiLowEvent` 两个生产者，见 STATUS） |
| T136 | **`hfixIBP`：`condExpDiag_stochDom_of_highProb` 的时间一致版**（T128 余项）。整条链 `stochDom_condRow_of_envelope`/`condStable_Lmax`/`stochDom_normSq_green_diag_sub_Lmax` 都是「先定 `t` 再量化 `N`」。**第 0 步：逐环查哪一环的 `∀ᶠ N` 阈值其实不依赖 `t`**（T128 对涨落侧就发现了这一点：矩界是逐 `(N,u)` 确定性的）；能重新量化的就做 `UnifDomIcc` 版，`hΩ` 用 T130 的 `highProb_goodSetFlow_of_localLaw`。**不改旧签名**，全部新增 | `Gauss/CondStableFlow.lean`（新建） | Claude Code | **完成**（`hfixIBP` 已卸：改用确定性控制 `Ψ²` 重跑该链，`CondStable` 退化、`E_i[L^max] ≺ L^max` 不再需要；三个 `hfix` 已全部供齐，见 STATUS） |
| T137 | **按字长分级的 `FlucGain` 接口**（T128 余项，paper-deltas #85）：T113 只证了有界字长的 gain，而 `norm_integral_prod_epsHom_flucDiag_le`/`integral_norm_flucAvg_pow_le_iter` 对**所有**字消费 `FlucGain`，实际只用到字长 ≤ `2p`。新增 `FlucGainUpTo (k)` 与消费者的带撇变体（只要 `k = 2p`），接上 T113 ⟹ `FlucGain` 在 `ρ ≍ Ψ` 处的所需部分成为定理 | `Gauss/FlucIter.lean`（追加） | Claude Code | **完成**（分级接口 + 全链 `_graded` 消费者；T113 已端到端接上（探针验证）。余：8 行的桥因 import 方向须放 `FlucIterHigh.lean`；`MinorGood` 缺 (4.2) 致威力为 `Ψ·η⁻¹`，见 STATUS） |
| T138 | **`FlowInputs` 的生产者**（T126 余项，paper-deltas #86）：把 T130 的 `GoodEvent` 一致高概率、T91 的 `LDERow`/`LDECol`、(2.76)（`Steps.aprioriDecay`）打包成同一事件；数值束 `Φ_N√ε_N ≤ N^{−D'}` 由区制假设推出。**第 0 步：逐条列出 `FlowInputs` 字段与现有生产者的对应**，缺的报告 | `Hierarchy/LKDecayQuant.lean`（续） | Claude Code | **完成**（`FlowInputs` 拆解完毕，(2.76) 条款与数值束已证；余 `hΩ`（= T130，即弱局部律）与 `LDEFlowDom`（u-一致的 (4.2)，控制无下界），见 STATUS） |

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

---

## T83 交接（Cowork → 谁都可以接，2026-09-20）

**为什么交出来**：这一单剩下的部分已经完全具名、没有设计决策了，而终端侧写 Lean 的速度比
Cowork 侧快一个量级（Cowork 每轮要等 `watch.sh` 重建、读 `build.log`，约两分钟一轮）。
Cowork 留在路线判断、审计、工单与论文侧。

**已落地（`RBM1D/Gauss/IBP.lean`，13 条，构建绿，逐格提交）**：

1. `green_sub_smul_one_eq` —— `G − m = m(−H − tm)G`（`mE_mul_smul_add_zt` 给出 `m = −(tm+z_t)⁻¹`）。纯代数。
2. `hasDerivAt_Hflow_update` —— 动一个高斯坐标，`H_u` 沿 `√u · B_p` 走。
3. `hasDerivAt_green_Hflow_update` —— `∂_{ω_c} G_u = −√u · G_u B_c G_u`（矩阵值）。
4. `mul_Bmat_mul_apply_of_ne` / `mul_Bmat_mul_apply_diag` —— 夹心塌缩成至多两个元素乘积。
5. `tame_green_apply`、`entryCLM`、`hasDerivAt_green_apply_update` —— 标量化 + `Tame`。
6. **`integral_coord_mul_green_apply`** —— 积分步：
   `E[ω_c · G_ab] = gvar_c · E[−√u · (G B_c G)_ab]`，消费 T104 的 `gaussIBP`。

**剩下三格，按顺序**：

* **(a) 从单坐标升到整行**。`H` 的一个矩阵元对应**一对**高斯坐标（实/虚标签），
  用 `Xmat_eq_sum` / `usedCoord` 的分解把 `∑_k H_ik G_ki` 写成对坐标求和，
  再用第 4 条把两个标签的贡献合起来。**注意** `gvar` 在对角与非对角差一个 `/2`
  （`gvar_diag` / `gvar_offDiag`），两个标签各出一半正好拼回 `S_ik`。
  目标形状：`E[∑_k H_ik G_ki] = t·∑_k S_ik·E[G_kk·G_ii] + （交叉项）`。
* **(b) 去掉 minor 上标**。`E_i(G_kk − m) = G_kk − m + O≺(Ψ²)`，直接用 T85
  （`Gauss/MinorReplace.lean`）的替换误差；条件期望用 T84 的 `condRow`。
* **(c) ≺ 记账，落成 `hIBP` 的签名**。终点**逐字**是
  `RBM.Gauss.trace_green_sub_mul_Eblk_stochDom`（`Gauss/FlucAvg.lean`）的 `hIBP` 参数，
  即对 `condExpDiag d N t (zt E t) (mE E) i` 的 `StochDom`。

**硬性约束**：**不许改 `Green/EntryBound.lean` 与 `Gauss/FlucAvg.lean` 的任何签名**，
它们是冻结接口；只在 `Gauss/IBP.lean` 里加东西。
**用 `gaussIBP` 而不是 `matrixStein`**：被积函数带 `H_ik` 因子，不是全局有界的。

**两个已经踩过的坑，别再踩**：
矩阵的范数实例要 `open scoped Matrix.Norms.L2Operator` 才在作用域里；
CLM 与 `HasDerivAt` 复合后函数停在 `(f ∘ g)` 且 ℂ 的 `AddCommGroup` 实例走了 normed 那条路，
`simpa` 关不掉，要 `simp only [Function.comp_def, entryCLM_apply] at h` 再 `exact h`。

---

# Cowork 只做调度（2026-09-20，Jun 指定）

**Cowork 侧不再写 Lean。** 证据：484 个提交里终端侧 413、Cowork 71；68 375 行 Lean 里
Cowork 写了 1 910 行（2.8%），却写了全部 107 张工单、全部路线判断与审计。
而 Cowork 改一次要等 `watch.sh` 全量重建再读 `build.log`，约**两分钟一轮**；
终端侧 `lake env lean 单文件`是**秒级**。同一个类型不匹配，终端试三次的时间 Cowork 试一次。

**分工从此固定**：

* **Cowork**：读论文、定路线、开工单、写规格、审计、蓝图、论文侧的编辑预算。
  发现设计决策没人做时，**由 Cowork 拍板并写成规格**，不要留在队列里等。
* **终端 agent**：全部 Lean 实现。

Cowork 手上原有的 T1、T58、T83 已全部交回队列，规格见下文。

---

## T58 交接：表示桥的设计决定（Cowork 拍板，2026-09-20）

**问题**（原记于 STATUS「一条需要先定下来的表示桥」）：`Hierarchy/Kernel.lean`（T42）的
张量算子 `Uker`、`ThetaOp` 作用在 `A : (Fin n → ZMod L) → ℂ`；loop 层用的是 `LoopIdx`
（两条 `List`：`σ : List Bool`、`a : List (ZMod L)`）。两者没有桥，卡住 (5.19)、(5.20)(5.21)、Def 5.4。

**决定：把小的一侧搬过去，不要搬大的一侧。**
`LoopIdx` 这边是 loop 层的地基（`primRhs`/`primBil`/`cutGlue` 全建在上面，几百条定理），
`Fin n` 那边只有 T42 的十来条。所以：

* **保留 `LoopIdx` 为规范表示**，把 `Uker` / `ThetaOp` **共轭到 `LoopIdx` 上**，
  得到 `UkerL` / `ThetaOpL`，并证它们与原版经桥相等；
* 桥用 `List.ofFn` / `List.get`：对 `I : LoopIdx α` 与 `h : I.a.length = n`，
  `I.a.get ∘ Fin.cast h : Fin n → α`；反向 `List.ofFn`。
  需要的引理 Mathlib 都有：`List.length_ofFn`、`List.get_ofFn`、`List.ofFn_get`。
  σ 一侧同理，且 `ThetaOp` 的 `ξ : Fin n → ℂ` 本来就是由 σ 逐位算出来的（`xiOf`）。
* **(5.19)、(5.20)(5.21)、Def 5.4 的 `E⊗E` 全部在 `LoopIdx` 一侧陈述**，
  不要把 loop 层搬到 `Fin n`。

**不要改**：`Hierarchy/Kernel.lean` 里 `Uker`/`ThetaOp` 的现有陈述（T42 已证的十几条），
只在新文件里加共轭版本与桥。`Hierarchy/Dynamics.lean` 里 T58 已落地的
(5.12)–(5.15)（`primBil`、`primBilLen`、`primBil_eq_two_add` 等）全部在 `LoopIdx` 一侧，不受影响。

**为什么这条卡着主定理**：Theorem 2.21 的六步总装等 (5.19)(5.20)(5.21)。
桥一搭，2.21 就从「阻塞」变成「排队」。

### 验收标准（做到这四条就算完，不要多做也不要少做）

1. **桥本身**：`LoopIdx` 与 `Fin n → ZMod L` 之间的双向转换 + 往返恒等式（`ofN_toN`、`toN_ofN`），
   长度条件写成显式假设，不要用 `Subtype` 包起来（下游 `primRhs`/`primBil` 都是裸 `LoopIdx`）。
2. **共轭版算子**：`UkerL`、`ThetaOpL` 在 `LoopIdx` 上定义，并证「经桥与 `Uker`/`ThetaOp` 相等」。
   T42 已证的那十几条（`Uker_self`、`Uker_comp`、`norm_Uker_apply_le`、`sum_ThetaOp_row` …）
   **各配一条 `LoopIdx` 版推论**即可，不要重证。
3. **四条目标全部成为 `LoopIdx` 一侧的定理**：**(5.19)**、**(5.20)**、**(5.21)**、
   **Def 5.4 的 `E⊗E`**。这四条是 Theorem 2.21 六步总装的直接输入。
4. **`Hierarchy/Kernel.lean` 一字未改**（`git diff` 对该文件为空），
   `Hierarchy/Dynamics.lean` 里 T58 已落地的 (5.12)–(5.15) 也不动。新东西全部进新文件。

**做完后在 `docs/STATUS.md` 写清楚**：四条的定理名、桥的名字，以及
「Theorem 2.21 的六步总装现在还差什么」——下一张单直接接着这句话开。

---

## T110 规格：`FlucGain` 的 `m ≥ 2`（Cowork 设计，2026-09-20）

**这是全队风险最高的一张，所以先说怎么控风险：不要一上来就建一般归纳。**

### 第 0 步（先做这一步，做完先在 STATUS 报一句，再决定要不要往下建）

**在 `m = 2` 上手算一遍，确认增益是乘性的。** 也就是要确认

    ‖Q_{κ₂} Q_{κ₁} Z_k‖ ≲ Ψ³     （而不是 2Ψ²）

`m = 1` 已经证了（`norm_qRow_flucDiag_le`：`Q_κ` 湮灭 `Z^{(κ)}_k`，而 `Z_k` 与它相差 T85 的 `ε ≍ Ψ²`）。
`m = 2` 的关键在于：把 `Z_k` 换成 `Z^{(κ₁)}_k` 之后，**剩下的那个 `Q_{κ₂}` 要作用在替换误差上再赚一个 `Ψ`**。
**如果这里只是加性的（每次替换各赚 `Ψ²`、互不相乘），整条路线就不成立，立刻停下报告。**
这正是 (4.12) 那个缺口的本体，不要绕过它去建框架。

### 第 1–4 步（第 0 步通过之后）

1. **`Finset` 索引的迭代小行**：`greenMinorSet d N u z (S : Finset (d.Idx N))`，
   即在 `{a // a ∉ S}` 上的预解式。**用 `Green/Minor.lean`（T40）的 (4.9) 迭代来建**——
   那里的 `minorGreen`、`green_off_diag_eq`、`green_diag_eq` 对**任意** Fintype 索引成立，
   与模型无关，正合适。**不要**试图把 T85 的 `minorReplace_*_stochDom` 原样套 `m` 次：
   它们的索引类型钉死在 `BIdx L W N` 上，小行的索引类型不是它。
2. **`FinDepOffRows`**：把 T84 的 `FinDepOffRow`（单行）推广到一个 `Finset` 的行。
   然后证：`S` 里任何一个 `Q_κ` 湮灭 `FinDepOffRows S` 的函数。这是湮灭那一半的全部内容。
3. **望远镜式的替换误差**：`|G_ll − G^{(S)}_ll|` 按 `S` 逐行展开，每一步用 (4.9)。
   `≺` 记账只在最后做一次，不要每行做一次。
4. **对 `m` 的归纳**，结论落成 `FlucGain d N u z m B ρ` 的现有定义
   （`ρ ≍ Ψ`，`B` 用 `flucBound_env` 那条无条件的）。

### 硬性约束

* **不许改** `Gauss/FlucCount.lean`、`Gauss/FlucAvg.lean`、`Green/EntryBound.lean` 的任何签名，
  也不许改 `FlucGain` 的定义本身——它是 T94 已经在消费的接口。只在新文件里加东西。
* **不许用 `1_Ω` 记账**：湮灭性依赖 `E_κ[(1−E_κ)X] = 0`，乘上指示函数就破坏它，
  且 `1_Ω` 不是 `FinDepOffRow` 的、提不出 `E_κ`。STATUS 已确认任何 `≺`/指示函数记账都补不回来。
* 复用而不是重证：`FinDepOffRow` 与 `condRow`（T84）、(4.9)（T40）、`FlucBound`/`flucBound_env`（T87/T88）、
  `applyOps`/`numQ`/`qRow`（T94）。

**为什么它值这个价**：补上之后 (4.12) 与 (4.5) 全部是无假设定理，[40] 这条外部输入彻底不需要，
论文里两条「引用外部文献」就都清干净了。

---

## T109 规格：`TraceMomentBound` 的 `p ≥ 2`（Cowork 设计，2026-09-20）

**先说一条可能省掉整张单大半工作量的判断，请接手的人第一件事就验它。**

`docs/STATUS.md` 里 T100 记的挡路石是「需要 Wick/Isserlis + 闭走计数，而 Mathlib 两样都没有，
还得在 `Measure.infinitePi` 上从 `P_map_restrict` 造分解」。**这条路确实很贵，但它不是唯一的路。**

### 建议路线：用已经证好的 `gaussIBP` 跑矩递推，绕开 Isserlis 与走计数

`RBM.Gauss.gaussIBP`（T104，**已是定理**）给的是多项式增长（`Tame`）测试函数的高斯分部积分。
而 `Tr(X^{2p})` 的被积函数是坐标的**多项式**——正好落在 `Tame` 里。于是：

    E Tr(X^{2p}) = ∑_{i,j} E[ X_ij · (X^{2p−1})_{ji} ]

对每个 `X_ij` 用一次分部积分，`X_ij` 变成方差乘导数，而

    ∂(X^{m})_{ji} / ∂X_{ji} = ∑_{k+l=m−1} (X^k)_{jj} · (X^l)_{ii}

于是得到**自洽递推**

    E Tr(X^{2p}) = ∑_{i,j} S_ij ∑_{k+l=2p−2} E[ (X^k)_{jj} (X^l)_{ii} ]

再用 `∑_j S_ij = 1`（`RBM.sum_Sblk_row`，`p = 1` 那条已经在用）与对 `p` 的归纳 + Cauchy–Schwarz，
就得到 `E Tr(X^{2p}) ≤ C_p · N`。这正是 Catalan 数那条递推，**但一行组合计数都不用写**。

**第 0 步（先做这个，再决定走哪条）**：把上面那条分部积分恒等式在**本仓库的实坐标参数化**下
验一遍——模型用的是实/虚两个标签的实高斯，非对角方差是 `S_ij/2`（`gvar_offDiag`）、对角是 `S_ij`
（`gvar_diag`）。**因子 2 和 Hermitian 约束下 `X_ji = conj X_ij` 的配对就在这里，是最容易错的地方。**
`RBM1D/Gauss/IBP.lean`（T83）里 `hasDerivAt_Hflow_update` 与 `mul_Bmat_mul_apply_of_ne`
已经把「动一个坐标 → 矩阵沿 `B_p` 走 → 夹心塌成两项」这条链做好了，**直接抄那两条的模式**，
只是把预解式换成 `X^m`。验通了就照这条走；验不通再回头考虑 Isserlis。

### 硬性约束

* **不许改 `Gauss/OpNorm.lean` 里 `TraceMomentBound` 的定义**，也不许改
  `opNormBound_of_traceMomentBound` 与 `Gauss/Model.lean` 的 `OpNormBound`——冻结接口，只把假设变定理。
* `p = 1` 已无条件（`traceMomentBound_one`），**拿它当归纳的起点，也当因子是否算对的体检**：
  你的递推在 `p = 1` 处必须退化成 `E Tr(X²) = ∑_{ij} S_ij = WL ≤ N`，对不上就是因子错了。
* 复用：`gaussIBP`（T104）、`Tame` 全套（`LDEQuad.lean`）、`frobSq`/`trace_pow_eq_frobSq`（T100）、
  `Xmat_update`/`Bmat`（T71）、`sum_Sblk_row`。

**这张单卸掉之后**：`‖X‖ ≺ 1` 无条件，`Gauss/Model.lean` 的 `OpNormBound` 字段变定理，
论文那条「直接使用、未证」的公开缺口（paper-deltas #49）补上。

---

## T111 规格：两条分布相等 (2.39) 与 (6.1)（Cowork 设计，2026-09-20）

**先厘清它们到底是什么。** 这三条在仓库里都不是「公设」，而是**`≺` 界的转移**：

* `RBM.Transfer` / `RBM.TransferLoop1`（`Flow/Consequences.lean`）—— (2.39)/(2.66)，
  把 `X.Lval` 上的 `≺` 界转移到 `gloop (T.Hband ...)` 上；
* `RBM.LoopScaling`（`Loop/ContinuityAssembly.lean`）—— (6.1)，
  把 `t₁` 处 loop 的 `≺` 界转移到 `t₂` 处、参数换成 `ztTilde E t₁ t₂`。

论文里这三条的理由都是**同一句话**：两边的矩阵在分布上相等（差一个确定性的标度）。
在一般模型里这要靠分布论证；**在我们的高斯实现里它是可以直接算的**，因为
`H_u = √u · X` 的律是显式的。

### 建议路线

**情形 A（最常见）：两边是同一个 `X` 的确定性标度。** 那就根本不需要分布论证——
把两边都写成同一个 `ω` 的函数，标度是确定性的，`≺` 的转移退化成一条不等式的重写。
**先逐条检查是不是这种情形**，是的话这一单就很轻。

**情形 B：真的换了律。** 那就走坐标标度的映射，两条 Mathlib 引理正好接上：

* `ProbabilityTheory.gaussianReal_map_const_mul`（`Gaussian/Real.lean:329`）——
  一维高斯乘常数还是高斯，方差乘 `c²`；
* `MeasureTheory.Measure.infinitePi_map_pi`（`ProductMeasure.lean:482`）——
  **逐坐标**映射可以提到无穷乘积外面：
  `(infinitePi μ).map (fun x i => f i (x i)) = infinitePi (fun i => (μ i).map (f i))`。

两条一拼就得到：

    (P d).map (fun ω c => a c * ω c) = infinitePi (fun c => gaussianReal 0 ((a c)² * gvar d c))

也就是**坐标逐个乘常数，`P d` 还是同族的乘积高斯，方差按 `a²` 缩放**。
(2.39)/(6.1) 需要的标度全部是这个形状，代进去即可。
`StochDom` 的转移随后由 `Measure.map` 下的积分/测度改写得到（注意 `StochDom` 是对失败事件的测度陈述，
`map_apply` 加可测性就够，不需要重做 `≺` 的记账）。

### 硬性约束

* **不许改** `RBM.Transfer`、`RBM.TransferLoop1`、`RBM.LoopScaling` 三个 `structure` 的字段签名——
  `Flow/Consequences.lean` 与 `Loop/ContinuityAssembly.lean` 的下游已经在消费它们。
  只在新文件 `Gauss/DistEq.lean` 里给出**高斯实现下的项**（`theorem transferLoop1_gauss : TransferLoop1 ...` 这种形状）。
* 与 T69 的 `Gauss/Model.lean` 对齐：`Hflow`、`Sample`、`Band` 的实例都在那里，不要另起一套。
* 先做 `TransferLoop1`（只涉及 1-loop，最小），通了再做 `Transfer`，最后 `LoopScaling`。

**卸掉之后**：全文图里三个「仍作为假设」的橙点去掉两个，Theorem 2.4 不再带额外假设。

---

## T112 规格：`≺` 在条件期望下的保持（Cowork 设计，2026-09-21）

**来历**：T83 把 `hIBP` 推到了只差两个输入（`Gauss/IBP.lean` 的
`condExpDiag_stochDom_of_pieces`），做 T83 的 agent 在 STATUS 里指出其中一个卡在一块
**仓库里没有的通用工具**上：

> 「被 `≺` 支配的量取 `E_i` 后仍被 `≺` 支配」——**这不是自动的**。

他说得对，而且这正是这张单的价值：它不只是 T83 的收尾，是一块**公共工具**。

### 为什么不自动（接手前先理解这一点）

`X ≺ Y` 的定义带一个例外事件：对每个 `τ > 0`，`P(|X| > N^τ Y)` 小于任意多项式。
取条件期望 `E_i` 是对第 `i` 行坐标积分，**例外事件在积分里不会自己消失**——
`E_i[1_{bad}·X]` 没有先验的小性，除非你对 `X` 在坏事件上也有控制。

**所以正确的形状不是「`≺` 蕴含 `E_i`-`≺`」，而是「`≺` + 坏事件上的确定性包络 ⟹ `E_i`-`≺`」。**
这和 T77（`Gauss/Envelope.lean`）的反向桥是同一个套路：**包络是免费的**，
因为 `Im z_t = η_t > 0` 给出 `‖G‖ ≤ η_t⁻¹` 在**全空间**成立。

### 建议的三步

1. **通用引理**（本单的主产出，放 `Gauss/CondDom.lean`）：

       X ≺ Y，且 ∃ 确定性 B 使 ∀ω, ‖X ω‖ ≤ B   ⟹   E_i[X] ≺ Y + (可忽略项)

   用 `condRow`（T84）把 `E_i` 写成精确的坐标积分，坏事件那部分用 `B · P(bad) ≤ B·N^{-D}` 吃掉。
   **直接照抄 T77 `Gauss/Envelope.lean` 的记账结构**，那里已经处理过同样的「好事件 + 包络」拆分。
2. **`hminor`**：`E_i(G_kk − m) − (G_kk − m) ≺ Ψ²`。用第 1 步 + T85
   （`Gauss/MinorReplace.lean` 的替换误差）+ `norm_green_apply_le_etaT` 当包络。
3. **`hprod`**：`E_i[(G_ii − m)(G_kk − m)] ≺ Ψ²`。两个因子各 `≺ Ψ`（局部律），
   乘积 `≺ Ψ²`，再用第 1 步过 `E_i`。包络同样由 `η_t⁻¹` 给。

做完把两项喂进 `condExpDiag_stochDom_of_pieces`，`hIBP` 就在冻结签名下真正卸掉，(4.5) 只剩 (4.12)。

### 硬性约束

* **不许改** `Gauss/IBP.lean` 里 `condExpDiag_stochDom_of_pieces` / `_of_ibpRem` 的签名，
  也不许改 `Gauss/FlucAvg.lean`、`Green/EntryBound.lean`——全是冻结接口。
* 第 1 步的引理**要写成通用形状**（对任意被包络控制的 `X`），不要写死在 `G_kk − m` 上：
  T110 的高阶小行展开大概率也要用它。
* 复用：`condRow`/`FinDepOffRow`（T84）、`Envelope`（T77）、`MinorReplace`（T85）、
  `norm_green_apply_le_etaT`（T88）。

---

## T114 规格：Theorem 2.21 的总装（Cowork 勘察，2026-09-21）

**这张单是 T58 之后的那一张，现在先把地图画好，等桥一通就能直接开工。**

### 已经存在的部分（不要重做）

* **最后一段链条已经有了**：`RBM.Bounds_of_Steps`（`Flow/Hypotheses.lean:349`）——
  由 `Steps X E s t` 加 `∀ N, s N ≤ t N` 直接给出 `Bounds X E t`，也就是 Theorem 2.21 的结论。
  `BoundsCore_of_Steps` 是它不用 Step 6 的版本。
* **六步各自的顶层定理都在**：
  `Hierarchy/Step1.lean:859` `step1`、`Hierarchy/Step2.lean:2015` `step2`、
  `Hierarchy/Step3.lean:1062` `flow_sharpLoop`、`Hierarchy/Step45.lean:458` `flow_steps45`、
  `Hierarchy/Step6.lean:779` `sharpExpect_step6`。

### 所以这一单真正要做的只有一件事

**把六步的顶层定理拼成 `Steps` 的八个字段**（`apriori`/`weakLaw`/`localLaw`/`aprioriDecay`/
`sharpLoop`/`sharpLmK`/`sharpDecay`/`sharpExpect`），然后

    theorem thm221_gauss ... : Thm221 (sample d) κ

其 `step` 字段 = 「给定 `Cond272` 与 `Bounds X E s`，造出 `Steps X E s t`，再喂 `Bounds_of_Steps`」。

### T58 在哪里被消费（这就是为什么要等桥）

`Hierarchy/Step2.lean` 的 `step2` 要一个 `Hyp X E s t`，而 `Hyp.H : SumZeroDyn.Hierarchy X E s t 0`
**就是 (5.20) 的积分形式** —— T58 的四条目标之一。Step 3 的 `hyp_flow` 同理。
所以顺序是：**T58 先把 (5.19)(5.20)(5.21) 与 Def 5.4 的 `E⊗E` 在 `LoopIdx` 一侧证出来，
本单再把它们组装成 `Hyp`。**

### 建议的做法

1. **先把 `Steps` 的八个字段逐个对账**：哪个字段由哪个步的哪条定理给出、量词次序差在哪、
   指标集是否要 `precomp_param` 搬一下（`Bounds_of_Steps` 里已有这种用法，照抄）。
   **这一步先只写成一张表放进 STATUS**，不写 Lean——对账对不上的地方才是真问题。
2. `Hyp` 的另外两个字段 `eG`（5.35）与 `mart`（5.44)–(5.46)）来自 `Step2Moment.lean`（T75，
   停时已换成连续归纳），确认它们的现有形状能直接填。
3. 全部对上之后再写 `Flow/Thm221.lean`。

### 硬性约束

* **不许改** `Flow/Hypotheses.lean` 的 `Steps`/`Thm221`/`Bounds` 定义，也不许改六个 step 文件——
  全是冻结接口。只在新文件里组装。
* 对不上的地方**不要改陈述去凑**，写进 STATUS 报告，由 Cowork 判断是改哪一侧。

**做完之后**：`Thm221` 从假设变成定理，`Bounds_of_Thm221`、`theorem2_5_of_Thm221`、
`Flow/Consequences.lean` 的 Theorem 2.3/2.4 全部接上，主定理链条闭合。

---

## Cowork 的两条裁决 + T115 规格（2026-09-21，据 T114 第 1 步）

T114 第 1 步用四个探针 + 一个负对照做了编译级对账，结论是：**`Steps` 的八个字段全部逐字对上**，
零 `precomp_param`、零量词重排。总装本身不是问题。真正的问题有三个，两个由我裁决如下。

### 裁决一：Step 2 走**路线 B**（`Step2Moment.step2`，矩路线）

理由：① 这是 Jun 已批准的方向；② 它的输入 `MomentHyp` 要的是**路径连续性**与
**确定性 Hölder 模**（`H_u = √u·X` 给出 γ = 1/2），而这些 T101/T106 基本已经交付；
③ **它不需要 T58 的表示桥**，而路线 A 需要。
**据此下调 T58 的优先级**：它仍是论文 §5.2 的内容，但不再挡主定理。

### 裁决二：`0 ≤ s` vs `0 < s` —— **放宽五个 step 定理到 `0 ≤ s`，不动 `Thm221`**

理由：`s = 0` **不是流的奇点**——`z_0 = E + m`，`η_0 = Im m_E > 0`，`ℓ_0` 有限；
奇性在 `s → 1` 那一端。而 `Thm221.step` 的 `0 ≤ s` 与论文一致，
且 `Flow/Iteration.lean` 的迭代在消费它，收紧它要付一条 paper-delta 并向下游传播。
**做法**：逐个 step 定理检查 `0 < s` 用在哪里，能放宽就放宽。
**若某一步的证明真的需要 `0 < s`，不要硬改——报告是哪一步、卡在哪个引理，由 Cowork 再裁。**

## T115 规格：总装的确定性缺口

**要证的四条**（全树无生产者，但文档都说得出来）：

* `hs1` / `hs2` —— Step 4 的基例。`Step45.lean` 的文档说「可由 (4.5) 与 (2.76)+(2.72) 得出」，但没证。
* `h0` / `h12` —— 文档说由 (2.73)(3.46) 与 (2.75)(2.76) 得出。

**已知的一个坎（T114 指出，接手前先看）**：`h12` 在 `m = 2` 处，`Step3.S … 2 l` 是对**全部四个**
`σ ∈ {+,−}²` 取 max，而 (2.76) 只覆盖 `σ = (+,−)`。**其余三个电荷的界从哪来，需要有人说明**——
这可能是文档漏写，也可能是真缺口。**第 0 步：先把这一条查清楚再写 Lean**，查不通就报告。

**为什么它现在最高优先级**：它是**纯确定性记账**，不依赖 T58、不依赖 T113、不依赖任何在飞行中的单，
而且它挡在总装前面。T114 的第 2 步等它。

**硬性约束**：不许改 `Flow/Hypotheses.lean` 与六个 step 文件的签名；新东西进
`Hierarchy/StepGlue.lean`。另：`hregS` 同时蕴含 Step 1 的 `hreg` 与 `Cond272`（T114 已编译验证），
**总装只需要这一条正则性假设**，不要再引入 `hc`/`hreg`。

---

## T120 规格：把四电荷缺口收缩到 `(+,+)` 一个（Cowork，2026-09-21）

**背景**：T115 查出 paper-deltas #72（原误编 #66）——(5.76) 对**所有** `σ` 取 max，(2.76) 只证 `σ = (+,−)`，
而 p.70 按四个电荷用它。`Hierarchy/StepGlue.lean` 的文件头已经把来龙去脉写清楚了，
缺口也已具名为 `AprioriDecayAll`，**没有被默默假设**。

### 这张单只做一件事：把缺口从「四个电荷」精确收缩到「`(+,+)` 一个」

**不要试图证 `(+,+)`**。已经确认便宜补法差整整一个 `A_u`，那是 Jun 要裁的事
（paper-deltas #72，已由 Jun 裁：走 (c)，见 T122）。这张单要交付的是**归约**：

1. **`(−,+)` ⟸ `(+,−)`**：迹的循环性。`Hierarchy/Decay.lean:1459` 的 `gloop_rotate_eq` 就是它，
   注意它要 `σ.length = a.length`。
2. **`(−,−)` ⟸ `(+,+)`**：共轭。`RBM.Gsig_conjTranspose` 与 `RBM.mSigma_false`
   （`StepGlue.lean:116` 那一段已经用过这条路，照抄）。
3. 于是把 `AprioriDecayAll` **重新表述**成只对 `σ = (+,+)` 的单条假设
   （建议名 `AprioriDecayPP`），并证 `AprioriDecayPP → AprioriDecayAll`。

**验收**：`AprioriDecayAll` 在仓库里不再是四个电荷的黑盒，而是
「`(+,−)` 已证 + 两条归约定理 + `(+,+)` 一条具名假设」。
`flow_hs2`、`flow_S_two` 等现有消费者**签名不变**（它们要的还是 `AprioriDecayAll`）。

**第 0 步**：先确认 `(−,+)` 那条归约在**带着 `L−K` 的差**时仍然成立——
`gloop_rotate_eq` 是对 `gloop` 说的，而 (2.76) 里是 `L − K` 的差，
`K` 那一侧也要同样旋转才对得上。**对不上就报告，不要硬凑。**

**为什么值得单独做**：它把一条「论文缺口」从模糊的四电荷问题变成一句可以直接拿去问作者的话——
「(2.76) 对常值电荷 `(+,+)` 成立吗？」Jun 裁决前，这是能做的全部。

---

## T122 规格：用 Lemma 5.11（`n = 2`）+ 自举卸掉 `AprioriDecayPP`（Cowork，2026-09-21）

**裁决（Jun 确认，Cowork 核对 PDF pp.64–72）**：paper-deltas #72 走 (c)——**(2.76) 的陈述不改**。
常值电荷 `(+,+)` 的来源是 **Lemma 5.11（p.65）在 `n = 2`**：`(+,+)` 满足 (5.82)（`σ₁ = σ₂`），
(7.16) 情形 1 的演化核直接收缩，不需要 Ward、sum-zero、尾函数；p.70 只是把出处写成了 (2.76)。
T115/T120 写的「旁证：Lemma 5.14（p.68）排除常值 σ」是**误读**——(5.96) 的「非常值」只出现在**交错**分支内部。
**顺手改掉**：`StepGlue.lean` 文件头「The two remaining inputs」一段与 `AprioriDecayAll` 的 docstring、
`ChargeReduce.lean` 文件头若有同样的话、STATUS 里 T115/T120 两节的「旁证」句（在原句后加一行更正，不删原文）。

### 数学（照这个做，不要另找路）

记 `A_u = Wℓ_uη_u`、`R = ℓ_t/ℓ_s`、`Ξ_{u,m} = Ξ^{(L−K)}_{u,m}`（四电荷 max）。

1. **`n = 2` 的 (5.83)**：`Ξ_{u,2} ≺ Λ^{1/2} + Ξ_{u,1} + Ξ_{u,2}·Ξ_{u,2}·A_u^{−1} + Ξ^{(L)}_{u,3}`，`Λ ≥ max_u Ξ^{(L)}_{u,6}`。
   二次项里**两个因子都是被估计的量自己**（`n = 2` 的剪切粘合 `k = 1, l = 2` 两侧都保留 `(σ₁,σ₂)`）。
   自举**直接对四电荷 max `Ξ_{u,2}` 做**即可：`(±,∓)` 那两个已 `≺ (η_s/η_u)^4`，不碍事。
2. **先验**：`Λ^{1/2} ≺ R^{5/2}`、`Ξ^{(L)}_{u,3} ≺ R^2`（(2.73)，`Steps.apriori`）；`Ξ_{u,1} ≺ A_u^{1/2}`（(2.75)，`flow_S_one` 已用过）。
3. **自举**：门槛 `A_u^{3/4}`。门槛内二次项 `≤ A_u^{1/2}`，故 `Ξ_{u,2} ≺ A_u^{1/2} + R^{5/2}`，由 `hregS` 严格低于门槛；
   起点 `Ξ_{s,2} ≺ 1`（`hLmK`，即 (2.68)/(5.110)）。闭合 ⇒ 全段 `Ξ_{u,2} ≺ A_u^{1/2} + R^{5/2}`。
   这已足够 `S(2,l)`：`A_u ≤ A_s`（`sc.A_le_As`）且 `R^{5/2} ≤ (Wℓ_sη_s)^{1/2}`（`hregS`）。
4. **Step 4 基例 `hs2`**（要 `≺ A_u^{1/4}`）：再代一次 (5.83)，这次用 `Ξ_{u,1} ≺ 1`（`flow_hs1` 的路子，或 `Eq45Flow` + `(+,−)` 的 (2.76)），
   二次项已 `≺ 1`，**不需要再自举**，得 `≺ R^{5/2} ≤ A_u^{1/4}`（`hregS`，`eventually_R4_le_rpow_quarter` 同款计算）。

### Lean 的现成零件

* `SumZeroDyn.bound_nonAlt`（`SumZeroDyn.lean:4982`）—— (5.84)，非交错电荷（含 `(+,+)`），在 `lemma514_flow'` 内对所有 `n ≥ 2` 生效。
  **但** `Step3.Lemma514` 的打包把 `n = 2` 的二次项列为假设 `hX2`（`X 2 * X 2 * A⁻¹ ≺ Φ`）——**直接喂 `Lemma514` 会循环**，这正是要自举的原因。
* `Step2Moment`：`le_of_bootstrap_weight`（变门槛连续归纳）、`continuousOn_phi`（逐样本连续 + 确定性包络 ⇒ 矩连续）、
  `stochDom_timeIcc_of_holder`（矩一致 + 确定性连续模 ⇒ 不可数并下的 `≺`）。**同一形状的自举 `(+,−)` 已走通过一次**，照抄结构。
* `ChargeReduce.aprioriDecayAll_of_pp`（T120），`StepGlue.flow_S_one`/`flow_hs1`/`eventually_R4_le_rpow_quarter`（T115）。

### 第 0 步（必做，先写进 STATUS 再动手）

判定自举在 Lean 里挂在哪一层：
* **(a) `≺` 层**：`bound_nonAlt` 及其输入（`Hierarchy`/`Lemma510`/`LKDecay`/`hLmK`）都对 `TimeIcc s t` 陈述。
  换成前缀 `TimeIcc s v` 是否**只是重新实例化**？若是，自举需要的是「对每个前缀、门槛内 ⇒ 改进」，
  而 `≺` 是对 `N → ∞` 的序列陈述的——**确认这在 `≺` 层能否表达**，大概率不能（这正是 T78 改走矩路线的原因）。
* **(b) 矩层**：仿 `Step2Moment.MomentHyp` 开 `MomentHypPP`，`step` 字段恰为「门槛内一步改进」= Lemma 5.11@`n = 2` 的矩版本。
  **(b) 是可接受的中间交付**：它把「论文缺口」变成和 `(+,−)` 同类的随机层接口——缺口的**性质**就变了，这本身就是进展。
  若走 (b)，再看 `step` 能否由 `SumZeroDyn.Hierarchy.bdg`（BDG + 二次变差）在 `good := 非交错` 上导出；导不出就留作字段，写明为什么。

**形状对不上就报告，不要硬凑。**

### 目标形状：以消费者为准

`flow_S_two` 只要 `Ξ_2 ≺ (Wℓ_sη_s)^{1/2}`，`flow_hs2` 只要 `≺ (Wℓ_uη_u)^{1/4}`。自举天然给的是 `≺ A_u^{1/2} + R^{5/2}`（不带 `(η_s/η_u)^4`），
**多半凑不回 `AprioriDecayPP` 的原形状**（`u = s` 处原形状要 `Ξ_{s,2} ≺ 1`，这个倒是有；但 `u` 靠近 `s` 时 `R^{5/2}` 不随 `u` 变小）。
若凑不回：新增弱化陈述（建议名 `AprioriBoundPP` 或直接陈述 `Ξ_{u,2}` 的界），给 `flow_S_two`/`flow_S_le_two`/`flow_hs2`/
`flow_sharpLoop_glue`/`flow_steps45_glue` 加**带撇变体**，**旧签名一律不动**。

### 验收

* `S(2,l)`（全部 `l`）与 `hs2` 由定理给出，剩余假设只属 `lemma514_flow'` 已有的随机层接口 + 自举所需的确定性连续性输入（或 (b) 的 `MomentHypPP`）；
* 零 `sorry`、零 `axiom`，`#assert_rbm_axioms` 通过；**全量 `lake build`**（CLAUDE.md：单文件查不出跨文件重名）；
* 「旁证」更正落地；STATUS 记录；paper-deltas #72 的「处理」栏补上最终定理名。

---

## T123 规格：一阶矩反向桥（T117 拆单 B；Cowork，2026-09-21）

**来源**：T117 勘察（STATUS「`Gauss/Step6Hyp.lean` — T117」）。Step 6 的 `hq11`/`hq13` 真实内容是一件**通用工具**：
`|Y| ≺ Φ` + 确定性包络 + 多项式下界 ⟹ `∫|Y| ≺ Φ`（`UnifDetDom` 形）。T77 的 `momentDom_of_stochDom` 只给偶数矩 `∫|Y|^{2p}`。

**第 0 步**：先看它是不是**两行推论**——概率测度上 `∫|Y| ≤ (∫|Y|²)^{1/2}`（Jensen / Hölder；Mathlib 查
`integral_mul_le_Lp_mul_Lq`、`eLpNorm_le_eLpNorm_of_exponent_le` 一类），配 `momentDom_of_stochDom` 的 `p = 1`。
是就**不要造新轮子**，只加一条 `unifDetDom_integral_of_stochDom` 包一下。

**范围**：(i) 上面那条通用定理，放 `Gauss/Envelope.lean`；(ii) 为 `lkErr` 之积供两个输入——确定性包络与多项式下界
（后者要 `η_u ≥ N^{-c}`，**不免费**，来自 `Wℓ_uη_u ≥ 1` ⇐ (2.72)，故桥带这条假设）；(iii) 经 T117 已给的
`norm_quad11_le_integral`/`norm_quad13_le_integral` 从 `Steps.sharpLmK 1`/`sharpLmK 3` 收口，卸掉 `hq11`/`hq13`。

**验收**：`sharpExpect_step6` 的七条假设只剩 A 组（`hH`/`hFD`/`h5133`/`hG`，归 T58）；零 `sorry`/`axiom`；全量 `lake build`；STATUS 记录。

---

## T132 规格：矩 Duhamel——随机层真正剩下的那堵墙（Cowork，2026-09-21）

> **Jun 2026-09-21 裁决（选项 (a)）**：论文保留布朗运动模型、随机层零改动（paper-deltas #88）。所以本单的合体不等式是 **Lean 侧的证明路线**，不必与 Lemma 5.5 字面同形，也**不要**为了「贴论文」去证残差的 (5.24)。对外仍按规矩：矩只活在 `Gauss/`，出口是 `≺`。

### 为什么现在开这张单

盘点结果：Steps 2–6 的随机层**全部**经 `SumZeroDyn.Hierarchy`（`duhamel`/`duhamelQ` 带鞅字段、`bdg`/`bdgQ`）或
`Step2Moment.MomentHyp.step`、`Step2PP.BootPP.step`、`Step6.Hierarchy` 取输入。T74/T76 已判定：在 `H_u = √u·X` 模型里，
逐路径的 `duhamel` 只能 fiat（`mart :=` 残差），而**残差的 BDG 在这个模型里不是生成元论证能给的**——残差含 `∫_s^v F(H_r) dr`，
代入 `H_r = √(r/v)·H_v` 后对 `v` 显式依赖（T74 理由 2），且无鞅结构（理由 3）。**这是结构性的，不是没做完**。
T74/T76 之后**没有任何工单接手这堵墙**。这张单接手。

### 数学（关键：只用一时刻边缘律，因而与模型无关）

固定目标时刻 `t`、电荷 `σ`、指标 `a`。令
`Φ(u, H) := (U_{u,t,σ} ∘ (L−K)_{σ}(H, z_u))_a`，`u ∈ [s, t]`——**它是 `(u, H)` 的函数，不是路径泛函**。

1. **逐点漂移恒等式**（确定性，T134）：`(∂_u + 𝓛) Φ = (U_{u,t,σ} ∘ F_{u,σ})_a`，其中 `𝓛 = ½ Σ S_ij ∂_ij ∂_ji`，
   `∂_u` 是对显式 `u`（经 `z_u`、`K_u`、`U_{u,t}`）的偏导，`F` 是 (5.15)/(5.19) 的非线性项（`K∼(L−K)`、`E^{(L−K)×(L−K)}`、`E^{(G̃)}`）。
   线性部分被 `U` 的定义**恰好**消掉——这就是论文 (5.20) 的 dt 部分，逐点成立。
2. **带显式时间的生成元恒等式**（T71 的推广）：`d/du E[Ψ(u, H_u)] = E[∂_uΨ(u, H_u)] + E[𝓛Ψ(u, H_u)]`。
   它**只依赖 `H_u` 的一时刻律**，故在 `√u·X` 与论文的布朗模型里**同一个式子**——这是整条路线合法的理由。
3. 取 `Ψ = |Φ|^{2p}`，由 T72 的 `genMomentPt_le` 与支点 `secondOrder_eq_quadVar`、T74 的 `emart_Uker`/`eeRaw_self_eq_quadVar`：
   `φ' ≤ 2p·E[|Φ|^{2p−1}·|U∘F|] + C_p·E[|Φ|^{2p−2}·((U⊗U)∘(E⊗E))_{a,a}]`，`φ(u) := E|Φ(u,H_u)|^{2p}`。
4. Hölder 后得 `φ' ≤ 2p·φ^{1−1/2p}·f + C_p·φ^{1−1/p}·g`（`f = ‖U∘F‖_{2p}`、`g = ‖(U⊗U)∘(E⊗E)‖_p`）。
   令 `y = φ^{1/2p}`，积分后对 `m = max_{r≤u} y(r)` 解二次不等式（**不需要 ODE 比较定理**）：
   **`‖(L−K)_{t,σ,a}‖_{2p} ≤ ‖(U_{s,t}∘(L−K)_s)_a‖_{2p} + 2∫_s^t ‖(U_{u,t}∘F_u)_a‖_{2p} du + (C_p ∫_s^t ‖((U⊗U)∘(E⊗E))_{u,a,a}‖_p du)^{1/2}`**。
   这就是 (5.20)+(5.24) 在 `L^{2p}` 里的合体（Minkowski 形；对 `≺` 用途与论文的 `E(∫QV)^p` 等价）。

**不要做的事**：不要试图在 `√u·X` 模型里对**残差**证 (5.24)——那条可能根本不成立（残差的增量完全相关）。
不要实例化 `SumZeroDyn.Hierarchy`（fiat 风险，见 T118）。

### 第 0 步（必做，先写进 STATUS 再动手）

1. **消费者清单**：`duhamel`/`duhamelQ`/`bdg`/`bdgQ`/`mart` 出现在 `SumZeroDyn.lean`、`Step2.lean`、`Step2Moment.lean`、`Step2PP.lean`、`DischargeBDG.lean`。
   逐个写出消费者**实际抽取的 `≺` 或矩层陈述**（多半是「`(Wℓη)^n|(L−K)_t| ≺ ‖U(L−K)_s‖ + ∫(≺-界) + (∫ QV-界)^{1/2}`」这一句）。
2. 据此设计**替代接口** `MomentDuhamel`（`≺` 进、`≺` 出，形如上面第 4 条经 T73/T77 转换后的样子），**以及 `Q_t` 版**（交错电荷走 (5.91)，同一论证，`F` 多出 `[Q,Θ]` 与 `P∘(L−K)·ϑ̇` 两项）。
3. 列出第 1–4 条每一步的现成零件与缺口（预期缺口：T133 的 loop `C²` 界、T134 的逐点漂移恒等式与 `z_u` 的全导数）。
**这一步不写证明，只交清单 + 接口草案**；Cowork 审过再开工。

### 交付（第 0 步审过之后）

* 第 4 条的定理（`Gauss/MomentDuhamel.lean`，矩只活在 `Gauss/` 里，对外 `≺`）；
* 由它产出：`Step2Moment.MomentHyp.step`（`(+,−)`）、`Step2PP` 的 `(+,+)` 自举的一步改进（**若事件形 `BootPP.step` 产不出，就加矩形变体，别硬凑**）、
  `lemma514_flow'` 的带撇变体（不经 `Hierarchy`）、`Step6.Hierarchy`（期望形，`p` 取最低阶即可）；
* **旧签名一律不动**，新路线全用带撇变体；全量 `lake build`；paper-deltas 记一条（`(5.24)` 在 Lean 里以合体形式出现）。


### Cowork 审查结论（2026-09-21 03:55）：**可开工**，按下面修改；拆成 T132a / T132b / T132c

**接受**：
* **修改 1（逐点漂移恒等式作必需字段，在定义层钉死 `F`）——强烈同意**，这是本单的主要收益。注意它是关于**确定性函数** `(u, M) ↦ (L−K)(u, M)` 的恒等式
  （`𝓛 = ½ Σ S_ij ∂_ij∂_ji` 只用到方差剖面 `S`），所以能在一般 `Band`/`Sample B` 上陈述，不需要高斯。
* 修改 2（结构陈述在一般 `Sample B`，高斯卸载单列）、修改 4（带撇件直接出 `≺`，不做带撇 `bound_nonAlt`/`bound_qGood`/`step_bound`）、
  修改 5（三块无主缺口：`(z,M)` 联合 `C²` → 并入 T134；参数积分的 `u`-一致控制 → 并入 T133；`Lp` 可积性字段 → T132a 自带）。
* 3(d) 的措辞更正：是「对**同一一时刻边缘律**的不同流无关」，不是「对模型无关」。同意，已按此理解 paper-deltas #88。
* `∂_u Uker` 免费（仿射因子之积）——好发现。

**退回：修改 3（改用 `e^{p(2p−1)(v−s)}` 的 Grönwall 形）——不行，会丢 `η` 的幂。**
理由：(5.77) 的每个 E 项与 (5.86) 的二次变差都带 `1/η_u`。Young + 常系数 Grönwall 给出的非齐次项是 `∫ ‖U∘F_u‖_{2p}^{2p} du`，
而论文要的是 `(∫ ‖U∘F_u‖_{2p} du)^{2p}`。当 `‖U∘F_u‖ ≍ Φ/η_u` 时前者 `≍ Φ^{2p} η_t^{1−2p}`，后者 `≍ (Φ·log)^{2p}`——
开 `2p` 次方后**差一个 `η_t^{−1}`**；二次变差项同理差 `η_t^{−1/2}`。改用 `1/η_u` 加权的 Young 也不行：Grönwall 因子变成 `(η_s/η_t)^{C p²}`，
随 `p` 二次增长，而 `≺` 需要对任意大的 `p`，时间步长 `τ'` 却要在 `ε, D` 之前定好——不闭合。**这正是 moment-route-plan 里标的「Hölder 记账」风险。**

**正确的收口不需要 ODE 比较定理，只要积分 + 取上确界**（照做）：
1. Hölder：`φ' ≤ 2p φ^{1−1/2p} f + C_p φ^{1−1/p} g`，`f_u = ‖(U_{u,t}∘F_u)_a‖_{2p}`，`g_u = ‖((U⊗U)∘(E⊗E))_{u,a,a}‖_p`。
2. 令 `ψ = (φ + ε)^{1/p}`（`ε > 0` 避开 `φ = 0` 处的除法，最后 `ε → 0`），则 `ψ' ≤ 2 ψ^{1/2} f + (C_p/p) g`。
3. 积分：`ψ(u) ≤ ψ(s) + 2 m(u) ∫_s^u f + (C_p/p) ∫_s^u g`，其中 `m(u) = sup_{r≤u} ψ(r)^{1/2}`；右端对 `u` 单调，取 `sup` 得
   `m² ≤ m_s² + 2 m F + c G`（`F = ∫_s^t f`、`G = ∫_s^t g`、`m_s = ψ(s)^{1/2}`）。
4. 解二次不等式：`m ≤ F + √(F² + m_s² + cG) ≤ 2F + m_s + √(cG)`。即
   **`‖(L−K)_{t,a}‖_{2p} ≤ ‖(U_{s,t}∘(L−K)_s)_a‖_{2p} + 2∫_s^t f + (c ∫_s^t g)^{1/2}`**——`p` 只进常数 `c = C_p/p`，`η` 只以 `∫ du/η_u = log` 的形式出现。
这就是规格里写的形状，不用 `gronwallBound`。

**拆单**：
* **T132a（现在开工，不依赖 T133/T134）**：`MomentDuhamel` / `MomentDuhamelQ` 结构（含修改 1 的漂移字段、`Lp` 可积性字段）、
  上面 1–4 的收口引理（纯实分析，放 `Analysis/`）、`∂_u Uker`、带撇件直接出 `≺` 并重新生产 `Step3.Lemma514`（`u`-一致性走 T124 的网引擎 + T125 的 loop 模）。
* **T132b（等 T133/T134）**：高斯卸载——带显式时间的生成元恒等式 + `(z,M)` 联合 `C²` ⟹ `MomentDuhamel` 的实例。
* **T132c（等 T132a）**：`Step2Moment.MomentHyp.step` 与 `Step2PP` 的 `(+,+)` 一步改进，由矩 Duhamel + (5.39)–(5.41)(5.45) 的矩形式给出。


### Cowork 中途抽查 T132a（2026-09-21 04:25，读的是未提交的 `Gauss/MomentDuhamel.lean` 与 `Analysis/MomentClosing.lean`）

**通过**：收口引理是「积分 + 取上确界 + 解二次不等式」（`le_two_mul_add_sqrt_of_sq_le`、`sqrt_le_of_integral_le`），**没有**常系数 Grönwall，文件头把理由写清楚了；
`drift` 字段逐点钉死 `F`（`F_unique`）；`momentDuhamel(Q)` 的量词序是「固定目标时刻 `v`、`∫_s^v`」，`Q_t` 版五项齐全；`cMD` 只依赖 `p`、不依赖 `N`，不会让不等式变空。

**两处要改（提交前）**：
1. **`EE` 仍是无约束的数据字段**——它只出现在 `momentDuhamel` 右端，取成随 `N` 增长的巨大值，不等式就空了；护栏又回到只有 `Lemma510.EE_le` 一条。
   **把 `EE` 钉死**：直接用 T127 的 `eeField`（类型与 `Hierarchy.EE` 逐字相同，Def 5.4 的具体张量）作定义，或加字段 `EE_eq : EE = eeField …`。
   这样 `F`、`EE` 两个数据都被钉死，T135 证的 `EE_le` 就是关于确定对象的命题。
2. **`drift` 对**所有** `M : Matrix … ℂ` 量化，范围太大**：非 Hermitian 的 `M` 可能使 `M − z_u` 不可逆（Lean 的逆在那里取 0），恒等式可能不成立，T132b 会卸不掉。
   **改成只对 Hermitian `M`**（高斯流的支撑就在那里，`Im z_u > 0` 保证可逆），并说明 `genLK` 里的 `∂_ij∂_ji` 是沿 Hermitian 方向的二阶导。

---

## T133 规格：loop 观测量的 `C²` 界（T76 的 `TestFun` 缺口；Cowork，2026-09-21）

> **补充（T132 第 0 步审查，03:55）**：界要对 `u ∈ [s,t]` **一致**（参数积分求导的 dominated convergence 要用），不只是固定 `u`。

T72 已对**预解式观测量** `φ(G)` 卸掉 `TestFun`（`bddC2_greenObs`）。loop `L_{σ,a}(H) = ⟨∏ G(σ_i)E_{a_i}⟩` 还差：
矩阵求逆的 Fréchet `C²`（Mathlib：`contDiffAt_ring_inverse` 一类）+ `List.foldr` 乘积的 Leibniz（`Generator.lean` 只有逐线 `iteratedDeriv` 版）。
**交付**：`bddC2_loopObs`——`L_{σ,a}` 及 `(U∘(L−K))_a` 对 `H` 是 `C²`，一、二阶导有**确定性**界（`η⁻¹` 的幂，由 `‖G‖ ≤ η⁻¹`），供 T132 第 3 条的 `genMomentPt_le` 与 dominated convergence 使用。
**第 0 步**：先 grep `Gauss/` 下是否已有 `foldr`/`List.prod` 的 Leibniz 或 `ContDiff` 乘积引理，**别造第二个轮子**。

---

## T134 规格：逐点漂移恒等式 + 动 `z_u` 的全导数（T76 的 `LoopIto` 与未做项；Cowork，2026-09-21）

> **补充（T132 第 0 步审查，03:55）**：另需 `(z, M) ↦ (M − z)⁻¹` 的**联合** `C²` 及其导数的确定性界（T132b 要用）。

1. **`LoopIto`（纯确定性）**：`½ Σ S_ij ∂_ij∂_ji L_{σ,a}(H)` = (2.45) 的 dt 部分（cut-and-glue 项 + `G̃` 项），**逐点、对固定 `H`、固定 `z`**。
   T76 只证了期望版；这里要逐点版。
2. **动 `z_u`**：`∂_u` 经 `z_u` 的部分（`∂_z G = G²`）与 1 合起来，再减去 `K` 的原始方程 (2.48)，得到 (5.15) 的逐点形：
   `(∂_u + 𝓛)(L−K)_{u,σ,a} = (Θ_{u,σ}∘(L−K))_a + F_{u,σ,a}`。(5.10)–(5.15) 的代数重组 T58 已落地，**复用**。
3. T76 卡住的「偏导连续 ⟹ 可微」：**绕开它**——`(u, H) ↦ L` 是光滑映射的复合（`z_u` 光滑、矩阵求逆解析），直接用 `ContDiff.comp` 得联合可微。
**第 0 步**：确认 T58 已落地的 (5.12)–(5.15) 是逐点（对 `H`）陈述还是对抽象张量陈述；是后者就先写适配，报告再动。

---

## T132b 规格：矩 Duhamel 的高斯卸载（Cowork，2026-09-21 05:40；等 T140、T141、T145）

**目标**：在高斯流 `H_u = √u·X` 上造出 `MomentDuhamel.Hyp` 的实例（T145 修好之后的结构：`EE = eeField`、`drift` 只对 Hermitian `M`），即证 `momentDuhamel` 与 `momentDuhamelQ` 两个不等式字段。

**五步（照做，第 0 步先核对前置）**：
0. **核对前置**：T145 已合入（`git grep eeField\|IsHermitian -- RBM1D/Gauss/MomentDuhamel.lean` 非空）；T140（`LoopIto.second` 冻结形式 + (5.19)）、T141（loop 导数界对 `z` 在球上一致）已合入。缺哪个报告哪个，**不要就地补**。
1. **带显式时间的生成元恒等式**：`d/du E[Ψ(u, H_u)] = E[∂_1Ψ(u, H_u)] + ½ Σ S_ij E[∂_ij∂_ji Ψ(u, H_u)]`。
   证法：`d/du Ψ(u, √u·X) = ∂_1Ψ + (2√u)⁻¹ Σ X_ij ∂_ij Ψ`（`hasDerivAt_comp_diag`，T134），再对第二项用 T70 的 `matrixStein`；求导进积分用 dominated convergence，控制函数取 T133/T141 的**对 `u` 一致**的确定性界。
   它是 T71 `hasDerivAt_momentIntegral` 的带时间版，**先 grep T71/T72/T134 有无现成的一半**。
2. **点态展开**：取 `Ψ(u, M) = |Φ(u, M)|^{2p}`，`Φ(u, M) = (U_{u,v}∘(L−K)(u, M))_a`。显式部分 `∂_1|Φ|^{2p} = 2p|Φ|^{2p−2} Re(Φ̄ ∂_1Φ)`；生成元部分用 T72 的 `genMomentPt_le`
   （`𝓛|F|^{2p} ≤ 2p|F|^{2p−2}Re(F̄ 𝓛F) + C_p|F|^{2p−2} Σ S|∂F|²`）。二者合起来一阶项是 `2p|Φ|^{2p−2}Re(Φ̄ (∂_1 + 𝓛)Φ)`。
3. **漂移代入**：`(∂_1 + 𝓛)Φ = (U_{u,v}∘F_u)_a`——由 `drift` 字段 + T132a 的 `hasDerivAt_Uker_apply`（`∂_u U_{u,v} = −U_{u,v}∘Θ_u`，线性部分恰好相消）。
   二阶项 `Σ S|∂Φ|² = ((U⊗U)∘eeField)_{a,a}`：T72 `secondOrder_eq_quadVar` + T74 `emart_Uker`/`eeRaw_self_eq_quadVar` + T127 `eeField`。
4. **Hölder + 收口**：`φ' ≤ 2p φ^{1−1/2p} f + C_p φ^{1−1/p} g`，喂 T132a 的 `sqrt_le_of_integral_le`（`ψ = (φ+ε)^{1/p}`，积分形，FTC 接上）得 `momentDuhamel`。
   **`Q_t` 版**同法，`F` 多出 `commS` 与 `Psum·ϑ̇` 两项（`Q_u` 对 `u` 求导，SumZeroDyn 已有 `hasDerivAt_Qop_hierarchy`）。
5. **`integrable` 字段**：T77 确定性包络 `‖G‖ ≤ η⁻¹` 给出，T131 的 ℝ 值可积性可复用。

**禁止**：常系数 Grönwall（见 T132 审查）；实例化 `SumZeroDyn.Hierarchy`；改 `Hyp` 结构（结构改动只经 T145）。
**验收**：`momentDuhamelGauss : MomentDuhamel.Hyp (sample d) E s t n`（名字可调），假设只剩 `|E| ≤ 2−κ`、`0 ≤ s`、`t < 1` 与 (2.72)；零 `sorry`/`axiom`；全量 `lake build`；paper-deltas 取号前查重。

---

## T132c 规格：Step 2 的一步改进——**先做可行性审查**（Cowork，2026-09-21 06:15）

### ⚠ 先说结论：`Step2Moment.MomentHyp.step` 在现有「同阶」形状下**很可能证不出来**

`MomentHyp.step` 的形状是「`∀ u ∈ [s,v]`，`φ_q(u) ≤ thr_q` ⟹ `φ_q(v) ≤ bnd_q`」，**假设与结论是同一个阶 `q`**（`φ_q = E[(J*_u)^q]`）。
但 (5.40)–(5.42) 的右端对 `J*` 是**超线性**的：(5.40) 有 `J*²`，(5.41)(5.42) 有 `(Wη_uℓ_u)^{−1/3}·J*³`。进矩 Duhamel 后，`q` 阶的一步改进要用 `‖J*_u‖_{3q}`——**`q` 阶的门槛管不住 `3q` 阶**。
两条看似的出路都不行：
* 用确定性包络插值（`E[J^{3q}] ≤ N^{2qK}E[J^q]`）：`J*` 的包络指数 `K` 约等于衰减轮廓的 `D`（`T_{u,D} ≥ A_u^{−2}W^{−D}`），损失 `N^{2K}` 远大于小因子 `A^{−1/3}` 能补的；
* 对所有阶同时自举：顶阶永远缺一环（`q` 阶要 `3q` 阶），且对 `q` 一致的连续模不存在（Lipschitz 常数含 `‖X‖`，其 `q` 阶矩随 `√q` 增长）。
论文靠停时绕开了这一点（停时之前 `J* ≤` 门槛**逐路径**成立，超线性项自动有界）；`√u·X` 里没有停时可用。**这不是论文的问题**（论文在布朗模型里是对的，Jun 已选 (a)），是矩路线自己的设计问题——正是 moment-route-plan 标过的「Hölder 记账」风险。
`Step2PP.BootPP.step`（`(+,+)` 在 `n = 2` 的自二次项）同样受影响，只是更温和（平方而非立方）。

### 建议的设计：**光滑截断**替代停时（第 0 步要核实它能闭合）

`J*_u = J(u, H_u)` 是**当前状态的函数**，不是路径泛函。用光滑截断 `χ(J/Θ)`（`χ = 1` 在 `[0,1]`、`= 0` 在 `[2,∞)`、`C²`）把它变成状态函数的权重：
1. 令 `Φ̃(u, M) := χ(J(u,M)/Θ)·Φ(u,M)`，`J` 取**光滑 max**（`r`-范数，`r ≍ log N`，与真 max 差常数因子），则 `Φ̃` 仍是 `(u, M)` 的 `C²` 函数，T132b 的带时间生成元恒等式直接适用。
2. `Φ̃` 的漂移 = `χ·U∘F` + `Φ·(∂_u+𝓛)χ` + `S`-加权交叉项 `⟨∂χ, ∂Φ⟩`。**在 `χ` 的支撑上 `J ≤ 2Θ`**，所以 `J²`、`J³` 全被门槛控制——超线性问题消失；
   带 `χ'`、`χ''` 的项**只活在缺口 `J ∈ [Θ, 2Θ]` 上**。
3. 缺口项的矩用 `P(J_u ∈ 缺口)^{1/2p}` 控制；而 `P(缺口)` 由同一个 `p` 阶的矩界 `≤ (bnd/Θ)^{2p} ≈ N^{−2pδ}` 给出——**同阶闭合，无阶数上升**，常数递推是压缩的（有 `N^{−δ}` 小因子）。
4. 缺口 + 对 `u` 的连续性（T106/T125 的模 + T124 的网）⟹ `J*_u` 越不过缺口 ⟹ `J*_u ≤ N^δ·bnd` 对全部 `u` 高概率成立，即 (5.47)。

### 第 0 步（只交报告，Cowork 审过再开工）
1. **核实上面的障碍**：`MomentHyp.step` 的消费路径里，(5.40)–(5.42) 的 `J*` 幂次是否确实超线性、包络指数 `K` 是否确实随 `D` 增长。若有我没看到的出路，写出来。
2. **核实截断方案能闭合**：写出 `Φ̃` 漂移三项各自的界（特别是 `(∂_u+𝓛)J` 与 `|∂J|²` 在缺口上的界——`J` 是尾函数之比的光滑 max，其导数需要 T133 那套 `C²` 界），以及第 3 步的常数递推。
3. **接口草案**：`MomentHyp.step` 保持不动（冻结），新增 `MomentHypCut`（或直接给出 `jS_stochDom` 的带撇版）；`BootPP.step` 同法。
**依赖**：T132b（带时间生成元恒等式）。第 0 步可以先做，不等 T132b。

### T132c 规格修订（2026-09-21 07:20，据 Jun 的回忆）——**解除暂缓**

**Jun 的说法**：在 `J* ≺ (η_s/η_t)^4` 之下，`(J*)² ≺ (η_s/η_t)^4·J*`，所以超线性项都能线性化，代价是 `(η_s/η_t)` 的幂要重算；
论文当时把问题放在 `J*` 的幂上，只是为了不反复核对 `(η_s/η_t)` 因子，**没有别的数学原因**（他记得的范围内）。

**这和光滑截断是同一个论证的两半**：线性化需要**逐点**的 `J* ≤ 门槛`——论文靠停时拿到；Lean 里 `√u·X` 没有停时，矩方法只知道 `‖J*‖_q ≤ 门槛`，不知道逐点的。
**光滑截断 `χ(J*/Θ)` 就是这个逐点工具**：在 `χ` 的支撑上 `J* ≤ 2Θ`，于是 Jun 的线性化在那里成立，漂移对 `J*` **线性**，同阶的矩闭合不再需要更高阶矩。

**两处可以无条件去掉的超线性**（不需要门槛）：(5.52)–(5.58) 里那些 `(1 + J*A^{−1})` 因子来自 (4.2)/(4.5) 对 `|G_xy|`、`⟨G̃E⟩` 的界，
改用 Step 1 的 (2.73)（`L_{(+,−)} ≺ R·A^{−1}`，不带衰减）即得 `|G_xy| ≺ R^{1/2}A^{−1/2}`、`Ξ^{(L)}_2 ≺ R`，与 `J*` 无关。
**真正内禀的只有 (5.34)/(5.50) 的 `J*²`**（尾部衰减要两个因子同时衰减，再用 √ 的凹性），这一项用截断支撑上的线性化处理。

**第 0 步（缩短为一张指数表，交 Cowork 审）**：把 (5.40)–(5.42) 线性化后每一项的系数写成 `A^{−α}(η_s/η_t)^β`，逐项核对在 (2.72)「`(η_s/η_t)^{30} ≤ A`，带增益 `N^c`」下仍是 `≤ N^{−c'}`。
我的草算（请核对）：(5.40) → `A^{−1}(η_s/η_t)^{6}`，宽裕；(5.42) 第二项 → `A^{−1/3}(η_s/η_t)^{8}`，`8/30 < 1/3`，余 `A^{−1/15}`，且它在根号里；**(5.41) 若照搬 `J*³` 线性化 → `A^{−1/3}(η_s/η_t)^{2+8} = A^{−1/3}(η_s/η_t)^{10}`，`10/30 = 1/3` 恰在边界，只靠 `hregS` 的 `N^c` 增益才小**——所以 (5.41) **先用 (2.73) 去掉 `(1 + J*A^{−1})` 因子**，把它降到 `J*` 一次或二次再线性化，别依赖边界增益。**若有一项不够小，停下来报告，不要改门槛指数**。

> **Jun 2026-09-21 补充**：(2.72) 的指数 30 是随手取的小数，**可以放宽到 50 或 100**（Lemmas 2.18–2.20 的迭代步数 `n₀` 仍有限）。这是**备用**选项：优先不动 30（`hregS` 自带 `N^c` 增益，(5.41) 用 (2.73) 降幂后本就有余量）；只有指数表证明某项确实不够时才启用，届时 Lean 侧给 `Cond272`/`hregS` 加指数参数的带撇版（旧签名不动），论文只改一个数字，记进论文改动预算。

> **Cowork 2026-09-21 08:55 补充（T155 的结果对本单的影响）**：(1) T155 已把 (5.35) 证成定理，**形状 2（`eG_le_reduced`）的远场括号逐字落实了第 0 步的预言**：`r^{3/2}A^{−1/2}·J* + r·A^{−1}·(J*)^{3/2}`。(2) **但近场项是 `r³` 不是 `r²`**（paper-deltas #112 ④），第 0 步的指数表只算了远场——**实现前先把近场 `r³` 补进指数表**，确认在 (2.72) 的 30 下仍 `≤ N^{−c'}`；不够再按 Jun 的备用授权放宽到 50/100。(3) 走形状 2，不需要形状 1 的额外假设 `J* ≤ A_u`（#112 ③）。(4) (5.35) 的左端要从 T163（钉死漂移上的具体 `E^{(G)}`）取，**不要**从 `Step2.Hyp.eG` 取。（6）**10:28 追加（T158 的交付边界）**：`CutoffBounds.lean` 对 `χ` 只收 `HasDerivAt` 与 `|χ′|` 界作假设，**没有构造具体的 `C²` 截断**——实现时必须给出一个具体 `χ`（Mathlib 的 `Real.smoothTransition` 或 `ContDiffBump` 拼出 `[0,1]` 值、在 `[0,1]` 上为 1、`[2,∞)` 上为 0 的函数），并证它满足那些假设，否则截断方案的前提没被实例化过。二阶导是方向导数而非 Fréchet，对 `𝓛 = ½ΣS_ij∂_ij∂_ji` 够用。（5）**09:35 追加（T156 的更正）**：(5.36) 的 Case 2(1a) 过完 (5.22) 的 `W∑_b` 后是 **`A^{−1/2}`**（`η_u^{−1}(ℓ_u/ℓ_s)^{3/2}A_u^{−1/2}(J*)²`），不是 `A^{−1}`；Case 2(1b) 是 `A^{−1}(J*)³`。**第 0 步的指数表按「都带 `A^{−1}`」算的 `β*` 偏乐观半格**——实现前把这一项与 (2) 的近场 `r³` 一起重算，确认 30 仍够；不够按备用授权放宽。(5.36) 的左端从 T167（钉死的 `eeFun`）取。

**然后照原设计做**：`Φ̃ = χ(J/Θ)·Φ`（`J` 取光滑 max）→ 漂移三项（支撑上线性化；`χ'`、`χ''` 项只活在缺口）→ 同阶矩闭合 → 缺口 + 对 `u` 的连续性 ⟹ (5.47)。
`(+,+)` 在 `n = 2` 的 `BootPP.step` 同法（平方项在截断支撑上线性化为 `Θ·Ξ_2/A`）。**交付还须包括 (5.48)**（`Step45.FlowEq548`，T147 查出无主——它是 Step 2 同一论证的副产品，论文 p.59 末尾「Notice that we have also proved」）。依赖 T132b。论文零改动（Jun 已选 (a)），记 paper-delta。

