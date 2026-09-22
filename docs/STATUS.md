# STATUS（当前状态摘要）

> **读法（2026-09-22 起，Jun：「STATUS + TASKS 文件太大了，每次 agent 读一下就要 200k 个 token」）**
> * 本文件只放**当前状态与最近的事**，目标长度 **≤ 400 行**。**不要读 `docs/archive/` 下的整份文件**——需要旧内容时用 `grep -n` 定位再读几十行。
> * 2026-09-19～22 的全部历史（原 STATUS 6800+ 行：每张单的完成报告、审计、裁定）原样保存在 **`docs/archive/STATUS-2026-09-19_22.md`**。查某张单：`grep -n "T222" docs/archive/STATUS-2026-09-19_22.md | head`。
> * **新的完成报告写进 `docs/reports/Txxx.md`**（完整版，不限长度）；本文件「最近完成」一节只追加 **≤ 8 行**摘要 + 指针。「无主的活」「待定夺」必须在本文件里写（短），调度才看得见。
> * 超过 400 行时，调度把「最近完成」里较早的条目移进 `docs/archive/STATUS-<日期>.md`。

---

## 1. 当前状态（2026-09-22 03:05 UTC）

* **规模**：约 190 个 Lean 文件、15 万行、5700+ 条定理；0 sorry、0 项目公理；HEAD 构建绿。
* **目标**：六步循环（Theorem 2.21 + Lemmas 2.18–2.20）正确无误 → T159 端到端核对 → Theorem 2.6（Jun：其余无高风险项后再开）→ 最终报告。
* **Theorem 2.21 第一遍**（不含 (2.71)）：T239 的六槽假设表里，**第 1 槽（`Step1.Hyp`，T242）、第 3 槽（`hΘ`，T243）、第 5 槽（`Eq45Flow`，T243）、第 6 槽的 `init`（T241）已关掉**——四例全是同一种结构性多余：生产者要的 `BoundsCore X E s` 就在下一层作用域里、往上传时被丢掉。**余**：第 2 槽 `MomentHypCut.cut`（→ **T230 (A′)**，最高优先）、第 6 槽的 `near`/`meas`/`modulus`（→ T244）与 `moment`（→ T230），以及把四处闭合合并进一份总装（机械）。
* **(2.71) 第二遍**：量词已修（T227）；余四个好集的 `HighProb` 与 `K` 的衰减率（→ T234）。
* **Lemma 5.14（`Q` 路线）**：`hkerC`（T219）、`NonAlt514`（T236）、`driftF` 包络（T238）已从假设表消失；`lkGood` 可测性绕过（T237 的可测核，`hΞm` 彻底消除）。**余一处**：`rhs514QAt_of_kernel_inputs` 的 `hDec*` 五行换成事件限制版（替代品已编译，换线未做，裁定走原地改 `Lemma514QAssembly.lean`）。
* **最高风险 = 最高优先**：**T230 (A′)**——Step 2 第一遍自举。**Jun 2026-09-22 03:50 明确指定「T230 (A′) is most important」**，03:50 派出实现（当时贴的是 Cowork 03:05 的 `∏χ(…)` 乘积权重）；**Cowork 04:05/04:15 的更正已于 04:12 与 04:17 两次 `SendMessage` 转给该 agent**：权重改 **ℓ^q 软最大值** `w_k = χ(J̃_k/Θ)`、`J̃_k^q = Σ_{j<k}Σ_a(|lk_{u_j,a}|²/T²)^{q/2}`（`q` 偶、`q ≥ log(k·L²)`），理由是 `abs_derivProd_le` 的 `Σ_{j<k}|ρ_j'|` 要对 `N^{Ccard}` 个网点求和（基数损失）且 `J` 是 max、`hasDerivAt_cutProd` 前提不成立；取 `Θ = e·Λ` 保「前缀事件上 `w = 1`」，§4 的 `cutProd` 引理保留。仍要求先交那一页只读设计（Stein 正则性 / `matrixStein` 够不够 / `∇χ` 与交叉项先验界 / `N₀` 对 `k` 一致）。见 §3。

## 2. 已定的裁定

完整表见 **`docs/HANDOVER.md` §7**（不要重开）。最近几条：

* **D17（Cowork 05:40）：p.24 第一格 `0 → u_1` 不是数学缺口；不削弱结论、不改论文（T251a 的论文改动不采纳）。** T249 的反例只否定了「对**每个** ω」的时间模；它需要 `‖X(ω)‖ = v^{−1/2} → ∞`。限制在 `Good N = {‖X‖ ≤ N}`（`Gauss.exists_highProb_normX`）上，第二预解式恒等式 `G_v − G_w = G_v[(√w−√v)X + (z_v−z_w)]G_w` 直接给出**包含 0 在内**的 Hölder-1/2 模：`‖G_v − G_w‖ ≤ η_v⁻¹η_w⁻¹(N·|v−w|^{1/2} + |z_v−z_w|)`，对 `v, w ∈ [0, t_N]` 一致；loop、`K_u`、`T_{u,D}`、`farChi` 对 `u` 都是多项式常数的 Lipschitz，所以 `J = jSfarSm` 在事件上满足 `|J_v − J_w| ≤ N^{Kmod}|v−w|^{1/2}`（`Kmod` 依赖 `D`，`γ = 1/2`），`mesh_fine`/`card_le` 仍是多项式。T249/T251 的「`{‖X‖ ≤ N}` 仍含 `X = v^{−1/2}A`，事件救不回来」不成立：那只在 `v ≥ N^{−2}` 时发生，此时右端 `N^{Kmod}v^{1/2} ≥ N^{Kmod−1}` 压过包络级的跳跃。这正是论文 (5.46) 默认使用的「高概率连续性」。**做法**：`EntryModulusEvOn`/`CutHypEvOn` 取 `Good = {‖X‖ ≤ N}`、`γ = 1/2`，**不要** `WindowLeft`；合并总装回到 `Thm221NoEL X κ`（不是 `Thm221NoELFrom`）。T256 改为：编译这条 Hölder-1/2 事件模（第 0 格的非退化见证）+ 一条证书说明 T249「事件救不回来」的说法为何不成立；若编译中发现反例，停下报 Cowork。
* **D16 → (i)**（Cowork）：`NonAlt514` 在矩路线上重证，不引用 `SumZeroDyn.Hierarchy`（其 `mart :=` 残差是 fiat）→ T236。
* **#155 → `C_{n,p}`**（Cowork）：论文 (5.103) 印有 `C_n`，(5.24) 写作 `C_{n,p}` → T231。
* **论文改动第 6–17 条全部经 Jun 确认**（`docs/cowork-paper-edit-budget.md`）。
* **T233 转交的 C1**（Cowork 03:05）：验收条「字面不再出现不带撇 `FlowEq548`」与「旧签名不改」冲突时，**以旧签名不改为准**；验收的实意是「Theorem 2.21 的链上没有一步经过不带撇版」，T233 已达到。不动冻结签名。
* **T233 转交的 C2**（Cowork 03:05）：`FlowEq548Sm`/`nearChi` 与 `Thm221NoEL` 之间缺一个同时 import 两边的下游文件 → **T239 总装单**（新建文件，只 import 不改上游；此后第一遍的具名假设都往这个文件里收口）。
* **T233 转交的 C3 = 本次文档瘦身**（Jun 同一时间提出）：见本文件开头的读法。

* **T231 转交**（Cowork 03:15）：plain 路线 `hQV` 的签名适配 → **T240**；两条旧 `momentIneq(Q)_of_derivBound` 的 `@[deprecated]` **等消费者都换完带撇版再加**，由换掉最后一个消费者的单一并加。

## 2a. 调度纪律（协调者自采，Jun 2026-09-22「最近的工单都没有完成、而是提出意见」之后）

1. **不接受「第 0 步交判断就收工」，除非判断是否定的**——判断为正就当场接着实现，不交回来再派一轮。
2. **每张单的验收多一条：「这张单让主链上哪一条具名假设减少了？」** 只在自己文件里加定理、不减少主链假设的，不算完成。派单 prompt 要贴主链当前假设表（**完整的一份在 `docs/reports/T239.md`**）。

3. **能自己做的不要交回来**——只有别人的文件、范围/论文决策、真实数学缺口才交回（Jun 2026-09-22）。
4. **跑过约 30 分钟先交中间报告**，写清卡在哪、已编译出什么、下一步试什么；协调者收到后要么给指导要么重新定范围，**不能只是等**（Jun 2026-09-22）。

（详见 `docs/agent-playbook.md` 第十二、十三节。同批里 T238/T239/T240 就是这个形状。）

## 2b. ⚠ 需要更正的过时记载（T234 查出）

STATUS 的「T227 无主项 2」、T205 无主项 3、TASKS 的 T234 行都把 `hKd` 记成「`c(1−v)ℓ_vN^τ ≳ D log N`，真数学缺口」——**错**。`cor35Rate` 是 `c₀√δ/4`（根号），见 `docs/reports/T234.md` 第 0 步。另：建议给 `exists_loopDecay_Kval` 加 `@[deprecated]` 指向 `loopDecay_Kval_quant`。

⚠ **运维**：**scratchpad 路径不是每会话隔离的**——T234 的探针被并发 agent 覆写，造成一次**假的 `Unknown constant`**。派单 prompt 起从下一批要求**探针文件名带工单号**。

## 3. ⭐ T230：Step 2 第一遍自举——路线 (B) 被编译否定，改走 (A′)

**第 0 步结论**（`Gauss/Step2Bootstrap.lean`，未入库时见工作树）：
* `J*` 确有确定性多项式包络（`exists_jS_envelope`；`tailT` 带 `W^{−D}` 地板）。
* **路线 (B)（无条件矩界 + 高概率前缀 + 包络付坏事件）不可行**，而且不是截断的问题：坏质量沿网格**几何放大**——一步给 `ρ_{k+1} ≤ ρ_k(1 + (env/c)^{2p}) + M/c^{2p}`，`c < env` 使放大因子 `≥ 2`，`O(log(1/g))` 步后界超过 1（`routeB_walk_vacuous`）。换 `p` 无济于事。**Cowork 先前向 Jun 推荐的正是 (B)，此处更正。**
* **(A′) 不在两条否定结论的射程内**：前缀指示换成光滑权重之积，权重是高斯矩阵 `X` 的函数、不依赖当前 `u`，Stein 在全测度上成立，**没有坏事件项**，递推是线性的（`bootBad_le_of_q_zero`）。文件明说「这不是 (A′) 可行的证据」。

**Cowork 裁定（03:05）：T230 继续走 (A′)**。建议权重直接取
`∏_{j<k} ∏_a χ(|lk_{u_j,a}|² / (Θ·T_{u_j,a})²)`（代替 `χ(J*/Θ)`：`|·|²` 光滑，避开 `max` 与绝对值的不可微）。实现前先交一页只读设计：Stein 需要的正则性、`matrixStein` 现有签名是否够用、`∇` 项在过渡带上的先验界从哪来。

**Cowork 04:05 对 (A′) 的两条技术补充（更正我 03:05 的建议）**：
1. **权重不要取「逐项截断之积」`∏_{j,a}χ(…)`**——它的梯度是对所有 `(j,a)` 求和，网点数 `N^C` × 指标数 `L^2` 全部进来（基数损失），交叉项压不住。改取**一个** ℓ^q 软最大值：`J̃_k := (∑_{j<k}∑_a (|lk_{u_j,a}|/T_{u_j,a})^q)^{1/q}`，`q ≍ log N`，权重 `w_k = χ(J̃_k/Θ)`。`J̃` 与真 max 只差 `e^{O(1)}` 倍，其梯度是各项梯度的**凸组合**（系数和为 1），没有基数损失；`|·|^q` 在 `q ≥ 2` 时光滑。
2. **(A′) 新出现、论文里没有的一项**：Stein 在 `E[w_k·|Ψ_u|^{2p}]` 上多出交叉项 `E[χ′(J̃/Θ)Θ^{−1}⟨∇_X J̃, S∇_X|Ψ_u|^{2p}⟩]`（早时刻 `u_j` 与当前时刻 `u` 的混合协变差）。Cauchy–Schwarz 拆成两个**同时刻**二次变差率之积，Young 后多一个 Grönwall 项 `Θ^{−2}·sup_{v≤u} QV-rate_v(J*)`。粗估（在 `J̃ ≤ 2Θ` 的支撑上用 (5.42)/(5.44)，`Θ ≍ (η_s/η_t)^4`、`t−s ≲ η_s`）：近场 `≲ R^{7/2}/R^8`，远场 `≲ R·A^{−1/3}R^4`，由 (2.72) 都 `≲ 1`，所以 Grönwall 因子 `O(1)`。**请 T230 在只读设计里把这条逐项核实**（这是 (A′) 能否闭合的关键估计）；**Jun 2026-09-22 04:10 确认（「yes」）：交叉项按「两个同时刻二次变差率之积」估计是对的，门槛取 `Θ ≍ (η_s/η_t)^4` 合适。** 仍须 T230 在只读设计里逐项编译核实，作者确认不代替证明。

**T230 中间报告（04:47 UTC，约 110 分钟，`Gauss/Step2Bootstrap.lean` 511 → 1332 行，34 条声明，单文件与模块 `lake build` 均 exit=0、公理干净）**：

* ⭐ **`CutHypCond.condMoment` 变成定理** `condMoment_of_weightedMoment`，其前件 `WeightedMoment` 是**全测度积分**、没有任何 `∫ … in Ξ` 项——这正是 (A′) 的结构性收益，也是 Stein 能作用的唯一形状。链上剩下的自由项是 `WeightedMoment` 本身，**是替换不是追加**（两条路线都没有新增自由字段）。⚠ 但 `APrimeHyp → CutHypCondEv → MomentHypCutEv` 的结构接线（~20 字段样板）**还没写**，所以「`cut` 由定理产出」目前是**字段级**而非结构级。
* **Cowork 04:05/04:15 的两条更正现在都有编译证据**：`abs_derivProd_le`（乘积权重的基数损失，`|Φ'| ≤ (15/8)Σ|ρ_j'|` 要对 `N^{Ccard}` 个网点求和）、`abs_deriv_softMax_le`（软最大值是**凸组合**，零基数损失）、`rpow_card_le_exp_one`（`q ≍ log N` ⟹ 损失 ≤ `e`）、`abs_le_two_mul_of_softW_ne_zero` + `cutChiD_softW_eq_zero`（支撑 `⊆ {Θ ≤ J̃ ≤ 2Θ}`，**每一项**都 `≤ 2Θ`）。
* **瓶颈被精确定位，且不是 `matrixStein`**：`matrixStein` 的签名够用；卡的是 `Gauss.hasDerivAt_integral_Phi` 要的 `TestFun`（`ContDiff ℝ 2` + `bdd₀/₁/₂`）。乘积权重在这里**根本进不去**——`J* = max_a |lk_a|/T_a` 是 max，C² 无从谈起，`hasDerivAt_cutProd` 的前提不成立；软最大值修好这一点（`J̃^q` 是多项式）。→ **已开 T250**。
* **唯一的真数学缺口候选**：对数型导数界 `‖∂_α lk_{u,a}‖ ≤ Λ_N‖lk_{u,a}‖ + (K 的确定性项)`。T230 判断是标准 `G∂G` 重排、不是障碍，但**库里没有**；⚠ 用现成的**绝对**界会把软最大值 `e^{O(1)}` 的优势吐回去。→ **一并归 T250**。
* **见证在 `R > 1` 上（验收条件达成）**：`sat_StepSide_gt_one` 八条约束**全部取等号**，`sat_StepSideSharp_gt_one` 同形，`sat_StepSide_two`（`x=1, R=2`）是数值实例；`one_lt_ratR` 证 `R = η_s/η_u > 1` 在窗口内部是常态（T222 的 `R = 1` 是塌缩情形）。
* **`N₀(ε,D)` 对 `k` 一致：是，按构造**（`∀ k ≤ cutNetTop` 写在 `∀ᶠ N` 内部），**没有新的一致性义务**。
* ⭐ **第 3 槽（T243/T245 的 `Ξ^{(L−K)}_{·,2}` 在 `A_s^{1/2}`）能一并覆盖、不用改一个字**：`condMoment_of_weightedMoment` 对一般 `J`、`lev`、`Θ` 陈述。**第 2、3 槽剩下的是同一个 `WeightedMoment` 障碍，不是两个。**
* **(A′) 的归约不碰 `modulus`、不需要 `s = 0` 那一格**（`prefNet` 是有限交，`measurableSet_prefNet` 只要每个固定时刻的 `J` 可测）。起点条件：`s_N` 落在窗口内且 `J_{s_N} ≺ 1`。**所以 T249 的反例不挡 (A′)。**
* **没有找到 (A′) 的否定结论**；§2/§3 的两条 no-go 确实够不到它（它们的核心假设是「坏事件质量被向前喂」，而 `condMoment_of_weightedMoment` 里根本没有补集项）。

**⚠ 退回给 Cowork 核实的一条**：交叉项粗估里的**近场 `≲ R^{7/2}/R^8` 与远场 `≲ R·A^{−1/3}R^4` 两个指数，T230 没能核到具体式子，明确表示不替 Cowork 背书**。它能核实的是这两项落进 `CutHypTheta.StepSide` 的哪两个槽：近场是 `q`（cap `q ≤ R²`，由 `Step2MomentStep.integral_nearInt_le` 经 `nearInt_fills_q_slot` **恰好填满、零余量**），远场是 `ε`（cap `ε·x^17R^10 ≤ 1`）与 `β/γ`；`A^{−1/3}` 与现有 `A ≥ x^17R^10` 的关系未验。`QV-rate` 的现成名字齐全：`Gauss.quadVar`（`MomentGronwall.lean:349`）与 `quadVarPairs`（:355），由 `quadVar_ukerObsT_eq_quadVarPairs` 相连；Cauchy–Schwarz 的 `quadVar` 版仓库里没有，T230 已接手自证（初等）。

**T230 中间报告 #2（05:01 UTC，本轮约 40 分钟，`Step2Bootstrap.lean` 1332 → 1912 行 / 79 条，模块 `lake build` exit=0、0 warning、59 条公理干净、`grep sorryAx` = 0，快照已入库）**：

* ⭐⭐ **`cut` 从字段级推到结构级**：`momentHypCutEv_of_aprime`（第一遍）与 `momentHypCut2Ev_of_aprime`（第二遍）**由定理产出**，输入 `APrimeHyp` **不含任何事件受限字段**。链上唯一的自由项是 `WeightedMoment`（全测度加权矩），它**替换**了 `condMoment`，没有追加字段。`APrimeHyp` 与 `CutHypCondEv` 逐字段相同，只有两处差别：`condMoment` → `W` + `weightedMoment`；`meas` 降到实际用到的 `Measurable`（T244 的 `measurable_lk` 正好供给）。
* **第二遍**：`Gauss/CutHypTheta.lean` 只读且没有 Ev 版，故在本文件新建 `MomentHypCut2Ev` 并把两个消费者逐字重证——**未新增假设**，第二遍仍不需要第二次 bootstrap、不需要第二个初值。⚠ `∀ N` 的原版 `MomentHypCut`/`MomentHypCut2` **故意不去满足**（T232 已证其 `modulus` 对随时间变动的 `J` 不可满足，满足它只会产出空真的东西）。
* **自己做掉了 `quadVar` 版 Cauchy–Schwarz**：`sum_gvar_mul_le_sqrt_quadVar`（仓库原先没有），即把混时刻协变差拆成两个同时刻二次变差率的那一步。
* **见证不是退化的**：`satAPrimeHyp` 用真软最大值权重（不是 `W ≡ 1`），功能 `J_u = 2u⁺` **真随时间变动**（T232 已证没有任何 `∀ N` 接口能承载它），`sat_satWval_eq_zero` 证明权重确会归零，`one_le_satW` 里显式处理了 `N = 0` 且 `δ ≠ 0` 的 `0/0` 支。`R > 1` 的见证仍是 `sat_StepSide_gt_one`（八条约束全取等号），两者互补。
* **交叉项的 Grönwall 收口只等 T250**：拆分（`sum_gvar_mul_le_sqrt_quadVar`）与导数界（`abs_deriv_softMax_le`）两块砖已备好，装配需要 T250 的 (i) 对数型界 + (ii) `TestFun` 先落地。**T250 是 (A′) 当前的关键路径。**

**T230 中间报告 #4（05:20 UTC，`Step2Bootstrap.lean` 2242 → 2387 行 / 73 条，模块与 `APrimeTestFun` 均 exit=0、公理干净、`sorryAx` = 0，快照已入库）**：

* **§12 已改写，接受 T250 的反驳。** 文件里现在明写那条纯乘性目标**被反驳**及其机制（`L = K` 的 Hermitian `M` 处右端为 `0`，而 `∂_α(L−K) = ∂_α L` 无理由为 `0`；**`∂K = 0` 让情况更糟不是更好**），展示签名换成仿射版；`LogDerivBound` 的 docstring 带 ⚠「语句本身对，但**在 loop 上无实例**，保留只因它是 `abs_deriv_softMax_le` 的字面前件」。
* ⭐ **并把「软最大值买到什么」这句话改对了：不是因子 `Λ`，是没有 `card`。** 朴素路线给 `card·K`；`sum_abs_pow_pred_le` 给 `card^{1/(2r)}·K`，再经 `rpow_card_le_exp_one` 在 `q ≍ log N` 处降到 `e·K`，**`Λ = 0` 时照样成立——而模型正好落在这一支**。乘积权重做不到（`abs_derivProd_le` 就是一个裸的网格求和）。`logDerivBound_gives_softMax` 里原先那句「绝对界严格更弱」**是错的，已删改**；文件头 Main results 同步标注。
* **§16 是 (A′) 侧最后一块接口砖**：`weightedMoment_bound_of_sq` / `_of_oneStep` / `_of_oneStepSharp` / `weightedMoment_mono`，与 T222 的 `condMoment_of_oneStep` 一一对应，只是把条件积分换成全测度加权积分（两边右端同为 `C·(N^{δ/2·p}·Θ^{2p})`，故 `rpow_sq_pow`、`stepRhs_div_le` 原样可用）；**锐版与钝版同一个损失指数**。
* **交回一条，原因是 import 方向不是范围**：模型级 `BddC2C` 实例。T230 验过 `BddC2C`（在 `Gauss/LoopC2.lean`）、`lkFun`、`LoopC2` 在 `Step2Bootstrap.lean` 里都是 `Unknown identifier`，而给共享文件加 import 是结构性改动它不自己决定；且常数还要 `Flow/Hypotheses.lean` 的东西（反方向）。⚠ **注意 `APrimeTestFun.lean` import 了 `Step2Bootstrap.lean`，所以 T250 的四条修复件全在 T230 的下游**——装配只能在下游做。→ **已开 T255**。
* **链上每一环现在都有名字，只差那一个实例**：`hsum` ← `bddC2C_pow_real` + `bddC2C_sum`；`hΨ` ← `LoopC2`；`TestFun` ← `testFun_softW_mul`；生成元恒等式 ← `hasDerivAt_integral_Phi`；`∇χ` 项 ← `abs_coordD1_le_affine` + `abs_deriv_softMax_le_affine`（`Λ = 0`、`K = a₁‖B_α‖`）；交叉项拆分 ← `sum_gvar_mul_le_sqrt_quadVar`；收口 ← `weightedMoment_bound_of_oneStep`。
* **状态未变的部分**：`MomentHypCutEv.cut` / `MomentHypCut2Ev.cut` 由定理产出；事件限制版 `APrimeHypOn → APrimeHyp(onEvent) → stochDom_of_aprimeOn` 已通；见证 `satAPrimeHyp`（软最大值权重、时间相关 `J`）与 `sat_StepSide_gt_one`（`R > 1`、八条约束全取等号）都在。链上唯一自由项仍是 `WeightedMoment`。起点条件仍是 **`s_N > 0`（应用中 `s_N ≥ N^{−C}`）+ `J_{s_N} ≺ 1`**。


**T255 交出的三条阻塞（(A′) 现在卡在这里）**：

1. ~~**Ω-桥**~~ —— **T259 已解除：它在定义上就成立**（`Gauss.sample_H` 是 `rfl` 且早已具名），T255 的诊断有误。原文：⭐⭐ **Ω-桥（结构性，纯接线但跨文件）**：`WeightedMoment P J s t …` 量化在**抽象** `(Ω, MeasurableSpace, P)` 上、`J` 来自 `RBM.Sample B`（`Flow/Hypotheses.lean:225`）；而 `hasDerivAt_integral_Phi` 活在**具体**高斯系综上 `∫ ω, Φ (Hflow d N s ω) ∂(P d)`（`Gauss/Generator.lean:803`）。**全仓没有任何引理把 `X.H N u ω` 与 `Hflow d N u ω` 认同**，也没有把生成元恒等式搬到 `Sample` 上的东西。→ **已开 T259**。
2. ~~**`J*` 是 `Finset.max` 不是软最大值**~~ —— **T259 已解除**（双边比较 + `card → e`）。原文：**`J*` 是 `Finset.max` 不是软最大值**（`Hierarchy/Step2.lean:642`）：软最大值只经权重 `W` 进来，而**模型指标集上 `jStar ≤ softMax r S ρ` 的比较全仓没做过**（`le_softMax`/`softMax_le` 只有抽象版）。→ **一并 T259**。
3. ⚠⚠ **近场 `≲ R^{7/2}/R^8` 与远场 `≲ R·A^{−1/3}R^4` 两个指数：T230 与 T255 两次独立拒绝背书**，都说无法从论文 §5.3 重建出那两个显示式。仓库里唯一产出第 7 步形状的是 `CutHypTheta.sat_oneStep`，那是 `J ≡ Θ ≡ 1` 的**平凡见证**。**这条必须由 Cowork 给出可核实的推导**，否则 (A′) 的最后一步没有落点。

## 4. 待 Jun 定夺

* ~~**p.24 网格的第一格 `0 → u_1` 是真数学缺口**~~ —— **Cowork 05:40 的 D17 已裁定：不是缺口**（见 §2）。事件限制版的 Hölder-1/2 模包含 `0`，`T251a` 的论文改动**不采纳**，合并总装回到 `Thm221NoEL X κ`。T256 已按新验收四条改向。协调者独立核过那条算术：反例需 `‖X‖ = v^{−1/2} ≤ N` 即 `v ≥ N^{−2}`，此时右端 `N^{Kmod}v^{1/2} ≥ N^{Kmod−1}`，取 `Kmod ≥ D−1` 即压过 `W^{D−2} ≤ N^{D−2}` 的跳跃——**站得住**。

## 5. 在飞与排队

见 `docs/TASKS.md`（只剩活跃单）。**截至 04:21，六条车道全满**：**T230 (A′)**（最高优先）、**T245**（总装合并 + `modulus` 换 `EntryModulusEv`）、**T246**（`hDec*` 换线）、**T247**（`hcont`/`hintU1`/`hintU2` + 下沉）、**T248**（三处逐字重复上移）、**T249**（`CutHypEv.modulus` 在 `s ≡ 0` 的反例 + 带撇接口）。T217 归 Codex；T159 已认领（等总装）。本轮完成并入库：T232/T235/T236/T237/T240/T241/T242/T243/T244。**T245–T249 的可写文件集两两不相交**，各行「状态」栏已写明认领的文件与隔开方式。

## 6. 最近完成（每条 ≤ 8 行；完整报告在 `docs/reports/` 或 `docs/archive/STATUS-2026-09-19_22.md`）

* **T259**（本次，新建 `Gauss/SampleFlowBridge.lean` 511 行/20 条）：⭐⭐ **Ω-桥在定义上就成立——T255 的诊断是错的**。`RBM.Gauss.sample_H : (sample d).H N u ω = Hflow d N u ω := rfl` **早就存在**（`Gauss/Model.lean:413`），`band_P`/`sample_G`/`sample_Lval`/`sample_ELval` 同；没有约定差、没有包装差、不需要新假设。真正缺的是**复合**（`lk_eq_loopObs_sub`，两行证明）。⭐ **`jStar ↔ softMax` 双边比较做出来了**，`card` 经 `card_loopArg_two` + `rpow_card_le_exp_one` **降为常数 `e`**。⭐ **甲乙合流**：`testFun_softW_jS` + `hasDerivAt_integral_softW_jS` 让生成元恒等式直接站在模型自己的 (5.29) 族上、写在 `Sample`/`band` 词汇里；`abs_cutTrunc_jS_pow_le` 把 `WeightedMoment` 那个不可微的 `sup'` 用光滑对象**逐点压住**。**七步里 1–4 与两条结构性阻塞全部解除**；余步 5（`∇χ` 接进 `u`-Duhamel）、步 6（模型侧 `quadVar` 率）、步 7（两个指数 → Cowork，第三次）。报告 `docs/reports/T259.md`；paper-delta T259a。

* **T256**（本次，新建 `Flow/FirstCell.lean` 300 行 + `Step345Producer.lean` §13，审计 13092）：⭐ **结论恢复 `Thm221NoEL`**（`thm221NoEL_of_inputs_mergedOnAll_gauss`，`WindowLeft` 从槽 3、6 删掉，p.24 网格从 `u_0 = 0` 跑完），并证明新表蕴含 T251 的旧表。⭐ **包含 `s = 0` 的 Hölder-1/2 预解式模仓库本来就有**（T106 的 `Gauss.norm_green_flow_sub_le`，对 `u,u'` 无正性假设），已包装成事件版。⭐ **D17 为什么对，它给出了真正的理由**：`t249_witness_norm_gt` —— **T249 已发表那条反驳的见证落在 `{‖X‖ ≤ N}` 之外**。⚠⚠ **但它同时发现 D17 在现有编码下还不能用**：`EntryModulusEv(On)` 把 `(Kmod,γ) = (1,1/2)` 写死在 `def` 里，而 **T249 的 `gap_lower` 丢了一个因子 `W`**（`gap_lower_W` 捡回后跳跃 `≍ W` 发散），故在 `v = N^{−2}` 处 `Kmod = 1` 仍被打掉，要 `Kmod ≳ D`。**D17 数学上成立，但必须先把指数参数化**（→ T258，已转达，含下游代价 `mesh ≥ N^{2Kmod}`、`Ccard = 2Kmod+1`）。报告 `docs/reports/T256.md`；paper-delta T256a。

* **T255**（本次，新建 `Gauss/APrimeRatioBdd.lean` 516 行/16 条，审计 13081）：(A′) 的分析前提**步 1–4 全部编译**（`hsum`/`hΨ`/`TestFun`/生成元恒等式），步 5 的模型侧输入也有了。⚠ **工单的字面第 1 步是假的，它编译了反驳**：未取幂的 `‖F‖/T` 的 `BddC2C` 可反驳（`z ↦ ‖z‖` 在 `0` 不可微且 `0` 取得到 = `L = K`，**与 T250 反驳乘性导数界同一配置**）——改在 `^(2r)` 层交付，什么都没损失。⭐ 另证**不带 `card`** 的逐点梯度 `norm_fderiv_sum_ratio_pow_le`。**`WeightedMoment` 仍未产出**，三条具名阻塞见 §3。报告 `docs/reports/T255.md`；paper-delta T255a。

* **T252**（本次，新建 `Gauss/LoopLipschitz.lean` 1120 行 + 下沉，全量 exit=0、审计 13057）：⭐ **loop 级时间模做出来了**——`norm_lk_sub_le_lip`，`‖lk_v − lk_w‖ ≤ |v−w|·lkLip`，**对每个 `ω` 成立且完全不需要 `‖X‖` 的界**（`mul_green_smul` 消掉 `X`），**`γ = 1` 不是 1/2**，`Kmod = 1 + C + D`。⭐ **`hsep_exampleGrow`：T249 的否定判决现在对一个真实模型成立**，不再只是条件性的。⚠⚠ **查出一个会挡住所有人的定义缺陷**：`EntryModulusEv` 把 `Kmod = 1`、`γ = 1/2` **硬编码在 `def` 里**，诚实常数 `N^{1+C+D}|v−w|` 在宽度 `≥ N^{−C}` 的窗口上填不进去——**`Kmod`/`γ` 必须参数化**（→ T258）。下沉按裁定做完（四条纯预解式引理进 `Gauss/`，原处留探针 + import，T249 §10 未动）。报告 `docs/reports/T252.md`；paper-delta T252a。

* **T251**（本次，+630，全量 exit=0、审计 13035）：⭐⭐ **「`s ≡ 0` 那一格要不要」的答案是「要，而且这条链供不出来」**。p.24 归纳 `boundsGrid_of_fields` 对**每一对**相邻格点施加 `step`（`k = 0` 含在内，`u_0 ≡ 0`），而 T249 已证那里的 `modulus` 为假；`not_windowLeft_gridT_zero` / `windowLeft_gridT_succ` 两条编译证书钉死了这一点。**合并总装的结论因此从 `Thm221NoEL X κ` 降为 `Thm221NoELFrom X κ C`**，残项就是 p.24 网格的唯一一格 `0 → u_1`。⚠ **`BoundsCore_zero` + (2.67) 补不上**——它给的是左端点**数据**，缺的是那一**步**，而 `u_1 ≍ 1` 不是短窗口。**真数学缺口 → T256。** 槽 3、6 加 `WindowLeft s C` 与事件，槽 2/4/5 刻意不动；旧签名一字未动，证书齐（新表被旧表蕴含、`Good = univ` 处新包即旧包、`eventually_nonempty_of_highProb` 是反空真闸门）。报告 `docs/reports/T251.md`；paper-delta T251a（⚠ **需改论文**）。

* **T253 / T254**（本次）：⭐ **T253 四条 `hErr*` 全部关掉**（`exists_uniform_errBudget`，接口探针逐字核对，**`T246a` 销掉**），而且**工单预设的紧性路线是不必要的**——`commErr`/`dotErr` 的指数是 `c₀(ℓr·K)/ℓr`，**`ℓr` 精确消掉**。⚠ **它订正了 T246 的一句话**：`δ'` 不是处处超多项式小，`qBlockErr` 自带的 `L^k·δ·(C/ℓr)^k` **没有指数因子**，任何 `δ'` 都至少 `N^{O(n)}·δ N`（不影响能否卸掉，`D` 自由；影响 `hnum` 的记账）。⭐ **T254 Case 1 换线完成**：`hDec*` 三行的 `∀ ω` 与 `hΞm` 都没了（在 `measCore` 处实例化，**一个 `refine`**），**并比要求多做一步**把 `hEnv*` 也移上事件（Case 2 做不到）；确认 **Case 1 不需要 `hErr*`**。两单的旧签名都字节不变。报告 `docs/reports/T253.md`、`T254.md`；paper-delta T253a、T254a（并关闭 `T236a`）。

* **T250**（本次，新建 `Gauss/APrimeTestFun.lean` 714 行/30 条，审计 12934）：⭐ **(A′) 的 `TestFun` 实例造出来了**（`testFun_softW_mul`）；`ContDiff ℝ 2` 查过**确实被用满**，于是证二阶而不是弱化。⚠⚠ **同时编译反驳了 T230 §12 的目标签名**：纯乘性的「对数型」导数界 `‖∂_α lk‖ ≤ Λ‖lk‖` **是假的**——`L = K` 的 Hermitian `M` 处右端为 `0` 而 `∂_α L ≠ 0`，且 `∂K = 0` 让情况**更糟**（`not_coordD1_le_mul_norm`、`not_logDerivBound_of_zero`）。⭐⭐ **更重要的是它纠正了我们对「对数型」价值的误判**：那个 `≺`-内容**从来不是因子 `Λ`，而是「没有 `card`」**——`sum_abs_pow_pred_le` 把朴素路线的 `card·K` 变成 `card^{1/2r}·K ≤ e·K`，**`Λ = 0` 时照样成立**。修复 `abs_deriv_softMax_le_affine` + `abs_coordD1_le_affine` 已交给 T230。报告 `docs/reports/T250.md`；paper-delta T250a。

* **T230 (A′) 中间报告 #3**（`Step2Bootstrap.lean` 1912 → 2242 行 / 79 条，快照入库）：新增 `APrimeHypOn`（事件限制版，照 T249 的 `CutHypEvOn` 装置：`weightOn` 在 `Good` 外取 `1`、`toAPrimeHyp` 走 `onEvent`、`stochDom_of_aprimeOn` 多付 `N^{−1}`）。**明确结论：`s_N > 0` 不被 `APrimeHyp` 任何字段蕴含**（`window`/`lev_ge`/`levpoly`/`card_le` 逐条查过），必须由生产者给；起点条件逐字是「`s_N > 0`（应用中 `s_N ≥ N^{−C}`）+ `J_{s_N} ≺ 1`，没有别的」，且 **(A′) 自己的归约既不碰 `modulus` 也不碰左端点**——T249 的病根在这条链上是**上游继承**。⚠ **踩到并修好一个 `p = 0` 坑**：`weightedMoment` 量化 `∀ p : ℕ` 含 `p = 0`，那里被积函数退化成权重本身、`Good` 外 `weightOn = 1 > W`，逐点压制失效；`toAPrimeHyp` 分了 `p = 0` 一支并把实例要求提到 `IsProbabilityMeasure`。**同型的 `∀ p` 字段别处也有，值得一并查。**

* **T249**（本次，+1028 行，审计 12791）：⭐⭐ **空真第 12 例，而且打在主链上**——`CutHypEv.modulus` 在 `s ≡ 0` 上 `¬Nonempty`（`not_cutHypEv_swapSample_of_far`）。机制：`H_0 = 0` ⟹ `J*^{sm}_{0,D} ≡ 1` 对所有 `ω`，于是左端取 `w = 0` 时「模」退化成绝对界；再用块对换对合 `blockSwap` 造 `swapSample` 让 `K_v` 两边抵消，得到**与 `v` 无关**的下界 `W⁻¹‖1−z_v²‖⁻²/2`。⭐ **病根是 `∀ ω` 不是 `∀ᶠ N`**：`ω` 自由则 `H_v = √v X(ω)` 在任何 `v > 0` 都跑遍全部 Hermitian 阵。**比 Cowork 的论证更强更便宜**（不需要跨块量级估计、不需要 `K` 的界）。**同时解答 T245 的追加问**：`EntryModulusEv` 做不出非退化见证是因为它在那里为假。正面替代：`norm_green_sqrt_sub_le_lip`（**所有 `ω`、不用 `‖X‖` 的界**，`Kmod = C`、`γ = 1`）+ `CutHypEvOn`（`onEvent` 在 `Good` 外置 0 ⟹ **下游零重证**）。⚠ **两者缺一不可**：`{‖X‖ ≤ N}` 仍含 `X = v^{−1/2}A`。报告 `docs/reports/T249.md`；paper-delta T249a。

* **T246 / T247 / T248**（本次）：⭐ **T246**——`rhs514QAt_of_kernel_inputs'` 的衰减行全部变成 `∀ ω ∈ Ξ N`（`Ξ` 不带可测性），**`hDecC`/`hDecD` 整条消失**（`commS`/`dot` 根本不要衰减）；查出真陷阱：那批常数必须是 `ℕ → ℝ`，否则 `commErr` 的因子 `L` 使之**不可满足**。工单预判的两个难点都不存在。⭐ **T247**——`hcont`/`hintU1`/`hintU2` **三条全关**，且先查过「阶数多了没有」，三条恰好是实际用到的阶；**`Bounds` 在 `s > 0` 的残余 7 → 4 组，假设表里没有一条是分析性的**；连续性链与 T244 的可测性链同构，只写了粘合。⭐ **T248**——三处逐字重复上移，`rfl` 探针同时挡住变强与变弱；**共删 151 行**（65 + 协调者按清单删的 86）；`Pr` 一般化不造成空真（责任转给消费者，两个实例都有可居见证）。报告 `docs/reports/T246.md`、`T247.md`、`T248.md`；paper-delta 仅 T246a。

* **T245**（本次，`Flow/Thm221Assembly.lean` §8 + `Flow/Step345Producer.lean` §§6–8，+599 行纯插入）：⭐ **一份总装里四槽同时关掉**——`Gauss.thm221NoEL_of_inputs_merged_gauss` 的表里 `Step1.Hyp`/`hΘ`/`Eq45Flow`/`Eq548EntryData.init` 都不出现，`Eq548EntryDataEv` 从五字段降到三。`git diff` **无删除行**，既有签名字节不变。见证 `Gauss.thm221Merged_witness`（p.24 网格第一步上三个生产者同时触发、窗口不塌缩、`init` 临界）。⚠ **两条更正**：(1) 工单说「只剩第 2 槽与 6d」是**太乐观**——第 3、5 槽**不是消失而是换成生产者的输入**，实际剩六项（2、3 残余、4、5 残余、6a、6c、6d，见报告表）；(2) 它没有把第 3、5 槽谎称成免费加强——`CutHypEv ⟹ hΘ`、`Eq45FlowInputs ⟹ Eq45Flow` 方向是**新的更强**，可接受的理由是**有生产者**，三条方向写在编译的 `thm221NoEL_of_inputs_merged_slots_imply_old` 里。报告 `docs/reports/T245.md`。

* **T244**（本次，`Flow/Eq548Producer.lean` 新建 27 条）：⭐ **`Eq548EntryData.meas` 无条件关掉**（`aestronglyMeasurable_jSfarSm`，对**每个** `Sample B` 成立；整条可测性链 `measurable_H → green → Gsig → 矩阵乘 → gloopProd → trace → Lval → lk → lkFarSm → Finset.sup'`，矩阵逆那步复用已有的 `measurable_matrix_inv_apply`）。附带：`measurable_Lval`/`measurable_lk` 是本仓第一批**一般 `Sample`** 上的可测性结果，`MomentHyp.meas` 与 `CutHyp*.meas` 现在都只差一步 `Finset.sup'`。`near` 接到 T207 锐版 (5.47)。⚠⚠ **`modulus` 按字面证明为假（空真第 11 例）**：`N = 0` 处右端 `(0:ℝ)^1·|v−w|^{1/2} = 0`，于是「模」变成「对每个 `ω`、每个标签对，`v ↦ ‖(L−K)_v‖/T_{v,D}` 在整段上恒定」的等式约束（`not_entryModulus_of_jSfarSm_ne`、`not_entryModulus_of_ratio_ne`）；**且第二个独立缺陷**是它仍对所有 `ω` 量化而所乘因子只 `≺ 1`（`entryModulus_uniform_in_omega`）。修复 `EntryModulusEv` + 整条替代路 `flowEq548W_of_sharp_entriesEv`（改走 T232 的 `CutHypEv`），**这条路上只剩 `hmoment` 与 `hinit` 是输入**。退化窗口上该字段确实成立（`sat_entryModulus_of_window_point`），所以否定是**锐的**——病在 `∀ N` 这个量词。报告 `docs/reports/T244.md`。

* **T241 / T242 / T243 / T235**（本次）：⭐⭐ **T239 假设表六槽里关掉了四项，而且四项是同一个病因**——生产者需要的 `BoundsCore X E s` 就是 `Thm221NoEL.step` 自己的参数、在下一层 `boundsCore_step_of_inputs_reg_W` 已在作用域，被往上传时丢掉了。**T242**：`Step1.Hyp` 的四个字段**一个都不缺**（早由 `step1Hyp_gauss_of_scale''` 总装好），差的只是那个前件；交出 `s > 0` 的非退化实例，并说明**无条件的 `s > 0` 实例原则上不可能**（那正是上一步的结论）。**T241**：`init` 有了生产者 `stochDom_jSfarSm_init_of_boundsCore`，`Eq548EntryData'` 只剩四字段；带「新表更弱」的编译证书；证明只用 `farChi ≤ 1`，**对尖锐 `jSfar` 同样成立**。**T243**：第 3、5 槽都关掉（`hΘ1`/`hinit` 变成定理；(4.5) 三条输入零新数学），附反 fiat 检查 `eq45FlowInputs_nonfiat`（对任意 `x` 该束都推出 (4.5) 本身）。**T235**：(2.71) 从 Theorem 2.2 的假设表退役，13 个重复证明体（330 行）删除、全部配 `rfl` 探针；顺带审掉 `MomentHyp.env_le` 的 `∀ ω`——那是**数据字段**的存在性界（见证 `Step2Bootstrap.jS_le_rpow`），不是 T164 类缺陷。报告 `docs/reports/T241.md`、`T242.md`、`T243.md`、`T235.md`；paper-delta 仅 T235a（另三张纯接线、无偏离）。

* **T236 / T237 / T232**（本次）：⭐ **`NonAlt514` 从全仓删除**——(7.16) Case 1 在矩路线上重证（`Gauss/Lemma514NonAlt.lean`，27 条），`flow_sharpLmK_Q_of_hHol_flow` 的 `NonAlt514`+`h0`+`h12`+`h1`+`h2` **五项换一项** `hrhsNA`，且有生产者 + 网格见证（`gridS` 上常数**不含** `N`/`W`/`τ'`/`k`）；代价只有 `C = 3 → 5`。⭐ **`MeasurableSet (lkGood …)` 不必证**——T237 取**可测核** `(toMeasurable P Ξᶜ)ᶜ`（等测度 + 子集，故估计零变化），`momNorm_norm_lkT_le_of_event(_of_hyp)` 的 `hΞm` **彻底消除**，`hDec*` 的事件限制替代品四条编译在案（`Gauss/LkGoodMeasurable.lean`，35 条）。⭐ **T232 把「接口过强」证成定理**：对真随时间变动的 `J_u = 2u⁺`，`CutHyp.modulus` 的 `∀ N` 形式对**任何** `Kmod, γ` 都假（`N = 0` 处右端为 `0`），故 `¬ Nonempty (CutHyp …)`——`∀ᶠ N` 的弱化是**严格**的，小 `N` 特例本来就不存在；原结构未动（`Step2FarMart.lean:1782` 在消费它），新增 `CutHypEv/CutHypEv'/CutHypCondEv` 共 67 条。报告 `docs/reports/T236.md`、`T237.md`、`T232.md`；paper-deltas T232a/T236a/T237a。

* **T239**（本次）：**(5.48) 从 `Thm221NoEL` 的假设表里整条消失**（`Flow/Thm221Assembly.lean`，新的下游总装文件解决「两个 import 叶子谁都放不下那条桥」）。⭐ 交出**完整假设表 + 每条归谁**（见 `docs/reports/T239.md`，后续派单请照它写）。`CutHyp` 的 `mesh_fine`/`card_le` 由 `cutHyp_jSfarSm_of_entries` **证出来不是假设**，故那对拉扯条件**不可能联合不可满足**。⚠ 查出 `Eq548EntryData.init` 是**结构性多余**——它是 (2.68)/(2.69) 在 `u = s_N` 的推论、**只有拿到 `hB` 才能证**，而上游 `thm221NoEL_of_inputs_W` **没把已在作用域内的 `hB` 透给 (5.48) 槽**；加 `BoundsCore X E s →` 前件是**免费的加强**。
* **T238**（本次）：`driftF` 的逐点确定性包络——**`hFb` 与 `hGd_Qop_driftF` 两处由同一条定理供给**；`momentIneqQ` 的 11 项从「5 项无条件」到**只剩 3 项有条件**。⭐ **工单假设的「缺 `Kval` 一致有界」其实仓库已有**（T203 的 `exists_norm_Kval_le_upto`），**只读文件零改动**；另删掉自己重复写的 `one_le_inv_etaT`。⚠ 如实：包络**是粗的**（`η_v^{−O(n)}`），**够可积性但不能做定量估计**。paper-delta T238a。
* **T234**（本次）：⚠⚠ **`hKd` 不是数学缺口——T205/T227 读错了**：`cor35Rate δ = c₀√δ/4` 是**根号**在间隙上，衰减长度正是 `ℓ̂_v = (1−v)^{−1/2}`，于是 `cor35Rate(1−v)·ℓ_vN^τ = (c₀/4)N^τ`（`cor35Rate_mul_ell_mul`，间隙**精确抵消**），**没有 `D log N` 门槛**。`loopDecay_Kval_quant` **无条件、任意环长**，同时交付 T220 转来的环长 `n+2`。四个好集 **3 完整 + 1 部分**，`hlk` 也通；残余 **10 → 7 项**。好集非空**是证出来的**。完整报告 `docs/reports/T234.md`。
* **T231**（本次）：`hbound` 的常数落实成 `cMDval' p n = (n+2)·max 0 (2p−1)`，**两条桥各读一遍、都恰好是 `(n+2)`**。判别性编译在案：`hbound_slot_one_fails` 证明 `(n+2)` 形的界**推不出** `1` 形的界，**旧 `hbound` 按字面永远卸不掉**；`deriv_le_*_sharp_one'` 三条取**等号**，说明新常数**无余量**。**不用改 `MomentDuhamelTime.lean`**（`of_diffIneq` 本来就把 `cMD` 收成参数）。plain 一路走通（`momentIneq_gauss_cMDval'`，只剩 `hQV`）。⭐ 顺带解决一个工单没点名的缺口：**二次变差看不见 `K`**，所以不需要「移位版」桥。完整报告 `docs/reports/T231.md`。
* **T233**（fd81869）：Steps 4–5 的脚本全部改吃 `FlowEq548W`，三份脚本并成两份；12 条 `rfl` 探针；`FlowEq548` 的生产者一个没动。转交 C1–C3（见 §2）。
* **T219**（37f5581）：`hkerC`/`hker2C` 从 Lemma 5.14 的假设表里消失（D14 核心目标达成）；网格见证在论文 p.24 网格上。交出 D16。
* **T226**（3280616）：`Q` 版二次变差桥无自由假设，系数 `(n+2)`；可积性 11 项关 6 项；交出 `driftF` 包络（→ T238）。
* **T218 / T220**（c10539b）：`P` 半边接上矩路线；`hGd` 5/5；两条否定结论入库（无护栏 `PHalf514` 不可做；自由 `Ξ` 取 `∅` 即平凡）。
* **T222 / T225 / T229**（5cdd000）：Step 2 钝版自举的断点精确定位（前缀事件上的条件矩界；截断版替代路证否）；`Q` 版 `hbound` 卸掉、查出少 `(n+2)`（#155）；漂移侧全是定理、`M_qf(1−s) ≺ 1`。
* **T223 / T227 / T228**（bd259fe）：`xi2` 共轭修正落地（183 处穷举）；Step 6 包络量词修完（6 条）；`M_m` 整条线删掉（D15）。
* **T221 / T224**：去重合一；`hsplit`/`hdiff` 卸掉（Leibniz 自 T140 就有）。
* 更早的（T1–T216）：见 `docs/archive/STATUS-2026-09-19_22.md`。

* **T238 / T239 / T240**（45e293a）：`driftF` 逐点包络两处同源（`exists_driftF_envelope`，粗包络，够侧条件不够定量）；**(5.48) 从 `Thm221NoEL` 假设表整条消失**（`Flow/Thm221Assembly.lean`，完整假设表见 `docs/reports/T239.md`）；plain 路线 `MomentIneq` 闭合、只剩窗口条件（T240 查出旧 `hQV` 对 `u` 无窗口限制、很可能空真，已绕开）。
* **T234**：`hKd` **不是数学缺口**——`cor35Rate` 带根号，衰减长度就是 `ℓ_v`（(2.52)），`e^{−c₀N^τ/4}`；四个好集 3½ 个；`Bounds` 在 `s > 0` 残余 10 → 7。报告 `docs/reports/T234.md`。

* **T232 / T236 / T237**（321b3b4）：`NonAlt514` 从全仓删除，换成有生产者的 `hrhsNA`（网格见证、常数不含 `N/W/τ′/k`，`C = 3 → 5`）——**Lemma 5.14 的 `Q` 路线结构性缺口关掉**；`lkGood` 可测性用「可测核」绕过，`hΞm` 消除、`hDec*` 有事件限制替代品；`CutHyp` 的 `∀ᶠ N` 版 `CutHypEv(′)` 落地，**并编译证明 `∀ N` 版对 `J_u = 2u⁺` 不可满足**（空真第十例：原结构在小 `N` 上本就没有居民）——`Step2FarMart` 里消费旧 `CutHyp` 的那条须换到 `CutHypEv`（已写进 T244）。

## 7. 无主的活

（全部已开单。T239 的主链假设表逐槽分派：第 1 槽 `Step1.Hyp` → T242；第 2 槽 `MomentHypCut` → T230 (A′)/T232；第 3、5 槽 `hΘ`/`Eq45Flow` → T243；第 4 槽 `Lemma514` → T236；第 6 槽 `Eq548EntryData`：`init` → T241，`near`/`meas`/`modulus` → T244，`moment` → T230。新的无主项写在这里，调度下一轮开单。）

* ~~**`hinit` 可免费消除**~~ —— **T241 已做掉**（`Eq548EntryData'`）。⚠ **同型的第四处仍在**：`thm221NoEL_of_inputs_cutHyp` 还带一个独立的 `hinit` 槽，同一条 `stochDom_jSfarSm_init_of_boundsCore` 就能消掉（机械）。：给 `thm221NoEL_of_inputs_W` 的各槽加 `BoundsCore X E s →` 前件（`hB` 已在作用域内），`Eq548EntryData.init` 即可由 (2.68)/(2.69) 在 `u = s_N` 推出。**全仓没有任何 `hinit` 的生产者。** 这是假设表里唯一结构性多余的一条。
* **`Step2FarMart` 的 `meas`/`modulus`/`moment` 三条生产者**（T239 交出）；⚠ 其中 **`.modulus` 对尖锐 `jSfar` 为假**，只对平滑版有希望。
* **`hcont`/`hintU1`/`hintU2`**（T234 交出；**已开 T247**（原「T234 续」），同一单带上 `nonempty_of_highProb` 的下沉）：`E(L−K)` 的时间连续性 + `U` 对两个漂移张量的区间可积性。**纯分析，无主**——这是 `Bounds` 在 `s > 0` 处余下 7 项里唯一不属 Steps 1–5 主线或总装线的。
* **`nonempty_of_highProb` 重复两份**（T234 交出；**已开 T247**，随甲一起做）：`FastDecayFlow.nonempty_of_highProb`(:708) 与 `Step6EnvWindow.highProb_nonempty` **逐字相同**，而前者在后者**下游、无法 import**。**建议下沉 `Defs/StochDom.lean` 并删两份。**
* **两条 `attribute [deprecated]` 的落地时机**（T231 交出，→ Cowork）：`momentIneq_of_derivBound` / `momentIneqQ_of_derivBound`——等 T226 的后继换完带撇版，还是现在加并接受 `MomentDuhamelQInt` 里的一片 warning。确切语句见 `docs/reports/T231.md`。
* **`Rhs514QAt` 的事件限制版生产者**（T237 交出，**裁定 (b)**；**已开 T246**（原「T237 续」））：在 `Gauss/Lemma514QAssembly.lean` **原地**把 `rhs514QAt_of_kernel_inputs` 的五处 `momNorm_Uker_*_le` 换成 T237 的 `…_event_untrunc_le`，`hDec*` 改 `∀ ω ∈ Ξ N`，`hnum` 多吃一项 `Env·pr^{1/(2p)}`（`eventually_env_mul_lkGood_le` 已备好，难点是把「先定 `p`、再 `N→∞`」穿过 `∃ C`）。短的是区间可积性接线，**不是数学缺口**，估 200–300 行。顺带把该文件第 92、617 行「`MeasurableSet (lkGood …)` 未证」的注释改为指向 `measCore`/`measurableSet_lkGoodM`。
* **Case 1/Case 2 的三处逐字重复应上移**（T236 交出；**已开 T248**（原「T236 续」））：(1) `SumZeroDyn.norm_Uker_short_scale_le`（`Hierarchy/SumZeroDyn.lean:4232`）是新 `Gauss.norm_Uker_short_scale_le'` 的特例，一般版应上移、旧版改一行推论；(2) 同型存量重复 `Gauss.norm_Uker_sumZero_scale_le'`（`Lemma514Q716.lean:393`）；(3) `MomentDuhamel.stochDom_of_momentDuhamel`（`Gauss/MomentDuhamel.lean:485`）应一般化成「对任意可判定谓词守卫」，`NonAlt` 版成为实例。
* **`hEnvF` 不能直接吃 T238 的包络**（T236 交出）：包络界 `DriftDef.driftF`，那一行界 `H.F`，中间要 `F_unique_flow`（`Gauss/MomentDuhamelHyp.lean`），且 `cF` 依赖 `N`，只能吃成 `hMψ` 的一条真实矩界。
* **`bootPP_of_net_ev` 与 `MomentHypCut2Ev`**（T232 交出）：前者要改 `Hierarchy/Step2MomentStep.lean`（T232 只读），后者是 `MomentHypCut2` 的 `∀ᶠ N` 版（本轮只做到 `MomentHypCutEv`）。
* **`Step2Moment.MomentHyp.env`/`env_le` 的量词**（T232 交出）：文件当时由 T235 持有，未动。
* **把四处闭合合并进一份总装**（T241/T242/T243 交出，机械；**已开 T245**（原「T243 续」，并含 T241/T244 各一条））：`thm221NoEL_of_inputs_step345`（第 3、5 槽）、`thm221NoEL_of_inputs_entries'`（第 6 槽 `init`）、`Gauss.thm221NoEL_of_inputs_entries_gauss`（第 1 槽）各自闭合，但**还没有一份同时不含这四项的总装**。T243 当时 import 的是 `Flow/Thm221NoEL.lean`（因为 `Thm221Assembly.lean` 正被 T241 改、树里是红的），现在两边都绿了。
* **(4.5) 的三条输入只有高斯版**（T243 交出）：`Gauss.ibpFlow_of_unifDom`、`flucRowFlow_of_gain'`、`flucBlkFlow_of_gain'` 各自还带网格数据（`hΩ`、`hHol`、`hfix`）→ T124 的续。
* ~~**`EntryModulusEv` 是合并表里唯一做不出非退化见证的字段**~~ —— **T249 已解答：它在 `s ≡ 0` 的非退化窗口上为假**（`not_entryModulusEv_swapSample_of_far`）。原文：（T245 交出，归 T249）：它仍是随机模型上**对所有 `ω` 量化的确定性不等式**（CLAUDE.md 规则 1 的模式），`∀ᶠ N` 只挡掉了 T244 的 `N = 0` 反驳；唯一编译的见证 `sat_entryModulusEv_of_window_point` 是**塌缩窗口** `t = s`。不显然不可满足（固定 `N` 时 `‖lk‖/tailT` 有确定性界：`η > 0` 的 Green 函数 + `tailT ≥ W^{−D} > 0`），但**需要一遍专门的可满足性**。
* **`modulus` 的事件限制版是真的新数学**（T244 交出，**已开 T249**（原「T244 续」，Cowork 04:15 第 ② 条））：`‖(L−K)_u‖/T_{u,D}` 的 `HighProb` 受限时间 Hölder 估计，全仓无生产者。Cowork 04:15 给了方向（`s_N ≥ N^{−C}` 上可**对所有 `ω`** 直接证 Lipschitz，由 `G_u − G_v = G_u[(√v−√u)X − (z_v−z_u)]G_v` 与 `X G_v = (I + z_v G_v)/√v`，常数约 `N^C/s_N`，**不需要 `‖X‖` 的界**；第一步 `s ≡ 0` 需要 `{‖X‖ ≤ N}` 上的带撇接口，`hclose` 在该事件上重证），并**怀疑 `CutHypEv.modulus` 在 `s ≡ 0` 上 `¬Nonempty`**（反例 `X = M(E_xy+E_yx)`、`√h·M = 1`、`x`/`y` 隔远块：`G_h` 跨块 `O(1)`、`G_0 = −1/z_0`，远场 `J_h − J_0 ≳ W^{D−2}` 而 `N^{Kmod}h^γ → 0`）。**该字段同时影响第 2、3 槽**（T230 / T243 的 `CutHypEv`）。
* **`Step2FarMart.cutHyp_jSfarSm_of_entries` 还在造 `CutHyp` 而不是 `CutHypEv`**（T244 交出，**T245 已带上**）：单字段改动（`modulus := …` + `Eventually.of_forall` 套 `mesh_fine`），归 `Hierarchy/Step2FarMart.lean` 的持有者；协调者已按「把 `Thm221Assembly.lean` 的 `Eq548EntryData.modulus` 换成 `EntryModulusEv`」派单。
* **四条 `hErr*` 的确定性界**（T246 交出，paper-delta T246a）：要一个 `δ' N` 在 `u ∈ [s N, v N]` 上一致压住 `qopErr1`/`commErr`/`dotErr`/`qqErr`。由紧性 + `ℓ̂` 单调性**界存在**，但没证；属 `Gauss/FastDecayFlow.lean`，**确定性、无 `ω`、无模型输入**。
* **Case 1 侧的同一条换线**（T246 交出，做法已写清）：在 `Ξ := measCore B.P (Ξ N)` 处实例化 `momNorm_Uker_short_scale_le_on_event`，`hΞm` 消失且不引入新假设；然后把 `rhsNonAltAt_of_kernel_inputs` 的三条 `hDec*` 改成 `∀ ω ∈ Ξ N`。**那边不需要 `hErr*`**（该引理原样返回输入的 `δ`）。三项而非五项，估 ~250 行。
* **`cKerShort_nonneg` 是同型的第四处重复**（T248 顺带发现）：`Hierarchy/Decay.lean:969` 与 `Hierarchy/SumZeroDyn.lean:1200` 各一份（同名不同 namespace）。
* **`Gauss.stochDom_lkT_nonAlt_of_momentDuhamel` 的证明可从 19 行缩到 6 行**（T248 验证过的一行实例，签名不改）——不删重复、只缩证明，留给下次碰那个文件的人。
* **`MomentHypCut2Ev` 应下沉到 `Gauss/CutHypTheta.lean` 与 `MomentHypCut2` 并列**（T230 交出，纯机械搬运）：现在它定义在 `Gauss/Step2Bootstrap.lean` 里，因为 T230 对 `CutHypTheta.lean` 只读。这同时补上 T232 交回的那条同名无主项。
* **把 `CutHypEvOn` 接到四处真实槽上**（T249 交出，接法已写清）：第 2、3 槽在 `Gauss/Step2Bootstrap.lean`（**归 T230**，bundle 换成 `CutHypEvOn`、`Good N := {ω | ‖X(ω)‖ ≤ N}`、结论走 `stochDom_of_cutHypEvOn`，`moment` 字段一个字不改）；第 6c 槽与合并总装的 `Eq548EntryDataEv.modulus` 在 `Flow/Thm221Assembly.lean`（**无主**，逐项字段加 `ω ∈ Good N`，现成模板在 `cutHypEv_jSfarSm_of_entries` 的 `modulus` 字段）。⚠ **必须同时把窗口左端提到 `s_N ≥ N^{−C}`**。
* **乙还没接到 `Kmod`/`γ` 字段上**（T249 交出）：`norm_green_sqrt_sub_le_lip` 是**算子范数**级结论，要变成 `EntryModulusEv`/`CutHypEvOn.modulus` 还缺「resolvent → loop → `‖lk‖/T`」的转写；`Gauss.abs_llErr_sub_le` 是现成模板，loop 版要新写。
* **`hsep` 在具体 `Dims` 上的编译验证**（T249 交出）：`12(log W)^{3/2}(1−t₀)^{−1/2} ≤ L/2` 对大 `N`，纯 `log`-vs-幂初等估计，需要一个具体 `Dims` 见证。
* **`abs_coordD1_lkFun_le` 的重新陈述**（T250 交出）：加性常数要在模型里定死（`lkFun`、`band d`、`η_u`），涉及 `Gauss/MomentDuhamel.lean` / `Flow/Hypotheses.lean`。→ T230 或 Cowork。
* ⚠ **`∀ p : ℕ` 的字段普遍要查 `p = 0` 那一支**（T230 中间报告 #3 踩到）：`weightedMoment` 在 `p = 0` 处被积函数退化成权重本身，逐点压制失效。**全仓同型字段值得扫一遍**（`grep -rn '∀ p : ℕ' RBM1D/ --include=*.lean`）。
* **`Q` 路线与矩路线的 `hnum` 算术**（T253、T254 各交出一次）：两边的 `hnum` 都该**渐近**卸掉，而不是靠「把误差送到 0」（那个技巧在两边都退化：`cE N = 0` 逼出 `Env·pr^{1/q} = 0`）。T253 给了量级账本——指数部分 `poly(N)e^{−c₀N^τ/2}` 随便够，**非指数部分 `N^{O(n)}·δ N` 要靠 `D` 自由**（`n`、`τ₁` 在 `D` 之前固定）。归做 `hnum` 算术的人。
