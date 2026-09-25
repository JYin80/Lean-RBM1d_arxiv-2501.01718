# 论文逐条证明清单（2026-09-25 快照）

页面：https://claude.ai/artifact/KCWCVS4YQH9WrEffStsMgp 。完整数据（459 行，含核对依据）：仓库 `Claude outputs/ledger/paper-ledger-2026-09-25.json`。依据：09-25 工作区，全量构建 02:15 UTC 通过；7 个只读审计 agent 分节读 Lean 签名，Cowork 复核合并。

状态：已证＝只用论文自己的前提（证明中间步骤指推导已形式化）；仅特例＝exampleGrow/首格/E=0/D=60/固定时刻等；条件＝从未证的具名假设推出；换路线＝随机积分类陈述由矩/逐点替代接管；未证；外部输入；已定义。

命题 55：已证 18，已定义 15，条件 15，换路线 4，仅特例 3。公式 404：已证 187，条件 74，已定义 61，未证 29，换路线 28，仅特例 24，外部输入 1。

## 命题

| 编号 | 页 | 状态 | 说明 |
|---|---|---|---|
| Definition 2.1 | 8 | 已定义 | (i)–(iv) 均有定义。约定差异：概率空间 (Ω,P) 固定、N 依赖放入随机变量（paper-deltas #23，等价）；(ii) 取对参数一致版本；并集事件 ∃u 用外测度；(iii) 对任意 Norm 陈述。 |
| Theorem 2.2 | 8 | 条件 | 结论与论文逐字对应，但假设 Thm221NoELN' X κ（能量随 N 变、去 (2.71) 的 Thm 2.21）。高斯 Transfer 已证；Thm221NoELN' (sample d) 无任何 producer，固定能量 Thm221NoEL 也只在 CutHypEvOnSlot/Lemma514/Eq45FlowInputs/Eq548 假设下得到。STATUS：开放。 |
| Theorem 2.3 | 8 | 条件 | 对任意 z 序列（/Re z/≤2−κ，N^{-1+τ}≤Im z≤1）给出 (2.3)(2.4) 与迹律，能量切片已去除（SpecSeqN.of_z）；形式正确。但需 Thm221N（或经 boundsCoreN' 的 Thm221NoELN'）于 sample d，无 producer。Transfer/TransferLoop1 高斯已证。 |
| Theorem 2.4 | 9 | 条件 | (2.6)–(2.9) 以 Thm221/Thm221'（含 (2.71)）为假设，且只在固定 Lemma 2.8 能量切片 SpecSeq（lemE z_N=E 固定）上成立——比论文对全域 z 一致更窄（#38 仅撤销局部律一半）。(2.6)(2.7) 可只用 Thm221NoEL'。sample d 上均无 producer。 |
| Theorem 2.5 | 9 | 条件 | 归约 (2.8)(2.9)[QDExpect] ⇒ (2.12)(2.13) 对任意 Band、任意 bulk 能量序列已证。高斯版仍假设 Thm221 (sample d) κ（未证），且需 SpecSeq κ τ' E' (queZ τ E)：谱参数落在固定 Lemma 2.8 能量切片，比论文 max_E 窄。 |
| Theorem 2.6 | 11 | 条件 | theorem2_6_of_steps 仅在假设 DBMUniversality+GreenComparison+StepTwoClaim 下给出 BulkUniversality；B、H 为任意 Hermitian 随机阵(未用高斯带模型)，OUFlow 无分布：取常值流时后两假设平凡成立、DBMUniversality 即结论本身(循环)。三假设均无生产者。 |
| Definition 2.7 | 15 | 已定义 | z_t=E+(1−t)m^{(E)} 逐字。m^{(E)} 用闭式定义并证其为 m(m+E)=−1、Im>0 的唯一根（eq_mE）；论文的极限定义未形式化（paper-deltas #7）。定义中 G_t 的 Itô SDE 由生成元恒等式替代。 |
| Lemma 2.8 | 16 | 换路线 | 确定性部分 (2.37)(2.38)(2.40) 及 E,t 显式式全部已证（常数更强）；唯分布相等 (2.39) 无布朗模型可言，由 H_t=√tX 下的逐 ω 恒等（已证）代替，故整体记 replaced。 |
| Definition 2.9 | 16 | 已定义 | G_t(σ)=Gsig(H_t,z_t,σ)（σ 用 Bool，true=+），n-loop=gloop；G(+)†=G(−) 为 Gsig_conjTranspose。 |
| Definition 2.10 | 17 | 已定义 | 三个 cut-and-glue 算子逐字定义，已对照图 1–3 例子核对下标；长度 n+1、k+n−l+1、l−k+1 已证。论文「a_n,a_1 总在左 loop」对 k=1 不精确（paper-deltas #4）。 |
| Lemma 2.11 | 18 | 换路线 | SDE 形式从未陈述；代之以期望形式 ∂_u E L_u = E[Ẽ^{(G̃)}+primRhs(L_u)]，对 H_u=√uX、所有 n≥1、u>0 已证（MatrixStein=matrixStein 与 hjoint 均已卸），逐点生成元恒等式亦证；鞅项无对应物（paper-deltas #52）。 |
| Definition 2.12 | 18 | 已定义 | IsPrimitive=方程+初值+n=1 约定。「唯一解」：存在性由树表示 Kgen 在 [0,T₀]（T₀<1、/m/≤1、L≥3）证出；唯一性需额外假设 2-loop 有界（paper-deltas #11），eq_Kgen_of_isPrimitive 合并二者。 |
| Definition 2.13 | 19 | 已定义 | Θ_ξ=Ring.inverse(1−ξS^{(B)})，‖ξ‖<1、L≥3 时为两侧逆。 |
| Lemma 2.14 | 19 | 仅特例 | 全部在 ‖ξ‖<1 加 L≥3 下、常数显式一致：(1)–(5)、(2.52)、(2.53) 全圆盘 proved。唯第 6 条 (2.54) 对复 ξ 只证 x≠y（对角仅实 ξ 覆盖），故整体记 narrower。 |
| Example 2.15 | 20 | 已证 | (2.57) 解 (2.55) 且满足初值（‖t m₁m₂‖<1，/E/≤2、t<1 时自动）；与 Def 2.12 的 K 相等经 Kgen_two 及 2-loop 有界下的唯一性；(2.58) 两式已证。 |
| Example 2.16 | 20 | 已证 | n=3 展开式（需 2-loop 旋转不变 hrot，对 (2.57) 由 kTwo_rotate 满足；回绕项下标见 paper-deltas #10）与三 Θ 乘积解（含初值）已证。 |
| Lemma 2.17 | 21 | 已证 | 确定性：对每个 n≥1 存在常数 C，使 ∀N、0≤t<1、良构 I：/K_{t,σ,a}/≤C(Wℓ_tη_t)^{-n+1}（比 ≺ 更强）。n≥3 走 Lemma 3.11 (3.46)，n=2 用 (3.35)，n=1 平凡。附加假设：L≥3、/E/≤2−k（体内）、t<1。 |
| Lemma 2.18 | 22 | 条件 | 只有条件版：以 Thm221NoEL'（Theorem 2.21 一步，去 (2.71)）为假设，经 p.24 网格归纳得 (2.60)(2.61)，量词 ∀κ,τ,/E/≤2−κ,0≤t≤1−N^{-1+τ}（另有能量序列版）。高斯模型上一步无生产者（Gate 1–2 未闭）。 |
| Lemma 2.19 | 22 | 条件 | (2.62) 只以完整 Thm221'/Thm221N'（含 Step 6 与 (2.71) 的第二遍归纳）为假设推出；(2.63)=BoundsCore.decay 由 Thm221NoEL' 条件推出。两者在高斯模型上均无生产者。 |
| Lemma 2.20 | 22 | 条件 | (2.64)=BoundsCore.localLaw 于 t，仅在 Thm221NoEL' 假设下经网格归纳得到。窄见证（exampleGrow、E=0、首格 t≤1/2 的局部律，Gauss/FirstCellStep1LocalLaw.lean）不计入。 |
| Theorem 2.21 | 24 | 条件 | 高斯模型上无生产者。当前一步装配只给去 (2.71) 的 Thm221NoEL，仍需 APrimeSlot'（仅 exampleGrow）、CutHypEvOnSlot、全阶 Lemma514、Eq45FlowInputs、Eq548EntryDataEvOn'；完整版还需 Step 6。步条件为 Cond272Reg=(2.72)+N^c≤Wℓ_tη_t（D13/#132）。 |
| Definition 3.1 | 27 | 已定义 | 唯一建模步(paper-deltas #124)：典范划分用其树表示——树、叶恰为互异 a_i、内点度≥3(等价类 II 的正规形)、每边恰在两条区域路径上(平面性)。多边形平面几何本身未形式化；T_SP 在 Lean 中定义为无交叉对角线集 TSP n，经 Lemma 3.2 与树模型等同。 |
| Lemma 3.2 | 28 | 已证 | 在 Def 3.1 树模型内对一般 n≥3 证明(T185；#8 已撤销，#128 记 3≤n，论文本就 n≥3)。它是定理而非定义：TSP 仍定义为无交叉对角集，但像恰为 TSP 且单射已证。decide 的 /TSP 4/=3、11、45 只是回归。Crossing.lean/Layer.lean 文档仍说“以 3.2 为定义”，已过时。 |
| Definition 3.3 | 29 | 已定义 | 无轴(laminar)编码：内点=F∪{whole}，叶 v 的边 Θ_{t m_v m_{v+1}}，对角线 (i,j) 的内边 Θ_{t m_i m_j}−1，对全部内点标号求和。其边与 canonGraph F 一致(onRegion_leaf/onRegion_node 给出 R_k∩R_l)；但没有“任意 IsCanonicalTree 的 (3.2) 值=treeValG”的单独定理，靠构造+canonIso。 |
| Lemma 3.4 | 30 | 已证 | 对一般长度 n≥3 证明：Def 2.12 的任一解 K 等于树和。附加假设 L≥3、t∈[0,T₀]、T₀<1、/m(±)/≤1、2-loop 一致有界(唯一性所需，#11/#16)。n=2 论文星图写法错(#9)，Lean 取单边树=Example 2.15(Kgen_two，not_hasDerivAt_starK_two 证星图不满足)。 |
| Corollary 3.5 | 30 | 已证 | σ=(+,…,+)：n≥3 经树表示，n=2 经 (2.52)。显式 gap 假设 δ≤/1−t m(+)²/(t≤T₀<1 时取 δ=1−T₀)；C_n、c 仅依赖 n,δ(#17)。体内 /E/≤2−k 版 norm_Kgen_pure_le 一致于 t<1 且保留 W^{-(n−1)}(论文 (3.6) 丢掉了 W 幂)。 |
| Lemma 3.6 | 33 | 已证 | (3.12) 对任意 Hermitian H 逐样本成立；(3.13) 对所有长度证明(归纳+Grönwall)，假设 /E/<2、L≥3、0≤t<1。路线比论文简：(1,m)/(m,n) 一并抵消，无需角上切口与 3-loop Ward(#15)；论文未证的循环不变性另证 isPrimitive_rot/Kgen_rot(#14)。 |
| Corollary 3.7 | 33 | 已证 | 对任意长度 n≥2 的 σ(比论文 σ1=+,σn=− 更一般)、体内 /E/≤2−k、0≤t<1：/Σ_{a2..an}K/≤C_n(k)(Wη_t)^{-(n−1)}，一致于 L。论文“由定义”的平移不变与未证的循环不变均已补证(#18)。 |
| Definition 3.8 | 38 | 已定义 | I：F_long={(i,j)∈F: σ_i≠σ_j}；II：T_SP(P_a,σ,π)={F∈TSP n: Flong F σ=π}；π⊆Z_n^off 即 diagonals n；层划分 sum_TSPlong 已证；Test/Layers.lean 用 decide 做 n=4,5,6 回归。 |
| Definition 3.9 | 40 | 已定义 | K^(π)=Kpi(与 W 无关)；Σ^(π)=SigmaPi(无轴编码，叶处 Kronecker δ，对全部内点标号求和)。(3.41)(3.42) 作为定理证出。n=2 例外(#19a)；论文 n=4 例子第三项应为 Θ_{t m̄²}(#19b)，Lean 未形式化该例子。 |
| Lemma 3.10 | 40 | 已证 | 对 n≥3 且 σ 循环相邻皆异号(即 σ^alt 或其反号，n 偶)、体内 /E/≤2−k、t∈[0,1)(论文含 t=1)：/L^{-1}Σ_dΣ^(∅)/≤Cη_t，C=C(n,k) 与 L,t 无关。(1) 对所有 σ,π 证。证明按论文结构但走闭式 A(σ,π)(#21)。 |
| Lemma 3.11 | 41 | 已证 | 确定性界(强于 O≺，且无 log，#22)：/K^(π)/≤C(η_tℓ̂_t)^{-(n−1)}、/K/≤C(Wη_tℓ̂_t)^{-(n−1)}，对 3≤n≤N_max、所有 σ,a,π、0<t<1、L≥3、/E/≤2−k，C=C(N_max,k)。n=2 未打包(由 Ex.2.15+(3.35) 得)，t=0 平凡。路线绕开 (3.66)。 |
| Lemma 4.1 | 48 | 条件 | 高斯√uX、任意Dims：(4.2)(4.3)在N无关的固定时刻无LDE假设已证；N相关/沿流版本只带加性地板N^{-B}；Step1消费形式Lemma41Flow已证；(4.5)仍需随机尺度(4.12)两输入(hFArow/hFAblk)，仅首格exampleGrow,E=0有，故整体conditional |
| Lemma 4.2 | 49 | 已证 | 确定性线性代数：任意Hermitian H、H−z可逆，附加G_ii≠0；(4.8)论文漏负号，Lean证G_ij=−G_ii Σ H_ik G^(i)_kj（paper-deltas#39，只用绝对值无影响） |
| Lemma 5.1 | 51 | 已证 | lemma_5_1对一般Sample以(6.1)的LoopScaling为假设；对高斯sample d由loopScaling_gauss无条件给出（径向模型逐点恒等式；结论只依赖单时刻律）。差异：t₂<1（论文≤1）、显式/E/≤2−κ；任意阈值版lemma_5_1_thr |
| Definition 5.2 | 53 | 已定义 | Θ_{t,σ}=ThetaOp、U_{s,t,σ}=Uker（边参数 ξ_i 作数据，xiOf 还原 m(σ_i)m(σ_{i+1})）。(5.16) 按更正后的核 ξ_iΘ^(B)_{tξ_i}S^(B)（论文漏 S^(B)，#106，Jun 已裁定）。 |
| Lemma 5.3 | 54 | 换路线 | SDE 的 Duhamel 未字面形式化（√u·X 无 Itô，#49/#88）。替代：确定性变差常数 hasDerivAt_Uker_path + 矩形 (5.20)+(5.24) 合体不等式 MomentIneq，无条件证出（任意 Dims、/E/<2、[s,t]⊂[0,1)）。停时版 (5.21) 只由 A′ 替代且仅 exampleGrow。 |
| Definition 5.4 | 54 | 已定义 | E⊗E 为显式张量（eeTens/eeArg，沿流 eeFun），非接口数据；(5.22) 的粘合 (2n+2)-loop 展开已证；σ(k) 后半段共轭已修正（SumZeroDyn.xi2，#144）；k 用 0-based（#84）。 |
| Lemma 5.5 | 55 | 换路线 | BDG/鞅不形式化。替代：生成元矩不等式（“鞅”换成 𝓛-恒等式，#55），QV 项 (C_{n,p}∫‖(U⊗U)∘(E⊗E)‖_p)^{1/2}，C=cMDval' p n，无条件已证；QV 桥 (5.25) 逐点已证（常数 n+2）。仅不停止版，停时版无。 |
| Lemma 5.6 | 56 | 已证 | 确定性，已证：(5.30) Θ_u 与 (1−sS)Θ_u(=Θ_s^{-1}Θ_u) 在 δℓ*_u 外 ≤W^{-D}；(5.31) 对每个 ω、终于 N 成立 /L_{(−,+)}/≤J*·T；(5.32) 显式 e^{√C(log W)^{3/4}} 损失与一致 ≺ 版。需 Cond272、/E/<2。 |
| Lemma 5.7 | 56 | 仅特例 | 确定性版在 Lemma57/EGDef/EEDef（输入为假设）。实际模型：(5.34) 已证；(5.35) T1389 任意 Dims 同一高概率事件逐点（D≥60、较弱远场系数、J=jG）；(5.36) 仅 a'=a、块 jG、Step-1 事件上逐点。均非论文字面 ≺ 形式。 |
| Definition 5.8 | 63 | 已定义 | (u,τ,D) 衰减：LoopDecay N ℓ δ F（长度≤N 的所有 loop，两标号距离≥ℓ⇒/F/≤δ），ℓ=ℓ_u·W^τ（仓库多用 ℓ_u·N^τ），δ=W^{-D}；LoopDecay.fastDecay 与 (7.13) FastDecay 对接；≺ 形式用 farInd 指示函数。 |
| Lemma 5.9 | 64 | 仅特例 | 确定性核心已证（Lemma 4.1 事件+(2.76) 衰减⇒L、L−K 衰减，半径 2N(ℓ+2)）。一般 ≺ 版 lkDecay_of_inputs'/lDecay_of_inputs' 仍需 FlowGoodEv（无生产者）与 (2.76)；实际高斯仅 exampleGrow、E=0、[0,1/2] 首格（L−K 半）。 |
| Lemma 5.10 | 64 | 条件 | 四条幂次计数在确定性显式常数形式（以衰减与 Ξ 界为假设）下已证；≺ 形式 stochDom_norm_driftF 需高概率 DriftInputs（Lemma 5.9 衰减+幂次计数+Ξ^{(L−K)}_1≤C1，无实际生产者）；第 3 行少因子 Ξ^{(L−K)}_{u,1}（#121）。 |
| Lemma 5.11 | 65 | 条件 | (7.16) Case 1 核估计与 (5.84)⇒(5.83) 积分组装为确定性已证（带 log((1−s)/(1−t)) 损失）。≺ 版：矩路线需 MomentDuhamel.Hyp（实际高斯可由 gaussHypOfMoments 给出）+RhsNonAltAt（需 (5.77)/衰减，未产出）；SumZeroDyn.bound_nonAlt 需 Hierarchy/Lemma510 占位。 |
| Definition 5.12 | 66 | 已定义 | P、sum-zero、ϑ_t=(1−t)^{n−1}∏Θ^{(B)}_t、Q_t=A−(PA)ϑ 均已定义（下标整体移位 n→n+1）；P∘ϑ=1（Psum_vartheta）、P∘Q_t=0（SumZero_Qop）已证，需 L≥3、/t/<1。 |
| Lemma 5.13 | 66 | 已证 | 确定性：(ℓ_tK,δ) 衰减且 ≤M 的 A 满足 /Q_tA/≤(1+(6e c K)^n)M+(2c)^nL^nδ，且 Q_tA 保持衰减（误差 +exp(−c₀K/2)·…）；K=W^τ 即论文 W^{Cnτ}。需 L≥3、0≤t<1。 |
| Lemma 5.14 | 67 | 条件 | STATUS：全阶 Lemma 5.14 未闭。实际高斯 Q 路线把 (5.92) 归约到 Rhs514QAt（五项核估计，需沿流快衰减/尺寸包络）、PHalf514（需 LKDecay）、RhsNonAltAt；Hyp 本身可由 gaussHypOfMoments 给出。已验收仅 T1391 首半 QV 矩与 T1393 MomentIneqQ。 |
| Lemma 5.15 | 72 | 条件 | 实际高斯任意 Dims：(5.127) 恒等式无条件已证；(5.128) 求逆确定性已证；(5.126) 需 hquad=E[(G−m)(G−m)]≺A^{-2}，由 (2.78)（SharpLmKFlow，Step 4 未闭）与 η≥N^{-c} 给出。需覆盖两种电荷（#127 附注）。 |
| Lemma 6.1 | 74 | 已证 | 任意复内积空间、有限族w_i、实p≥1（cfc）及自然数p版；确定性 |
| Lemma 7.1 | 76 | 已证 | 确定性。norm_Uker_apply_le给C^n‖A‖（C为边核行和界），行和界(t−s)/(1−t)代入得((1−s)/(1−t))^n=(η_s/η_t)^n（η_u取1−u，与Im z_u差κ常数）；无单一定理逐字写出(7.1) |
| Lemma 7.2 | 77 | 已证 | 确定性显式常数，σ=(+,−)、0≤s≤t<1、W≥e；路线不同（按16ℓ_s≤ℓ_t分情形，无log损失），因子C(1+2L e^{-(logW)^{3/2}/8})=O(1)；η_u=1−u、ℓ_u=ℓ̂(u) |
| Lemma 7.3 | 78 | 已证 | 确定性显式常数：K≥1代W^τ、δ代W^{-D}；Case 2为K^{2n}且无需交替假设（需ξ_i≠0）；η_u=1−u、ℓ_u=ℓ̂(u)（paper-deltas#35） |
| Definition A.1 | 85 | 已定义 | G-chain定义；共轭、chain→loop等代数性质已证 |
| Lemma A.2 | 85 | 条件 | 仅确定性内核（固定H、≺→显式常数、Φ≥chainScale）：/1/G_ii/≤K与Ξ₁基例(Thm 2.3)、LoopBound(2.77)、链LDE ChainLDE16/19([39])均为未释放假设；无≺/高斯模型组装；论文称附录A不用于主定理 |

## 未完成的公式（仅特例 / 条件 / 换路线 / 未证 / 外部输入）

| 编号 | 页 | 状态 | 说明 |
|---|---|---|---|
| (1.1) | 4 | 未证 | 引言中 T-observable 的启发式定义（∼ 而非等式），Lean 未定义；全文实际使用块级 2-loop (2.41)（gloop），故不构成证明缺口。 |
| (1.2) | 4 | 未证 | 引言中广义 T-observable 的定义，Lean 未定义；论文随即改用 G-loop (1.3)/(2.41)，后文不再使用，非缺口。 |
| (1.4) | 5 | 未证 | 引言启发式「朴素估计」/L/∼(max/G_xy/)^n，非定理，论文不证、Lean 无对应陈述。 |
| (1.5) | 5 | 条件 | 引言启发式；其严格形式是 Lemma 2.18/Thm 2.21 的 loop 界 (2.60)=BoundsCoreN.LmK（G-loop）与 Lemma 3.11（K）。G-loop 版依赖未证的 Thm 2.21（对实际高斯模型无 producer）。 |
| (2.3) | 8 | 条件 | Theorem 2.3 第一合取 ‖G−m‖_max ≤ W^τ(Wℓη)^{-1/2}（失败概率 ≤N^{-D}）；依赖未证的能量一致 Thm 2.21。 |
| (2.4) | 8 | 条件 | Theorem 2.3 第二合取（部分迹律，需 TransferLoop1，高斯已证）；依赖未证的 Thm 2.21。 |
| (2.6) | 9 | 条件 | Theorem 2.4 (+,−) 高概率界；只在固定能量切片；需 BoundsCore/Thm221NoEL'，对实际模型未证。 |
| (2.7) | 9 | 条件 | Theorem 2.4 (+,+) 高概率界；同 (2.6)：固定能量切片、依赖未证 Thm 2.21。 |
| (2.8) | 9 | 条件 | 期望界需 (2.71)=Bounds.expect（Step 6）即完整 Thm221；固定能量切片。PLAN Gate 2：Step 6 与完整 Thm221 对实际模型均未证。 |
| (2.9) | 9 | 条件 | 同 (2.8)，(+,+) 情形；需完整 Thm221（含 (2.71)），固定能量切片。 |
| (2.12) | 9 | 条件 | Theorem 2.5 结论一：由 QDExpect 的归约已证，但 QDExpect 对实际模型只能经未证的 Thm221 且在固定能量切片得到。max_E 写作任意能量序列（等价）。 |
| (2.13) | 10 | 条件 | Theorem 2.5 结论二；同 (2.12) 的条件性；Lean 要求 A 非空（事件用 ≥ 阈值，paper-deltas #45）。 |
| (2.17) | 10 | 条件 | 由 (2.8)(2.9) 推出的期望界；在 que_of_QDExpect 内以 QDExpect 为假设证出（算术 queBound_le 无条件）。QDExpect 对实际模型未证 → conditional。 |
| (2.18) | 11 | 条件 | (2.18) 写为 BulkUniversality(∀/E/≤2−κ,∀k,∀光滑紧支 O)；ρ_H 用无密度 corrPairing(有密度时与论文积分相等，未证，deltas #45)，GUE 侧为显式 GUE 密度边缘。仅经 theorem2_6_of_steps 在三条未证假设下得到。 |
| (2.19) | 11 | 换路线 | OU SDE 未形式化：OUFlow 只记路径/Hermitian/H_0=H，无分布。替代物=固定时刻边缘 e^{-t/2}X+√(1−e^{-t})G(T1401/T1420 已证,任意 Dims)，但跨时刻共用同一 G、非布朗路径，且未接入 OUFlow/theorem2_6_of_steps。 |
| (2.20) | 11 | 条件 | Lean 中 H_∞ 以显式 GUE 相关函数 gueCorrPairing 代替(H_∞~GUE 未证、未需)；(2.20) 经 F.start 与 corrPairing_congr 与 (2.18) 同式，条件于 DBMUniversality/GreenComparison/StepTwoClaim。 |
| (2.21) | 12 | 外部输入 | 唯一授权外部输入([51] Thm 2.2 复 Hermitian 版，deltas #114)。前提未核验：Lean 的 DBMUniversality 直接把结论 (2.21) 假设给无分布 OUFlow，[51] 一般陈述未写入；(g,G)-正则性(需 Thm 2.3 局部律，Gate 3 未闭)、条件化、时间换算均未证。 |
| (2.23) | 12 | 未证 | (2.23) 只作为假设 StepTwoClaim(∀E,n ∃c'>0,C,τ0)出现，全仓无生产者，Step 3 未组装；已接受的只有确定性部件 T1436/T1448(乘积 Hessian 收缩与核界)。 |
| (2.24) | 12 | 条件 | 只在假设 GreenComparison((2.23)⇒(2.24)，[37] Thm15.3+[70] Prop4.17，按 PLAN 须内部证明而未证)与 StepTwoClaim 下于 theorem2_6_of_steps 内取出；相关已证件仅 T1407 确定性谱乘积分解。 |
| (2.25) | 12 | 未证 | [70] Lemma 4.18 须自证。只证逐点确定性部分：乘积 Hessian 中心化收缩恒等式(T1436)与 L1/L2 核范数界(T1448, deltas T1448a)；OU 期望对时间的导数与积分未证(OUFlow 无分布)。 |
| (2.26) | 13 | 未证 | 弱局部律 max/(G_t)_xx/≺1 未形式化(Universality/GUEPhase 头注均写 not formalized)；论文由 (7.26)+(7.28) 推出，二者均未证。T1463 只给固定时刻谱二阶矩 R≺1。 |
| (2.27) | 13 | 条件 | Thm 2.5 对 H_t(τ*=c/3)：由占位 Eq747 或 Eq747Inputs(law726=(7.26)、eq729=(7.29) 均未证)推出；对任意无分布 OUFlow、单一时刻序列 t_N，需 ζ≤η/16，η 取 Thm 2.5 尺度 N^{-1-c/3}(W²/N)^{1/3}。 |
| (2.28) | 13 | 未证 | 只证其前的确定性单调性 ηIm m(E+iη)≤η̃Im m(E+iη̃)(T1395)；(2.28) 本身依赖 (2.25)、(2.26)，均未证，无 Lean 陈述。 |
| (2.29) | 13 | 未证 | 未证。坏事件 P(B_y)≤3N^{-c/18} 仅在 Eq747 下条件性证明，阈值改为 N^{-c/36}(按字面 (2.12) 只能如此，疑似论文笔误，deltas #45，c'→c/36)；T1397/T1457/T1466 为确定性谱展开/bulk-tail 界；实际 OU 事件缺。 |
| (2.30) | 13 | 未证 | 未形式化：双本征向量 M_{y,α,β}、坏事件 B̃ 与其概率/期望界均无 Lean 对应；依赖 (2.25)–(2.27)。 |
| (2.31) | 13 | 未证 | 只证确定性精确谱展开与三角界(T1397)及 M_{y,α}=blockM 表示；≺ 形式未证。T1456：沿 OU 区间的无损 (2.31) 需更强实际 bulk 输入，现有弱路线带 N^{aτU} 损失(a=2或4)。 |
| (2.32) | 14 | 未证 | 未证。T1456 指出首式 max_{α,y}/M_{y,α}/≺N^{CτU} 对全谱不能由 (2.10)(仅 bulk)推出——论文证明范围问题；已证：Σ_α/M/≤2N 与 α 尾界(T1466)、固定时刻 R≺1(T1463)。 |
| (2.33) | 14 | 未证 | 好事件 B^c 上按 /λ_α−E/≤N^{-1+c/6} 分裂的估计未形式化；依赖 (2.27)(条件)与 (2.26)/(2.32)(未证)。 |
| (2.34) | 15 | 换路线 | 矩阵布朗运动未构造；以 H_u=√u·X（X 高斯带矩阵，乘积测度）代替，单时刻边缘律一致（方差 uS），但无独立增量/鞅/Itô（paper-deltas #49）。凡需路径性质处须另证（PLAN Gate 0）。 |
| (2.39) | 16 | 换路线 | 论文为分布相等；矩路线中 H_t=√tX 与 H_1=X 共用 X，√t·G_t^{(E)}=G(X,z) 为逐 ω 恒等（强于同分布，但只对此模型），经 transfer_gauss 传递 ≺ 界，已证（paper-deltas #99）。 |
| (2.45) | 18 | 换路线 | 随机微分恒等式不陈述；取期望后的形式（鞅项消失）对高斯矩路线模型已证，替代物本身无条件。路径版依赖它的下游（BDG 等）改走矩估计。 |
| (2.46) | 18 | 换路线 | 鞅微分在矩路线不存在；其用途（BDG/二次变差控制）由生成元作用于 /F/^{2p} + Grönwall 代替（secondOrder_eq_quadVar、DischargeBDG）；下游全阶矩估计（如 Lemma 5.14）仍 conditional（STATUS）。 |
| (2.54) | 20 | 仅特例 | 复 ξ 全圆盘只证 x≠y：≤1728/(‖x−y‖+1)；对角 x=y 仅实 ξ∈[0,1) 有 ≤3；复 ξ 对角只有 norm_Theta_second_diff_diag_le 的 4‖A(1−ρ)‖，非一致 O(1)。数学上平凡，但未形式化。 |
| (2.60) | 22 | 条件 | = BoundsCore.LmK 在时刻 t（∀n≥1，max 取遍 σ,a）。只由未生产的 Thm221NoEL'/Thm221' 经网格归纳推出；一步所缺：全阶 Lemma 5.14、(4.5) 随机尺度、锐 (5.48)、停时截断，以及一般 Dims 的 Step 2。 |
| (2.61) | 22 | 条件 | 推导步 (2.60)+(2.59)⇒(2.61) 已证（stochDom_norm_Lval_of_LmK，∀n≥1，需 Wℓ_tη_t≥1），但 (2.60) 本身条件，故整体 conditional。注：Hypotheses.lean 文档称只对 n≥3，已过时。 |
| (2.62) | 22 | 条件 | E L 为 Bochner 积分，确定性 ≺（UnifDetDom），σ∈{+,−}²。需 Step 6（(2.80)）与带 (2.71) 的完整 Theorem 2.21 一步（Thm221'），均无高斯生产者；Theorem 2.2 路线只用 Thm221NoEL，不给 (2.62)。 |
| (2.63) | 22 | 条件 | σ=(+,−)，/a₁−a₂/ 取环距离 zdist；W^{-D} 放在 decayProf 内（乘 (Wℓη)^{-2}），∀D 下与论文等价。只由 Thm221NoEL' 条件推出。 |
| (2.64) | 22 | 条件 | ‖G_t−m‖_max ≺ (Wℓ_tη_t)^{-1/2}，编码为 llErr 的 StochDom。仅由未生产的 Thm221NoEL' 推出（Gate 1–2 未闭）。 |
| (2.65) | 22 | 换路线 | 论文为分布相等。Lean 模型 H_t=√t·X、带矩阵取 X，(2.39)/(2.65) 变为逐点恒等式 t^{1/2}G_t=G(z)（已证，无额外假设），再用 Transfer 传递 ≺ 界。替代已证；不是布朗路径上的分布陈述。 |
| (2.66) | 22 | 换路线 | 论文为分布相等 Tr G E_a G^{(±)} E_b ∼ t·L_t。Lean 在 √t·X 模型中为逐点恒等式（任意长度 gloop_Hflow_lemT_eq），并给期望版 loop2_expect；替代已证。(2.57) 的 K 显式式不在本条。 |
| (2.68) | 24 | 条件 | 作为 s 时刻假设忠实编码为 BoundsCore.LmK（n≥1，max_{σ,a}）；s=0 由 (2.67) 给出；作为 t 时刻结论（Step 4 推出）依赖未闭的一步装配，故 conditional。 |
| (2.69) | 24 | 条件 | s 时刻假设编码为 BoundsCore.decay（σ=(+,−)，∀D>0，环距离，W^{-D} 在 decayProf 内）；t 时刻结论来自 Step 5，需锐 (5.48)，conditional。 |
| (2.70) | 24 | 条件 | s 时刻假设编码为 BoundsCore.localLaw；t 时刻结论即 Step 2 的 (2.75)@u=t（BoundsCore_of_flow 投影），而 Step 2 仅 exampleGrow 已证、整步装配仍条件，故 conditional。 |
| (2.71) | 24 | 条件 | 编码为 Bounds.expect（UnifDetDom，Bochner 积分）。Thm221NoEL 路线按 p.25 注去掉 (2.71)；t 时刻结论需 Step 6 装配 bounds_step_gauss_window_analytic（含 Step 3/4 数据、FlowInputs），conditional。 |
| (2.75) | 24 | 仅特例 | T1337 接受：仅 d=Dims.exampleGrow（∀/E/≤2−κ、任意窗、给定 BoundsCore(s)+Cond272Reg）。一般 Dims 的 APrimeSlot'（随机 (5.41) majorant、全阶 QV、停时过程）未证。 |
| (2.76) | 24 | 仅特例 | 同 (2.75)，只对 exampleGrow。Lean 形式 R^4A_u^{-2}(exp(−√(d/ℓ_u))+W^{-D})，W^{-D} 在括号内（paper-delta T1337a，∀D 下等价）。 |
| (2.77) | 25 | 条件 | Step 3 的确定性归纳 (5.107)–(5.120) 已编译，但需 hΘ：Ξ^{(L−K)}_2≺(Wℓ_sη_s)^{1/2}（来自 CutHypEvOnSlot，停时全电荷非线性截断，未证）与全阶 Lemma 5.14（Step3.Lemma514，未证）。 |
| (2.78) | 25 | 条件 | 需 Lemma 5.14（n≥2）、Step 3 输出与沿流 (4.5)（Eq45Flow←Eq45FlowInputs：IBP+两处 (4.12)，随机尺度版未证）。条件。 |
| (2.79) | 25 | 条件 | 近场由 (2.78) n=2 给出；远场需 (5.48)（Eq548EntryDataEvOn'：near、单事件模、截断矩），锐 (5.48) 与远截断矩未证；Kmod 在 ∀D 外固定的量词接口问题见 STATUS。条件。 |
| (2.80) | 25 | 条件 | (5.126)–(5.136) 的确定性部分与连续性/可积性（hcont_gauss 等）已证；仍需 LKDecayQuant.FlowInputs、Step3.Hyp、S(m,l)、Lemma514 n=2、SharpLmKFlow 与 Bounds(s)。Lean 版对 u∈[s,t] 一致。条件。 |
| (2.81) | 25 | 换路线 | (2.45) 的示意式 dL=E^(M)+E^(G̃)+二次项。鞅项/Itô 路径分解未形式化；以矩形式层级（Stein 生成元下期望导数）替代：MatrixStein 已证，TestFun 光滑界作假设输入。 |
| (3.37) | 39 | 未证 | Figure 10 的具体例子(n=10, π={{1,5},{5,7},{8,1}})，Lean 未形式化；非数学主张，一般机制由 Kpi_cut/Qlayer_cut 的最内长边切割承担。 |
| (3.38) | 39 | 未证 | 该例子的四个局部子树(单分子划分)示意，Lean 未形式化；一般的分子分解改用逐次切最内长边(Kpi_cut)。 |
| (3.66) | 45 | 未证 | (3.66) 本身(带 min_k(‖a_k−d_1‖+1)^{-1} 因子、比 (3.45) 强)无 Lean 对应；paper-deltas #22 指论文证明只给 a_n 方向且对 d_1 求和多 log。Lean 以 d_1 为中心展开绕开，母引理 3.11 已证。 |
| (3.70) | 46 | 未证 | f0 界即 (3.35)；f1 由一致梯度 /∇Θ_t/≤3/2 得 ≤(3/2)/s/(不弱于论文)；f2 的逐点 O((‖a−d_1‖+1)^{-1}) 无 Lean 对应(Lean 用离对角 /ΔΘ/≤24/ℓ̂ 的求和版)。母引理 3.11 已证。 |
| (3.72) | 47 | 未证 | 带 min 因子的 (3.72) 未证。Lean 对应的四种情形(偶项/两奇项、单奇项因对称为 0、全零项用 sum-zero)在对中心求和后给不带 min 因子的界，足以得 (3.45)。 |
| (4.2) | 48 | 仅特例 | 实际高斯√uX、任意Dims：固定（与N无关）u∈[0,1]、z无LDE假设已证；N相关时刻/时间一致版只带加性地板2N^{-B}(T148，远块处弱于论文)；仅i≠j；(a',b')下标对调(paper-deltas#32) |
| (4.3) | 48 | 仅特例 | /E/≤2−κ、固定（N无关）t<1：高斯无LDE假设已证；时间一致/N相关时刻版带地板N^{-B}（Ω上Lmax≥W⁻¹/4本可吸收，但没有写成无地板的(4.3)定理） |
| (4.4) | 48 | 仅特例 | (4.4)是引理自身假设，Lean以HighProb(goodSet)形式出现；由它去掉1_Ω的结论只有通用版（带LDE假设），高斯固定时刻LDE已证可直接喂入但未合成；时间一致版同(4.2)(4.3)带地板 |
| (4.5) | 48 | 条件 | 固定时刻：IBP输入已由(4.4)推出，但仍需随机尺度(4.12)两输入hFArow/hFAblk(≺Lmax)，一般未产出；实际Eq45Flow仅首格Dims.exampleGrow、E=0、κ=1；后续格随机尺度(4.5)为STATUS开放项 |
| (4.10) | 49 | 仅特例 | 确定性内核（Ω与LDE结论作显式Φ假设）已证；随机层同(4.2)：高斯LDE在N无关固定时刻已证，时间一致仅地板版(Green/EntryBoundFloor.lean:norm_sq_green_le_row_floor) |
| (4.11) | 49 | 仅特例 | 确定性两侧迭代已证；随机层状态同(4.2)（固定N无关时刻无地板，时间一致带地板） |
| (4.12) | 50 | 仅特例 | 论文引自[40](4.11)（非授权外部输入）。Lean：任意Dims、确定时刻列、确定性尺度Ψ(W^{-1/2}≤Ψ≤N^{-a})且假设该尺度局部律，对两族权重证≺Ψ²；随机尺度Ψ²=max L仅首格exampleGrow,E=0；后续格未证 |
| (5.1) | 51 | 换路线 | 论文为布朗流路径连续性（除指数小事件）。Lean 模型 H_u=√u·X，改用逐 ω 确定性 √/u−u'/ 模 ‖G_u−G_u'‖≤η_t^{-2}(‖X‖+1)/u−u'/^{1/2} 加 N^{-C} 网提升（均已证，任意 Dims）；不是布朗路径陈述。 |
| (5.3) | 51 | 仅特例 | Step 1 的 Lean 证明绕过 (5.3)（不需要，Step1.lean docstring、#44）。单独的版本只有 exampleGrow、E=0、首格 [0,u_1≤1/2] 上的锐局部律 ‖G_u−m‖≺W^{-1/2}；一般 Dims/能量/窗口未证。 |
| (5.10) | 52 | 换路线 | Itô 形式未形式化（无矩阵布朗运动）。替代：逐点生成元恒等式 (∂_u+𝓛)L=Ẽ[G−m]+W∑(G^L∘L)S(G^R∘L)（Hermitian M，无条件）与期望形 d/du E L=E[Ẽ+primRhs]（matrixStein 与 hjoint 已卸）；替代已证。 |
| (5.12) | 53 | 换路线 | 代数部分（(5.10)−(5.11) 的极化 primBil K D+primBil D K+primBil D D）已证；含 E^{(M)} 的随机微分形式由逐点生成元漂移恒等式替代（已证，F=driftF 被唯一钉死）。 |
| (5.15) | 53 | 换路线 | 拆出 l_K=2 的代数恒等式已证；(5.15) 作为随机微分方程由逐点恒等式 ∂_u(L−K)+𝓛(L−K)=genS(L−K)+driftF 替代（Hermitian M，0≤u<1，已证；仅内点双侧导数，#109）。 |
| (5.20) | 54 | 换路线 | 逐路径积分层级不陈述（√u·X 中只能 fiat，#88）。替代：‖(L−K)_v‖_{2p}≤‖U(L−K)_s‖_{2p}+2∫‖U∘driftF‖_{2p}+(C∫‖(U⊗U)∘(E⊗E)‖_p)^{1/2}，无条件已证（任意 Dims）。 |
| (5.21) | 54 | 换路线 | 停止层级未形式化（无布朗流/停时，V6-paper-stopped-model-alignment）。替代为光滑前缀权重/截断（A′）：仅 exampleGrow 闭合（T1331/T1335/T1337）；一般 Dims 的停止全电荷非线性截断开放（STATUS 1）。 |
| (5.24) | 55 | 换路线 | BDG 不形式化；由生成元矩不等式替代（C_{n,p}→cMDval' p n；QV 项取 ∫‖·‖_p 形，按 Minkowski 比 E(∫QV)^p 弱，但为消费者所用）；不停止版无条件已证，停止版无。 |
| (5.25) | 55 | 换路线 | QV 以生成元 ∑_α S_α/∂_αΨ/² 逐点表达（非 Itô 二次变差）；已证 QV≤(n+2)‖(U⊗U)∘(E⊗E)_{a,a}‖（C_n=n+2，#155），只需窗口与 Hermitian；链式法则多 M.IsHermitian（#153）。 |
| (5.29) | 56 | 仅特例 | J* 定义为 max_a/(L−K)_a//T+1，isGreatest_jStar 证等于 max_ℓJ(ℓ)。目标 J*≤(η_s/η_u)^4 仅以 J*/R^4≺1（JSNormDom）对 exampleGrow、D≥60、BoundsCore(s)+Cond272Reg 证出（T1337）；一般 Dims 开放。 |
| (5.33) | 56 | 仅特例 | Lemma 5.7 的假设区：Lean (5.36) 只在 a'=a（b=b'）形式化（#113①，一般 a' 需 tailT_sub_le 未拼接）；实际模型版取 D≥60 而非 D≥10；尾函数以 T_{u,D} 归一（#112①）。 |
| (5.35) | 57 | 仅特例 | 确定性 eG_le_paper/eG_le_reduced（输入为假设，需 J*≤A_u，#112③）。实际模型 T1389：任意 Dims、同一高概率事件逐点近/远界，D≥60、N^ζ 损失、远场含 (Wℓ_tη_t)^{-1/6}+W^{-1}、近场 r³ 与显式泄漏，J=jG≤1+N^τ(9e^{√3}J*+2)。 |
| (5.36) | 57 | 仅特例 | 确定性版余 h273/h564/h42sq。h273 由 Step1 (2.73)@n=6 在事件上卸掉；h564 改为 h564′ 由 h42sq 推出（需 jG≤N 等区制）；h42sq 用块 jG 按定义成立。实际版 early_raw_full 仅 a'=a、D≥60、逐点、非 ≺ 包装。EarlyQVRateEv 的 jStar 另见可疑项。 |
| (5.37) | 57 | 未证 | 启发式 power counting（Ẽ^{(G)}∼η_u^{-1}A_u^{-2}），论文不作为待证陈述；Lean 无对应，无需形式化。 |
| (5.38) | 57 | 未证 | 启发式 power counting（E⊗E∼η_u^{-1}A_u^{-4}），与 hEE 形 E⊗E≤W∑_bL^{(1)} 一致；Lean 无对应，无需形式化。 |
| (5.39) | 57 | 仅特例 | 确定性核传播已证但较粗：损失 Ξ=W^{o(1)}，以 (η_u/η_v)² 代 (ℓ_t/ℓ_s)²·1(/a₁−a₂/≤ℓ*_t)+1（#47）；保留指示函数的远场版在 Step2MomentStep §11。 |
| (5.40) | 57 | 仅特例 | 由 (5.34)+Lemma 7.1 的确定性组合（Ξ 损失、长度×sup 代积分）；组合只出现在条件性 step_bound（需 Step2.Hyp）内；exampleGrow A′ 的二次行 T1299 为光滑前缀替代。 |
| (5.41) | 58 | 未证 | STATUS：随机占优 (5.41) majorant 未证。已有：(5.35) 源（T1389）与任意 Dims 逐点漂移剖面 T1474（未经 U 传输/时间积分），exampleGrow A′ 行 T1293/T1297；Lean 近场系数为 r³（#136）。 |
| (5.42) | 58 | 仅特例 | 演化 QV 率逐点界：任意 Dims，于 Step-1 SourceEvent 上、J=jG、D≥60、A_u≥1、log W≥(4D)²，远场取锐形 (J*)²（不做 −1/2→−1/3 吸收）；随机包装与 QV 积分仅 exampleGrow（T1341）。 |
| (5.43) | 58 | 换路线 | 布朗流停时未形式化（无布朗过程/停止 Itô 积分）。旧路线 Step2.stopTime 只在条件性 Step2.Hyp 下；A′ 光滑截断替代仅 exampleGrow 闭合；一般 Dims 停止全电荷截断开放，径向交叉项为替代路线代价（HOLD）。 |
| (5.44) | 58 | 换路线 | 停止 QV 积分由 A′ 权重下的 QV 积分替代：exampleGrow 全电荷两割 QV 积分已证（T1341，C N^{ε/4}A_s^{1/3}）；近场积分 integral_nearInt_le 确定性已证；一般 Dims、全阶 QV 开放。 |
| (5.45) | 58 | 换路线 | 停止鞅+BDG 不形式化。不停止矩版已证；Lean 左端为 Duhamel 亏量 farMart 且只断言远场一半（#147），其界是 FarInputs' 的假设；A′ 仅 exampleGrow。 |
| (5.46) | 58 | 换路线 | N^{-C} 网：通用网/Hölder 模引理已证（需 N^{-B}≤Φ），首格模 Kmod=2+2D 已证；被网化的停止鞅界无生产者；Eq548EntryDataEvOn' 的 Kmod 置于 ∀D 之外为接口问题（STATUS 1）。 |
| (5.47) | 59 | 仅特例 | /L−K/≺R_u²T_{u,60}（等价 J*_{u,60}≺(η_s/η_u)²，对 u 一致）仅 exampleGrow、固定 D=60 已证（T1454/T1471）；一般 D/Dims 只有条件性 jS_stochDom_sharp（MomentHypCutSharp.cut）与 exampleGrow 的 R⁴ 版。 |
| (5.48) | 59 | 未证 | STATUS：完整锐 (5.48) 开放。近场半边仅 exampleGrow、D=60（T1454）；远场 O(1) 半边无实际生产者（需停止 QV/不出界路线）；flowEq548_of_farInputs' 等为条件性（FarInputs'），阈值 12ℓ*_u 且光滑化（#151）。 |
| (5.54) | 60 | 仅特例 | 远 b 贡献未证为 J*W^{-10}：Lean 保留为显式加性余项 κ₁(ℓη)^{-1}Lρ（h554，#112⑤）；T1389 近场分支保留精确泄漏项，只在近输出支撑上吸收。 |
| (5.57) | 60 | 仅特例 | 确定性引理以 (5.57) 为假设（h557C/h557R）。实际模型（T1389，任意 Dims，事件上）只证较弱形 W^{-1}∑/G/≤(Wℓ_tη_t)^{-1/6}+W^{-1}（弱局部律），非论文 (Wℓ_uη_u)^{-1/2}(1+J*A^{-1})。 |
| (5.70) | 62 | 仅特例 | a'≠a 的平移（T_u≤T_t 与 (5.32)）未拼入 (5.36)：Lean 只在 a'=a 形式化（#113①）；a'=a 时即 (5.69)。 |
| (5.73) | 63 | 仅特例 | (2.75) 由 (2.76)+(2.59)+Lemma 4.1：实际模型仅 exampleGrow（T1337，BoundsCore(s)+Cond272Reg）；Step2.localLaw 为条件性（Step2.Hyp）。一般 Dims 开放。 |
| (5.75) | 64 | 仅特例 | 同 Lemma 5.9。Lean 拆为 LKDecay(/L−K/) 与 LDecay(/L/) 两谓词（同一事件，paper-deltas #78），半径 ℓ_u N^τ。一般情形条件于 FlowGoodEv+(2.76)；实际证明仅首格 E=0 exampleGrow。 |
| (5.77) | 64 | 条件 | Lemma 5.10 结论。确定性逐点版 norm_driftF_le 已证；≺ 版条件于 DriftInputs（Lemma 5.9 衰减未对实际模型产出）。第 3 行 Lean 带额外因子 Ξ^{(L−K)}_{u,1}（#121）；Lean 用和代替 max（差常数）。 |
| (5.79) | 64 | 条件 | 确定性形式已证，但 ℓ_u 因子来自 L−K 的衰减（Lemma 5.9，随机，未对实际模型产出）；故作为 ≺ 估计为条件性。 |
| (5.80) | 65 | 条件 | 确定性 norm_eG_le 已证，需 L 衰减（Lemma 5.9）与单圈界 Ξ₂（论文用 (4.5)）；论文此后以 (2.76) 称 Ξ^L_{u,2}≺1，Lean 保留该因子（#121）。(4.5) 本身 Gate 1 未闭。 |
| (5.81) | 65 | 条件 | 确定性 norm_eTens_le（E⊗E 以抽象粘合 J 为参数）已证，需 L 衰减；具体 E⊗E 张量的 ≺ 界经 EEBridge，仍需 Lemma 5.9 输入。 |
| (5.83) | 65 | 条件 | Lemma 5.11 结论；见上。paper-deltas #72：n=2 的 (+,+) 由本引理给出（论文 p.70 误归 (2.76)）。 |
| (5.84) | 65 | 条件 | 积分步确定性已证（以积分层级不等式与被积项界为假设）；输入 (5.20)（实为矩路线 MomentIneq）与 (5.77) 界，后者条件性。 |
| (5.85) | 65 | 换路线 | BDG/鞅项不作路径形式化；由矩不等式 MomentIneq（含 QV 桥 quadVarPairs_Uker_le_norm_eeFun_flow）替代，对实际高斯、任意 Dims、/E/<2、0≤s≤t<1 已编译证明（STATUS 未单列验收）。 |
| (5.86) | 65 | 条件 | 核部分（xi2 电荷的 (7.16) Case 1）确定性已证；E⊗E 的 (5.77) 界需 Lemma 5.9/5.10 输入，条件性。 |
| (5.88) | 66 | 换路线 | Q_t∘(L−K) 的 Itô 方程不作路径形式化：确定性乘积法则 hasDerivAt_Qop_hierarchy 已证；随机部分由矩/生成元路线 MomentIneqQ 替代，实际高斯已证（T1393 验收）。 |
| (5.91) | 67 | 换路线 | 积分 Q-层级（含鞅项）由投影矩不等式 MomentIneqQ 替代：实际高斯、任意 Dims、/E/<2、0≤s≤t<1、C_{n,p}=(n+2)(2p−1) 已证（T1393）。SumZeroDyn.Hierarchy.duhamelQ 为自由字段，不计。 |
| (5.92) | 67 | 条件 | Lemma 5.14 结论，Lean 取较弱的界传递形式 Step3.Lemma514（右端各项 ≺Φ ⇒ Ξ_n≺Λ^{1/2}+Φ，max 扩到整个 [s,t]，#33）；生产者均条件性，见 Lemma 5.14。 |
| (5.94) | 67 | 条件 | 父 Lemma 5.14 条件性；矩路线下为 Rhs514QAt，其核估计已证但快衰减/尺寸输入（依赖 Lemma 5.9、5.10）未对实际模型产出。 |
| (5.96) | 68 | 条件 | Ward 恒等式（L−K 的槽和）与抽象界已证；其余指标求和给 ℓ_u^{n−2} 需 L−K 快衰减（Lemma 5.9），高斯版以 LKDecay 为假设；仅对 QGood 电荷。 |
| (5.97) | 68 | 条件 | (5.95)（已证）与 (5.96)（条件性）之合成。 |
| (5.98) | 68 | 条件 | 核估计已证；但 [Q_u,Θ]∘(L−K) 的快衰减需 L−K 衰减（lkGood 事件，highProb_lkGood 以 LKDecay 为假设），条件性。 |
| (5.100) | 68 | 条件 | (5.98)+(5.99)+(5.96) 之合成；依赖 L−K 衰减与 (5.96)，条件性。 |
| (5.101) | 68 | 条件 | 分解 A=Q_tA+(PA)ϑ_t 已证；O≺ 项依赖 (5.96)（条件性）；矩范数版多一项 Env·P(Ξᶜ)^{1/q}（#157）。 |
| (5.102) | 68 | 条件 | (5.94) 插入 (5.97)(5.100)(5.101) 所得，父 Lemma 5.14 条件性。 |
| (5.103) | 69 | 换路线 | 鞅项 QV 计算+BDG 由 QV 桥与矩不等式替代（常数 C_{n,p}=(n+2)(2p−1)，#155），实际高斯任意 Dims 已证（T1393）；仅在实时间上，用 conj ϑ_u=ϑ_u（#161）。 |
| (5.105) | 69 | 条件 | U⊗U 核估计确定性已证；需 (Q⊗Q)(E⊗E) 的快衰减与 (5.77) 第 4 行（条件性）。T1391 仅给首半（exampleGrow,E=0,[0,1/2]）传输前 QV 包络矩界。 |
| (5.109) | 70 | 条件 | 抽象蕴含已证（给定 Step3.Hyp，含 lemma514 字段 ∀n≥3），额外用 S(2,3)，取 k=n+1（#33）；对实际流需 hyp_flow 的 h514 输入，而 Lemma 5.14 未闭，故条件性。 |
| (5.111) | 70 | 条件 | 步骤逻辑（(5.107)+(5.118)+S(m,k−1)⇒Ξ^{(L)}_{2n+2}≺Ψ²）已证且不用 (5.92)，但签名经 Step3.Hyp 捆绑 lemma514 字段；在 (5.109) 的条件链内。 |
| (5.112) | 70 | 条件 | 直接由 (5.92) 得出，Lemma 5.14 未闭。 |
| (5.113) | 70 | 条件 | 依赖 (5.112)，条件性；不等式部分 ineq_quad/ineq_long 确定性已证。 |
| (5.119) | 71 | 条件 | 步骤逻辑已证（(5.107)、(5.118)、S(2l_m,k−1)），不用 (5.92)，但签名经 Step3.Hyp（含 lemma514 字段）；处于 (5.109) 条件链内。 |
| (5.120) | 71 | 条件 | 确定性不等式 rhs5119≤4Ψ² 已证（仅需 Scales，由 (2.72) 得 scales_flow）；作为 ≺ 界属 (5.109) 条件链。 |
| (5.122) | 71 | 未证 | 启发式说明（(5.92)+(5.121) 的改写），证明不需要，Lean 无对应；其实质依赖 Lemma 5.14（条件性）。 |
| (5.124) | 72 | 未证 | 启发式说明，证明不需要，Lean 无对应。 |
| (5.125) | 72 | 条件 | 由 (5.92)（需 n=2 亦成立）+(2.77) 推出，界传递形式；归纳需先验界 Ξ_n≺A（#36）。flow_sharpLmK 另需 (4.5) 基例 h1、(2.76) 基例 h2，均未闭。 |
| (5.126) | 72 | 条件 | Lemma 5.15 结论（UnifDetDom，u∈[s,t] 一致）；条件于 (2.78) SharpLmKFlow。 |
| (5.133) | 73 | 条件 | 需高概率 QuadInputs（Lemma 5.9 衰减+(2.78) 长度 2 计数）与包络；(2.78)、Lemma 5.9 未对实际模型闭合。 |
| (5.134) | 73 | 条件 | 拆分恒等式已证；论文的 '≺W·ℓ_u·max/E[…]/' 若按一致界 Λ 转写（hG）为假，ℓ_u 来自 3-loop 衰减（#127，Lean 侧问题）；衰减输入条件性。 |
| (5.135) | 73 | 条件 | 需 EGInputs（Lemma 5.9 衰减与幂次计数）、(5.126)（条件于 (2.78)）、(2.78)。 |
| (5.136) | 73 | 条件 | (5.129)–(5.131)+(7.14)⇒(5.136) 确定性已证（藏有 log((1−s)/(1−u))，靠 (2.72)，#37）；实际高斯 (2.80) 汇总仍需 FlowInputs、Step3.Hyp(含 Lemma514)、Lemma514 n=2、h1、h2、(2.78)。 |
| (6.1) | 74 | 换路线 | 分布相等未字面形式化；在H_u=√u·X模型中是逐点恒等式L̃_{t₁}=(t₁/t₂)^{n/2}L_{t₁}（已证），以≺转移形式LoopScaling供Lemma 5.1；(6.1)只涉单时刻律，替代无损；替代物已证 |
| (7.25) | 81 | 仅特例 | 方差 E/H̃_xy/²=(1−ζ)S_xy+ζ/N 对固定时刻边缘 e^{-t/2}X+√ζ G 证明(任意 Dims、N、t≥0，T1420 公共载体)；H̃=H_{tU} 作为 OU 路径未构造，未与 OUFlow/Eq747 的 F.Ht 连接。 |
| (7.26) | 81 | 未证 | 分布恒等 (7.26) 只作为 Eq747Inputs.law726(期望形式，全 N/σ₂/a,b)的假设出现；两相布朗流未构造，GUEFlow 无分布。V6-OU-terminal-726 与 Brownian-path 预检：HOLD。 |
| (7.27) | 81 | 条件 | 抽象自举：对任意 Lm/Dm/Km，若 (7.45) 的 ≺ 界 h745、(7.36) 的 K 界 hK、w.h.p. 时间连续性成立则得 (7.27)；从未对实际 GUE 相 loop 实例化；对 n 的归纳改为 2..n₀ 同时连续性论证。 |
| (7.28) | 81 | 条件 | 同 (7.27)：以 h746 与长度至 2n₀ 的 (7.27) 为假设的抽象自举，未对实际 loop 实例化；(7.46) 本身未证。 |
| (7.29) | 81 | 未证 | 未形式化(GUEPhase 头注 '(7.29) itself ... not formalized')；仅在 t₀、σ=(+,±) 作为 Eq747Inputs.eq729 假设，K 取闭式 kTwoGUE(与论文 K̃ 等同需未形式化的 ODE 唯一性)。 |
| (7.31) | 82 | 条件 | K 部分=Lemma 2.17((2.59), norm_Kval_le 确定性已证)；L 部分=Lemma 2.18(条件于 Thm221，Gate 1–2 未闭)且需 t≤t₁ 时 L̃_t~L_t 同分布(GUEFlow 无分布，未证)；GUE 相无专门陈述。 |
| (7.32) | 82 | 条件 | t=t₁ 由 (7.31) 与 ℓ_{t₁}=L 得到；K 部分确定性可得(norm_Kval_le+ellHat_eq_L，未组装成单一定理)，L 部分依赖 Lemma 2.18 与同分布(未证)；Lean 中仅以 h732/hinit 假设出现。 |
| (7.37) | 82 | 未证 | GUE 相 Duhamel 表示(Lemma 5.3/5.5 取 s=t₁，配 Lemma 7.1)未对该流证明，在 eq745_of_terms 中为假设 hduh(T58 占位)；GUE 相无矩路线替代。 |
| (7.38) | 82 | 未证 | BDG 鞅不等式未形式化(仓库无滤子/鞅)，在 eq745_of_terms 中为假设 hmart。 |
| (7.41) | 83 | 未证 | E^{(G̃)}≺N·L₂·L_{n+1} 需对 G̃_t 证 (4.5)，未形式化；eq742_of 以其为输入。 |
| (7.42) | 83 | 条件 | eq742_of 证实数约化 (7.41)+Cauchy–Schwarz+(5.117)⇒(7.42)，三者为假设；(5.117) 确定性已证(loopMax_two_mul_add_le)，(7.41) 未证。 |
| (7.43) | 83 | 未证 | S_GUE 常数阵下用 Ward 恒等式对 b,b′ 求和的 E⊗E 界未形式化；eq744_of 以其为假设。 |
| (7.44) | 83 | 条件 | eq744_of：(7.43)+(5.117)⇒(7.44) 的实数约化已证，(7.43) 未证。 |
| (7.45) | 83 | 条件 | eq745_of_terms 逐路径把 (7.37)(7.38)(7.39)(7.40)(7.42)(7.44)(7.32) 组合为 (7.45)，但 hduh/hmart/hF/hinit 均为假设；eq727 以 ≺ 形式假设 h745。 |
| (7.46) | 84 | 条件 | 只定义右端 rhs746 并在 eq728 中以 ≺ 假设 h746 使用；无组合定理((7.41)(7.43) 未证)。 |
| (7.47) | 84 | 条件 | eq747_of_inputs：由 Eq747Inputs(law726=(7.26) 期望式、eq729=(7.29) 于 t₀、可积性)推出 Eq747(QDExpect 形式，误差 W^δ(Nη)^{-3})；输入均未证，F/G 无分布；需 /E_N/≤2、0≤ζ≤1。 |
| (A.2) | 85 | 条件 | 启发式；其中chain↔loop恒等式已证；尺寸界的严格版即(A.3)(A.4)，状态同Lemma A.2 |
| (A.3) | 85 | 条件 | 对角部分；同Lemma A.2 |
| (A.4) | 85 | 条件 | 非对角部分；同Lemma A.2 |
| (A.7) | 86 | 条件 | 归纳步确定性版已证，但依赖未释放的ChainLDE16/19、LoopBound、/1/G_ii/≤K假设 |
| (A.12) | 86 | 换路线 | (A.12)本身未证；总装改用单边比较/C^(ii)−C/≤c_D(B+Ξ^(o)_n)Φ^{-n}（确定性已证），其所在Lemma A.2仍conditional（paper-deltas#40） |
| (A.14) | 86 | 条件 | 实数自举闭合已证，但依赖ChainLDE16与LoopBound假设 |
| (A.16) | 87 | 条件 | 精确部分已证；[39]LDE作为假设ChainLDE16未对高斯模型释放；误差项改用C E C†半正定性而非4n-loop |
| (A.17) | 87 | 条件 | 依赖ChainLDE19假设 |
| (A.19) | 87 | 条件 | 精确部分已证；LDE为未释放假设ChainLDE19；论文(C E C†)_jj应为(C† E C)_jj（paper-deltas#34） |
| (A.20) | 87 | 条件 | (A.18)+(A.19)+LDE⟹(A.20)确定性已证，LDE假设未释放 |
| (A.25) | 88 | 换路线 | 只证精确迹恒等式，论文的乘积界未写出；作用由单边比较取代（见(A.12)） |
| (B.6) | 91 | 换路线 | dyadic分解(B.6)未形式化；其作用（证(2.53)(2.54)）由d=1闭式解路线在整个圆盘/ξ/<1上完成（已证） |
