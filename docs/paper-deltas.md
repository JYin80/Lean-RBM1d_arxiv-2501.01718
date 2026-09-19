# 形式化过程中对论文的修正 / 补充假设

记录所有「Lean 里的陈述 ≠ 论文字面陈述」的地方。每条给出：论文位置、问题、
形式化里怎么处理、以及是否影响主定理。

| # | 论文位置 | 问题 | 处理 | 影响 |
|---|---|---|---|---|
| 1 | §2.1, `S^(B)_{ab} = (1/3)·1(dist_{Z_L}(a,b) ≤ 1)` | 论文未显式要求 `L ≥ 3`。但 `L = 1` 时行和 = 1/3，`L = 2` 时 `1 = -1`，行和 = 2/3，随机性 `∑_b S^(B)_{ab} = 1` 失效 | Lean 中把 `3 ≤ L` 作为显式假设写进所有涉及随机性的引理（`RBM.sum_SB_row` 等） | 无。论文关心 `L → ∞`，`L ≥ 3` 自动满足 |
| 2 | Def 2.1 (ii)，确定性 `≺` | 论文 (ii) 只说「对非负确定量」，没写一致性；但 (2.53)(2.54) 等是对格点一致成立的，且 (i) 本身是「uniformly in u ∈ U(N)」 | `RBM.UnifDetDom` 带参数族 `U : ℕ → Type*`，`N₀` 与 `u` 无关；`RBM.DetDom` 是单点参数的特例。定义里**不要求非负**，需要非负的引理（自反、乘法、常数吸收）显式带非负假设 | 无。对非负量与论文定义一致 |
| 3 | §2.1，`S = S^(B) ⊗ S_W`、(2.5) 的 `E_a` | 论文用 `Z_N` 作指标、`α ∈ {1,…,W}`，而块 `I_a = {aW,…,aW+W−1}` 实际上是 0 起的偏移 | Lean 以块/偏移 `ZMod L × Fin W`（偏移 0 起）为主指标：`Svar = SB ⊗ₖ SW`、`Eblk`。论文原式在 `ZMod (W*L)` 上照写为 `Spaper`、`Epaper`，经双射 `i ↦ (⌊i/W⌋, i mod W)` 证明逐元素相等（`Spaper_eq`、`Epaper_eq`、`split_bijective`） | 无 |
| 4 | Def 2.10 (2) 后的注记「`a_n, a_1` are always in `G^{(a),L}_{k,l}` for any k,l」 | `a_n` 确实总在左 loop 里；但 `k = 1` 时左链是 `E_{a_l},…,E_{a_n}`，不经过 `E_{a_1}`，新 loop 的标号是 `(a, a_l, …, a_n)`，不含 `a_1` | 证明精确版：`getLast?_cutGlueL`（`a_n` 总在）、`head?_cutGlueL_of_two_le`（`k ≥ 2` 时 `a_1` 在首位）、`head?_cutGlueL_one`（`k = 1` 时首位是新标号） | 无，只是注记不精确，定义本身无歧义 |
| 5 | Thm 2.2 的证明 (2.10) | 论文由 local law (2.3) 以高概率给出 `G = O(1)` 再代入 (2.10) | 只形式化确定性部分：(2.10) 本身（`sq_norm_eigenvector_le_im_green`），以及「若 `‖G_xx(λ_k+iη)‖ ≤ C` 则 `|ψ_k(x)|² ≤ Cη`」（`sq_norm_eigenvector_le_of_norm_green_le`）。`G` 的界作为假设。特征值按 Mathlib 的 `IsHermitian.eigenvalues` 编号（不保证论文的 `λ_1 ≤ … ≤ λ_N` 次序），陈述对每个 `k` 成立故无影响 | 概率部分待随机层 |
| 6 | Def 2.12「`K` is the unique solution」、Example 2.15 | (a) 论文把 `K` 定义为唯一解；(b) (2.57) 里 `Θ_{t m₁m₂}` 只在 `‖t m₁ m₂‖ < 1` 时有定义，论文隐含 | (a) `IsPrimitive` 是谓词（给定时间集 `T` 上满足 (2.48)、`t=0` 初值、`n=1` 特例），存在唯一性未证；`m` 作参数。(b) `hasDerivAt_kTwo` 显式带 `‖t m₁ m₂‖ < 1`；`‖m‖ = 1`、`t < 1` 时成立 | 无 |
| 7 | Def 2.7 `m^{(E)} := lim_{ε→0+} m_sc(E+iε)`；Lemma 2.8 | (a) 论文用极限定义 `m^{(E)}`，Lemma 2.8 又说它是 `m(m+E) = −1` 且 `Im m > 0` 的解；(b) Lemma 2.8 的 `t = m_sc(z)²/(m^{(E)})²` 写成复数 | (a) Lean 用显式公式 `mE E = (−E + i√(4−E²))/2`，证明它满足方程且 `|E|<2` 时是唯一满足 `Im > 0` 的根（`eq_mE`），极限定义未形式化；`m_sc` 定义为 `m²+zm+1=0` 中虚部为正的根。(b) `lemT z := ‖m_sc(z)‖²`（实数），`lemT_eq` 证明它等于论文的复数表达式。(2.40) 与 `|E| ≤ 2−cκ`、`t ≥ c_κ` 推迟到随机层 | 无 |
| 7 | Def 3.1、Lemma 3.2，`T SP (P_a)` | 论文的 `T SP` 是典范划分等价类对应的树，要平面几何；Lemma 3.2 证明它与无交叉非相邻对集合一一对应 | **不是偏离，是把论文的分类定理当定义**：`RBM.TSP n` 直接定义为 `diagonals n` 的无交叉子集（`Loop/Crossing.lean`），Lemma 3.2 被引用而非证明。代价：Def 3.1 的几何不在形式化范围内；收益：第 3 节剩下的组合全部可 `decide`。下标 0-based（论文顶点 `i` ↦ `i−1 : Fin n`）。回归：`TSP 4` = Figure 6 的三张图，`#TSP 5 = 11`、`#TSP 6 = 45`（小 Schröder 数） | 无 |
