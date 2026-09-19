# 进度（对照论文编号）

工具链：Lean 4.34.0 / Mathlib `5ed2965256`。构建：macOS 本机，`./watch.sh` 自动编译到 `build.log`。

## 已完成（0 sorry，公理审计只含 propext / Classical.choice / Quot.sound）

### `RBM1D/Defs/Block.lean` — 论文 §2.1

| Lean | 论文 |
|---|---|
| `RBM.SB` | `S^(B)_{ab} = (1/3)·1(dist ≤ 1)`，实现为 `Matrix.circulant` |
| `RBM.SB_isSymm` / `SB_transpose` | 对称性 |
| `RBM.SB_apply_add_right` | 平移不变 |
| `RBM.card_sbSupport` | `L ≥ 3` 时 `{0,1,-1}` 三点互异（论文隐含假设，见 paper-deltas.md） |
| `RBM.sum_SB_row` | 行和 = 1 |
| `RBM.SB_mulVec_one` | `S^(B) 1 = 1`（(3.47)、Lemma 3.6 Step 4 要用） |

### `RBM1D/Propagator/Basic.lean` — Definition 2.13 + Lemma 2.14

| Lean | 论文 |
|---|---|
| `RBM.norm_SB` | `‖S^(B)‖ = 1`（ℓ∞ 算子范数） |
| `RBM.Theta` | Def 2.13，`Θ_ξ = (1 - ξ S^(B))⁻¹` |
| `RBM.Theta_mul` / `mul_Theta` | 双边逆 |
| `RBM.eq_Theta_of_mul` | 逆的唯一性（下面几条都靠它） |
| `RBM.Theta_transpose` / `Theta_isSymm` | **Lemma 2.14 (1)** 对称 |
| `RBM.Theta_apply_add_right` | **Lemma 2.14 (2)** 平移不变 |
| `RBM.Theta_commute_SB` / `Theta_commute` | **Lemma 2.14 (3)** 可交换 |
| `RBM.Theta_eq_tsum` | **Lemma 2.14 (5)** 随机游走表示 `Θ_ξ = ∑ ξ^k (S^(B))^k` |
| `RBM.sum_Theta_row` | `∑_b (Θ_ξ)_{ab} = (1-ξ)⁻¹`（(3.47)–(3.48) 要用） |

设计要点：Θ 用 `Ring.inverse` 定义，(1)(2)(3) 全部由**逆的唯一性**从 `S^(B)` 的相应性质推出，
不走 Neumann 级数的逐项论证；(2) 用 `Matrix.submatrix` 沿 `Equiv.addRight c` 共轭。

### `RBM1D/Propagator/Deriv.lean` — (2.51)

| Lean | 论文 |
|---|---|
| `RBM.Theta_sub_Theta` | 预解式恒等式 `Θ_ζ - Θ_ξ = (ζ-ξ) Θ_ζ S Θ_ξ` |
| `RBM.continuousAt_Theta` | `ξ ↦ Θ_ξ` 连续 |
| `RBM.hasDerivAt_Theta_apply` | **(2.51)** `∂_ξ Θ_ξ = Θ_ξ S^(B) Θ_ξ`（逐元素形式） |

(2.51) 陈述成逐元素，一是第 3 节本来就全是逐元素求和，二是避开 Matrix 上
Pi 拓扑与范数拓扑的实例菱形（`HasDerivAt` 现在按一般拓扑向量空间陈述）。

### `RBM1D/Propagator/Bounds.lean` — (3.35)(3.36)

| Lean | 论文 |
|---|---|
| `RBM.norm_entry_le_norm` | 元素被 ℓ∞ 算子范数控制 |
| `RBM.norm_Theta_le` / `sum_norm_Theta_row_le` | **(3.36)** `max_a ∑_b \|Θ_ab\| ≤ (1-\|ξ\|)⁻¹` |
| `RBM.norm_Theta_apply_le` | **(3.35)** 逐元素界 |

### `RBM1D/Defs/Dist.lean` + `RBM1D/Propagator/Support.lean`

| Lean | 内容 |
|---|---|
| `RBM.zdist` | 循环图 `ZMod L` 上的图距离，含三角不等式 |
| `RBM.SB_pow_apply_eq_zero` | `(S^(B))^k` 在带宽 `k` 外为零 |
| `RBM.Theta_eq_geom_add` | 截断 Neumann 级数 `Θ = ∑_{k<N} (ξS)^k + (ξS)^N Θ` |
| `RBM.norm_Theta_apply_le_pow` | 初步指数衰减 `\|Θ_xy\| ≤ \|ξ\|^{dist(x,y)}/(1-\|ξ\|)` |

## 进行中 / 下一步

1. **Lemma 2.14 (4) 的锐化版 (2.52)**。上面的 `norm_Theta_apply_le_pow` 已经是真正的指数衰减，
   但衰减长度由 `1-|ξ|` 控制；论文要的是由 `|1-ξ|` 控制，即 `ℓ̂(ξ)=min(|1-ξ|^{-1/2},L)`。
   两者在 `ξ = t m²`（`|ξ|→1` 而 `|1-ξ|` 保持 O(1)）时差别巨大，正是论文关心的区制。
   计划：构造 `ρ(ξ)`（`ρ²-(3/ξ-1)ρ+1=0` 中模 <1 的根），证 `(Θ_ξ)_{xy}=c(ξ)(ρ^d+ρ^{L-d})`，
   再由此读出 (2.52)(2.53)(2.54)。
2. Section 3 的组合层：Def 2.9/2.10 的 loop 与 cut-and-glue 算子。
3. 蓝图渲染需要 `pip install leanblueprint`（见 `blueprint/README.md`）。

---

# 工作单：(2.52) 锐化衰减（在 Claude Code 里做）

数学部分已在 Cowork 侧推完并交叉验证，这里只剩 Lean 落地。**不要重新推导，照抄下面的公式。**

## 1. 方程

`Θ = circulant k`，`S = circulant s`，`s` 支撑在 `{0,1,-1}` 上取 `1/3`。
`circulant s * circulant k = circulant (circulant s *ᵥ k)`，而
`(circulant s *ᵥ k)(u) = (1/3)(k(u-1) + k(u) + k(u+1))`。
于是 `(1 - ξS)Θ = 1` 逐点等价于

    k(u) - (ξ/3)[k(u-1) + k(u) + k(u+1)] = δ_{u,0}      (★)

取 `ξ ≠ 0`，乘 `-3/ξ`，记 `c := 3/ξ - 1`，齐次部分的特征方程是

    ρ² - c·ρ + 1 = 0,    两根之积 = 1

## 2. 根不在单位圆上（这是整件事的关键，也是 Lean 里最需要小心的一步）

设 `|ρ| = 1`。由 `ρ·ρ' = 1` 得 `ρ' = 1/ρ = conj ρ`，于是
`c = ρ + conj ρ = 2·Re ρ ∈ ℝ` 且 `|c| ≤ 2`。
由 `c = 3/ξ - 1` 得 `3/ξ = c + 1 ∈ ℝ`，`|c+1| ≤ 3`，且 `c+1 ≠ 0`（否则 `3/ξ = 0`）。
故 `ξ = 3/(c+1)` 是实数且 `|ξ| = 3/|c+1| ≥ 1`，与 `|ξ| < 1` 矛盾。∎

因为两根之积为 1，所以**恰有一根在单位圆内**。记它为 `ρ(ξ)`。

同时得到 `ρ ≠ ±1`：`ρ = 1 ⟺ c = 2 ⟺ ξ = 1`，`ρ = -1 ⟺ c = -2 ⟺ ξ = -3`，都不在 `|ξ| < 1` 内。
又 `|ρ| < 1` 给出 `ρ^L ≠ 1`。这两条保证下面的分母非零。

## 3. 闭式解

    (Θ_ξ)_{xy} = A(ξ) · (ρ^d + ρ^{L-d}),      d = (x - y).val ∈ [0, L)

    A(ξ) = 3ρ / [ ξ · (ρ^L - 1) · (ρ² - 1) ]

推导要点（Lean 里就按这个分情况）：令 `F(n) = A(ρ^n + ρ^{L-n})`，`n ∈ ℤ`。`F` 对所有 `n` 满足齐次递推。

- `1 ≤ d ≤ L-2`：三个邻点分别是 `F(d-1), F(d), F(d+1)`，齐次成立，(★) 左边 = 0 ✓
- `d = L-1`：`u+1` 的 val 是 `0`，而 `F(0) = A(1 + ρ^L) = F(L)`，**这正是闭式取对称形式的原因**。
  于是三元组是 `F(L-2), F(L-1), F(L)`，齐次成立 ✓
- `d = 0`：`u-1` 的 val 是 `L-1`，用到的是 `F(L-1)` 而非 `F(-1)`。差额
      `F(L-1) - F(-1) = A(ρ^L - 1)(ρ⁻¹ - ρ)`
  于是 (★) 左边 `= -(ξ/3)·A(ρ^L-1)(ρ⁻¹-ρ)`，令其 `= 1` 即定出上面的 `A(ξ)`

## 4. 交叉验证（已做，务必在 Lean 里也留一条）

对闭式求行和：

    Σ_{d=0}^{L-1} A(ρ^d + ρ^{L-d}) = A·(ρ^L - 1)(1 + ρ)/(ρ - 1) = 3ρ / [ξ(ρ-1)²]

而由特征方程 `ρ² + 1 = (3/ξ - 1)ρ` 得 `ξ(ρ-1)² = 3ρ(1-ξ)`，故行和 `= 1/(1-ξ)`。

这与**已经独立证明的** `RBM.sum_Theta_row` 完全吻合 —— 闭式没抄错。
建议在 Lean 里把这条也证出来当作 regression test。

## 5. 衰减长度为什么是 |1-ξ|^{-1/2}

令 `ξ = 1 - ε`，则 `c = (2+ε)/(1-ε) ≈ 2 + 3ε`。设 `ρ = 1 - δ`，由 `ρ + ρ⁻¹ = c` 得 `δ² ≈ 3ε`，即

    δ ≈ √3 · |1-ξ|^{1/2},      衰减长度 ~ 1/δ ~ |1-ξ|^{-1/2}

在 `L` 比它小时被 `L` 截断，正好是 `ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)`。
前因子也对得上：`L ≫ ℓ̂` 时 `ρ^L ≈ 0`，`|A| ≈ 3/(2δ) ~ ℓ̂`，而 (2.52) 的前因子
`1/(|1-ξ|·ℓ̂) ≈ 3/δ² · δ = 3/δ`，同阶。

## 6. Lean 落地顺序

**先写数值检查，再写证明**（防止闭式抄错却证明通过）：

1. `RBM1D/Test/Sanity.lean`：`L = 5, 7`，`ξ = 1/2`（此时 `c = 5`，`ρ = (5-√21)/2`，是无理数，
   所以数值检查改用 `(1 - ξS)·Θ = I` 在 `ℚ` 上 `decide`，闭式那条用 `norm_num` 验
   `ρ² - 5ρ + 1 = 0` 与 `A` 的定义式即可）
2. `RBM1D/Propagator/Root.lean`：构造 `ρ`
   - 用 `IsAlgClosed.exists_pow_nat_eq` 取 `w` 使 `w² = c² - 4`，两根 `(c ± w)/2`
   - `rho_mul_rho' = 1`、`rho_add_rho' = c`
   - `norm_rho_lt_one`：按 §2 的论证
   - `rho_sq_ne_one`、`rho_pow_L_ne_one`
3. `RBM1D/Propagator/Decay.lean`：
   - `theta_apply_closed_form`：把闭式代回验证 `(circulant k) * (1 - ξ • SB) = 1`，
     再用**已有的** `RBM.eq_Theta_of_mul` 收口。这是有限的 `ZMod` 分情况代数，按 §3 的三种情况写。
   - `sum_closed_form`（§4 的交叉验证）
   - `theta_apply_le_pow_zdist`：`|Θ_xy| ≤ 2|ρ|^{zdist(x-y)} · |A|`
   - `(2.52)`：把 `|ρ|` 与 `|1-ξ|` 的关系做成显式不等式（常数不求最优，用 `∃ C c > 0, ∀ ...`）

`ξ = 0` 单独处理：`Θ = 1`（`Ring.inverse 1 = 1`），闭式不适用。

## 7. 注意

- `d = (x-y).val`，不是 `zdist`。`zdist = min d (L-d)`，只在最后放缩时出现。
- `ρ^d + ρ^{L-d}` 对 `d` 和 `L-d` 对称，这既给出 `Θ` 的对称性（已独立证明，可交叉验证），
  也是 `d = L-1` 那个 wrap 情况成立的原因。
- 不要动附录 B 的 Fourier 路线，那是 `Propagator/Symbol.lean` 的独立任务，(3.48) 才用得到。
