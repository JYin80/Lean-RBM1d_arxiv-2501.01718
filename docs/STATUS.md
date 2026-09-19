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
