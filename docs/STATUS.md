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


---

# CI / 站点

- 仓库：https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718
- 站点：https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/
- **只有 push 才会发布。** `docgen-action` 的上传与部署步骤条件是
  `github.event_name == 'push'`，手动 Run workflow 会「成功」但什么都不发布。
- Mathlib 不会被重新编译：`lake exe cache get` 拉的是预编译 olean，
  本机 `.lake/packages/mathlib/.lake/build` 约 6.6 GB 已就位。
  只有 `lake update` 换 rev 或改 `lean-toolchain` 才会触发重编译，而两者都锁死了。

# 任务认领

**(2.52) 锐化衰减由 Cowork 侧接手**（2026-09-19）。原计划交给 Claude Code，
但那边尚未开工，为避免闲置改由 Cowork 做。Claude Code 若要接手，先在此处改认领标记，
避免两边重复劳动。


---

# 更新 2026-09-19：闭式解已证

`RBM1D/Propagator/Root.lean` 和 `RBM1D/Propagator/Decay.lean`，全绿 0 sorry。

| Lean | 内容 |
|---|---|
| `RBM.rho` / `norm_root_ne_one` / `norm_rho_lt_one` | 特征根 ρ(ξ)，模 < 1；两根都不在单位圆上 |
| `RBM.kern` / `kern_rec` / `kern_zero_eq_kern_L` | 齐次三项递推；两端相等 |
| `RBM.kern_defect` | n = 0 处的亏损，定出常数 A(ξ) |
| `RBM.thetaKernel_rec` / `thetaKernel_eq` | 逐点恒等式 |
| **`RBM.theta_eq_circulant`** | **闭式解 Θ_ξ = circulant(A(ρ^d + ρ^{L−d}))** |
| `RBM.theta_apply_closed_form` | 逐元素形式 |
| `RBM.norm_theta_apply_le_rho_pow` | `‖Θ_xy‖ ≤ 2‖A‖·‖ρ‖^{zdist(x−y)}` |

## 关于工作单里的数值自洽检查

原计划先写 `L = 5, 7` 的数值检查防止闭式抄错。**现在不需要了**：`kern_defect`
（那条定出 A(ξ) 的等式）如果 A 抄错就根本证不出来，闭式已经是定理而非猜测。
`sum_Theta_row` 的交叉验证同理——`theta_eq_circulant` 已证，它自动成立。

## 下一步

`norm_theta_apply_le_rho_pow` 的衰减率是 `‖ρ(ξ)‖`，论文 (2.52) 要的是
`exp(−c·dist/ℓ̂(ξ))`，`ℓ̂(ξ) = min(|1−ξ|^{−1/2}, L)`。缺的是定量桥梁：

    1 − ‖ρ(ξ)‖ ≍ |1 − ξ|^{1/2}

（渐近推导见上面的工作单 §5：ξ = 1−ε、ρ = 1−δ 给出 δ² ≈ 3ε）。
这是纯复分析的估计，与矩阵无关，可以独立做。
还需要 `‖A(ξ)‖` 的上界，配合 (2.52) 分母上的 `|1−ξ|·ℓ̂(ξ)`。


---

# T1 进展：平方根从哪来

由 `rho_eq` 与 `cc ξ = 3/ξ − 1` 直接得到**精确恒等式**（非渐近）：

    ξ (1 + ρ + ρ²) = 3ρ          `RBM.xi_mul_poly`
    (1 − ξ)·3ρ = ξ (1 − ρ)²      `RBM.one_sub_xi_mul`

即 `1 − ξ = (1−ρ)² / (1+ρ+ρ²)`。

**这就是 ℓ̂(ξ) = |1−ξ|^{−1/2} 里那个平方根的来源**：ξ = 1 对应 ρ = 1，而且是**二重根**。
所以衰减长度 1/(1−ρ) 按 |1−ξ|^{−1/2} 而不是 |1−ξ|^{−1} 标度。

取模得 `RBM.norm_one_sub_rho_sq`：`‖ξ‖·‖1−ρ‖² = 3‖1−ξ‖·‖ρ‖`（精确等式）。

## 还缺什么：方向问题

上面给的是 `‖1−ρ‖` 的**上界**（ξ 近 1 ⟹ ρ 近 1）。但衰减需要的是 `1 − ‖ρ‖` 的**下界**
（ρ 的模离 1 有多远），两者不等价：ρ 可以靠近单位圆但远离 1。

分析：
* **ξ 实、∈ (0,1)**（即论文的 long edge，ξ = t|m|²，因 |m| = 1 故 ξ = t 是实的）：
  此时 c = 3/ξ − 1 > 2 实，两根都是正实数，ρ ∈ (0,1)，于是 `1 − ‖ρ‖ = 1 − ρ`。
  又 `1+ρ+ρ² ∈ (1,3)`，恒等式给出**双边**界

      √(1−ξ) ≤ 1 − ρ(ξ) ≤ √3 · √(1−ξ)

  这正是 (2.52) 要的衰减长度。
* **ξ 复**（short edge，ξ = tm²，|ξ| = t 但 |1−ξ| = O(1)）：衰减长度 O(1)，是更容易的区制。

所以下一步是 **ρ(ξ) 对实 ξ ∈ (0,1) 为实**。这需要证明 `disc ξ`（判别式的平方根，
目前由 `Classical.choose` 取）在 c² − 4 > 0 时是实数 —— 即平方为正实数的复数必为实数。
Mathlib 里应该有类似 `Complex.eq_conj_iff_re` / `Complex.normSq` 的工具可用。

做完之后 (2.52) 的 long edge 情形就完整了。

---

# 更新 2026-09-18（Claude Code）：T5、T6 完成

全量 `./check.sh` exit=0、errors: 0，0 sorry，新声明公理审计只含 propext / Classical.choice / Quot.sound。

### `RBM1D/Defs/Domination.lean` — Def 2.1 (ii)（T6）

| Lean | 内容 |
|---|---|
| `RBM.UnifDetDom` | 确定性 `≺`，对参数 `u ∈ U(N)` 一致（`N₀` 与 `u` 无关） |
| `RBM.DetDom` / `detDom_iff` | 标量版本，逐字对应 Def 2.1 (ii)；scoped 记号 `f ≺ g` |
| `refl` `trans` `add` `mul` `add_left` | 闭包性质（`mul` 等需非负假设） |
| `const_mul` `const_mul_left` `const_mul_right` `DetDom.smul_left` | 常数吸收 |
| `of_eventually_le_const_mul` `of_le` `mono_left` `mono_right` | `f ≤ C g ⇒ f ≺ g` 及单调性 |

偏差见 `paper-deltas.md` #2（一致性显式化、定义不要求非负）。

### `RBM1D/Propagator/Symbol.lean` — 附录 B (B.1)（T5）

频率 `p : ZMod L` 代表 `2πp/L`，平面波 `e_p(x) = ZMod.stdAddChar (p * x)`。不依赖闭式解。

| Lean | 内容 |
|---|---|
| `RBM.Shat` / `Shat_eq_cos` | `Ŝ(p) = (1 + 2cos(2πp/L))/3`，论文原式 |
| `RBM.norm_Shat_le_one` / `one_sub_mul_Shat_ne_zero` | `‖ξ‖ < 1 ⇒ 1 − ξŜ(p) ≠ 0` |
| `RBM.SB_mulVec_apply` | `(S v)(x) = (v x + v(x−1) + v(x+1))/3` |
| `RBM.SB_mulVec_char` | `S e_p = Ŝ(p) e_p` |
| `RBM.inv_mul_sum_stdAddChar` | 特征标正交性 `(1/L)Σ_p e_p(u) = δ_{u0}` |
| `RBM.fourierKernel` / `fourierKernel_sub_SB_mulVec` | `K − ξ S K = δ_0` |
| **`RBM.Theta_eq_circulant_fourierKernel` / `Theta_apply_fourier`** | **(B.1)** |

下游 (3.48) 直接用 `Theta_apply_fourier`。

### `RBM1D/Test/Numeric.lean` — 数值回归测试（T12，Claude Code）

`L = 5, 7`、`ξ = 1/2`，在 `ℚ` 上独立于 `RBM.SB` 按论文重写 `S^(B)`，显式逆矩阵由精确高斯消元给出：
双边验证 `(1 − ξS)Θ = Θ(1 − ξS) = I`，行和 `= 2 = (1−ξ)⁻¹`，特征方程 `ρ² − 5ρ + 1 = 0`。
**`RBM.Numeric.Theta_five_half`**：`RBM.Theta 5 (1/2)` 逐元素等于该有理矩阵（经 `SB_five_apply` 把 `RBM.SB 5` 与独立定义对上，再用 `eq_Theta_of_mul`）。
这个文件编译约 40 秒（L = 7 的两条 `simp` 展开占大头）。

### `RBM1D/Defs/Model.lean` — §2.1 模型层 + (2.5)（T15，Claude Code）

主指标是块/偏移 `ZMod L × Fin W`。论文在 `Z_N` 上的原式也照写了，并证明两者逐元素相等。

| Lean | 内容 |
|---|---|
| `RBM.SW` / `RBM.Svar` | `(S_W)_{αβ} = W⁻¹`，`S = S^(B) ⊗ₖ S_W` |
| `RBM.sum_Svar_row` / `Svar_transpose` | 行和为 1，对称 |
| `RBM.Eblk` | (2.5) 的 `E_a` |
| `RBM.sum_Eblk` / `Eblk_conjTranspose` / `Eblk_mul_Eblk` | `Σ_a E_a = W⁻¹ I`，自伴，`E_a E_b = δ_ab W⁻¹ E_a` |
| `RBM.Iblk` / `mem_Iblk` | `I_a = {aW,…,aW+W−1}`；`i ∈ I_a ↔ ⌊i/W⌋ = a` |
| `RBM.Spaper` / **`Spaper_eq`** | 论文 §2.1 的 `S_ij` 原式 = `Svar` 在 `split` 下 |
| `RBM.Epaper` / **`Epaper_eq`** | (2.5) 原式 = `Eblk` 在 `split` 下 |
| `RBM.split_bijective` / `splitEquiv` | `ZMod (W*L) ≃ ZMod L × Fin W` |

### `RBM1D/Loop/Index.lean` — Def 2.9/2.10 的指标层（T16，Claude Code）

`LoopIdx α`：两条 list `σ : List Bool`（`true` = `+`）、`a : List α`（论文里 `α = ZMod L`），
`WF` 是长度相等。算子取论文的 1 起下标 `k, l`，用 `take`/`drop` 实现。

| Lean | 内容 |
|---|---|
| `cutGlue k b` / `cutGlueL k l b` / `cutGlueR k l b` | `G^{(b)}_k`、`G^{(b),L}_{k,l}`、`G^{(b),R}_{k,l}` |
| `length_cutGlue` / `length_cutGlueL` / `length_cutGlueR` | `n+1`、`k+n−l+1`、`l−k+1` |
| `length_cutGlueL_add_length_cutGlueR` | 两条链长度和 `= n+2` |
| `length_cutGlueL_le` / `length_cutGlueR_le` / `length_cutGlueR_one` | 都 `≤ n`；`k=1, l=n` 时右 loop 等于 `n`，**长度不能直接当归纳量** |
| `two_le_length_cutGlueL/R` | 都 `≥ 2` |
| `WF.cutGlue` / `WF.cutGlueL` / `WF.cutGlueR` | 良构性保持 |
| `getLast?_cutGlueL` / `head?_cutGlueL_of_two_le` / `head?_cutGlueL_one` | `a_n` 总在左 loop；`a_1` 只在 `k ≥ 2` 时在（见 paper-deltas #4） |
| 三个 `example` | Figure 1、2、3，`rfl` 验证 |

下一步（第 3 节）：`L_{t,σ,a}` 本身（需要 Green 函数，定义为 `Tr ∏ G(σ_i) E_{a_i}`，可以对任意矩阵族先定义）。

### `RBM1D/Delocalization.lean` — Thm 2.2 的谱论部分 (2.10)（T13，Claude Code）

| Lean | 内容 |
|---|---|
| `RBM.green` | `G(z) = (H − z)⁻¹` |
| `RBM.green_eq_spectral` / `green_apply_self` | `G = U diag((λ−z)⁻¹) U*`，`G_xx = Σ_l |ψ_l(x)|²/(λ_l − z)` |
| `RBM.im_green_apply_self` | `Im G_xx(E+iη) = Σ_l η|ψ_l(x)|²/((λ_l−E)²+η²)` |
| `RBM.sq_norm_eigenvector_le_sum` / `sum_eq_mul_im_green` / **`sq_norm_eigenvector_le_im_green`** | **(2.10)** 两步 |
| **`RBM.sq_norm_eigenvector_le_of_norm_green_le`** | `‖G_xx(λ_k+iη)‖ ≤ C ⇒ |ψ_k(x)|² ≤ Cη`（Thm 2.2 的确定性内核） |

local law 作为假设，概率部分待随机层（paper-deltas #5）。

### `RBM1D/Loop/Primitive.lean` — Def 2.12 + Example 2.15（T18，Claude Code）

**下标核对通过**：`primRhs_two` 证明一般式 (2.48) 在 n=2 用 `cutGlueL/R` 展开后恰为 (2.55)。
算子给出 `Σ_{a,b} K_{σ,(a,a₂)} S_ab K_{σ,(a₁,b)}`（与工单手算一致，`change` 定义性验证），
对换哑指标 + `S^(B)` 对称即得 (2.55)。`Loop/Index.lean` 的约定与论文一致，无需改动。

| Lean | 内容 |
|---|---|
| `RBM.primRhs` / **`primRhs_two`** | (2.48) 右端；n=2 时 = (2.55) |
| `RBM.primInit` / `RBM.IsPrimitive` | Def 2.12 初值；谓词形式（时间集 `T`，`m : Bool → ℂ` 作参数，n=1 单列） |
| `RBM.kTwo` / **`hasDerivAt_kTwo`** | **Example 2.15**：(2.57) 满足 (2.55)，假设 `‖t m₁m₂‖ < 1` |
| `RBM.kTwo_zero` / `Theta_zero` | `t=0` 时等于 Def 2.12 的初值 |
| `RBM.kTwoLoop` / **`hasDerivAt_kTwoLoop`** | 同上，一般式 (2.48) 的形式 |
| 两条 `example` | (2.58) 的 σ=(+,−)、(+,+) |

等 T19 的 `m_sc`/`m^{(E)}` 落地后，把 `m` 实例化即可。

### `RBM1D/Defs/Semicircle.lean` — Def 2.7 + Lemma 2.8 的代数部分（T19，Claude Code）

| Lean | 内容 |
|---|---|
| `RBM.mE` / `mE_mul` / `mE_im_pos` / **`norm_mE`** / `eq_mE` | `m^{(E)}`：`m(m+E) = −1`，`Im > 0`，**`|m^{(E)}| = 1`**，唯一性 |
| `RBM.mSigma` / `norm_mul_mSigma_lt_one` | (2.42) 的 `m(σ)`；`‖t m₁m₂‖ = t < 1`（T18 的假设由此满足） |
| `RBM.msc` / `msc_mul` / `msc_im_pos` / **`norm_msc_lt_one`** | `m_sc`：`m(m+z) = −1`，`Im > 0`，`|m_sc| < 1` |
| `RBM.zt` / `zt_im` | Def 2.7 `z_t^{(E)} = E + (1−t)m^{(E)}`、(2.35) |
| `RBM.lemE` / `lemT` / **`mE_lemE`** | Lemma 2.8 的 `E`、`t`；关键一步 `m^{(E)} = m_sc/|m_sc|` |
| `lemT_eq` / `lemT_pos` / `lemT_lt_one` / `abs_lemE_lt_two` | `t = m_sc²/(m^{(E)})² ∈ (0,1)`，`|E| < 2` |
| **`msc_eq_sqrt_mul_mE`** / **`eq_inv_sqrt_mul_zt`** | **(2.38)**、**(2.37)** |

`Loop/Primitive.lean` 新增 `hasDerivAt_kTwo_mSigma`：取 `m := mSigma E`，Example 2.15 对 `0 ≤ t < 1` 无条件成立。
(2.40)（T35，储备 B6）已补：`msc_add_eq_neg_inv`、**`abs_lemE_le`**（`|E| ≤ |Re z|`）、**`lemT_ge`**（`t ≥ (1+|z|)⁻²`）、
**`zt_im_lemma28`**（`Im z_t = t^{1/2} Im z`）、**`lemma28_quant`**（论文形式，`c_κ = 1/16`，与 κ 无关；paper-deltas #20）。

---

# 更新 2026-09-19（Claude Code #2）：T17 完成

`RBM1D/Loop/Crossing.lean`，全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。

| Lean | 内容 |
|---|---|
| `RBM.IsDiag` / `RBM.diagonals` | n 边形的对角线 `(i,j)`，`i<j`，模 n 不相邻（`(0,n−1)` 是边） |
| `RBM.Crossing` / `RBM.CrossingFree` | 论文 Lemma 3.2 的交叉条件，严格不等号，共端点不算交叉 |
| `RBM.TSP n` | **定义**为 `diagonals n` 的无交叉子集（Lemma 3.2 引用而非证明，见 paper-deltas #8） |
| `crossing_comm` / `not_crossing_self` / `mem_TSP` / `empty_mem_TSP` | 基本性质 |
| `TSP_three` / `TSP_four` | `{∅}`；`{∅, {(0,2)}, {(1,3)}}` = Figure 6 |
| `card_TSP_five` / `card_TSP_six` | 11、45（小 Schröder 数），纯 `decide`，n=6 需 `maxRecDepth 10000`，约 8 s |

未做：可选的 `F.card ≤ n − 3`。T20 现在可开工。

**git 注记**：T17 的代码与蓝图节点 `def:TSP`、`lem:TSP-small` 被 T19 的提交 `4b108f0`
一并带走（共享 index：我暂存了自己的 hunk，对方的 `git commit` 把整个 index 提交了）。
内容无误，只是提交信息不对应。**教训：共享工作树里不要把东西留在 index 上等待；
用 `git commit -- <文件名>` 一步提交，或者暂存后立刻提交。**

### `RBM1D/Loop/Tree.lean` — Def 3.3 的星图与 n=4（T20，Claude Code）

**判断与发现（工单要求写进这里）：**

1. **n = 4 显示式的边界下标是笔误。** Def 3.3 第 1 条：`a_i` 在 `R_i` 与 `R_{i+1}` 之间，边界边取 `Θ_{t m_i m_{i+1}}`；
   Figure 6 下的显示式写成 `Θ_{t m_{i−1} m_i}`，工单里的星图公式抄的是后者。
   用 Python 有限差分在 `L = 5` 直接核对 (2.48)（用我们的 `cutGlueL/R`，n=2 用 `kTwo`）：
   `Θ_{t m_i m_{i+1}}` 在 n=3、4 误差 `~1e−11`；`Θ_{t m_{i−1} m_i}` 误差 `~1e−2`。内部边两项无误。
   Lean 采用更正后的下标（paper-deltas #8′）。
2. **n = 2 必须特判（工单的猜测正确）。** 星图值是 `Θ²`，`not_hasDerivAt_starK_two` **严格证明**它不满足 (2.55)
   （t=0 处导数是右端的 2 倍）。二角形的树是单条边 `a₁—a₂`，`kTwo_eq_edge`：此时 (3.5) = Example 2.15（paper-deltas #9）。
3. 设计上按工单建议，**不构造图**：树值直接写成求和式；n=4 的三棵树 `starGamma`、`splitGamma₀₂`、`splitGamma₁₃`
   分别对应 `TSP_four` 的 `∅`、`{(0,2)}`、`{(1,3)}`。

| Lean | 内容 |
|---|---|
| `RBM.thetaEdge` / `starGamma` | `Θ_{t m m'}`；星图值 `Σ_b Π_i (Θ_{t m_i m_{i+1}})_{a_i b}` |
| `RBM.starGamma_two` | n=2 星图 = `(Θ·Θ)_{a₀a₁}` |
| **`RBM.not_hasDerivAt_starK_two`** | n=2 星图值**不**解 (2.55) |
| `RBM.kTwo_eq_edge` | n=2 单边树 = Example 2.15 |
| `RBM.gammaFour` / **`gammaFour_eq`** | n=4 显示式（更正下标）= 三棵树之和 —— **一般树值定义的验收标准** |

下一步：一般 `F ∈ TSP n` 的树值（按 `F` 递归劈多边形），在 n=4 化归到 `gammaFour`，n=2 单列；
然后 Lemma 3.4（需 (2.48) 解的唯一性 / Grönwall）。

---

# 更新 2026-09-19（Claude Code #2）：T1c 完成 —— 复 ξ 的衰减率

`RBM1D/Propagator/RateComplex.lean`，全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。
没有动 `Decay.lean`（Cowork 的文件），新文件只 import 它。

对**全部** `0 < ‖ξ‖ < 1`（不只实 ξ）：

    ‖1 − ξ‖ / 8  ≤  (1 − ‖ρ(ξ)‖)²  ≤  3 ‖1 − ξ‖        `RBM.norm_one_sub_xi_le` / `RBM.sq_one_sub_norm_rho_le`
    √(‖1−ξ‖/8) ≤ 1 − ‖ρ‖ ≤ √3 √‖1−ξ‖                  `RBM.rho_complex_bounds`

这解决了上面「T1 进展」里写的**方向问题**：ρ 靠近单位圆但远离 1 的情形被 `‖ξ‖ < 1` 排除了。
关键是一个精确多项式恒等式（`p = Re ρ`，`r = ‖ρ‖`，`(Im ρ)² = r² − p²`）：

    |1+ρ+ρ²|² − 9r² = −4 (r − p − (1−r)²)(r + p) + (r² − 4r + 1)(r² + 1 − 2p)

`r ≥ 1/2` 时第二项 ≤ 0，于是 `‖ξ‖ < 1` ⟹ `r − p ≤ (1−r)²`（ρ 在 1 附近的抛物区域里），
即 `‖1−ρ‖² ≤ 3(1−r)²`。`RBM.sub_re_le_of_poly` 是这一步的纯实变量版本。

**对 T2/T3 的意义**：`norm_AA_le_of_real` 与 (2.52) 目前只对实 ξ；衰减率这一环现在对复 ξ 也有了，
short edge `ξ = t m²` 不需要另写一套论证。常数（8、3）比实情形差，但 (2.52) 只要 `∃ C c`。

---

# 更新 2026-09-19（Claude Code #2）：T23 完成 —— 树表示在 n = 3 成立

`RBM1D/Loop/Example3.lean`（提交 `30a64bc`），全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。
**里程碑达成：Lemma 3.4 的形状在第一个非平凡情形被 Lean 确认。**

| Lean | 内容 |
|---|---|
| `primRhs_three` | 一般 (2.48) 右边在 n=3 的三项 `(1,2),(1,3),(2,3)` |
| `primRhs_three_paper` / `kTwo_rotate` | 与论文展开式逐项对上；回绕项需要 2-loop 的旋转不变（paper-deltas #10） |
| `rhs_kTwo_left` / `rhs_kTwo_right` | 第二步：代入 (2.57)，`W·W⁻¹ = 1` |
| `kThree` / `kThree_eq_starGamma` | 星图值 `W⁻² m₁m₂m₃ Σ_b Θ₁₂ Θ₂₃ Θ₃₁`，与 T20 的 `starGamma` 一致 |
| **`hasDerivAt_kThree` / `hasDerivAt_kLoop3`** | **星图满足 (2.48)**（后者直接用 `primRhs`） |
| `kThree_zero` / `kLoop3_zero` | `t = 0` 时等于 Def 2.12 的初值 |
| `hasDerivAt_kLoop3_mSigma` | 论文的 `m(σ)`、`0 ≤ t < 1` 版本，无需范数假设 |

**给 B2（一般 Lemma 3.4）的结构提示**：证明就是「星的每条边各贡献 (2.48) 的一项」，
两个可复用零件是 `hasDerivAt_thetaEdge`（边的导数 = `μ ΘSΘ`）和
`sum_mul_sum_eq`（`Σ_x M_{ax} Σ_b N_{xb} g_b = Σ_b (MN)_{ab} g_b`，把矩阵因子穿过星的求和）。
n=3 只有星图；一般情形多出的内部边 `Θ − 1` 的导数也是 `μ ΘSΘ`，同一套零件应该够用。
T20 的边界约定 `Θ_{t mᵢ mᵢ₊₁}` 在这里被 ODE 独立验证了一次。

### `RBM1D/Loop/Tree.lean` — 一般树值（T21，Claude Code）

按 T20 的路线，对配对表 `F` 递归定义 Γ，不构造图。

**设计上一个要点（工单公式需要细化）**：若把两个子多边形各自当普通多边形求值再乘 `(Θ−1)`，
新顶点会多带一条边界边 `Θ`，与 n=4 的真值不符。实现方式：多边形的每个顶点带自己的边界矩阵；
劈开时两边的新顶点共享标号 `y`（求和），左边新顶点的矩阵是 `(Θ_{t m_i m_j} − 1)ᵀ`，
右边是单位阵（把右边中心钉在 `y` 上），合起来恰好是中心之间的一条内部边。

| Lean | 内容 |
|---|---|
| `RBM.polyVal` | 递归定义；`termination_by 区域数 + |F|`（注释写明：对角线非相邻 ⇒ 两片都更小） |
| `RBM.leftPairs` / `rightPairs` / `reindexR` | `F` 的分裂与重编号 |
| **`RBM.noncrossing_split`** | 不交叉 ⇒ 整个落在左弧或右弧（一般 n，omega） |
| `RBM.isDiag_split_lt` | 两片边数 `< n` |
| `RBM.treeVal` / `treeSum` / `diagList` | Def 3.3（n ≤ 2 为单边）；(3.5) 的 `Σ_{F∈TSP}`；`F` 按字典序排成列表（固定主元，不需证与选择无关） |
| **`RBM.treeSum_four`** | **验收**：一般定义在 n=4 化归到 `gammaFour`（`{(1,3)}` 项需 `Θ` 对称，论文两项的内部边方向相反） |
| **`RBM.kTwo_eq_treeSum`** | **Lemma 3.4 在 n=2 成立**：`m_σ W⁻¹ Σ Γ = K`（Example 2.15） |

推迟：主元无关性（换一条对角线展开给出同值）——在文件注释里记下了，后续需要时再证。

---

# 更新 2026-09-19（Claude Code #2）：T22 完成 —— (2.48) 解的唯一性

`RBM1D/Loop/Unique.lean`（提交 `c4698e1`），全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。

**`RBM.isPrimitive_unique`**：`IsPrimitive L W m T K`、`IsPrimitive L W m T K'`、`Icc 0 T₀ ⊆ T`，
且两者的 **2-loop** 在 `[0,T₀]` 上有界 `≤ R` ⟹ 对所有 WF、长度 ≥ 2 的 loop 相等。

| Lean | 内容 |
|---|---|
| `LoopIdx.length_cutGlueR_eq_two` / `length_cutGlueL_eq_two` | **结构引理**：一条链满长 n ⟹ 另一条长 2 |
| `eq_on_level` | 归纳一步：低阶相等 + 初值相等 ⟹ 长度 n 相等（Grönwall，`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`） |
| `isPrimitive_unique` | 对 n 强归纳 |

**设计**：工单原本分 n=2（Riccati）和 n≥3（线性）两步；实际上一个估计就够——
每项之差 `(X−X')sY + X's(Y−Y')`，差只在满长链上非零，此时另一因子是有界 2-loop，
得 `‖D'‖ ≤ C‖D‖`。n=2 时「低阶相等」是空条件，这个估计就是 Riccati 右端的 Lipschitz 界。
长度-n 的状态空间用 `List.Vector Bool n × List.Vector (ZMod L) n`（Mathlib 有 Fintype），sup 范数现成。

**给 B2 的接口**：要得到「树和 = K」，只需 (a) 树和满足 `IsPrimitive`，(b) 两者 2-loop 有界。
2-loop 就是 (2.57)，`‖t m₁m₂‖ < 1` 时 Θ 有界。T23 的 `kLoop3` 已满足 (a) 的 n ≤ 3 部分。

---

# 更新 2026-09-19（Claude Code #2）：T8 完成 —— (B.3) 符号的双边界

`RBM1D/Propagator/SymbolBound.lean`（提交 `cc4681c`），全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。
队列空时按「永不停工规则」接的第一条。

**`RBM.norm_one_sub_mul_Shat_asymp`**：对所有 `L`、`‖ξ‖ < 1`、`p : ZMod L` 一致，

    (‖1−ξ‖ + θ(p)²) / (6π²)  ≤  ‖1 − ξ Ŝ(p)‖  ≤  ‖1−ξ‖ + θ(p)²

动量 `θ(p) = 2π·valMinAbs(p)/L ∈ [−π,π]`（`RBM.theta`，`abs_theta_le_pi`），`Ŝ(p) = (1+2cos θ(p))/3`（`Shat_eq_cos_theta`）。
零件：`le_one_sub_cos`（`1 − cos x ≥ 2x²/π²`，|x| ≤ π，Jordan）、`one_sub_cos_le`、`Shat_bounds`。

（已对照论文 p.90 核对：(B.3) 为 `|1−ξŜ(p)| ≍ κ² + |p|_*²`，`κ = |1−ξ|^{1/2}`，与此一致。
本机现在可用 `pypdf`（用户同意后 `pip3 install --user pypdf`）抽取 PDF 文字。）

**下一步（T9）**：无穷体积核 + 围道平移 (B.4)(B.5)，同一文件或新文件。T8 给的下界正是
`1/(1−ξŜ)` 的 Fourier 求和可控的依据。

### T24（+ T7）：硬性公理审计、删 Probe、linter 清理（Claude Code）

* **`#assert_rbm_axioms`**（`RBM1D/Test/Axioms.lean`）：遍历 `RBM` 命名空间的**全部**声明，用 `Lean.collectAxioms`
  （即 `#print axioms` 的底层）收集公理，出现 `propext / Classical.choice / Quot.sound` 之外的任何东西
  （含 `sorryAx`、项目自己的 `axiom`）就**编译失败**；少于 50 个声明也失败（防命名空间改名后空跑）。
  在根文件 `RBM1D.lean` 末尾执行，所以覆盖整个库，没有 import 清单需要同步。已用含 `sorry` 与 `axiom`
  的反例验证它会报错。当前：684 个声明全部通过。随机层引入 `axiom` 接口时须在 `allowedAxioms` 显式登记。
* `RBM1D/Probe.lean` 已删；结论并入 **`docs/mathlib-api.md`**（外加本期新核实的 API 与本工具链的弃用名对照）。
  `CLAUDE.md` 规则 2、3 相应更新。
* linter：我名下文件的警告清零（unused section variables → `omit`，`if_neg` → `ite_eq_right`，
  超长行，未用 simp 参数，maxHeartbeats 注释位置）。`Decay.lean` 与 #2 的文件未动。

### 站点改为定时发布（Claude Code，应用户要求）

`.github/workflows/blueprint.yml` 不再由 push 触发，改为**每 3 小时**（cron `23 */3 * * *`）+ 手动 Run workflow。
原因：多方高频 push 让构建队列不断被取消，文档缓存（仅成功时保存）从未写入，站点一直 404。
`docgen-action` 只在 `push` 事件上构建 API 文档 / Jekyll 并部署，所以新 workflow 只用它编译蓝图与 `checkdecls`，
API 文档（同一脚本、同一 Mathlib 文档缓存）、Jekyll、上传、部署改为 workflow 自己的步骤，**手动 Run workflow 现在也会发布**。

本地：`python3 scripts/blueprint_preview.py` 检查所有 `\lean{}` 名字存在（即 CI 的 checkdecls）与 `\uses{}` 标签，
并生成 `blueprint/preview.html`（依赖图 + 各章节点表；不需要 leanblueprint/graphviz）。

---

# 更新 2026-09-19（Claude Code #2）：T9 完成 —— 无穷体积核与围道平移 (B.2)(B.4)(B.5)

`RBM1D/Propagator/Contour.lean`（提交 `cf1d231`），全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。
另：`SymbolBound.lean` 加了实变量版 `le_norm_one_sub_mul_real`、`cos_symbol_bounds`（提交 `51d81d7`）。

| Lean | 论文 | 内容 |
|---|---|---|
| `Kinf` | (B.2) | `K_{ξ,∞}(u) = (2π)⁻¹ ∫_{−π}^{π} e^{ipu}/D_ξ(p) dp` |
| `norm_cos_add_mul_I_sub_le` | — | `|cos(x+iy) − cos x| ≤ y² + 2|x||y|`（`|y| ≤ 1`） |
| `le_norm_Dxi` | (B.4) | `|p| ≤ π`、`|η| ≤ c₀κ` ⟹ `|D_ξ(p+iη)| ≥ (κ²+p²)/(12π²)`，`c₀ = 1/(16π²)` |
| `integral_kernelFun_shift` | (B.5) 前半 | 围道平移：矩形 Cauchy 定理，竖边因 `2π` 周期相消 |
| **`norm_Kinf_le`** | **(B.5)** | **`|K_{ξ,∞}(u)| ≤ (6π²/κ) e^{−c₀κ|u|}`** |

Mathlib 关键 API：`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`、
`intervalIntegral.norm_integral_le_of_norm_le`（被积函数无需先证可积）、`integral_inv_one_add_sq`、
`Real.cosh_le_exp_half_sq`、`Real.abs_exp_sub_one_le`。

**下一步（T10）**：Poisson 求和 `K_{ξ,L}(u) = Σ_n K_{ξ,∞}(u + nL)`（论文 p.89 (B.2) 下一行），
再由 (B.5) 得环上的 (2.52)。`Symbol.lean` 的 `Theta_apply_fourier` 给出 `K_{ξ,L}` 的有限 Fourier 和。

## 蓝图工件的刷新流程（Cowork 侧，每次心跳执行）

蓝图页面（claude.ai artifact `WjEFtu47pbMNGbUxJhx3Pm`）**由 `blueprint/src/content.tex` 自动生成**，
不再手写。流程固定为三步：

1. `device_stage_files` 把 `blueprint/src/content.tex` 传进云端容器；
2. 在容器里跑 `python3 build.py <content.tex> <定理数>`（脚本在 Cowork 会话的 scratchpad 里）：
   它解析每个 `\begin{...}\label{...}` 环境，按 `\chapter{}` 分节，按 `\leanok` 判「已证」，
   按 `\uses{}` 的依赖是否全绿判「可开工」，用 graphviz 逐章画依赖图，再套模板输出 HTML；
3. `Artifact publish` 到同一个 URL。

**所以：往 `content.tex` 里加节点、标 `\leanok`、写 `\uses{}`，蓝图页面下次刷新就会自动反映。**
Claude Code 侧只要维护 `content.tex` 即可，不必碰页面。
节点的中文短名在 `build.py` 的 `SHORT` 字典里；没登记的节点回退到 LaTeX 标题。

---

# 更新 2026-09-19（Claude Code #2）：T10 完成 —— 周期化与复 ξ 的 (2.52)

全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。

**`Propagator/Poisson.lean`**（`870f86d`）：论文 (B.2) 下一行 `Θ_xy = Σ_n K_{ξ,∞}(u + nL)`（`Theta_apply_periodize`）。
**没走 Fourier 反演**，而是用逆的唯一性：`∫_{−π}^{π} e^{ipw} = 2πδ_{w0}` ⟹ `K_∞ − ξSK_∞ = δ₀` 于 ℤ（`Kinf_sub_SB`）；
由 (B.5) 周期化绝对收敛（`summable_Kinf_shift`）且在 ℤ_L 上解同一方程（`perK_sub_SB_mulVec`）；
其 circulant 与 `Theta_eq_circulant_fourierKernel` 同法用 `eq_Theta_of_mul` 收口。

**`Propagator/DecayComplex.lean`**（`d70e341`）：**(2.52) 对所有 `‖ξ‖ < 1`**（`norm_Theta_apply_le_complex`）

    ‖Θ_xy‖ ≤ C · exp(−c₀·zdist(x−y)/ℓ̂) / (‖1−ξ‖·ℓ̂),   ℓ̂ = ellHat L ξ,  c₀ = 1/(16π²)

照论文 p.90 分两区：`κL ≥ 1` 用周期化 + (B.5) + 两条几何级数（`tsum_exp_neg_abs_shift_le`）；
`κL < 1` 用 (B.1) + (B.3)，零模 `1/(κ²L)`，其余 `(3/2)ZL`（`Z = Σ_{n≠0} n⁻²`，`zetaTwoInt`，未求值）。
陈述形状与 Cowork 的实版本 `norm_Theta_apply_le_of_real` 一致（同一 `ellHat`、`zdist`），可直接替换或并用。
这条只用 T8–T10 的一般 Fourier 机器，不用最近邻闭式，所以是一般 variance profile 时仍然成立的那条证明。

**T11（下一步）**：(2.53)(2.54) 的 dyadic 分解证明（论文 p.90–91 (B.6)）。
Cowork 已用闭式证了实 ξ 的 (2.53)（`e118333`）；T11 是一般机器版本，难点是离散分部求和。

### `RBM1D/Loop/Ward.lean` — Lemma 3.6 Step 1（T26 进行中，Claude Code）

| Lean | 内容 |
|---|---|
| `RBM.etaT` / `etaT_eq_zt_im` | `η_t = (1−t) Im m = Im z_t`（(2.35)） |
| `RBM.mE_mul_conj` / `mE_sub_conj` | `m m̄ = 1`、`m − m̄ = 2i Im m` |
| **`RBM.ward_two`** | (3.13) 在 n=2，即 (3.16)：两边都是 `W⁻¹(1−t)⁻¹` |
| `RBM.mul_Theta_sub_mul_Theta` | `m A − m' B = (m − m') A B`（`m ξ₂ = m' ξ₁` 时） |
| **`RBM.ward_three`** | (3.13) 在 n=3（`kThree`，σ = (+, σ₂, −)） |

**剩余（一般 n，论文 Step 2–5）**：对满足 `IsPrimitive` 的 `K` 定义 `D = Σ_{aₙ} K − (K⁺ − K⁻)/(2Wiη_t)`，
证 `∂_t D = W Σ_k Σ_{a,b} D(a_k→a) S_ab K_{(σ_k,σ_{k+1}),(a_k,b)} + D/(1−t)`（(3.18)）与 `D(0) = 0`，
再用 #2 的 Grönwall（`Loop/Unique.lean` 的 `eq_zero_of_abs_deriv…` 那一套）得 `D ≡ 0`。
难点在 (3.18) 的推导：要把 `primRhs` 在 `Σ_{aₙ}` 下按 `k, l` 是否碰到第 n 条边分类，用到 n−1 长度的 Ward（归纳假设）。

#### T26 一般 n 的拆解（Claude Code 读完论文 Step 2–5 后的判断）

论文的归纳证明比预想的重，至少要以下四块，建议拆成子工单：

1. **循环不变性 `K_{t,rot(σ,a)} = K_{t,σ,a}`**（`rot` = 把第一条边挪到最后）。论文 Step 4 多处用到
   （`v⁻_b = K_{(σ_{n−1},−),(a_{n−1},b)}`、三圈 Ward 右端的 `u⁻`），称为 "cyclicity"，但 **`IsPrimitive` 不含它，
   论文也没证**。证法：逐层归纳 + Grönwall——在长度 n 上 `K∘rot − K` 满足以 2-圈为系数的齐次线性方程。
   需要先证 cut-and-glue 与 `rot` 的交换关系（纯列表引理：`rot I` 在 `(k,l)` 处切开 = `I` 在 `(k+1,l+1)` 处切开，
   `l = n` 时变成 `I` 在 `(1,k+1)` 处切开且**左右互换**），再改写 `Unique.lean` 的 `eq_on_level` 为只要求第 n 层方程的版本。
2. **(3.19)(3.20)**：`Σ_{aₙ}` 与 `primRhs` 交换；`∂_t η_t⁻¹ = η_t⁻¹/(1−t)`。
3. **四类切口的抵消**（论文 Step 3–4，(3.21)–(3.33)）：内部切口 `2 ≤ k < l ≤ n−1`、边界对 `(1,m)+(m,n)`、
   `(1,n)`、四个角 `(1,2),(1,n−1),(2,n),(n−1,n)`。依赖 1 与长度 < n 的 Ward（归纳假设）、`S` 对称、`Σ_a S_ab = 1`、
   n=2 和 n=3 的 Ward（已证）。
4. **收尾**：`D(0) = 0` 与 Grönwall ⇒ `D ≡ 0`。

我接着做第 1 块的列表引理（`Loop/Index.lean` 里，`rot` 与 `cutGlueL/R` 的交换关系），这部分自足、不碰别人的文件。

T26 第 1 块进展：`Loop/Index.lean` 加了 `LoopIdx.rot` 与四条交换引理
（`cutGlueL/R_rot_of_lt`：`rot I` 在 `(k,l)` 切 = `I` 在 `(k+1,l+1)` 切；`cutGlueL/R_rot_last`：`l = n` 时左右互换，
对应 `I` 在 `(1,k+1)` 切）。下一步：`primRhs K (rot I)` 按这四条重排成 `I` 的项，再做逐层 Grönwall 得循环不变性。

---

# 更新 2026-09-19（Claude Code #2）：T25 —— Lemma 3.4 对 n ≤ 4 成立；一般 n 卡在「轴无关性」

`RBM1D/Loop/TreeRep.lean`（`b027f65`、`935e329`、`aac59d3`），全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。
另：`Unique.lean` 的 `eq_on_level` 改为**只要求第 n 层方程**（`4ef3a89`）——上面 T26 那节第 639 行计划要做的正是这件事，已做完，直接用。

**主结果 `treeRep_of_isPrimitive`**：若 `K` 在 `[0,T₀]`（`T₀ < 1`）满足 Def 2.12、2-loop 有界、`|m| ≤ 1`，
则对长度 `n ∈ {2,3,4}` 的每个 loop

    K_{t,σ,a} = (σ.map m).prod · W^{−(n−1)} · treeSum L m t σ a        （论文 (3.5)）

| Lean | 内容 |
|---|---|
| `primRhs_four` | (2.48) 在 n=4 的 6 项 `(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)` |
| `star4` / `spl02` / `spl13` / `trees4` | T_SP(4) 的三棵树，边矩阵作参数；`*_slot0..3` 为「某一边界行线性」 |
| `sum_bilin` | `Σ f(PSP)g = Σ (fP) S (Pg)`：内部边求导后分解成两棵子树 |
| **`hasDerivAt_kFour`** | **n=4 的树表示满足 (2.48)**；`kFour_zero` 初值；`kFour_eq_treeSum` 接 T21 的 `treeSum` |
| `eq_kLoop4_of_isPrimitive` | 用 T22 唯一性逐层（n=2,3,4）比较 |

**n=4 上看清的双射（一般证明的骨架）**：
* 4 条**边界边** ↔ 含 2-链的 4 项 `(1,2),(2,3),(3,4),(1,4)`：边界行在三棵树里都出现，求导即 `Σ_x (μΘS)_{a_i x} K(…x…)`；
* 2 条**内部边** ↔ 含两条 3-链的 2 项 `(1,3),(2,4)`：`d/dt(Θ−1) = μΘSΘ`，把那棵树沿该对角线切成 `K₃ S K₃`。
一般地：(树 Γ, Γ 的一条边 e) ↔ ((k,l), 左链上的树, 右链上的树)。边界边 ↔ l = k+1（及回绕 (1,n)），内部边 ↔ 对角线 (k−1, l−1)。

**一般 n 卡在哪（T25b）**：
1. **边界边**部分应当能直接对 `polyVal` 归纳证「边界矩阵的行线性」——没有障碍，只是没做。
2. **内部边**部分需要：树值沿 **F 中任意一条对角线** 都能分解成左右两块的乘积。
   但 T21 的 `polyVal` 只沿**列表头**（字典序最小的对角线）分解，**轴无关性没有证**（`Tree.lean` 文档里也写明了）。
   这是一般证明缺的那条引理。两种补法：
   * (a) 直接证 `polyVal` 对 F 的排列不变（对 |F| 归纳，两条不交叉对角线的分解可交换）；
   * (b) 另给一个「真正的树」定义：对内部顶点标签求和、各边权相乘，证 `polyVal` 等于它；此定义下沿任意边分解是 Fubini。
   我倾向 (b)：交换求和比证递归定义的交换律干净。
3. 有了 2，一般 (2.48) 就是把上面的双射写成 `Finset` 上的 `sum_bij`，外加 n=4 已用过的 `sum_bilin`。

T28（Cor 3.5）依赖一般 n，仍然「待 T25b」。

T26 第 1 块完成：**`RBM.isPrimitive_rot`**（`Loop/Cyclic.lean`）——满足 Def 2.12、2-圈有界的 `K` 在循环轮换下不变。
配套 `primRhs_rot`（(2.48) 在轮换圈上按原圈切口重排）、`primInit_rot`、`rot_eq_on_level`。论文未证此事，记入 paper-deltas #14。
下一步：第 2 块 (3.19)(3.20)。

---

# T25b 设计（Claude Code #2，2026-09-19）：一般 n 的 Lemma 3.4

**核心观察：把树的根放在最后一个顶点 `a_n`。** 这样「(树 Γ, Γ 的一条边 e)」与「((k,l), 左链上的树, 右链上的树)」
的双射是**纯结构性的**，不需要换轴、也不需要换根：
* 在 e 处剪开：含根 `a_n` 的那块 = 左链（`cutGlueL` 保留 `E_{a_n}`），剪下来的子树 = 右链；
  子树以剪口为根，而剪口正是右链的**最后一个**顶点（`cutGlueR` 把新标号 `b` 放在末尾）。
* 叶边 k ↔ `(k, k+1)`（右链是 2-loop，值为单边 Θ）；根边 ↔ `(1, n)`（左链是 2-loop）；内部边 ↔ 其对角线。

**编码：层状区间族。** 顶点 `0..n−1`，根为 `n−1`。区域对角线 `(i,j)` ↔ 顶点区间 `[i, j−1] ⊆ [0, n−2]`；
T17 的「无交叉」恰是区间族「两两嵌套或不交」（层状）。Γ 的边 ↔ 区间：单点 `{k}`（叶边）、全体 `[0,n−2]`（根边）、F 中的区间（内部边）。
Γ 的内部顶点 ↔ `F ∪ {全体}`，父亲 = 严格包含它的最小区间。

**无轴的树值**：`Val(F) = Σ_{b : F∪{全体} → ZMod L} Π_{叶 k} Θ_{m_k m_{k+1}}(a_k, b(par k)) · Π_{d∈F} (Θ_d − 1)(b(d), b(par d))`
（根叶 `a_{n−1}` 挂在「全体」上）。沿**任意**边分解 = 把标号和按 `N ≃ N_out ⊕ N_in` 拆开（Fubini），轴无关性自动成立。
n = 2 特判为单边（与 T20/T21 一致）。

**步骤**：(1) 抽象层：带权树的值、对一条边求导、沿边分解；(2) 层状区间族与剪切双射 `{F : J ∈ 𝓘(F)} ≃ TSP(左) × TSP(右)`；
(3) 求导用 `HasDerivAt.finset_prod`，初值 `t=0` 时只剩 `F = ∅`；(4) 与 `primRhs` 的列表下标对接；
(5)（可选）与 T21 的 `treeSum` 对接——至少在 n ≤ 4 上用 `kLoop4` 交叉验证。文件：`Loop/TreeRepGeneral.lean`。

T26：**`RBM.ward_two_of_isPrimitive`**——(3.13) 在 n=2 对**任意**满足 Def 2.12 且 2-圈有界的 `K` 成立（不只是显式的 `kTwo`）。
证法即论文 Step 2 的 Grönwall：`D = Σ_{a₂}K − c_t`，`c_t = (W(1−t))⁻¹`，`∂_t D = W Σ K S D + W c_t D`（因 `∂_t c_t = W c_t²`），`D₀ = 0`。
这验证了一般 n 收尾所需的 Grönwall 骨架。下一步：n ≥ 3 的 (3.19)(3.20) 与四类切口。

**T25b 进度（Claude Code #2）**：`Loop/TreeRepGeneral.lean`
* 步骤 1 ✔（`904301a`）：无轴树值 `treeValW`/`treeValG`（对全部内部顶点标号求和），`treeValW_empty`（星图），
  `hasDerivAt_treeValW`（导数 = 每条边各求一次导之和）。
* 步骤 2 ✔（`0ab6d4d`）：层状性 `nodes_laminar`、`leafPar_eq`/`nodePar_eq`（父亲 = 最小容器的刻画）、`leafPar_root`。
* 步骤 3a ✔（`5e05224` + 修复 `7a253e6`）：通用带权树值 `gval`（任意有限的节点/叶/边类型），
  `gval_congr`（同构不变）、`gval_split`（两块经一条权为 `PSQ` 的边相连 ⟹ `Σ_{u,w} 块₂(u) S_{uw} 块₁(w)`，剪口作为额外叶还给两块）。
* 步骤 3b ✔（`1155ff2`、`36cd7f7`）：`leafPar_spec`/`nodePar_spec`；剪口两侧的父亲归属；
  **`treeValW_cut`**：J 边权为 `PSQ` 时，树值 = `Σ_{u,w} (内侧树 + 根叶 (u,Pᵀ)) S_{uw} (外侧树 + 叶 (w,Q))`，两侧为子类型上的 `gval`。
* 步骤 3c（内侧）✔（`3eaf881`）：`gval_in_eq`——内侧部分 = 内侧多边形 `Fin (wIn J + 1)` 上的 `treeValW`（J → 根节点，叶平移 −J.1）。
* 步骤 3c（外侧）✔（`a464a0f`）：`gval_out_eq`——外侧部分 = 外侧多边形 `Fin (n − wIn J + 1)` 上的 `treeValW`（J 塌缩为胶点 `J.1`，胶叶挂在 J 的父亲上）。
  **至此：一棵树在任一内部边 J 处剪开 = 两棵小多边形上的树值，经 `S` 相连。**
* 步骤 4 ✔（`3a629a4`、`69f1a19`、`66702f1`）：`unShift`/`unColP` 回拉；`FIn_mem_TSP`/`FOut_mem_TSP`/`glueF_mem_TSP`；
  `FIn_glueF`/`FOut_glueF`/`glueF_cut` 互逆；**`sum_cut`：`Σ_{F∈TSP n, J∈F} f(FOut F J, FIn F J) = Σ_{G∈TSP(外)} Σ_{H∈TSP(内)} f G H`**。
* 步骤 5a ✔（`4b99515`）：`treeValW_leaf_mul`（叶的行线性，处理叶边/根边项）；**`treeValW_internal_cut`**：
  带 Θ 权时把 `Θ_J S Θ_J` 放在边 J 上 = `Σ_{u,w} treeValG(内侧, 根 u) S_{uw} treeValG(外侧, 胶 w)`，小多边形的 σ、a 只通过简单的重标号假设进入。
* 步骤 5b ✔（`7e030b3`）：`Kn`（函数形式的 (3.5)）、`hasDerivAt_Kn`（每叶一项 + 每条内部边一项）、
  `leaf_term`（叶 v ⟹ `Σ_x (μΘS)_{a_v x} Kn(a_v := x)`）、`sum_edges_swap`、
  **`internal_term`**（边 J 对所有含 J 的树求和 ⟹ `W Σ_{x,y} Kn(外, 胶 x) S_{xy} Kn(内, 根 y)`，正是 J 的剪接项）。
  **函数层面的 (2.48) 已全部到位**，只差列表层对接。
* **步骤 5c ✔（`cb8fd03`）：`hasDerivAt_Kgen`——对每个长度 n ≥ 3 的 WF loop，树表示 `Kgen` 满足 (2.48)。**
  （`root_pair_term` `e186cb2`、`prod_chains` `af340ee`、`diag_pair_term` `167e9a4`。）
* 下一步：步骤 6——n = 2 的方程（`kTwo`）、n = 1 的值、`t = 0` 初值（只剩 F = ∅ 的星图 → δ）、2-loop 有界，
  然后 `IsPrimitive Kgen` 并用 T22 唯一性得 **一般 n 的 Lemma 3.4**。
* 步骤 5c 旧记录：`Kgen`（列表上的 K）、`sum_pairs`（`(k,l)` = 叶对 ⊔ 根对 ⊔ 对角线，各一次）（`400021d`）；
  `getD` 引理与 **`leaf_pair_term`**（叶对 `(v+1,v+2)` = 叶 v 的项）（`0e6aa07`）。剩：`root_pair_term`、对角线对的列表对接（含 `hprod`）、总装、初值、唯一性。
* 原步骤 5c 计划：列表层：`Kgen`（n=1: m；n=2: `kTwo`；n≥3: `Kn`），`primRhs` 的 `(k,l)` 按「叶/根/对角线」三类拆分，
  `cutGlueL/R` 列表的 `getD` 对到 `leaf_term`/`internal_term` 的假设上；再初值、唯一性。原步骤 5b 说明：（n=1 取 m，n=2 取 `kTwo`，n≥3 取 `m_σ W^{-(n-1)} Σ_F treeValG`），
  把 `cutGlueL/R` 列表的 `getD` 对到 5a 的重标号假设上；然后导数、初值、唯一性。原步骤 5 说明：(i) 叶边/根边两种退化剪切（同一族 F、另一侧为 2-loop 单边）；(ii) 树值的时间导数按边求和后交换求和
  `Σ_F Σ_{J∈F} = Σ_J Σ_{F∋J}`，套 `treeValW_cut`+`gval_in_eq`/`gval_out_eq`+`sum_cut`；(iii) 与 `primRhs` 的 `(k,l)` 及 `cutGlueL/R` 列表对接；
  (iv) 初值；(v) 唯一性收口。原计划（剪切双射）： `{F ∈ TSP n : J ∈ F} ≃ TSP(外) × TSP(内)`（`F ↦ (FOut, FIn)`，需证 FOut/FIn 是 TSP、反向拼接），
  以及叶边、根边两种退化剪切（右链或左链为 2-loop）。原计划： `Fin (w+1)`（内侧，J 平移到 0，根为胶点）与 `Fin (n−w+1)`（外侧，J 塌缩为胶点）上的 `treeValW`；
  原步骤 3b 的余下说明：：`N(F) = N_out ⊔ N_in`，叶与边的归属，标号和按 Fubini 分解；然后把两块搬运到
  `cutGlueL`/`cutGlueR` 的列表坐标上（左链：J 塌缩成胶点；右链：J 平移到 0 且胶点为根）。

T26 一般 n 的推进方案（比论文 Step 3–4 简单，不需要四角特判和 3-圈 Ward）：
记 `fullLoop μ a' x = (+, μ, −; a', x)`、`pmLoop ± μ a' = (±, μ; a')`（`Loop/WardInd.lean`）。
* 所有 `l ≤ n−1` 的切口：`fullLoop` 的左链仍是 `fullLoop`（末标号还是 `x`），`pmLoop ±` 的左链是对应的 `pmLoop ±`，
  所以对 `x` 求和后恰为「下一层的 `D` + 下一层的 `K**`」；`k ≥ 2` 时右链与首电荷无关，直接抵消。
* `(1,m)` 与 `(m,n)`（**所有** `2 ≤ m ≤ n−1`）两两抵消：`pmLoop ±` 在 `(1,m)` 的右链正是 `fullLoop` 在 `(m,n)` 的左链的 `pmLoop ±`，
  剩下一个因子用循环不变性对上。
* 剩下的正好是 (3.18)：相邻切口的 `D·S·(2-圈)` 与 `(1,n)` 切口 + `∂_t η_t⁻¹` 合成的 `D/(1−t)`。
第 1 阶段（上述列表恒等式）已提交。

T26 第 2 阶段完成：**`RBM.ward_rhs_identity`**（`Loop/WardStep.lean`）——在「循环不变 + 更短长度的 Ward + 2-圈值 c」下，
`Σ_x (2.48)(+,μ,−;a',x) − κ((2.48)(σ⁺) − (2.48)(σ⁻)) = W(Σ_k wD(相邻切口)·S·K₂ + wD((N,N+1) 切口)·S·K₂ + c·Σ_x K)`。
这就是 (3.18) 的组合核心；`(1,m)`/`(m,n)` 对所有 m 一次抵消（证明里的 `hcancel`），无需论文的四角特判。
剩余：第 3 阶段——加上 `∂_t κ = κ/(1−t)`、`Wc = 1/(1−t)` 得 (3.18)，Grönwall + 对长度归纳，得一般 n 的 Lemma 3.6。

## T26 完成：Lemma 3.6 (3.13) 对一般 n 成立（Claude Code）

**`RBM.ward_of_isPrimitive` / `RBM.sum_fullLoop_eq`**（`Loop/WardGeneral.lean`）：满足 Def 2.12（`m = m^{(E)}`, `|E| < 2`）
于 `[0,T₀]`（`T₀ < 1`）且 2-圈有界的 `K`，对任意 `(+, μ, −; a', x)`：
`Σ_x K_{t,(+,μ,−),(a',x)} = (K_{t,(+,μ),a'} − K_{t,(−,μ),a'}) / (2 W i η_t)`。

组成：`Loop/Cyclic.lean`（循环不变性 `isPrimitive_rot`，论文未证）、`Loop/WardInd.lean`（切口的列表恒等式）、
`Loop/WardStep.lean`（`ward_rhs_identity`：(3.18) 的组合核心）、`Loop/WardGeneral.lean`
（`∂_t κ_t = κ_t/(1−t)`、初值 `wD_primInit`、一层 Grönwall `ward_level`、对长度归纳）。
与论文的差别见 paper-deltas #14、#15。下游 Cor 3.7（(3.14)）现在可以做了。

## 一次自查发现的缺口（2026-09-19）

把形式化的陈述逐条对回论文时发现：我最初给 (2.54) 的界是 `24/ℓ̂`，**不带衰减因子**，
而论文 (2.54) 的右端是 `1/(‖x−y‖+1)`。两者在 `‖x−y‖ ≫ ℓ̂` 时方向相反——
`24/ℓ̂` 是个常数，`1/(‖x−y‖+1)` 却在变小，所以我的界推不出论文的界。

原因是我在放缩里把 `ρ^{d−1} + ρ^{L−d−1} ≤ 2` 一步扔掉了衰减。
补救：`norm_Theta_second_diff_le_pow` 保留 `‖ρ‖^{‖x−y‖−1}`，再分两个区间得到
`norm_Theta_second_diff_le_inv_dist : ‖2Θ−Θ₊−Θ₋‖ ≤ 60/(‖x−y‖+1)`。

**教训**：证完一条估计，要回头确认它**蕴含**论文那条，而不只是"看起来同一个量级"。
常数不优化没关系，量纲和衰减不能丢。

## 自查发现的第二个缺口：(3.35)(3.36) 只覆盖了一半（2026-09-19）

蓝图节点 `lem:Theta-bounds` 一度标题写着「(3.35)--(3.36)」，实际证的是一致界
`‖Θ_ξ‖ ≤ (1−‖ξ‖)⁻¹`。对回论文才发现那两条是**分短边/长边**的，而且：

* **长边**（`ξ = t|m|² = t`）：max 界由 (2.52) 给出，ℓ¹ 界就是我们证的精确值 `(1−t)⁻¹`——
  但论文写的是 `1/η_t`，要接上还差字典 `1−t ≍ η_t`，那属于 Lemma 2.8 被推迟的 (2.40)。
* **短边**（`ξ = tm²`，`m` 非实）：`‖ξ‖ = t → 1`，一致界直接发散，**给不出 `≺ 1`**。
  需要的是 `|1 − tm²|` 的下界，也就是复 ξ 那条线。

已把节点标题改成「一致 ℓ¹/ℓ∞ 界」，另开 `lem:3.35` 节点如实标为未形式化并写清缺什么，
工单 T29 负责补。**教训与 (2.54) 那次同源：节点标题写成论文的编号，就等于宣称覆盖了它。**

### ⚠ 事故说明（Claude Code，T29）

Cowork 在 `7472752` 先认领了 T29，Claude Code 的认领脚本随后（`9fc40f9`）把那一行改成了自己——是竞态，
我读表时它还显示「空闲」，但改表前没有重新核对。接着我**覆盖了 Cowork 尚未提交的 `RBM1D/Propagator/Edges.lean`**
（写之前没先读），原内容不在 git 里，**无法恢复**，非常抱歉。

已做：认领还给 Cowork；把我写的草稿从 `Edges.lean` 移走（它有编译错误，留着会弄坏构建）。
现在工作树里 `RBM1D.lean` 有 Cowork 未提交的 `import RBM1D.Propagator.Edges`，而文件已不存在——**请 Cowork 重新建这个文件**。

可能有用的数学（我草稿里的，未编译通过，仅供参考）：
* `|1 − t m²| ≥ Im m^{(E)}`（`0 ≤ t ≤ 1`, `|E| ≤ 2`）：`|1−tm²|² − (Im m)² = t² − (E²−2)t + E²/4 ≥ 0`
  （`E² ≤ 2` 时各项非负，否则判别式 `(E²−1)(E²−4) ≤ 0`）。由此 `|1−ξ|·ℓ̂(ξ) ≥ Im m`，短边 max 界 `≤ cTwo52 / Im m`。
* **长边不需要 (2.40)**：本项目里 `η_t := (1−t) Im m`（即 (2.35) 的定义），所以 `(1−t)⁻¹ = Im m / η_t ≤ 1/η_t`；
  论文 (2.59) 的 `ℓ_t` 就是 `ellHat L t`，且 `(1−t)ℓ̂(t) ≥ η_t ℓ_t`。

**教训（已记给自己）**：改共享表格前重新读最新版本并确认那一格仍是「空闲」；新建文件前先确认路径不存在。

---

# 更新 2026-09-19（Claude Code #2）：T25b 完成 —— **Lemma 3.4 对一般 n 成立**

`RBM1D/Loop/TreeRepGeneral.lean`（主结果提交 `b90336d`），全绿 0 sorry，公理只有 `propext` / `Classical.choice` / `Quot.sound`。

**`RBM.treeRep_general`**：若 `K` 在 `[0,T₀]`（`T₀ < 1`，`|m| ≤ 1`）满足 Def 2.12 且 2-loop 有界，则对每个 WF、长度 `n ≥ 3` 的 loop

    K_{t,σ,a} = (σ.map m).prod · W^{−(n−1)} · Σ_{F ∈ TSP n} treeValG L m t σ a F        （论文 (3.5)）

`eq_Kgen_of_isPrimitive` 对 `n ≥ 2` 给出 `K = Kgen`；`isPrimitive_Kgen` 说树表示本身就是 Def 2.12 的解（存在性）。

**证明结构**（设计见上面「T25b 设计」节）：
1. 无轴树值 `treeValW`（层状区间族，对全部内部顶点标号求和）；`hasDerivAt_treeValW`：导数 = 逐边求导之和。
2. 层状性与父亲刻画（`nodes_laminar`、`leafPar_spec`、`nodePar_spec`）。
3. 剪切：`treeValW_cut`（沿内部边 J 分解）、`gval_in_eq`/`gval_out_eq`（两侧搬到小多边形）、`sum_cut`（剪切双射）。
4. 逐项：`leaf_term`、`internal_term`；`sum_pairs`（`(k,l)` = 叶对 ⊔ 根对 ⊔ 对角线）；`leaf_pair_term`/`root_pair_term`/`diag_pair_term` 对上 `cutGlueL/R` 的列表。
5. 总装 `hasDerivAt_Kgen`；初值 `Kgen_zero`（`t=0` 时内部边 `Θ₀−1 = 0`，只剩星图 → δ）；唯一性收口。

**与 T21 `treeSum` 的关系**：一般 n 用的是新的无轴编码（paper-deltas #16）；两者在 n ≤ 4 相等已证，一般 n 的等价未证、也不需要。
**解锁**：T28（Cor 3.5）现在可开工；T26（Ward，一般 n）也可直接用 `eq_Kgen_of_isPrimitive`。

### T30：Lemma 3.6 与循环不变性对真正的 `K` 无条件成立（Claude Code）

`Loop/WardKgen.lean`：借 #2 的 Lemma 3.4（`isPrimitive_Kgen` + `norm_Kgen_two_le`），
**`RBM.ward_Kgen`**（(3.13)）与 **`RBM.Kgen_rot`**（循环不变）对树表示 `Kgen`（`m = m^{(E)}`, `|E| < 2`）
在所有 `0 ≤ t < 1` 上成立，不再需要「2-圈有界」这一假设。下一步可做 Cor 3.7 (3.14)（依赖 T28 的 Cor 3.5）。

---

### `RBM1D/Loop/Cor35.lean` — Corollary 3.5（T28，Claude Code #2）

| Lean | 论文 |
|---|---|
| `RBM.sum_pow_zdist_le` / `sum_exp_zdist_le`（T38 起在 `Defs/Sums.lean`） | `Σ_u r^{‖u‖} ≤ 2/(1−r)`，对 `L` 一致 |
| `RBM.Cor35.chain` / `chain'` | 树中任一内部顶点到根的距离 ≤ 内部边总长（沿父链归纳） |
| `RBM.Cor35.dist_bounds` | 任两叶距离 ≤ 2D；任一顶点到末叶距离 ≤ D（D = 全部边长之和） |
| `RBM.Cor35.norm_treeValW_le` | 各边 `≤ B e^{−κ‖x−y‖}` 的树值 `≤ B^{n+n²}(2/(1−e^{−κ/(2n²)}))^{n²} e^{−κ‖a_i−a_j‖/4}` |
| `RBM.Cor35.norm_Theta_apply_le_of_gap` | 复 ξ 的 (2.52) + gap `δ ≤ \|1−ξ\|` ⟹ `\|Θ_xy\| ≤ (2C/δ) e^{−c₀√δ‖x−y‖}` |
| `RBM.Cor35.norm_thetaEdge_le` | `Θ_{tm(+)²}` 与 `Θ_{tm(+)²} − 1` 的逐元素指数衰减 |
| **`RBM.cor35`** | **Corollary 3.5 (3.6)**，n ≥ 3：`\|K_{t,(+…+),a}\| ≤ C_{n,δ} e^{−c_δ‖a_i−a_j‖}` |
| `RBM.cor35_two` | n = 2（即 (2.52)） |

gap 假设见 paper-deltas #17（`T₀ < 1` 时 `δ = 1 − T₀` 自动成立，`gap_of_le`）。

### T32：Corollary 3.7（Claude Code）

论文说它是 Lemma 3.6 的直接推论，实际证明还要：K 的**平移不变性**（论文「by definition」）、**循环不变性**、以及 **Cor 3.5 的纯圈界**。
* `Loop/Cyclic.lean`：**`isPrimitive_shift`**（任意解，2-圈有界）——平移与 cut-and-glue 交换、`S^(B)` 平移不变，唯一性收尾。
* `Loop/WardKgen.lean`：`allSum`（对所有标号列表求和）、`exists_rotate_true_false`（混合电荷列必有一个轮换形如 `(+,μ,−)`）、
  `totalSum_ward` / `totalSum_rotate` / **`norm_totalSum_le`**（(3.15) 的代数部分，常数 `2ⁿ⁻¹`）、`partialSum_eq`（平移不变 ⇒ 对 `a₂…aₙ` 求和 = `L⁻¹` 总和）、
  **`cor37_reduction`**（(3.15)，对真正的 K 无条件）、**`cor37`**（(3.14)：`≤ 2ⁿ⁻¹ n C (Wη_t)^{-(n-1)}`，以 `L⁻¹P_m ≤ C W^{-(m-1)}`（m ≥ 2）为假设）。
**已完成**（去掉假设）：`gap_mSigma`（两种电荷的 bulk gap `√k ≤ |1−t m(b)²|`，用 Cowork 的 `sqrt_le_norm_one_sub_short`）、
**`norm_Kgen_pure_le`**（纯 n-圈 n ≥ 3 逐点：`W^{-(n-1)} C_n e^{-c‖a_i−a_j‖}`）、`norm_totalSum_pure_two`（n = 2 精确求和）、
**`norm_totalSum_pure_le`**（`‖Σ_a K_{(b…b),a}‖ ≤ L W^{-(m-1)} pureConst m k`）、**`cor37_bulk`**（(3.14) 无条件：`|E| ≤ 2−k`、`0 ≤ t < 1` ⇒ `≤ cor37Const n k · (Wη_t)^{-(n-1)}`）。paper-deltas #18。

### `RBM1D/Loop/Layer.lean` — Definitions 3.8/3.9（T31，Claude Code #2）

| Lean | 论文 |
|---|---|
| `RBM.Flong` | Def 3.8 I：长内部边 `F_long(Γ,σ) = {{i,j} ∈ F : σ_i ≠ σ_j}` |
| `RBM.TSPlong` | Def 3.8 II：`T_SP(P_a,σ,π)` |
| `RBM.disjoint_TSPlong` / `biUnion_TSPlong` / **`sum_TSPlong`** | 各层互不相交、并为 `T_SP`；按层求和 = 总和 |
| `RBM.Kpi` | (3.40) `K^(π)`（不含 W） |
| `RBM.Kn_eq_sum_Kpi` / **`K_eq_sum_Kpi`** | (3.41) `K = W^{-n+1} m_σ Σ_π K^(π)`（后者对任意满足 Def 2.12 的 K，n ≥ 3） |
| `RBM.selfW` / `selfE` / `SigmaPi` | Def 3.9 II 自能 `Σ^(π)(t,σ,d)`：去掉边界边，`d_v = b(leafPar v)` 为 Kronecker δ，其余内部顶点求和 |
| `RBM.treeValW_eq_sum_selfW` / **`Kpi_eq_sum_SigmaPi`** | (3.42) `K^(π) = Σ_d Σ^(π)(d) Π_i (Θ_{t m_i m_{i+1}})_{a_i d_i}` |
| `RBM.selfW_empty` | 星图（单分子、无内部边）的自能 = `δ_{d_1⋯d_n}` |

下游：T34（Lemma 3.10，对称性与 sum-zero）现可开工。

**T34 设计（Claude Code #2）**：`Loop/SumZero.lean`。第 1 块 ✔（`a46c585`）：Lemma 3.10 (1) 对**所有** σ、π 成立
（`SigmaPi_add_const`、`SigmaPi_neg`）；(3.48) 的精确形式 `sum_Kpi_eq`。
关键观察：**对全部标号求和的树值有闭式**。边权列和为常数 `r_e` 时，从无子节点的内部顶点逐个剥离得
`Σ_b Π_e E_e(b_e, b_{par e}) = L Π_e r_e`；于是 `A(σ,π) := L⁻¹ Σ_a K^(π) = Π_v (1−ξ_v)⁻¹ · Q(σ,π)`，
`Q(σ,π) = Σ_{F∈T_SP(σ,π)} Π_{e∈F} ξ_e/(1−ξ_e)`（与 L、W 无关）。论文 §3.4 的各步变成精确恒等式：
* (3.49)：Cor 3.7（`cor37`，纯圈界由闭式直接给出）+ (3.41)；
* (3.52)：取 π 中最内的长边 J，`Q(σ,π) = r_J · Q(内, ∅) · Q(外, π∖J)`（T25b 的剪切双射 `sum_cut`），
  即 `A_n = t(1−t) · A_内 · A_外`（论文 (3.60)–(3.64) 的 `f*` 论证的闭式）；
* (3.65) π = ∅ 由总和减去 π ≠ ∅；(3.51) 交替 σ 时 `Q(σ^alt, ∅) = (1−t)^n A_n = O(η)`。

### `RBM1D/Loop/SumZero.lean` — Lemma 3.10（T34，Claude Code #2）✔

| Lean | 论文 |
|---|---|
| `RBM.SigmaPi_add_const` / `SigmaPi_neg` | **Lemma 3.10 (1)**，对所有 σ、π |
| `RBM.sum_out` / `treeZ_peel` / **`treeZ_eq`** | 全标号求和的树值闭式 `Σ_b Π_e E_e(b_e,b_{par e}) = L Π_e r_e` |
| `RBM.sum_SigmaPi` / `sum_Kpi_closed` | (3.47)(3.48)：`L⁻¹Σ_a K^(π) = A(σ,π) = Π_v(1−ξ_v)⁻¹ Q(σ,π)`，`L⁻¹Σ_d Σ^(π) = Q` |
| `RBM.norm_sum_Alayer_le` | (3.49)：由 `cor37_bulk`（W = 1）+ (3.41) |
| `RBM.Qlayer_cut` / `prod_leaves_cut` / **`Alayer_cut`** | (3.52)–(3.64)：最内长边处 `A = t(1−t) A_内 A_外` |
| **`RBM.norm_Alayer_le`** | (3.50)(3.65)：`\|A(σ,π)\| ≤ C_n η_t^{-(n-1)}`，对 n 归纳 |
| **`RBM.sum_zero`** | **Lemma 3.10 (2)**，(3.44)：交替 σ 时 `\|L⁻¹Σ_d Σ^(∅)\| ≤ C η_t` |

公理审计：`sum_zero`、`norm_Alayer_le` 只含 propext / Classical.choice / Quot.sound。paper-deltas #21。

### `RBM1D/Test/Layers.lean` — Def 3.8 的 `decide` 回归（T36，Claude Code #2）

交替电荷下 `TSPlong` 的层大小与独立的暴力枚举一致：n=4 三棵树全在 `π = ∅`（论文 (3.42) 后的例子）；
n=5 为 `5, 3, 3`；n=6 为 `18 + 9 + 9 + 9 = 45`，两条相交的长对角线不共存。
维护：蓝图全部 405 个 `\lean{}` 名字均解析到真实声明（以 `#check` 逐个核对，无 `leanblueprint` CLI）；
根模块 `lake build RBM1D` 通过，公理审计 2307 条声明全在允许范围内。

### T37：Lemma 3.11 设计（Claude Code）

记 `δ = 1−t`、`ℓ = ℓ̂(t)`、`A = C/(ℓδ)`（`η_t ≤ δ`，故 `A ≲ (ℓη)^{-1}`）。目标 (3.45)：`|K^(π)_a| ≤ C_n A^{n-1}`。

**论文证明的一个缺口**：(3.66) 要带 `min_k(‖a_k−d₁‖+1)^{-1}`，但 “WLOG ξ_n = 2” 只给出 `a_n` 方向的衰减，
不是最远的 `a_k`；且对 `d₁` 求和会多出 `log ℓ`。**改走不需要 min 因子的路线**：

* 长边核 `θ = Θ_t`（实 t，闭式 `A(ρ^d+ρ^{L−d})`）的六个界：`sup ≤ A`、`ℓ¹ = 1/δ`、`sup∇ ≤ C`（**一致**，
  用 `|ρ^j−ρ^n| ≤ |j−n|(1−ρ)`；现有 `C/(ℓ√δ)` 在 `ℓ = L` 区不够）、`ℓ¹∇ ≤ Cℓ`、`supΔ ≤ C/ℓ`、`ℓ¹Δ ≤ C`。
* 离散 Taylor（ZMod L 上任意 f）：`f(c+s) = z + o(s) + e(s)`，`o` 为奇部（`|o| ≤ |s| sup∇`），`e` 为偶部余项（`|e| ≤ s² supΔ`），ℓ¹ 版同理。
* π = ∅：`K = Σ_{d₁} θ₁(a₁,d₁) F(d₁)`，`F = Σ_s g(s) Π_{i≥2} θ_i(d₁+s_i)`，`g = Σ^(∅)`。展开乘积：全 z 项用 sum-zero（Lemma 3.10 (2)）得 `δ`；
  恰一个 o 的项由 `g(−s) = g(s)`（Lemma 3.10 (1)）为 0；其余每项至少增益 `δ`。于是 `|F| ≤ C A^{n−1} δ`，对 d₁ 求和付 `1/δ`。
  非交替 σ 有短边：对短边求 ℓ¹（`≤ C`），无需展开。需要 `Σ_s |g(s)|(1+|s|)² ≤ C`（(3.43) 的加权 ℓ¹ 形式）。
* π ≠ ∅：论文的度 1 分子归纳 `K^(π) = Σ_{c₁} A(c₁) B(c₁)`；`B` 的 c₁ 边是 `Θ_t − 1 = t SΘ_t`，故 `B = t S K^(π')`，
  `sup|B| ≤ C A^{n−m+1}`（归纳）；`Σ_{c₁}|A| ≤ C A^{m−2}` 同上展开（ℓ¹ 放在 z/o/e 中的一个因子上；各情形都够，用到一致的 `sup∇ ≤ C`）。

落地顺序：(P1) `Propagator/LongDiff.lean` 长边六界 + 离散 Taylor；(P2) Σ^(∅) 的加权 ℓ¹；(P3) π = ∅；(P4) 分子剖分与归纳。

## 一次重复劳动（2026-09-19）：两边各造了一遍同一个轮子

`RBM.Cor35.sum_pow_val_le` / `RBM.Cor35.sum_pow_zdist_le`（Claude Code，`Loop/Cor35.lean`）
与 `RBM.sum_pow_val_le` / `RBM.sum_pow_zdist_le`（Cowork，`Propagator/Edges.lean`）
是**同一条引理的两份独立证明**，只因为前者在嵌套命名空间 `RBM.Cor35` 里才没撞名。
两边都是在各自的估计里需要"环上几何级数求和"时顺手证的，都没先查仓库。

值得一提的是 Claude Code 那份更漂亮：利用 `ZMod (k+1)` 与 `Fin (k+1)` 的 defeq，
`Fin.sum_univ_eq_sum_range` 加 `geom_sum_Ico_le_of_lt_one` 四行搞定；
我那份绕了 `image ZMod.val = range L` + `Finset.sum_image` + `tsum` 一圈。

**规则**（已写进 `CLAUDE.md`）：证任何**通用工具引理**（ZMod 上的求和、几何级数、
exp 不等式、Finset 重标）之前，先 `grep -rn "关键词" RBM1D/`。
按文件分工能避免改同一个文件，但**避免不了重复造轮子**——那要靠查。

清理留给 T38（低优先级），不急着动，因为两份都编译通过、都有用户。

## 对账：Corollary 3.5 的陈述形式（通过）

论文 (3.6) 写的是 `|K| ≤ C_n exp(−c_n max_{ij} ‖a_i − a_j‖)`；
Lean 里的 `cor35` 写成「对每一对 `i, j`，`|K| ≤ C exp(−c‖a_i − a_j‖)`」。
两者**等价**：对 i,j 全称量化等于取所有上界里最小的那个，而
`min_{ij} exp(−c d_{ij}) = exp(−c max_{ij} d_{ij})`。
Lean 的形式还省去了形式化「对所有指标对取 max」。**结论：无缺口。**

## 对账审计第二轮（2026-09-19）：四条全部通过

前两次审计各逮到一个缺口（(2.54) 丢衰减、(3.35)(3.36) 只覆盖一半），都在 Cowork 这边的
工作或蓝图标注里。这一轮查 Claude Code 的第 3 节成果，**四条全部通过**：

* **Corollary 3.5**。论文写 `|K| ≤ C exp(−c max_{ij}‖a_i−a_j‖)`，Lean 写成「对每一对 `i,j`
  都有 `|K| ≤ C exp(−c‖a_i−a_j‖)`」。两者等价（全称量化 = 取最小上界，
  而 `min_{ij} exp(−c d_{ij}) = exp(−c max_{ij} d_{ij})`），且 Lean 形式省掉了对指标对取 max。
* **Definition 3.9**。`Kpi` 不含 `W` 也不含 `m_σ`，与论文「K^(π) 按约定与 W 无关」一致；
  `Kn_eq_sum_Kpi` 即 (3.41)；`Kpi_eq_sum_SigmaPi` 即 (3.42)，边界因子用的是更正后的
  `Θ_{t m_i m_{i+1}}`。
* **Lemma 3.10**。论文设「`4 ≤ n ∈ 2ℤ` 且 σ 交替」，Lean 只设 `3 ≤ n` 加上循环交替条件
  `∀ v, σ v ≠ σ (v+1)`——**偶数性是被蕴含的**（奇圈没有真二染色），所以 n 为奇数时假设空真。
  两者对非空情形等价。结论用 `η_t` 而非 `1−t`，比论文更直接。
* **Lemma 3.4**。`treeRep_general` 的结论逐字对应 (3.5)。它比论文多一个假设 `hR`
  （长度为 2 的 loop 在时间区间上一致有界），这是 n=2 的 Riccati 型方程做 Grönwall
  唯一性所必需的——论文一句「K 是唯一解」略过了这一点。这是**正确的细化**，不是偏离。

**观察**：两次有效发现都出在 Cowork 这边（放缩丢信息、节点标题过度声称），
而不在 Claude Code 的数学里。审计的价值在于**换一双眼睛**，不在于谁更可靠。

### `RBM1D/Defs/Sums.lean` — 共用求和工具下沉（T38，Claude Code #2）✔

`sum_zmod_val`、`sum_pow_val_le`（用 `geom_sum_Ico_le_of_lt_one` 的短证明）、`sum_pow_sub_val_le`、`pow_zdist_le_add`、
`sum_pow_zdist_le`、`zdist_neg`、`one_sub_exp_neg_ge`、`sum_exp_neg_zdist_le`、`sum_exp_zdist_le` 各只证一次；
`Propagator/Edges.lean` 与 `Loop/Cor35.lean` 的副本已删，`WardKgen` 的一处调用改指新文件。只依赖 `Defs/Dist.lean`。
**未移动**：`mul_exp_neg_le_exp_neg_one`、`two_mul_zdist_le` 仍在 `Propagator/Decay.lean`——该文件由 Cowork 认领（T1–T4 进行中），
不碰；等那边收工后可顺手下沉。受影响模块（Sums、Edges、Cor35、WardKgen、DiffComplex、SumZero、KBound）全部编译通过。

**T37 进度（Claude Code）**：`Propagator/LongDiff.lean`（P1：均匀 `|∇Θ_t| ≤ 3/2`、`Σ|∇Θ_t| ≤ 3ℓ̂`、`|ΔΘ_t| ≤ 3`、`Σ|ΔΘ_t| ≤ 6`）；
`Loop/KBound.lean`：(3.43) `norm_SigmaPi_empty_le`、加权 ℓ¹ `sum_pinned_SigmaPi_le`、离散 Taylor、展开 `Kpi_empty_expand`、
余项 `sum_prod_taylor_le`、一阶相消 `sum_taylor_single_eq_zero`，**(3.45) 的 π = ∅ 情形 `norm_Kpi_empty_le`**（任意 σ；交替 `norm_Kpi_empty_alt_le`，
含短边 `norm_Kpi_empty_short_le`）。paper-deltas #22。**π ≠ ∅ 完成**：`treeValW_long_cut`（单棵树在长边处切割，`Θ−1 = (t·1)SΘ`）、`Kpi_cut`（(3.75) 的层版本）、
`innerId`/`sum_norm_innerId_le`（根叶为恒等的内分子，`Σ_u|A(u)| = O(X^{N−2})`）、**`norm_Kpi_le`**（(3.45) 对所有 π，n ≤ N_max 一致）、
**`norm_Kgen_le`**（(3.46)：`|K| ≤ C (W η_t ℓ̂)^{−(n−1)}`）。**T37 完成。**

### `RBM1D/Defs/StochDom.lean` — Def 2.1 (i)(iii)(iv)（T41，Claude Code）

**随机层的签名约定（下游全部按此）**：概率空间 `(Ω, P : Measure Ω)` 固定，族为 `ξ : ∀ N, U N → Ω → ℝ`（`U N` 为参数集）。
`StochDom P ξ ζ`（论文 (i)，并集在概率里面）、`NormStochDom`（(iii)，任意 `[Norm E]`）、`HighProb`/`HighProbIn`（(iv)）。
性质：`refl`/`trans`/`add`/`mul`/`const_mul_left`/`const_mul_right`/`of_unifDetDom`（确定性 ⇒ 概率）、
**`of_forall_le`**（union bound，`#U(N) ≤ N^C`）、`StochDom.highProb`、`HighProb.inter`/**`biInter`**（多项式多个 w.h.p. 事件）。
通用工具 `of_subset`/`of_subset_union`：新性质只需证失败事件的包含关系。paper-deltas #23。

### `RBM1D/Flow/Initial.lean` — (2.67)（T47，Claude Code 并行 agent）

`Gsig_zero_zt_zero`：`G_0(σ) = m(σ)·I`；**`gloop_zero_zt_zero_eq_Kgen`**：`L_{0,σ,a} = K_{0,σ,a}`（无假设，§2.7 基例）；
`gloop_zero_zt_zero_eq_of_isPrimitive`（对任意满足 Def 2.12 且 `0 ∈ T` 的 K）。paper-deltas #24。

### `RBM1D/Propagator/ZeroMode.lean` — §7.2 末的零模去除（T46，Claude Code 并行 agent）

`ThetaTilde_eq`：`(1−ξS̃)⁻¹ = Θ_{ξ(1−ζ)} + α·J`（手搓 Sherman–Morrison）；**`ThetaTilde_sub_ThetaTilde`**（p.84 的差分恒等式）；
`norm_one_sub_mul_comparable`（需 `ζ ≤ |1−ξ|`，paper-deltas #25）；(2.52)(2.53)(2.54) 搬到 `S̃`：
`norm_ThetaTilde_sub_zeroMode_le`、`norm_ThetaTilde_sub_shift_le`、`norm_ThetaTilde_second_diff_le`。

### `RBM1D/Flow/Scales.lean` — 流的尺度与时间网格（T48，Claude Code 并行 agent）

**网格约定（下游 T57 按此）**：先固定 `κ > 0`、`τ ≥ 0`、`τ' > 0`（`60τ' < τ`）、`n₀`（`n₀τ' ≥ 2`，如 `n₀ = ⌈2/τ'⌉`，只依赖 τ'），
网格 `gridT W τ' t k = min(1 − W^{−kτ'}, t)`（在 t 处截断）。**`flow_grid_2_72`**：存在 `W₀`，对 `W ≥ W₀`、`1 ≤ L ≤ W`、`|E| ≤ 2−κ`、
`(WL)^{−1+τ} ≤ 1−t` 有 `u₀ = 0`、`u_{n₀} = t`、单调、`A_t⁻¹ ≤ W^{−30τ'}` 且每步 (2.72)。另有 `flowScale_antitoneOn`（`A_s` 非增）、
`le_etaT`/`etaT_le`（`η_t ≍ 1−t`）、`ellZ_zt_le`、`lemma28_scales`。paper-deltas #26。

### `RBM1D/Analysis/StretchedExp.lean` — `exp(−√·)` 演算（T43，Claude Code 并行 agent）

`tailT`（(5.27)）、`ratioJ`（(5.28)）、`tailT_antitone`、`tailT_sub_le`/`unifDetDom_tailT_sub`（(5.32)）、`integral_exp_sqrt_triangle_le`（≤ 16）、
`integral_Ioi_exp_neg_sqrt`（= 2）、`integral_exp_half_sqrt_triangle_le`（(5.62)）、**`mul_sum_tailT_mul_tailT_le`**（(5.50)(5.72) 卷积界）、
`sqrt_zdist_sub_sqrt_zdist_le`（(7.12)）。paper-deltas #27。

### `RBM1D/Loop/Continuity.lean` — §6 的确定性骨架（T50，Claude Code 并行 agent）

(6.3) `green_eq_add_smul_mul`/`Gsig_eq_add_smul_mul`；(6.7) `list_prod_add_eq`（非交换）；(6.8) `gchain_eq_add_sum_gchainMixed`；
(6.9) `norm_gchain_apply_sq_le`；(6.5) `gloop_symm_eq_trace`；(6.12) **`ward_chain_row`**/`ward_chain_row'`；
`ztTilde_arith`（`z̃` 的四条算术界）。未做（范围外）：(6.1)、(6.10)(6.11)(6.13) 总装；(6.4)/Lemma 6.1 属 T44。paper-deltas #28。

### `RBM1D/Flow/Hypotheses.lean` — 随机层假设接口（T54，Claude Code 并行 agent）

**接口约定（T57 按此）**：固定 `(Ω, P)`，时间是 `N` 的序列 `s t : ℕ → ℝ`；定长 `n` 的 loop 的 max 化为参数集
`LoopData (L N) n = (Fin n → Bool) × (Fin n → ZMod (L N))` 上的一致性；Steps 的 `u ∈ [s,t]` 进参数集 `TimeIcc s t N`。
`Band`（维数、(2.2)）、`Sample`（(2.34)，`G`、`Lval`、`ELval`）、`BoundsCore`/`Bounds`（(2.60)(2.62)–(2.64)）、`Cond272`、`Thm221`、
`Steps`（(2.73)–(2.80) 八个字段）、`Transfer`（(2.39)(2.65)(2.66)）。已证：`BoundsCore_of_Steps`/`Bounds_of_Steps`、
`BoundsCore.stochDom_norm_Lval`（(2.61)，n ≥ 3，需 `1 ≤ Wℓη`——T57 可用 `Flow/Scales.lean` 的 `flowScale_ge` 消去）、
`Transfer.green_sub_msc`（(2.65)）。paper-deltas #29。

### `RBM1D/Loop/Split.lean` — loop 的 Cauchy–Schwarz 劈分（T44，Claude Code 并行 agent）

(5.2) `norm_gloop_le_opNorm`；(5.115)(5.116) `norm_sq_gloop_le_symIdx`、`norm_gloop_symIdx_split_le`；**(5.117) `loopMax_two_mul_add_two_le`**；
(5.118) `loopXi_le`；(6.4) `loopMax_odd_sq_le`；**Lemma 6.1 `sum_norm_inner_sq_le_trace_rpow`**（实 p ≥ 1）。`loopMax` 为 iSup 形式的 max。paper-deltas #30。
T53（Step 3）现已解锁。

（`Hierarchy/SumZero.lean` 的编译问题 Cowork 已修复，HEAD 已恢复全绿。）

### `RBM1D/Flow/Iteration.lean` — Lemma 2.18–2.20 由 Theorem 2.21 推出（T57，Claude Code 并行 agent）

**`Bounds_of_Thm221`**：`Thm221 X κ`、`|E| ≤ 2−κ`、`0 ≤ t N`、最终 `N^{−1+τ} ≤ 1 − t N` ⟹ `Bounds X E t`（(2.60)(2.62)(2.63)(2.64)），
**无额外假设**；基例 `Bounds_zero`（(2.67)，零误差）；网格 `Band.eventually_flow_grid`。**`stochDom_norm_Lval_of_Thm221`**：(2.61) 对所有 `n ≥ 1`
（`Band.norm_Kval_le`：n ≥ 3 用 (2.59) `norm_Kgen_le`，n = 1 用 `Kgen_one`，n = 2 用新证的 `norm_Kval_two_le`）。paper-deltas #31。

### `RBM1D/Green/EntryBound.lean` — Lemma 4.1（T45，Claude Code 并行 agent）

两层：确定性核（固定 `H`、显式因子 `Φ` 代 `≺`、`GoodEvent G m δ` 即 Ω(t,c)、LDE 以具体向量的结论 `LDERow/LDECol/LDEQuad` 入参、
稳定性 `Stable S ξ K` 对块模型**已证** `stable_Sblk_short_edge`）+ `≺` 层（`StochDom.of_det` 把确定性蕴含变成 `≺`）。
(4.2) `norm_sq_green_le_blk`/`entry_bound_stochDom`、(4.3) `norm_sq_green_diag_sub_le_blk`/`diag_bound_stochDom`、(4.5) `avg_bound_stochDom`，
以及去掉 `1_Ω` 的 `_of_highProb` 版。paper-deltas #32。

（`Green/Minor.lean` 的编译修复已随 T66 提交，HEAD 全绿。）

### `RBM1D/Hierarchy/Step3.lean` — Step 3（T53，Claude Code 并行 agent）

**抽象形式（T55/T56 按此）**：`≺` 为 `StochDom P`，对时间参数 `U : ℕ → Type*` 一致；`X n` = Ξ^{(L−K)}_{·,n}、`Y n` = Ξ^{(L)}_{·,n}、
尺度 `A N u`、`As N`、`R N`。`Psi`/`S`（(5.108)）、`Scales`（(2.72) 在 Step 3 中的全部作用）、`Lemma514`（(5.92) 的较弱形式，唯一随机输入）、`Hyp`；
**`S_all`**（(5.109) 双重归纳）、`xiLK_le`、**`xiL_le_one`**（(2.77)）。流的实例：`hyp_flow`、**`flow_sharpLoop`**（(2.77)，所有 `n ≥ 1`，
形状同 `Steps.sharpLoop`）。n = 2 的 (5.107) 由 T57 的 `Band.norm_Kval_le` 补上。paper-deltas #33。T55、T56 现已解锁。

### `RBM1D/Loop/ChainExpand.lean` — 附录 A 的确定性核心（T49，Claude Code 并行 agent）

`minorExt`（`G^(i)`，(4.6)）、`gchainMinor`/`gchainMinorTail`（(A.9)(A.10)）、`XiDiag`/`XiOff`（(A.5)(A.6)）、`compSum`（(A.24) 的指示函数和）；
(A.18) `gchainMinorTail_apply_eq`、望远镜展开 `gchainMinor_apply_expand`/`gchainMinorTail_apply_expand`、(A.24) `norm_gchainMinorTail_sub_gchain_le_A24`、
(A.26)+(A.27) ⟹ (A.13) `norm_gchainMinor_sub_gchain_diag_le_trichotomy`、(A.15) `quad_Eblk_apply_self_split`、梯子 `XiDiag_add_le`、`xi_trichotomy`。
`1/G_ii = O(1)` 与 [39] Lemma 3.3 为显式假设。未做：(A.25) 的界形式、(A.20) 最后一步。依赖 `Green/Minor.lean`（见上方 ⚠）。paper-deltas #34。

### `RBM1D/Hierarchy/KernelDecay.lean` — Lemma 7.2、7.3（T51，Claude Code 并行 agent）

`FastDecay`（(7.13)）、`SumZeroAt`（(7.15)）；**`norm_Uker_fastDecay_le`**（(7.14)）、`norm_Uker_fastDecay_le_short`/`_of_eq`（(7.16) Case 1）、
`norm_Uker_fastDecay_le_sumZero`/`_sigma`（(7.16) Case 2，(7.24)）；**`norm_Uker_tail_le`**/`_ellStar`/`_sigma`（(7.2)）。显式常数（`K` 代 `W^τ`、`δ` 代 `W^{-D}`）。
T56（Step 6）可用 `norm_Uker_fastDecay_le` 消去其 (7.14) 假设。paper-deltas #35。

### `RBM1D/Hierarchy/Step45.lean` — Steps 4、5（T55，Claude Code 并行 agent）

`Eq5125`（(5.125)，界传递形式）、`eq5125_of_lemma514`、**`xiLK_le_one`**（对 n 归纳，Ξ^{(L−K)} ≺ 1）、**`flow_sharpLmK`**（(2.78)，形状同 `Steps.sharpLmK`）；
`Eq548`/`FlowEq548`（(5.48)）、`decay_of_split`、**`flow_sharpDecay`**（(2.79)，形状同 `Steps.sharpDecay`）、`flow_steps45`。paper-deltas #36。

### `RBM1D/Hierarchy/Step6.lean` — Step 6（T56，Claude Code 并行 agent）

(5.128) `eq_Theta_of_selfConsistent`、Lemma 5.15 `lemma515`、(5.133)–(5.135) `driftBound_of_5133`/`driftBound_of_5134`、
(5.136) `core_bound`/`sharpExpect_of_hierarchy`，**`sharpExpect_step6`**（(2.80)，形状同 `Steps.sharpExpect`，u ∈ [s,t] 一致）。
(7.14) **已由 T51 的 `norm_Uker_fastDecay_le` 证出**（`est714At_cKer`），不是假设。随机层输入（期望后的 hierarchy、快衰减、(5.132)(5.133)、
`Eq527`、两条来自 (2.78) 的期望界、可积性、(2.72)）均为显式假设。paper-deltas #37。

**第二批（T42–T57）Claude Code 部分全部完成**：T43–T51、T53–T57（T42、T52 为 Cowork）。Steps 1–6 中 (2.77)(2.78)(2.79)(2.80) 均已有形状匹配
`Steps` 字段的定理；Lemma 2.18–2.20 由 Thm 2.21 推出（T57）。

### T66（维护，Claude Code）

蓝图补齐第二批 Cowork 部分的节点：`lem:4.2`（Minor，T40）、`def:5.2`（Kernel，T42）、`def:5.12`（SumZero，T52）；`\lean{}` 全部解析（989 个，
`scripts/blueprint_preview.py` 校验；本机无 `leanblueprint`）。`Green/Minor.lean`：提交工作树中已存在的编译修复（HEAD 版在本机 3 处报错）
并清掉全部 12 条警告（`omit … in`、`if_pos/if_neg → ite_eq_left/ite_eq_right`）；`Hierarchy/Kernel.lean` 已无警告。

## 一条需要先定下来的表示桥（2026-09-19，T58 发现）

`Hierarchy/Kernel.lean`（T42）里的张量算子 `Uker`、`ThetaOp` 作用在

    A : (Fin n → ZMod L) → ℂ

而 loop 层（`Loop/Index.lean` 起）用的是 `LoopIdx`，即两条 `List`：`σ : List Bool`、`a : List (ZMod L)`。
`primRhs` / `primBil` 都建在 `LoopIdx` 上。

**这两种表示目前没有桥。** T58 的 (5.12)–(5.15) 全部在 `LoopIdx` 一侧完成，不受影响；
但下面三件事必须跨过去：

* **(5.19)** `Θ_{t,σ} ∘ (L−K) = [K∼(L−K)]^{l_K=2}` —— 左边是 `ThetaOp`（`Fin n` 表示），
  右边是 `primBilLen 2`（`LoopIdx` 表示）。
* **(5.20)(5.21)** 的积分形式用 `Uker`，同样是 `Fin n` 表示。
* **§5.5 的 `Q_t`**（T52）也建在 `Fin (n+1) → ZMod L` 上。

**建议的桥**（谁先做 (5.19) 谁定，定完写回这里）：固定 `σ : List Bool`，
对每个 `n = σ.length` 给一个

    toTensor : (LoopIdx (ZMod L) → ℂ) → (Fin n → ZMod L) → ℂ
    toTensor F v = F ⟨σ, List.ofFn v⟩

并证 `List.ofFn` 与 `List.get` 互逆的那两条，剩下的就是把 `cutGlueL k l a` 在 `l = k+1`
（即 `l_K = 2`）时的显式形状翻译成 `Function.update`。

**不建议**把 loop 层改成 `Fin n` 表示：`LoopIdx` 的 `List` 形态是 `cutGlue*` 三个算子
（取前缀、丢后缀、拼接）能写得干净的原因，第 3 节整套树表示都压在上面。

### `RBM1D/Flow/Consequences.lean` — Theorems 2.3、2.4（T63，Claude Code 并行 agent）

**`localSemicircleLaw_of_Thm221`**（(2.3)(2.4) 与迹律）、**`quantumDiffusion_of_Thm221`**（(2.6)–(2.9)）；逐式版 `*_of_bounds` 与 `W^τ` 概率版。
缺口（接口所致）：只在固定能量切片 `SpecSeq`（`lemE (z N) = E`）上成立——全域一致需 `Bounds`/`Thm221` 允许 N 相关能量；
(2.4) 需新假设 `TransferLoop1`（1-loop 版 (2.39)）。paper-deltas #38。

### `RBM1D/Loop/ChainBound.lean` — Lemma A.2（T64，Claude Code 并行 agent）

**`lemma_A2`**（(A.3)(A.4)，显式常数，`Φ ≥ chainScaleUpTo … n`）、**`XiDiag_XiOff_step`**（(A.7) 一步，含 (A.14)(A.17)）、`XiDiag_XiOff_le_chainBound`（迭代）；
`sum_Sblk_mul_eq`（补上 T49 的 (A.20) 末步）。输入 `1/G_ii`、loop 界 `LoopBound`、[39] `ChainLDE16`/`ChainLDE19` 为假设。
(A.12)(A.13) 以单边比较绕过，T49 的 (A.25) 缺口不再需要。paper-deltas #40。

### `RBM1D/Loop/ContinuityAssembly.lean` — Lemma 5.1（T62，Claude Code 并行 agent）

**`lemma_5_1`**/`lemma_5_1'`（(5.7) 形式）：`c ≤ t₁ ≤ t₂ < 1`、(5.5) 在 t₁、(6.1) 作为假设 `LoopScaling` ⟹ `1_Ω max|L_{t₂}| ≺ (Wℓ₁η₂)^{-n+1}`。
确定性部分：(6.10) `wmass_gchainMixed_le`（经 Lemma 6.1 与 `trace_gram_rpow_le`）、(6.11) `loopMax_two_mul_le_tilde`、(5.6) 基例 `loopMax_one_le`；
随机部分：`StochDom.continuity_recursion`（(6.13) 递推）、`StochDom.of_le_add_sqrt_mul`。paper-deltas #41。

### `RBM1D/Hierarchy/Decay.lean` — §5.4（T59，Claude Code 并行 agent）

`LoopDecay`（Def 5.8，接 T51 的 `FastDecay`）；**(5.77)**：`norm_couplingLen_le`、`norm_primBil_sub_le`、`norm_eG_le`、`norm_eTens_le`（张量形式 `norm_loopTensor_*`），
E 项的衰减 `fastDecay_*`；(5.14) 的右分级 `primBilLenR`、`couplingLen`；Lemma 5.11 `lemma511_assembly`；Lemma 5.9 `lemma59`（在 Lemma 4.1 事件上）。
T60 可 import 此文件替换其 (5.77) 占位。paper-deltas #42。

### `RBM1D/Hierarchy/SumZeroDyn.lean` — Lemma 5.14 (5.92)（T60 ⭐，Claude Code 并行 agent）

**`lemma514_flow'`**：`∀ n, 2 ≤ n → Step3.Lemma514 B.P (flowXiLK …) (flowXiL …) (flowA …) n`——**T53/T55 所假设的 (5.92) 现在是定理**，
条件是：`Hierarchy`（(5.20)(5.91) 与鞅的 BDG/二次变差 (5.85)(5.103)，**唯一的真随机输入**）、`Lemma510`（(5.77) 占位）、`LKDecay`（(5.75) 占位）、
(2.72)、(2.68)@s。Ward 恒等式对 L−K 已证（`wardP_holds`）。
**剩余缺口**：`Lemma510`/`LKDecay` 与 T59（`Hierarchy/Decay.lean`）的确定性定理形状不同——需要 (i) 具体的 `E^{(G)}` 与 Def 5.4 的 `E⊗E` 粘合
（T58 的表示桥），(ii) 把 `Decay.lemma59` 从「Lemma 4.1 事件上」提升为「对 u ∈ [s,t] 一致的 ≺」。paper-deltas #43。

### `RBM1D/Hierarchy/Step1.lean` — §5.1 Step 1：(2.73)(2.74)（T67，Claude Code 并行 agent）

**`Step1.step1`** 给出 `(apriori, weakLaw)`，形状与 `Steps.apriori`/`Steps.weakLaw` 逐字一致（已临时构造 `Steps` 验证）。
(5.9) 的禁区论证抽成独立引理 **`forbidden_region`**，确定性核心 `lt_of_forall_ne_of_continuousOn`（介值定理），高概率版 `bootstrap`。
(5.4) `eq54`、(5.5) `eq55`（起点 `max(s,1/2)`）、(5.8) `eq58`；(5.2) `norm_Lval_le_of_le_half`。
假设（结构 `Hyp`）：(6.1) `LoopScaling`、`NetLift`（网 + (5.1)）、`Lemma41Flow`（Lemma 4.1 沿 `z_u`——现有 `entry_bound_stochDom` 只对固定谱参数）、`u ↦ ‖G_u−m‖_max` 连续。
**额外假设** `∃ c>0, N^c ≤ Wℓ_tη_t`（尚未从 `t ≤ 1−N^{−1+τ}` 经 `flowScale_ge` 推出，需 W/N 换算）。paper-deltas #44。

### `RBM1D/Flow/Universality.lean` — Theorems 2.5（QUE）与 2.6（普适性）（T68，Claude Code 并行 agent）

**Theorem 2.5 全证**：(2.14) `sum_window_le`（谱分解，常数 4）、(2.15) `norm_integral_trace_imGreen_queObs_le`、(2.16) `msc_gap`、(2.17)+Markov →
`theorem2_5_of_QDExpect`（(2.12)(2.13) 字面事件 `queEvent212/213`），并经 `QDExpect.of_Thm221` 接上 Thm 2.21 → 2.4 → 2.5（`theorem2_5_of_Thm221`，固定能量切片）。
**Theorem 2.6**：`theorem2_6_of_steps`——(2.21) `DBMUniversality`[51]、(2.23)⇒(2.24) `GreenComparison`[37,70]、(2.23) `StepTwoClaim` 为假设；GUE 关联函数 `gueCorr` 按特征值密度的边缘显式写出。
Step 3 已做部分：(2.27) `que_flow_of_eq747`、坏事件 `measure_bad_flow_of_eq747`（概率 ≤ 3N^{-c/18}，阈值 N^{-c/36}——疑似论文笔误）。
**剩余缺口**：(2.25)–(2.33) ⇒ (2.23) 的 L₁/L₂ 估计（需 [70, L4.18/4.20]、离域化、特征值计数）；`Eq747` 待 T65 替换。paper-deltas #45。

### `RBM1D/Hierarchy/GUEPhase.lean` — §7.2 GUE 相（T65，Claude Code 并行 agent）

**`eq747_of_inputs`** 产出 `Eq747`（T68 的占位），`que_flow_of_inputs` 把它接到 `que_flow_of_eq747`，(2.27) 端到端成立；输入结构 `Eq747Inputs`（(7.26) 期望形式、(7.29)@t₀、可积性）。
(7.25) `Stilde`/`zetaU`（复用 T46 `SBTilde`）；(7.30)–(7.32) `eq730`、`ellHat_eq_L`；(7.33)(7.34) `primRhsGUE` 与幂计数；(7.35)→(7.36) `K_bootstrap`/`eq736`；
(7.41)–(7.44) `eq742_of`/`eq744_of`；(7.45) `eq745_of_terms`；(7.27)(7.28) `eq727`/`eq728`/`eq728_of_eq745`；GUE 相 2-loop 闭式 `kTwoGUE`。
**剩余缺口**：`h745/h746`（(7.45)(7.46) 的 ≺ 界）需 T58 的 L−K 层级 + Duhamel/BDG；(7.29) 本身（§5.8 对 GUE 相的论证）与 (2.26)；GUE 相 ODE 的唯一性；`eq727` 的抽象极大值尚未实例化到具体 loop。paper-deltas #46。

### `RBM1D/Hierarchy/Step2.lean` — §5.3 Step 2：(2.75)(2.76)（T61，Claude Code 并行 agent）

**`Step2.step2`** 给出 (2.75)(2.76)，形状与 `Steps.localLaw`/`Steps.aprioriDecay` 一致（(2.74) 取自 `Step1.weakLaw`）。
(5.26)–(5.29) `tailLK`/`jStar`（复用 T43 `tailT`/`ratioJ`）；Lemma 5.6 `eq530`/`eq531`；Lemma 5.7 (5.34) `norm_eLL_le`；(5.39)–(5.41) `norm_Uker_le_of_tail`/`step_bound`；
自改进核心 `self_improving`（确定性）、停时 `stopTime` (5.43)；(5.47) `jS_stochDom`：`J*_{u,D} ≺ (η_s/η_u)^4`（D ≥ 60）。
假设（`Step2.Hyp`）：`SumZeroDyn.Hierarchy`（(5.20)，T58/T60 接口，漂移 F 抽象）、`eG`（(5.35)，兼作 T58 缺口：`eLL` 与具体漂移 `primBil` 的 (L−K)×(L−K) 部分的等同尚无证明）、`mart`（(5.44)–(5.46)）、`cont`（`(L−K)_u` 高概率连续）。
**⚠ 需 Jun 看一眼**：(2.72) 被加强为 `N^c(η_s/η_t)^30 ≤ Wℓ_tη_t`——按字面 (2.72)，`J*³(Wℓη)^{-1/3}` 项恰在阈值上，论证不闭合。另停时阈值加了 `N^δ` 余量。paper-deltas #47。
**剩余**：(5.48) 细化形式；(5.35)(5.36) 的证明（待 T58 具体化 F 与 E⊗E）；(5.42)(5.44)–(5.46) 由 BDG 推出。

### `RBM1D/Gauss/Domination.lean` — 矩 ⟹ ≺、`N^{-C}` 时间网（T73，Claude Code 并行 agent）

第四批「矩路线」的第一块落地。**`stochDom_of_momentDom`**：`MomentDom`（∀ε>0 ∀p ∃C，`E|Y|^{2p} ≤ C·N^{εp}Φ^{2p}`）+ `#U(N) ≤ N^Ccard` ⟹ `RBM.StochDom`（经已有的 `StochDom.of_forall_le`）；`stochDom_one_of_momentDom` 是 Φ=1 的情形。
**`stochDom_Icc_of_holder`**：`N^{-C}` 网（`netSize`/`netPt`/`exists_netPt_close`/`card_net_le`）+ 逐点 Hölder-γ 模 ⟹ **Def 2.1(i) 中对 u ∈ [0,T] 的不可数并在概率内部**——这是不可数并的解法。`stochDom_Icc_of_lipschitz` 是 γ=1 的推论。
**⚠ 接口提醒**：Hölder 而非 Lipschitz 是刻意的——T69 的 `‖H_u − H_{u'}‖ = |√u−√u'|·‖X‖` 在 u=0 附近**不是** Lipschitz，只有 1/2-Hölder。
**T69 对接时取 γ = 1/2**，并需 `‖X‖ ≤ N^K` 对每个 ω 成立（或先限制到好事件）。`hmom` 待 T72 的 Grönwall 输出。
假设：`[IsFiniteMeasure P]`、`|Y|^{2p}` 可积、`Φ > 0`；不需可测性（`badSet` 用外测度 `measure_mono`）。paper-deltas #48。

### `RBM1D/Gauss/Model.lean` — 高斯带矩阵与 `H_u = √u·X`（T69，Claude Code 并行 agent）

**`sample : RBM.Sample (band d)`**——`Sample` 的三个字段现在是**定理**（`Hflow_zero`、`Hflow_isHermitian`、`measurable_Hflow`）。
`integral_normSq_Xentry : ∫ ‖X_ij‖² dP = S_ij`（含对角）——这条是约定是否抄对的自检。
Lipschitz：`norm_Hflow_sub : ‖H_u − H_u'‖ = |√u − √u'|·‖X‖`（ℓ²→ℓ² 算子范数）、`abs_sqrt_sub_sqrt_le : |√u−√u'| ≤ √|u−u'|`——正好对上 T73 的 Hölder-γ 接口（取 γ=1/2）。

**⚠ T70/T71 必须逐字对上的指标约定**（详见文件头）：`idxKey d N (a,α) = W·a.val + α`，「i < j」一律指 `idxKey i < idxKey j`；
坐标 `Coord d = Σ N, Idx × Idx × Bool`（`true` = 实部，`false` = 虚部）；方差 `gvar = S_ij`（i=j）或 `S_ij/2`（i≠j），两个 tag 相同；
`X_ji = conj X_ij` 对每个 ω **逐点**成立（非 a.e.）。冗余坐标（`idxKey j < idxKey i`、对角虚部）从不被读取——**T71 对坐标求和时必须限制到被用到的那些**。
T70 的入口是 `P_map_eval`（单坐标律）与 `P_map_restrict`（任意有限坐标集的联合律 = `Measure.pi`）。

**两处缺口（未开工单，只在此记录，等 Jun 安排）**：
1. `‖X‖ ≺ 1`（算子范数的高斯尾）未证，现为假设结构 `OpNormBound`；Mathlib 既无矩方法也无矩阵范数的高斯集中。
2. **`Dims` 尚无实例**——整条矩路线在形式上以「`Dims` 非空」为前提。给出 `L=3, W=N/3, c=1/4` 之类的实例，唯一不平凡处是 (2.2)：`N^{3/4} ≤ ⌊N/3⌋` 终于成立（实 `rpow` 的活）。
另：本文件 import `Green.EntryBound` 仅为 `RBM.Sblk`；若不想要这个依赖方向，应把 `Sblk` 下沉到 `RBM1D/Defs/`。paper-deltas #49。

### `RBM1D/Gauss/Generator.lean` — 生成元恒等式（T71，Claude Code 并行 agent）

矩路线的核心。**`hasDerivAt_integral_Phi`**（坐标形式，右端**就是** (5.25) 的二次变差，T72 要的是这一版）与 **`hasDerivAt_integral_Phi_pairs`**（论文字面的 `½ Σ_i Σ_j S_ij E[∂_ij∂_ji Φ]`，`∂_ij∂_ji = wirtSecond`）。
证法即工单所述：在 `s ∈ Ioi (u/2)` 上 `hasDerivAt_integral_of_dominated_loc_of_deriv_le`，被积函数导数 `(2√s)^{-1} Σ_α ω_α ∂_α Φ`，逐坐标用 Stein，`√u` 相消。常数在两个算例上验过（标量 `Φ=M²`、2×2 的 `Φ=|M₁₂|²`，都恰好给出 `S`）。
**全局导数界**（工单要求，下游每处都用）：`norm_green_le : ‖G‖ ≤ η⁻¹`、`norm_iteratedDeriv_green_le : ‖∂^k G‖ ≤ k!·η^{-(k+1)}‖A‖^k`，都在**全空间**成立，故下游的 dominated 条件全是常数。
**一个坑已排掉**：`(M−z)^{-1}` 不是处处有定义，`Φ = |F(G(M))|^{2p}` 并非全局 `C²`、无法满足 `TestFun`；解法是先与 Hermitian 投影 `hermCLM` 复合（所有基点 `Hflow` 与方向 `Bmat` 都已 Hermitian，值不变）。

**⚠ 给 Cowork（T70）的接口**：矩阵版 Stein 作假设 `MatrixStein`（单字段），假设刻意取强以让 T70 的活尽量小——`FinDep`（有限依赖）让 `P_map_restrict` 把无穷乘积塌成 `Measure.pi`，之后就是对其余坐标 Fubini + 已落地的一维 `RBM.integral_mul_gaussianReal`。未碰 `Stein.lean`，也未写乘积版，无冲突。
**剩余**：`MatrixStein` 待 T70 卸掉；为具体的 `|F|^{2p}` 造 `TestFun` 是 T72 的活。paper-deltas #50。

### `RBM1D/Analysis/Bootstrap.lean` — 连续归纳（T78，Claude Code #2）✔

`RBM.le_of_bootstrap`：`φ` 在 `[a,b]` 上连续、`φ a ≤ B`、`B < C`，且逐点自改进 `φ u ≤ C → φ u ≤ B`，
则 `φ ≤ B` 于 `[a,b]`；`le_of_bootstrap_two_mul` 是 `C = 2B`（`B > 0`）的常用形。
证法：自改进把闭的下水平集 `{φ ≤ B}` 和开集 `{φ < C}` 认同，于是它在 `[a,b]` 里既开又闭，含 `a`，而 `[a,b]` 连通。
只依赖 Mathlib，公理审计干净。

**给 T75 的接口**：Step 2 的 bootstrap 里 `φ(u) := E[(J*_{u,D})^q]` 一旦是确定性连续函数，
停时 (5.43) 直接换成这条，不需要 optional stopping；只需另外提供 `φ` 在时间区间上的连续性。
**前缀形 `le_of_bootstrap_prefix` 已补**：自改进的前提可以是「直到 `u` 都满足 `φ ≤ C`」
（即 T61 写的「设 `J* ≤ (η_s/η_t)⁴` 直到 τ ⟹ 改进 τ 处」那个形状），证法是取「好时刻」的上确界 `s`，
连续性给出 `φ s ≤ B`，若 `s < b` 则连续性在 `s` 右侧给出 `φ < C`，自改进把它升成 `≤ B`，与上确界矛盾。

### `RBM1D/Gauss/Envelope.lean` — 反向桥 `≺ ⟹ 矩`、确定性包络（T77，Claude Code 并行 agent）

**`momentDom_of_stochDom`** 产出的就是 T73 的 `RBM.Gauss.MomentDom`（量词序逐字一致，两座桥按构造可复合）；
`momentDom_of_stochDom_of_nonneg`（`bdg`/`bdgQ` 实际用的形状）、`momentDom_of_normStochDom`。
常数 `C = P.real univ + 1`，阈值 `τ = ε/2`，例外指数 `D' = 2p(Kenv+B)+1`。
**确定性包络** `norm_gloop_le_det : ‖gloop‖ ≤ η_t^{-n}·W^{-(n-1)}`——**无测度、无 ω、无例外集**，对每个 Hermitian 矩阵成立；
覆盖 `loopMax_le_det`、`loopXi_le_det`、`norm_gloop_sub_le_det`（L−K，K 的逐点界作假设）；多项式增长形式 `norm_gloop_le_rpow` 是交给 T72 的对接点。
`J*` 未重证：已有的 `RBM.jStar_le` 已把它归约到分子的逐点界，重证会让 `Gauss/` 依赖 `Hierarchy/Step2.lean`（方向不对）。
假设：`Measurable (Y N u)`（`StochDom` 用外测度不需要，但分割积分需要）、`|Y|^{2p}` 可积、`Φ > 0` 且 `N^{-B} ≤ Φ`、包络 `|Y| ≤ Env N ≤ N^Kenv`（每个 ω）。paper-deltas #51。

### `RBM1D/Gauss/Hierarchy.lean` — Lemma 2.11 的矩形式（T76，Claude Code 并行 agent）

**`hasDerivAt_integral_gloop_hierarchy`**：`∂_v E[L(H_v,z)]|_{v=u} = E[Ẽ] + E[primRhs L_u]`——(2.45) 的期望版，`primRhs` 就是仓库里已有的那个。
`hasDerivAt_integral_Lval_hierarchy` 是 `z := zt E u` 的版本。**(2.45) 本身从不被证明**（工单明令）。
`integrable_sample_Lval`：`L_{u,σ,a}` 可积——**这条补上了 `Flow/Hypotheses.lean` 偏差清单里明确标记的可积性缺口**。
确定性包络 `norm_sample_Lval_le`（(5.2)，处处成立）；`loopObs` + `testFun_loopObs`（`bdd₀` 字段已卸，即 (5.2)）。

**⚠ 与现有假设字段的对接结论（需 Jun/Cowork 定夺）**：`RBM.Hierarchy` 的 `duhamel`/`duhamelQ` 是**逐路径**（∀ω）的积分恒等式且含鞅字段 `mart`，
矩路线既无逐路径 Duhamel 也无鞅，**这两个字段在现有形状下不可卸**——本文件的结果是它们的 `∂_u E[…]` 替代品，是不同的陈述，不是同签名的更小版本。`bdg`/`bdgQ` 属 T72+T73/T77，不在此。
`Bounds`/`Thm221`/`Steps`/`Transfer` 里没有与本文件同形状的字段。
**剩余假设**：`MatrixStein`（欠 T70）、`TestFun`（需矩阵求逆的 Fréchet `C²` + `List.foldr` 乘积的 Leibniz；Generator.lean 只有逐线的 `iteratedDeriv` 版）、`LoopIto`（纯确定性的 cut-and-glue 代数）。
**未做**：动 `z_u` 的全导数——需「偏导连续 ⟹ 可微」，Mathlib 没有可直接用的引理；这是冻结陈述与 (2.45) 字面期望之间唯一缺的分析步骤。paper-deltas #52。

### `RBM1D/Gauss/MomentGronwall.lean` — 对矩的 Grönwall 与支点恒等式（T72，Claude Code 并行 agent）

**支点 `secondOrder_eq_quadVar`**：`Σ_{α∈usedCoord} S_α‖∂_αF‖² = Σ_{i,j} ‖E^{(M)}_{ij}‖²`（`EmartCoeff = √S_ij · wirtFirst`）。
非对角的记账就是平行四边形恒等式 `‖½(x−iy)‖²+‖½(x+iy)‖² = ½(‖x‖²+‖y‖²)`——这正是论文按**有序对**加权 `S_ij` 与坐标按**一个代表**加权 `S_ij/2` 之间的那个因子 2。
`hasDerivAt_momentIntegral`：`d/du E|F(H_u)|^{2p} = E[𝓛(|F|^{2p})]`（u > 0）；`genMomentPt_le` 给出工单那个展开式，**但它是不等式**（见 paper-deltas #53；已用 p=3、p=1 两个 `norm_num` 算例核过）；`momentIntegral_le_gronwallBound` 收口。
`TestFun` 已为观测量 `φ(G)` 卸掉：`resH`（与 `hermCLM` 复合的预解式）的全局界 `η⁻¹`、`η⁻²`、`2η⁻³` ⟹ `bddC2_greenObs` ⟹ `testFun_momentFun_greenObs`；
capstone `hasDerivAt_momentIntegral_greenObs` **除 `MatrixStein` 外假设全部卸掉**。

**⚠ 支点与仓库现有 BDG 写法对不上（T74 需要知道的两件事）**：
1. `SumZeroDyn.Hierarchy.EE` 是**未解释的结构字段**，仓库里没有任何地方按 Def 5.4 把它定义成 `Σ_α E^{(M)}(α,k)·E^{(M)}(α,k)`——没有可等同的 Lean 对象，硬写等式就是凭空假设，agent 拒绝这么做（正确）。
2. 表示问题：支点这边是**矩阵的函数**，`EE`/`bdg` 活在 `LoopArg`/`LoopIdx` 上——就是 STATUS 里 T58 那条表示桥。
另：论文 (5.25) 的字面形式在 Schwarz 拆出 `Σ_k` 之后，本文件是拆分之前。**矩阵这一侧已经做完**；T74 要补的是 (i) 把 `L_{u,σ,a}` 写成 `H` 的函数并按 Def 5.4 定义 `EE`，(ii) `LoopIdx ↔ Fin n → ZMod L` 的桥。
**未做**：`BddC2` 对乘积封闭（故只实例化了一次的观测量 `φ(G)`，真正的预解式乘积还没有）；`Σ_k` 的 Schwarz 步；把 `genMomentPt_le` 变成 Grönwall 的前提（需 Hölder + loop 界，在下游）。paper-deltas #53。

### `RBM1D/Gauss/Moments.lean` — T81 进行中（Claude Code #2）

高斯矩的确定性输入，T81 与 T82 共用：

| Lean | 内容 |
|---|---|
| `RBM.integrable_pow_gaussianReal` | 多项式矩存在（由 `memLp_id_gaussianReal'`） |
| `RBM.integrable_mul_gaussianPDFReal` | 测度形式 ⟹ 密度形式的可积性桥（`withDensity`） |
| `RBM.integral_pow_gaussianReal_succ` | Stein 递推 `E[X^{2p+2}] = (2p+1)v·E[X^{2p}]` |
| **`RBM.integral_pow_gaussianReal`** | `E[X^{2p}] = (2p−1)!!·v^p`（`v = 0` 也成立） |
| `RBM.dfac` / `RBM.sum_choose_dfac` | `(2p−1)!!`；卷积恒等式 `Σ_k C(p,k)(2k−1)!!(2(p−k)−1)!! = 2^p p!`（Pascal 拆分 ⟹ `S(p+1) = (2p+2)S(p)`） |
| **`RBM.integral_add_sq_pow_gaussian_prod`** | 复中心高斯的绝对矩 `E[(X²+Y²)^p] = p!(2w)^p = p!σ^{2p}` |

Mathlib 没有高斯矩公式，这里是用我们自己的一维 Stein（T70 已落地部分）做递推得到的。
**下一步**：独立性引理（`G^(i)` 只依赖第 `i` 行以外的坐标，`FinDep` 见证集不含该行），
条件化后 `∑_k H_ik X_k` 是中心复高斯 ⟹ 用上面的矩公式 ⟹ 经 T73 的 Markov 桥落成 `≺`。
**插曲**：期间 `Gauss/Stein.lean` 一度编不过（Cowork 的 T70 在改，未提交），我用 HEAD 快照
（`.lake/packages` 软链 + `.lake/build` 复制到 scratchpad）离线验证，等对面提交后再在主工作区编译通过才提交。

**T81 第三块 ✔**（`Gauss/RowIndep.lean`）：`AgreeOffRow d N i ω ω'`（两个样本点在所有避开 `i` 的坐标上相等）⟹
`Xentry_congr_of_ne` ⟹ `Hflow_submatrix_congr`（minor 矩阵相同）⟹ **`greenMinor_congr_of_offRow`**：
在两边预解式都存在、对角元非零处，`G^(i)` 不读第 `i` 行的坐标。用的是 T40 的 `inv_minor_resolvent`。
这就是工单点名要抽出来、T82 也要用的那条独立性引理。
**下一步**：把「条件化」写成乘积测度上的 Fubini——行 `i` 的坐标是**有限**集，`G^(i)` 只依赖其补集，
于是 `∑_{k≠i} H_ik G^(i)_kj` 在冻结补集后是中心复高斯，矩由 `integral_add_sq_pow_gaussian_prod` 给出，
最后经 T73 的 `stochDom_of_momentDom` 落成 `≺`。

### `RBM1D/Hierarchy/Step2Moment.lean` — 不用停时的 Step 2（T75，Claude Code 并行 agent）

**停时真的没了**：`Step2.stopTime`/`tau`/`le_stopTime_iff`/`stopTime_eq_right`/`self_improving`/`step_bound`/`jS_highProb`/`Step2.Hyp` 在本文件里**一处都没引用**。
替代物：`le_of_bootstrap_weight`（复用 Cowork 的 `RBM.le_of_bootstrap_prefix`，`Analysis/Bootstrap.lean`，未重证）作用在**确定性**的 `φ_q(u) = E[(J*_{u,D})^q]` 上；
停止鞅字段 `Step2.Hyp.mart` → 不停止的矩字段 `MomentHyp.step`；高概率路径连续性 `Step2.Hyp.cont` → 逐 ω 的 `MomentHyp.cont`；Def 2.1(i) 的不可数并 → `stochDom_timeIcc_of_holder`（(5.46) 的网，T73 的版本写死在固定 `[0,T]`，故按 N-依赖区间重做）。
`continuousOn_phi` 用 `continuousOn_of_dominated` + T77 确定性包络给的常数控制函数。
**结论与 T61 逐字同形**：`jS_stochDom` 结论与 `Step2.jS_stochDom` 完全一致（复用 T61 的 `Step2.jS`，两条路线可互换），`aprioriDecay`、`step2` 同理；且假设更少（不需 `BoundsCore`、`hreg`、`60 ≤ D`——它们只在下游出现）。

**唯一真正缺的输入**：`MomentHyp` 的 `bnd/thr/init/step/bnd_poly`——(5.39)–(5.41)+(5.45) 的矩形式。
这正是 T74/T76 那道坎：`Gauss/Hierarchy.lean` 给的是 `∂_u E[L_u]`，而 `Step2.step_bound` 消费的 `SumZeroDyn.Hierarchy.duhamel` 是带 `mart` 字段的逐路径积分恒等式（STATUS 已记「现有形状下不可卸」）。agent 没有伪造推导。
`cont`/`holder`/`env`/`meas` 四个字段原则上都能由 `Gauss/Model.lean` + `Gauss/Envelope.lean` 给出（γ=1/2），但那要写在 `Gauss/` 下，本工单不许碰——**留给后续工单**。paper-deltas #54。

**T81 第四块 ✔**（`Gauss/LinearForm.lean`）：`iIndepFun_coord`（坐标独立，由 Mathlib 的 `iIndepFun_infinitePi`）、
`hasLaw_coord`（每个坐标是 `N(0, gvar c)`）、`hasLaw_const_mul_coord`（`a·ω c` 是 `N(0, a² gvar c)`）。
**下一步**（已探明 Mathlib 侧零件）：有限实线性型 `∑ a_c ω_c` 的律——
`iIndepFun.hasGaussianLaw_fun_sum` 给出和是高斯，`IsGaussian.eq_gaussianReal` 由均值/方差定出具体的 `gaussianReal`，
方差用 `variance_sum`（独立）。再把 `(Re Z, Im Z)` 的联合律认成两个独立一维高斯的乘积
（零协方差 + 联合高斯 ⟹ 独立），最后接上已证的 `integral_add_sq_pow_gaussian_prod`。

**T81 第五块 ✔**（`Gauss/LinearForm.lean`）：**`map_sum_const_mul_coord`**——有限实线性型 `∑_c a_c ω_c` 的律是
`N(0, ∑_c a_c² v_c)`。证法是对有限集归纳：`iIndepFun_const_mul_coord` + Mathlib 的
`indepFun_finsetSum_of_notMem`（单个坐标与其余之和独立）+ `gaussianReal_conv_gaussianReal`（高斯卷积）。
没走「均值/方差 + `IsGaussian.eq_gaussianReal`」那条路，卷积归纳更短。
**下一步**：`(Re Z, Im Z)` 的联合律 = 两个独立 `N(0, σ²/2)` 的乘积（零协方差 + 联合高斯 ⟹ 独立），
接上 `integral_add_sq_pow_gaussian_prod` 即得 `E‖Z‖^{2p} = p!σ^{2p}`；再冻结补集坐标（行 `i` 坐标是有限集，
`G^(i)` 只依赖补集，见 `RowIndep.lean`），最后经 T73 的 `stochDom_of_momentDom` 落成 `≺`。

**T81 第六块 ✔**：`map_sum_const_mul_of_indep`——第五块的抽象版，对**任意**独立高斯族成立（不绑定 `P d`），
`map_sum_const_mul_coord` 变成它的推论。这样冻结补集后得到的**有限块乘积测度**也能直接用同一条。
**收口路线已定**（比原计划省事）：LDE 只需矩的**上界**，不必精确等式——
`‖Z‖^{2p} ≤ 2^{p−1}((Re Z)^{2p} + (Im Z)^{2p})`，而 Re、Im 各自是实线性型，
其律由上面这条给出、矩由 `integral_pow_gaussianReal` 给出，于是 `E‖Z‖^{2p} ≤ 2^p(2p−1)!!σ^{2p}`。
**这样就完全绕开了「联合律 = 两个独立一维高斯之积」那一步**（零协方差 ⟹ 独立那套不必碰）。
剩下的唯一机器是分块 Fubini：`iIndepFun.indepFun_finset`（行 `i` 的坐标块 ⟂ 其余块）
+ `indepFun_iff_map_prod_eq_prod_map_map` + `integral_prod`，把 `G^(i)` 冻结成常系数。

### `RBM1D/Gauss/DischargeBDG.lean` — Def 5.4、(5.22)(5.25)、Lemma 5.5（T74，Claude Code 并行 agent）

**结论先说：`bdg`/`bdgQ` 在现有签名下不可卸，且不是「暂时做不到」而是结构性的。** agent 核实了 T72 的两条，并找到第三条（模块文档里写全了）：
1. `SumZeroDyn.Hierarchy` 的 `F`/`EE`/`mart`/`martQ` 是**无约束的数据字段**，`duhamel` 可以**按定义造出来**（取 `mart :=` 残差即可对任意 `F` 成立），于是全部内容都压在 `bdg` 上；
   甚至能取到使 `bdg` 空洞的 `F`（同时让 `SumZeroDyn.Lemma510` 为假）——那是伪造，agent 没做。
2. 残差 `∫_s^v U_{u,v}∘F_u(H_u) du` **不是 `H_v` 的函数**（路径依赖）：代入 `X = H_v/√v` 后 `Ψ_v` 通过两个位置依赖 v，需要 T71 不提供的「对 v 的偏导」——与 T76 卡在动 `z_u` 是同一堵墙。
3. 没有任何东西保证残差**无漂移**：Grönwall 要 `𝓛F = 0`，真 Itô 鞅自动满足，而 `H_u = √u·X` 给不出（无域流无鞅）。
**故 `bdg`/`bdgQ` 保持假设，未碰任何 `Hierarchy/` 文件**；本文件给的是同一陈述（≺ 进、≺ 出）在矩路线词汇下的版本 `stochDom_of_quadVar`。

**正面成果**：`eeRaw` 给了 Def 5.4 一个**定义**，且 `eeRaw_self_eq_quadVar` 证明其对角**就是** `quadVar`——这正是 T72 说「仓库里没有可等同的对象」的那条等式，现在有了。
(5.22) `eeEdge_eq_sum_SB`（`W` 因子由 `S = S^(B)/W` 与 `E_a = W⁻¹P_a` 自然落出，不是手插的）；(5.25) 的 Schwarz 步 `quadVarPairs_le_of_split`；
`LoopArg ↔ LoopIdx` 桥 `toIdx` 与 `emart_Uker`/`quadVarPairs_Uker`（论文「`U_{u,t,σ}` 是确定性线性算子」那一步，因 `RBM.Uker` 字面就是这样的线性组合）。
**剩余假设**：`MatrixStein`（T70）、`BddC2`（T72 只对预解式观测量卸掉，loop 观测量待 T76 的 `List.foldr` Leibniz 缺口）、`hdrift : 𝓛F = 0`、`hsplit`（链式法则 `E(α)=Σ_k E(α,k)`）、`hdiff`——后三条同源于同一个缺失的 Leibniz 规则。paper-deltas #55。

**T81 第七块 ✔**（`Gauss/LinearForm.lean`）：`linVar`（线性型的方差）、`map_lin`、`integrable_pow_lin`、
**`integral_pow_lin`**（`E[(∑ a_i X_i)^{2p}] = (2p−1)!!·(∑ a_i² v_i)^p`，由线性型的律 + `integral_pow_gaussianReal`）、
**`integral_sq_add_sq_pow_le`**（`E[(Y²+Y'²)^p] ≤ 2^p (2p−1)!!(V_a^p + V_b^p)`，即模的矩界，
不需要识别联合律）。纯分析部分到此齐活。
**只剩最后一步**：分块 Fubini——把行 `i` 的坐标块与补集分开（`iIndepFun.indepFun_finset`），
冻结补集后 `G^(i)` 成常系数，套用上面两条得条件矩界，最后经 T73 的 `stochDom_of_momentDom` 落成 `≺`。

**T81 第八块 ✔**：`integral_indep_pair`（`U ⟂ V` 时 `E[F(U,V)]` = 对两个律的迭代积分）与
`integral_indep_pair_le`（内层条件积分的一致上界 ⟹ 整体上界）。这就是把 `G^(i)` 冻结成常系数的那一步。
**T81 剩下的全是对接**：(1) 取 `K` = 行 `i` 的坐标（有限），`U` = 该块、`V` = 其余坐标；
`iIndepFun.indepFun_finset` 给 `U ⟂ V`。(2) 用 `RowIndep.lean` 把 `G^(i)` 写成 `V` 的函数
（对 minor 预解式 `((H^(i) − z)⁻¹` 直接成立，无需可逆性边条件）。(3) 内层用第七块的
`integral_sq_add_sq_pow_le`，得条件矩界 `≤ (2p−1)!!·σ^{2p}`，其中 `σ² = t ∑_k S_ik |G^(i)_kj|²`。
(4) 外层用 T73 的 `stochDom_of_momentDom` 落成 `≺`。

### `RBM1D/Gauss/CondRow.lean` — `E_k` 即对行的积分（T84，Claude Code 并行 agent）

全文建在一个小工具上：`rowSplit k ω ω'` 取 `ω'` 的第 k 行坐标、其余取 `ω`；`condRow k X ω := ∫ ω', X (rowSplit k ω ω')`。
因为 `rowSplit k (rowSplit k ω ω') ω'' = rowSplit k ω ω''`，所有代数恒等式**逐点成立，没有 a.e.**：
幂等 `condRow_condRow`、**`condRow_sub_condRow`（`E_k∘(1−E_k) = 0`，消失引理的全部依据）**、`integral_condRow`（`E[E_k X] = E[X]`）、`condRow_mul_of_finDepOffRow`（提出不读第 k 行的因子）。
唯一真正的测度论输入是 `measurePreserving_rowSplit`（`(ω,ω') ↦ rowSplit` 把 `P ⊗ P` 推成 `P`，按盒子用 `Measure.eq_infinitePi` 证）。

**给 T81/T82/T86 的公共引理**：`FinDepOffRow d N k g`（见证集不含第 k 行坐标），主实例 `finDepOffRow_of_minor` —— 任何 `F (H_u 的删行删列子矩阵)` 都满足；
消费形式 `FinDepOffRow.rowSplit_eq`、`condRow_of_finDepOffRow : E_k[g] = g`、`FinDepOffRow.comp`、`FinDepOffRow.finDep`（可直接喂给 `MatrixStein`）。
**注意**：`greenMinorMat` 是 ω 的**全函数**（`Matrix.inv` 是全函数），故 `finDepOffRow_greenMinorMat` **不带可逆性边条件**——与 `Gauss/RowIndep.lean` 的 `greenMinor_congr_of_offRow`（需 `hdet`/`hGii` 等四个条件）不同；`greenMinorMat_eq_minorGreen` 在论文假设成立处把两者接回。已复用 Cowork `RowIndep.lean` 的 `Hflow_submatrix_congr`/`AgreeOffRow`，未改动该文件。
可积性：幂等与提出因子**不需要**任何可积性；`condRow_add/sub` 需逐 ω 的 `RowIntegrable`；`integral_condRow` 只需 `Integrable X`。
**未做**：`Measurable (condRow k X)` 未证——T84–T88 目前不需要，但若 T87 要在外层积分里迭代 `E_{k₁}E_{k₂}` 就会需要（`StronglyMeasurable.integral_prod_right`，是个小后续）。paper-deltas #56。

### `RBM1D/Gauss/MinorReplace.lean` — 替换误差 `|G_ll − G^(k)_ll| ≺ Ψ²`（T85，Claude Code 并行 agent）

确实如工单所说是便宜活：(4.9) 是**恒等式**且仓库里已有两份（`Green/Minor.lean` 的 `inv_minorMat`、`Green/EntryBound.lean` 的 `greenMinor`/`greenMinor_sub`，已与 p.49 对过），
确定性估计也已有（`GoodEvent.norm_greenMinor_sub_le_le`：事件 (4.1) 上 `‖G^(k)_{jl} − G_{jl}‖ ≤ 2‖G_{jk}‖‖G_{kl}‖`）。本单只做随机装配。
**`minorReplace_diag_stochDom`** 即工单陈述；三元组版 `minorReplace_stochDom` 与 Ψ-级版 `minorGreen_localLaw_*` 顺带白得。
**`|G_kk|` 的下界不是额外假设**——由事件 (4.1) 经 `GoodEvent.half_le_norm_diag` 读出（`≥ 1/2`），与 `EntryBound.lean` 里 Lemma 4.1 的打包方式一致，故 T86 可以复用它**已经需要**的那个 `hΩ`，不必再背一条冗余假设。每条结论都给了 `1_Ω` 指示函数版与 `hΩ` 版两种。
唯一的假设是 `hoff : |G_{ij}| ≺ Ψ`（`i ≠ j`），即 Step 2 的 (2.75)；`stochDom_offdiag_of_localLaw` 负责形状转换，`Ψ` 留成自由的 `ℕ → ℝ` 供 T86 实例化。
**未做**：Ψ-级结论右端是 `Ψ² + Ψ` 而非 `Ψ`（收拢需 `∀ᶠ N, Ψ N ≤ 1`，agent 选择不硬塞一条 `hdet` 看不见的假设；`StochDom.mono_right_eventually` 一行可收）。paper-deltas：无新增。

**T81 第九块 ✔**：`glue` / `measurable_glue` / `eq_glue_of_congr`——把「只读 `S ∪ T` 的量」写成
`F(块_S, 块_T)` 的形状（其余坐标填 0），正是 `integral_indep_pair` 需要的输入。
至此 T81 的通用机器全部就位（矩、线性型、行独立、分块 Fubini、胶水）。
**剩下**：定义行 `i` 的坐标有限集 `rowSet`、与「其余相关坐标」`usedCoord ∖ rowSet` 两块，
用 `iIndepFun.indepFun_finset` 得独立，再把 `ldeRowLHS`/`ldeRowRHS` 用 `eq_glue_of_congr` 写成两块的函数，
内层套 `integral_sq_add_sq_pow_le`，外层接 T73。

**T81 第十块 ✔**（`Gauss/RowIndep.lean`）：`rowSet d N i`（索引对含 `i` 的坐标，有限集）、`mem_rowSet`、
`agreeOffRow_of_agree_compl`（在 `rowSet` 之外相等 ⟹ `AgreeOffRow`，接上第三块）、
**`indepFun_rowSet`**（行块与任何不交坐标块独立，由 `iIndepFun.indepFun_finset`）。
**T81 余下**：把 `ldeRowLHS`/`ldeRowRHS` 用 `eq_glue_of_congr` 写成 (行块, 其余相关块) 的函数
（`G^(i)` 只依赖后者，需要用 minor 预解式的形式以避免可逆性边条件），
内层对冻结的系数套 `integral_sq_add_sq_pow_le`，外层用 T73 的 `stochDom_of_momentDom`。

**T81 第十一块 ✔**：`rowCoord d N i k b` / `rowSign`——把行 `i` 的坐标按「(列 k, 实/虚标志 b)」参数化；
`Xentry_eq_rowCoord`（`X_{ik} = ω(实) + ε i ω(虚)`，`ε = ±1`）、`rowCoord_mem_rowSet`、`rowCoord_injOn`（单射）。
这样行和就是以 `(k, b)` 为指标的线性型，**不需要把和重标号到 `Coord` 上**——
直接用 `iIndepFun.precomp`（单射前合成）把坐标族拉到这个指标集上，再套第六/七块。

### `RBM1D/Gauss/FlucVanish.lean` — 消失引理（T86，Claude Code 并行 agent）

**`norm_integral_prod_flucDiag_le`**：`k i₀` 恰好出现一次 ⟹ `‖E[∏ᵢ Z_{kᵢ}]‖ ≤ (#ι−1)·ε·B^(#ι−1)`。
抽象层 `integral_mul_prod_eq_zero` 证的是替换之后期望**恰为 0**（T84 的 `condRow_sub_condRow`），误差由 `norm_prod_sub_prod_le` 逐项望远镜化。
补齐了 `FinDepOffRow` 的封闭性（CondRow 只有 `.comp`/`.finDep`）：`.mul`/`.sub`/`finDepOffRow_prod`/**`finDepOffRow_condRow`**（`E_{k'}` 不会重新引入对第 k 行的依赖——这正是 `G^{(k₁)}` 前面那个 `(1−E_{kᵢ})` 无害的原因）。

**为什么用矩形式而不是 `≺`**：`E[∏ᵢ Z_{kᵢ}]` 是个**数**，没有随机变量可供 `≺` 支配；写成 `≺` 就得凭空造一个常数随机变量。
T87 展开 `E|Σₖ tₖZₖ|^{2p} = Σ_{(k₁,…,k_{2p})} (∏t)·E[∏ᵢ Z_{kᵢ}]` 并按不同指标个数分层，每个被加项正是这个形状的数；`≺` 到 T88 末尾经 `stochDom_of_momentDom` 才回来。
**T87 要的索引形状**：抽象 `[Fintype ι] [DecidableEq ι]`（T87 取 `ι = Fin (2p)`）加特选 `i₀`，多重指标 `k : ι → Idx`，「只出现一次」即 `hone : ∀ i ≠ i₀, k i ≠ k i₀`；
抽象层把 `Z Y : ι → Ω → ℂ` 当**任意族**，不强制 `k i = k j ⟹ Z i = Z j`，故 T87 可在一半 slot 放共轭因子。

**⚠ 与 T85 的接缝（T87/T88 要处理）**：`B`、`ε` 是**逐点一致**的参数，而 T85 的 `minorReplace_diag_stochDom` 给的是 `≺ Ψ²`（高概率事件上的界）。
把后者变成一致的 `ε` 是指示函数/截断的记账，属 T87/T88。陈述**不空洞**：`Im z > 0` 已使 `B`、`ε` 确定性地有限（Envelope 的 `norm_green_zt_le`），只是不小——小是截断买来的。
已备好两座桥供 T85 直接插入：`greenMinorMat_apply_eq_greenMinor`（T84 的全函数 `greenMinorMat` = T85 的 `RBM.greenMinor`）与 `norm_flucDiag_sub_flucDiagMinorFam_le`（entry 误差 `e` ⟹ 因子误差 `2e`）。
**剩余假设**：可测性 `hZmeas`/`hYmeas`（CondRow 有意未证 `Measurable (condRow k X)`，见 paper-deltas #56；仓库也没有 `ω ↦ green (Hflow …) z k k` 的可测性——都很浅但不在本单范围）、`hrow : RowIntegrable`、`hB : 0 ≤ B`。paper-deltas #57。

**T81 第十二块 ✔**：`RowIdx`（(列 k ≠ i, 实/虚标志)）、`rowVar`（该指标上的高斯坐标）、
系数 `rowRe`/`rowIm`，以及 **`re_row_sum` / `im_row_sum`**——
`Re(∑_{k≠i} H_ik c_k)` 与 `Im(...)` 都写成了 `rowVar` 上的实线性型（系数显式）。
**下一步**（T81 的倒数第二块）：`rowVar` 族的独立性（`iIndepFun.precomp`，单射由 `rowCoord_injOn` 给出）
与各自的律（`P_map_eval` + `gvar_offDiag` 得方差 `S_ik/2`），
然后 `linVar` 算出 `V_a = V_b = (u/2)∑_k S_ik‖c_k‖²`，套第七块得
`E‖∑_k H_ik c_k‖^{2p} ≤ 2(2p−1)!!(u ∑_k S_ik‖c_k‖²)^p`（系数 `c` 为常数的冻结版本）。

**T81 第十三块 ✔**（关键一步）：**`integral_norm_row_sum_pow_le`**——系数冻结时
`E‖∑_{k≠i} H_ik c_k‖^{2p} ≤ 2·(2p−1)!!·(u ∑_k S_ik‖c_k‖²)^p`。
用到 `iIndepFun_rowVar`（沿单射的行参数化做 `precomp`）、坐标的律与方差 `S_ik/2`（`gvar_rowCoord`）、
`linVar_rowRe`/`linVar_rowIm`（两个方差都等于 `(u/2)∑_k S_ik‖c_k‖²`），最后套第七块。
**T81 只剩最后一步**：把常系数 `c` 换成 `G^(i)_{·j}`——用 `indepFun_rowSet` + `eq_glue_of_congr`
把行块与其余块分开（`G^(i)` 只依赖后者，见 `greenMinor_congr_of_offRow`），
内层套这一条，外层经 T73 的 `stochDom_of_momentDom` 落成 `≺`。

**T81 第十四块 ✔**：`relCoord d N`（`H` 在尺度 `N` 实际读到的坐标）、`offRowCoord = relCoord ∖ rowSet`、
两块不交（`disjoint_rowSet_offRowCoord`），以及 **`Hflow_submatrix_congr_offRowCoord`**——
minor 矩阵 `H^(i)` 只读 off-row 块。注意这条比第三块的 `AgreeOffRow` 更贴合分块 Fubini：
只要求在**有限**的 off-row 块上相等（`AgreeOffRow` 要求所有避开 `i` 的坐标，包括非规范序的那些）。
**T81 最后一步**：`U` = 行块、`V` = off-row 块；`indepFun_rowSet` 给 `U ⟂ V`；
`eq_glue_of_congr` 把行和与 `G^(i)` 分别写成 `U`、`V` 的函数；内层套第十三块；外层接 T73。

**T81 第十六块 ✔（核心结论）**：**`integral_norm_rowSum_pow_le`**——系数 `C` 只读 off-row 块时，
`E‖∑_{k≠i} H_ik C_k‖^{2p} ≤ 2(2p−1)!!·E[(u ∑_k S_ik‖C_k‖²)^p]`。
即「条件化后行和是中心复高斯」这一步已经**完整证出**：用 `indepFun_rowSet` + `glue` 把两块分开
（`integral_indep_pair_le`），纤维上套第十三块的冻结界，再积回去。
可积性作为显式假设（实例化到 `G^(i)` 时由确定性包络 `‖G‖ ≤ η⁻¹` 给出），另需 `C` 可测。
**T81 只差最后对接**：取 `C ω := G^(i)_{·j}(ω)`（`greenMinor_congr_of_offRow` / 
`Hflow_submatrix_congr_offRowCoord` 给出「只读 off-row 块」），得到
`E[ldeRowLHS^p] ≤ 2(2p−1)!!·E[(t·ldeRowRHS)^p]`，再经 T73 的 `stochDom_of_momentDom` 落成 `≺`。

### `RBM1D/Gauss/FlucCount.lean` — 计数（T87，Claude Code 并行 agent）

**`integral_norm_flucAvg_pow_le`**（任意实权重 `t`，`Σ|t_k| ≤ 1`）：`∫‖Σ_k t_k Z_k‖^{2p} ≤ (2p−1)·ε·B^{2p−1} + (Σ_{v : ¬HasLoneSlot} ∏_i |t_{v i}|)·B^{2p}`；
`integral_norm_flucAvg_pow_le_uniform` 把权重和算出来，得 `… + c^p·p^{2p}·B^{2p}`。
展开用 `prod_epsHom_sum_eq`（`‖Σ t_k Z_k‖^{2p} = Σ_v (∏ t)·∏_i e_i(Z_{v i})`，`epsHom` 在左半 slot 取恒等、右半取共轭）。
分层用谓词 `HasLoneSlot`（**就是 T86 的 `hone`**）配 `Finset.sum_filter_add_sum_filter_not`：lone 那层逐字喂给 T86 的 `norm_integral_prod_le`，其总权重经 `Finset.sum_prod_piFinset` 由 `(Σ|t_k|)^{2p} ≤ 1` 控住；
补集那层走 `two_le_card_fiber → two_mul_card_image_le → card_filter_not_hasLoneSlot_le`（`≤ (#A)^p·p^{2p}`）。**如 T86 文档所许诺，`FlucVanish.lean` 一行都不用改。**
两组系数都已备好：`uniformWeight_blockAvg`（`c = W⁻¹`、`#A = W`）与 `uniformWeight_Sblk`（`c = (3W)⁻¹`、`#A = 3W`），基数由 `card_filter_fst_mem`/`card_filter_sub_mem_sbSupport` 算出。

**⚠ 与 T85 的 `≺`/逐点接缝仍未合拢——留给 T88**（agent 明说没有伪造）。本单的贡献是把截断要打的靶子压成**一个平坦的接口**：只对指标集量化的六条假设 `hZmeas`/`hYmeas`/`hrow`/`hZB`/`hYB`/`hεb`（加 `0 ≤ B`、`0 ≤ ε`）；
T86 那种逐多重指标的形状（`flucDiagMinorFam`、依赖 `hone` 的子类型）已在证明内部消化干净。可测性与 `RowIntegrable` 承自 T84/T86（paper-deltas #56、#57），非新增。paper-deltas #58。

**T81 第十七块 ✔**：`rowCoeffNorm`（系数除以随机标准差 `√V`）与 `rowVarSum_rowCoeffNorm`
（归一化后方差恰为 `1`，`V = 0` 时为 `0`）。把它代入第十六块即得**常数**矩界
`E[(‖Z‖²/V)^p] ≤ 2(2p−1)!!`——正是 `MomentDom`（Φ = 1）要的形状，比值形式直接对接 T73。

**T81 第十八块 ✔**：**`integral_norm_rowSum_norm_pow_le`**——归一化后得到**常数**矩界
`E‖Z/√V‖^{2p} ≤ 2(2p−1)!!`（`V = 0` 的退化分支一并处理），配套 `measurable_rowVarSum`、
`measurable_rowCoeffNorm`。这正是 `MomentDom`（Φ = 1）的输入。
**T81 仅剩**：取 `C ω := (H^{(i)} − z)⁻¹` 的第 `j` 列（`Hflow_submatrix_congr_offRowCoord`
给出「只读 off-row 块」），把它与 `ldeRowLHS`/`ldeRowRHS` 对上（需要 `greenMinor` = minor 预解式，
即 T40 的 `inv_minor_resolvent`，带可逆性前提），最后经 `stochDom_of_momentDom` 得 `≺`。

### `RBM1D/Gauss/LDEQuad.lean` — 二次 LDE（T82，Claude Code 并行 agent）

按工单的路线 (b)：每个行坐标做一次高斯分部积分，化成对矩的递推；**先做 p=1 再上归纳**（工单要求），p=1 得到的是**精确恒等式**。
`integral_chaos_mul`（分部积分主恒等式）← `sum_coord_mul_deriv`（Euler：`Σ_α ω_α ∂_α Q = 2(Q + Σ_k σ_k B_kk)`）；
`moment_recursion` → `two_mul_mom_succ_le` → **`mom_succ_le : E|Q|^{2p} ≤ (2p−1)^p·E[T^p]`**（用自证的 `young_pow` 收口，有理指数，不需 `rpow`、不需 Hölder）；
`mom_one : E|Q|² = E[Σ_{k,l} σ_k‖B_kl‖² σ_l]` 精确。
**与 `RBM.LDEQuad` 的对接**：`norm_chaos_sq_eq_ldeQuadLHS`、`Vq_eq_ldeQuadRHS`、`integral_ldeQuadLHS_eq` 把两边与 `ldeQuadLHS`/`ldeQuadRHS` **逐字**对上（纯重排）。
**行独立性假设**（T84 可卸）：`RowChaos` 的 `Ifree`/`Ifree_free`/`B_free` 三个字段，正是「`B` 是 `FinDep` 且见证集不含第 i 行坐标」；T84 的 `rowSet`/`greenMinor_congr_of_offRow` 是自然的卸法。

**唯一真正的缺口**：`E[T^p] ≤ C_p E[Vq^p]`——`mom_succ_le` 把一切归约到它，p=1 时就是已证的 `momT_zero`。
教科书证法是带**随机权重**的 Jensen，需要 T84 的条件期望；免条件化的证法是对 `E[T^p]` 再跑一遍同样的分部积分（导子 `D_l = r∂_{a_l} − rε_l i∂_{b_l}` 杀掉 `U_k`、`\bar V_k`），得 `E[T^p] ≤ c_p E[Vq·T^{p−1}]` 再配 `young_pow`——文件头有完整草图。
**另未做**：模型上的具体 `RowChaos` 实例（需 `co`/`eps` 由 `Xentry` 的 `idxKey` 分情况给出，以及 `greenMinor` 的全局连续性与有界性——属 T84/T85 领地）；`StochDom` 收尾（`stochDom_of_momentDom` 要**确定性**控制，而 `ldeQuadRHS` 是随机的，应走 `StochDom.of_det`）。
携带假设 `GaussIBP`（同 `MatrixStein`，属 T70 领地；文件头记了由 `MatrixStein` 经截断推出 (i) 的论证）。paper-deltas #59。

## ⚠ HEAD 编译失败：`Gauss/RowIndep.lean`（Cowork / Claude Code #2 的 T81，2026-09-20）

`lake build RBM1D` 在 `RBM1D.Gauss.RowIndep` 上失败（最新提交 `f6b959c`「T81 (part 18)」）：

- `RowIndep.lean:656:4: `simp` made no progress`
- `RowIndep.lean:659:10: invalid `▸` notation`（`dif_neg h` 的等式两边都不含期望的结果类型 `Measurable fun c ↦ if h : k ≠ i then … else 0`）

**不是我这边的文件**，我没有改它。我这一批（T82/T84/T85/T86/T87）各文件的 `lake env lean` 与全局的 `Replayed` 行都是绿的。
按 CLAUDE.md「build 红着的时候」那一节：这期间两边判断自己的文件是否通过，要看 `build.log` 里自己文件的 `Built/Replayed` 行，而不是末尾的 `errors:`。

**T81 第十九、二十块 ✔**：`measurable_det_entries`/`measurable_adjugate_entries`/`measurable_inv_entries`
（逐元素可测 ⟹ 行列式、伴随、逆的元素可测）、`minorCol`（`(H^{(i)} − z)⁻¹` 的第 `j` 列）及其可测性与
「只读 off-row 块」（`minorCol_congr`），最后接成
**`integral_norm_rowSum_minorCol_pow_le`**：归一化后的行和满足常数矩界 `≤ 2(2p−1)!!`。
**这就是 T81 的核心分析结论**（论文的线性 LDE 的矩形式）。
**T81 收尾还需**：(a) 可积性假设的消除（由 `‖G^{(i)}‖ ≤ η⁻¹` 的确定性包络给出，接 T77）；
(b) 与 `Green/EntryBound.lean` 的 `ldeRowLHS`/`ldeRowRHS` 对齐（`greenMinor` = minor 预解式，
即 T40 的 `inv_minor_resolvent`，带可逆性前提）；(c) 经 T73 的 `stochDom_of_momentDom` 落成 `≺`。

**T81 第二十一块 ✔**：与论文 LDE 量的对齐——`minorCol_eq_greenMinor`（用 T40 的 `inv_minor_resolvent`，
带可逆性前提）、**`ldeRowLHS_eq`**（`ldeRowLHS = ‖行和‖²`）、**`rowVarSum_eq`**（`rowVarSum = u · ldeRowRHS`）。
于是第二十块的常数矩界可以逐字翻译成论文的 `|∑_k H_ik G^(i)_kj|² ≺ ∑_k S_ik |G^(i)_kj|²`。
**T81 只差**：(a) 消掉可积性假设（由 `‖G^(i)‖ ≤ η⁻¹` 的确定性包络，接 T77）；
(b) 经 T73 的 `stochDom_of_momentDom` 正式落成 `≺`（需按 `MomentDom` 的量词次序组织：ε 在 p 外）。

**T81 第二十二块 ✔**：`lintegral_indep_pair` / `lintegral_indep_pair_le`（Tonelli 版分块引理）。
**为什么需要它**：第十六/十八块的可积性假设**不能**用确定性包络消掉——比值的分母 `V` 可能任意小，
`‖Z‖/√V` 没有一致界。正确做法是对非负被积函数走 Tonelli：无需先有可积性即可得
`∫⁻ ‖Z/√V‖^{2p} ≤ 2(2p−1)!!`，再由有限性**反推**可积性。
**下一步**：把第十三块的冻结界转成 `∫⁻` 形式（非负可积 ⟹ `∫⁻ = ofReal ∫`），
套 `lintegral_indep_pair_le` 得无假设版本的比值界，然后接 T73。

### `RBM1D/Gauss/FlucAvg.lean` — (4.12) ⟹ (4.5) 的总装（T88，Claude Code 并行 agent）

**先说结论**：`hFA` **已在原签名下卸掉**（`EntryBound` 一字未动），(4.5) 由 (4.12) + `hIBP` 得出（确定性版与 ≺ 版都是定理）。
`norm_trace_green_sub_mul_Eblk_le_flucAvg` 把 `EntryBound` 的 `x` 实例化到新的 `condExpDiag`，之后 `hFA`/`hFA'` **字面上就是**对 `flucAvg` 的界（`flucAvg_eq_sum_sub` 是 `rfl`）。
**两条可测性都证了，不再是假设**：`measurable_green_apply`（经新证的 `measurable_matrix_inv_apply`：`A⁻¹ = Ring.inverse(det A) • adjugate A`）与 `measurable_condRow`（`StronglyMeasurable.integral_prod_right'` 沿联合可测的 `rowSplit`）——
**T87 的 `hZmeas`/`hYmeas`/`hrow` 全部卸掉**，T84/T86 标记的那两个浅缺口就此补上。
截断接缝在唯一无条件的方向上合拢：`flucBound_env` 由 `norm_green_zt_le` 给出真正逐点一致的 `B = 2(η_t⁻¹+1)`、`ε = 4η_t⁻¹`，故 T87 的矩界成为无条件定理，`stochDom_flucAvg_blockAvg_env` 是**无假设**的 ≺ 陈述（控制是常数，证明接口不空洞）。
两组系数的基数条件由模型自己的 `Dims.dim`/`bandwidth` 证出，故两条推论不带基数假设。

## ⚠⚠ (4.12) **尚未成为定理**：一个真实的数学缺口（T88 发现，2026-09-20，**需要 Jun 决定**）

不是记账问题，也不是截断问题。T87 给的是
`E|Σₖ tₖZₖ|^{2p} ≤ (2p−1)·ε·B^{2p−1} + c^p p^{2p} B^{2p}`；(4.12) 要 `≲ N^{δp}Ψ^{4p}`。
第二项没问题（`c = W⁻¹ ≤ Ψ²` 给出 `Ψ^{4p}`）。**第一项**即便取到理想参数 `ε ≍ Ψ²`（T85）、`B ≍ Ψ`，也只有 `Ψ^{2p+1}`——`p=1` 时是 `Ψ³`，而要的是 `Ψ⁴`。
**这正是 `docs/TASKS.md` 第六批开头记下的方差路线的那个亏空。**
根因：**T86 的小行替换只迭代到一阶**（`Z_{kᵢ} ↦ Z^{(k_{i₀})}_{kᵢ}` 换一次），标准证法要迭代到 `2p` 阶，残项才是 `Ψ^{4p}`。
**任何 ≺/指示函数记账都补不回来**：T86 的消失性依赖 `E_k[(1−E_k)X] = 0`，而 `1_Ω·X` 破坏它，且 `1_Ω` 不是 `FinDepOffRow`、无法从 `E_k` 里提出来。
缺口被隔离成单独一条假设 `hsmall`（(4.12) 的其余部分全部已证）。**要补的是一条新工单：把 `FlucVanish` 的机器迭代到 `2p` 阶。** 我不写工单，留给 Jun/Cowork 定。
另一条剩余假设是 `hIBP`（T83，堵在 Cowork 的 T70 矩阵版 Stein）。paper-deltas #60。

## HEAD 编译已恢复（2026-09-20）

上一节记的 `Gauss/RowIndep.lean` 编译失败已由对面修好；`lake build RBM1D` 绿，公理审计 6568 条声明全部合规。

**T81 第二十三、二十四块 ✔**：`integrable_norm_row_sum_pow`（冻结行和的偶数阶矩存在，
用两个实线性型的矩做控制）与 `lintegral_norm_row_sum_pow_le`（冻结界的 `∫⁻` 形式）。
**下一步**：用 `lintegral_indep_pair_le` 把它提升到随机系数，得到**无可积性假设**的
`∫⁻ ‖Z/√V‖^{2p} ≤ 2(2p−1)!!`，再由有限性反推可积性，替换掉第十六/十八块里的假设。

**T81 第二十五块 ✔（去掉假设）**：**`lintegral_norm_rowSum_norm_pow_le`**——
对**任意**可测、只读 off-row 块的系数 `C`，直接有 `∫⁻ ‖Z/√V‖^{2p} ≤ 2(2p−1)!!`，
**不带任何可积性假设**（Tonelli 只要可测与非负）。这替代了第十八块的带假设版本。
**T81 收尾**：由右端有限即得可积性与 Bochner 版 `∫ ‖Z/√V‖^{2p} ≤ 2(2p−1)!!`，
再取 `C := minorCol`（第十九块）并经 T73 的 `stochDom_of_momentDom` 得 `≺`。

**T81 第二十六、二十七块 ✔（全部假设消除）**：`integrable_norm_rowSum_norm_pow`（由 `∫⁻` 界的有限性
反推可积性）、`integral_norm_rowSum_norm_pow_le'`（Bochner 版，无边条件），以及
**`integral_norm_rowSum_minorCol_pow_le'`**——对 minor 预解式列的系数，
`E‖Z/√V‖^{2p} ≤ 2(2p−1)!!` **无任何假设**（只需 `0 ≤ u`）。
**T81 只剩**：把这条按 `MomentDom` 的量词次序（ε 在 p 外）组织，经 T73 的 `stochDom_of_momentDom`
落成 `≺`；`ldeRowLHS_eq`/`rowVarSum_eq`（第二十一块）负责与论文量对齐。

**T81 第二十八、二十九块 ✔（主目标达成）**：**`stochDom_rowSum_minorCol`**——
`|∑_{k≠i} H_ik G^(i)_kj| ≺ (∑_k S_ik|G^(i)_kj|²)^{1/2}`，对 `(i,j)` 一致，即工单要的
`LDERow` 的 `StochDom` 版本。并已一般化为 **`stochDom_rowSum_general`**（任意「只读 off-row 块」
的系数族 + 多项式大小的指标集），`minorCol` 版本是其实例。
**下一步**：列版本 `LDECol`——由 `H` 的 Hermitian 性，`∑_{l≠j} G^(j)_kl H_lj` 的共轭是
以 `conj G^(j)_{k·}` 为系数的**行和**（行 = `j`），故同样是 `stochDom_rowSum_general` 的实例。

**T81 完成 ✔**（`Gauss/RowIndep.lean`，30 块，零 sorry）：行 LDE `stochDom_rowSum_minorCol` 与
列 LDE `stochDom_rowSum_minorRowConj`，均为一般定理 `stochDom_rowSum_general` 的实例。
蓝图节点 `lem:lde-linear`，paper-deltas #61。

**维护/审计（Claude Code #2，T81 收尾后）**：`lake build RBM1D` 全量通过；
公理审计 **6583 条声明**全部只含 propext / Classical.choice / Quot.sound；
蓝图 **1502 个 `\lean{}` 名字**逐条 `#check` 全部解析（含新节点 `lem:lde-linear`）。

**T89 ✔（维护）**：`measurable_matrix_inv_apply` 原本在 `Gauss/FlucAvg.lean`（T88，涨落平均）与
`Gauss/RowIndep.lean`（T81，线性 LDE）各证了一遍——第二次重复造轮子（前一次见 T38）。
现下沉到 **`Defs/MatrixMeasurable.lean`**：矩阵形式 `measurable_matrix_inv_apply`（保留 T88 那份更短的证明，
用 `continuous_id.matrix_det` / `.matrix_adjugate`）+ 逐元素包装 `measurable_inv_entries`（T81 侧用）。
两边调用点签名不变。全量构建通过，公理审计 6581 条声明全部合规（比去重前少 2 条，正是删掉的副本）。
**教训重申**：写新引理前先 `grep -rn` 一下全库，尤其是「可测性 / 求和 / 范数」这类通用工具。

**T90 ✔（维护：全库重复扫描）**：写了个小脚本比对所有 `theorem/lemma` 的**陈述文本**（归一化空白后），
找出「不同文件里同一条陈述」。结果：

| 重复项 | 位置 | 处理 |
|---|---|---|
| `half_le_ellHat` | `Propagator/Edges.lean`、`Loop/Cor35.lean` | **已下沉**到 `Propagator/DecayComplex.lean`（两边都已 import，不新增依赖；全库名字 `RBM.half_le_ellHat` 不变，`L` 改为显式） |
| `ellHat_real_pos` / `ellHat_real_pos'` | `Hierarchy/KernelDecay.lean`、`Hierarchy/SumZeroDyn.lean` | 待 T51/T60 负责人合并 |
| `cKerShort_nonneg` | `Hierarchy/Decay.lean`、`Hierarchy/SumZeroDyn.lean` | 待 T59/T60 负责人合并 |
| `rpow_pow_eq` / `natCast_rpow_pow` | `Hierarchy/SumZeroDyn.lean`、`Hierarchy/Step2.lean` | 同一条 `((N^a)^k = N^(a·k))`，待合并（建议下沉到 `Defs/`） |
| `cor35Const_nonneg` | `Hierarchy/Decay.lean`、`Loop/WardKgen.lean` | 同名同义，待合并 |

（`treeRep_general` vs `K_eq_sum_Kpi` 是脚本的假阳性：前缀绑定相同、结论不同。）
全量构建通过，公理审计 6580 条声明全部合规。**这是第三次发现重复造轮子**（前两次 T38、T89），
建议新引理入库前固定动作：`grep -rn "陈述关键词" RBM1D/`。

**T91 ✔**（`Gauss/LDEHyp.lean`，新建，零 sorry）：把 T81 的 `≺` 落成 `RBM.entry_bound_stochDom`
**逐字要求**的两条假设：

```
stochDom_ldeRow : StochDom (P d) (ldeRowLHS (Hflow …) (green …)) (ldeRowRHS (Sblk …) (green …))
stochDom_ldeCol : StochDom (P d) (ldeColLHS (Hflow …) (green …)) (ldeColRHS (Sblk …) (green …))
```

指标是 `OffPair d.L d.W N`（`EntryBound` 用的那个），假设只有 `0 ≤ u ≤ 1` 与 `z.im ≠ 0`。
三处缺口各自补上：

1. **`G_ii ≠ 0` 现在是定理**（`RBM.green_diag_ne_zero`，一般 Hermitian 矩阵，无例外集）：
   由单点 Ward 恒等式 `RBM.im_green_diag`——`Im G_ii = Im z · ‖G e_i‖²`。证法是取 `v = G e_i`，
   则 `conj G_ii = ⟪v, (H−z)v⟫`，Hermitian 部分不贡献虚部；`v ≠ 0` 因为 `(H−z)v = e_i`，
   正性由 `dotProduct_star_self_pos_iff`（需 `open scoped ComplexOrder`）。
   这条以前在 `#40`/`#34` 里一直是携带的假设。
2. **`V = 0` 的退化分支**：`highProb_norm_rowSum_sq_le`（`Gauss/RowIndep.lean`，T91 第二块）
   把 `StochDom.highProb` 与 `rowSum_ae_eq_zero_of_varSum_eq_zero` 的 a.s. 论证交起来，
   得到对每个 `τ > 0` 的高概率不等式 `‖Z‖² ≤ N^{2τ}·V`（在 `V = 0` 处也成立）。
   辅助引理 `rowSum_rowCoeffNorm`：`V > 0` 时 `rowSum (rowCoeffNorm C) = (√V)⁻¹ · rowSum C`。
3. **因子 `u`**：条件方差是 `u · ldeRowRHS`（`ldeRowRHS` 按论文用 `S` 而非 `tS`），
   `u ≤ 1` 把它丢掉。通用桥 `stochDom_sq_of_rowSum` 一次写好，行/列两边都是它的实例
   （取 `τ/4`，再用 `N^{τ/2} ≤ N^τ` 造矛盾）。

列版本另需 `minorRowConj_eq_greenMinor`、`ldeColLHS_eq`、`rowVarSum_minorRowConj_eq`
（`conj(∑ G^{(j)}_{kl} H_{lj}) = ∑ H_{jl} conj G^{(j)}_{kl}`，用 `Hflow` 的 Hermitian 性与 `Sblk_comm`）。
顺手把 `#LdeIdx ≤ N²` 抽成 `eventually_card_LdeIdx_le`（原先在 `RowIndep.lean` 里抄了两遍）。

蓝图节点仍是 `lem:lde-linear`（证明段补了三处缺口的说明），paper-deltas **#62**。
全量 `lake build RBM1D` 通过，公理审计 **6605 条声明**全部合规。

**下一步（给接手的人）**：`entry_bound_stochDom` 的 `hLrow`/`hLcol` 已备齐，
`diag_bound_stochDom` 还差 `hLquad`（T82 的 `LDEQuad`，`Gauss/LDEQuad.lean`）与
`hLdiag`（`‖H_ii‖² ≺ S_ii`，尚无工单）——两者同样需要从矩界经 `stochDom_of_momentDom` 落成
`StochDom`，`stochDom_sq_of_rowSum` 的写法可以照抄。

**T92 ✔**（`Gauss/LDEDiag.lean`，新建，零 sorry）：`diag_bound_stochDom` 的最后一条**容易**假设

```
stochDom_normSq_Hflow_diag (hu0 : 0 ≤ u) :
  StochDom (P d) (fun N i ω => ‖Hflow d N u ω i i‖ ^ 2) (fun N i _ => Sblk (d.L N) (d.W N) i i)
```

关键观察：**对角元是实的**。Hermitian 矩阵对角无虚部，`Xentry` 在 `i = j` 那一支只读单个坐标
`ω ⟨N,i,i,tt⟩`，所以 `‖H_ii‖² = u·(ω c)²`，`E‖H_ii‖^{2p} = u^p·(2p−1)!!·S_ii^p`
（`integral_norm_Hflow_diag_pow`）。因子 `u^{2p}` 进 `MomentDom` 的常数 `C(ε,p)`，
故**不需要 `u ≤ 1`**（比论文弱的假设，paper-deltas #63）。
控制的严格正性由 `Sblk_diag_pos`（`S_ii = 1/(3W) > 0`）给出，union bound 跑 `LW ≤ N` 个格点
（`eventually_card_Idx_le`）。顺带两条通用小引理：`integral_pow_coord`、`integrable_pow_coord`
（单个坐标的矩与可积性，经 `P_map_eval` 推到 `gaussianReal`）。

蓝图新节点 `lem:lde-diag`。全量构建通过，公理审计 **6613 条声明**全部合规。

**`diag_bound_stochDom` 的四条假设现状**：`hLrow` ✔（T91）、`hLcol` ✔（T91）、`hLdiag` ✔（T92）、
**`hLquad` 仍缺**——T82 证到 `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`，还差 `E[T^p] ≤ C_p E[Vq^p]`
（`Gauss/LDEQuad.lean` 文件头有草图）。这是通往 (4.3) 的唯一剩余缺口。

**T93 进行中**（`Gauss/LDEQuadT.lean`，新建，**不碰 `Gauss/LDEQuad.lean`**）：补 T82 留下的唯一
数学缺口 `E[T^p] ≤ C_p E[Vq^p]`。

**第一块 ✔**：行方向的 Wirtinger 导子与它的分部积分恒等式。

```
wirtVal C l a b = r * (a − ε_l·i·b)          -- D_l = r(∂_{a_l} − ε_l i ∂_{b_l})
integral_conj_h_mul_gen : ∫ conj(h_l)·Z = w_l · ∫ D_l Z        （Z tame）
```

四个导子值（这是整条路线成立的原因——`T` 由 `U·Ū`、`V·V̄` 组成，求导后只剩 `B`）：

| | 值 |
|---|---|
| `D_l U_k` | `0` |
| `D_l V̄_k` | `0` |
| `D_l Ū_k` | `2r²·B̄_{kl}` |
| `D_l V_k` | `2r²·B_{lk}` |

代数上全由 `(ε_l·i)² = −1` 一条闭合（`linear_combination`）。
`integral_conj_h_mul_gen` 是 `GaussIBP.stein` 对行的两个坐标各用一次，
再配 `conj(h_l) = r(ω_{a_l} − ε_l i ω_{b_l})`；它是 `integral_chaos_mul` 的「单个行元」版本。

**下一步**：`E[T^p] = ∑_k σ_k E[(U_kŪ_k + V_kV̄_k)T^{p−1}]`，对每个 `h̄_l` 用上面的恒等式；
对角项恰好给出 `E[Vq·T^{p−1}]`，交叉项先在 `(k,m)` 后在 `k` 用两次 Cauchy–Schwarz
压成 `Vq·T`，最后用 `young_pow`（与 `mom_succ_le` 同一条）闭合。

蓝图新节点 `lem:lde-quad-T`（**故意不打 `\leanok`**：结论未证，依赖图上应当显示为缺口），
节点里记了路线与已落地的部分。全量构建通过，公理审计 **6624 条声明**全部合规。

**T93 ✔**（`Gauss/LDEQuadT.lean`，新建 ~1000 行，零 sorry，**全程没碰 `Gauss/LDEQuad.lean`**）：
T82 留下的唯一数学缺口补上了。

```
momTpow_le     : E[T^{q+1}] ≤ (4q+2)^{q+1} · E[Vq^{q+1}]
mom_le_momVpow : E|Q|^{2p}  ≤ ((2p−1)(4p−2))^p · E[Vq^p]        -- 配 T82 的 mom_succ_le
```

`Vq = ∑_{k,l}σ_k‖B_{kl}‖²σ_l` 就是论文的右端（差因子 `t²`，见 `Vq_eq_ldeQuadRHS` 与 #59），
所以 (4.7) 的二次 LDE 现在是**带显式常数的定理**，不再是引用结果。

**路线（无条件期望）**。教科书证法要对 `B` 取条件期望；这里改为对 `E[T^p]` 再跑一次同样的
行分部积分。关键是行方向的 Wirtinger 导子

```
D_l = r(∂_{a_l} − ε_l·i·∂_{b_l}),   D_lU_k = 0,  D_lV̄_k = 0,  D_lŪ_k = 2r²B̄_{kl},  D_lV_k = 2r²B_{lk}
```

`U` 与 `V̄` 都被 `D_l` 杀掉，所以 `T = ∑_kσ_k(U_kŪ_k + V_kV̄_k)` 求导后只剩 `B`。七块：

1. `integral_conj_h_mul_gen`：`∫ h̄_l·Z = w_l·∫ D_lZ`（`GaussIBP.stein` 对行的两个坐标各一次）；
2. `TA`/`TB` + `wirtVal_TA_TB`：`D_lT = 2r²∑_kσ_k(U_kB̄_{kl} + B_{lk}V̄_k)`；
3. `Tq_eq_sum_conj_h_mul`：`T = ∑_l h̄_l·W_l`，`W_l = ∑_kσ_k(B_{kl}Ū_k + V_kB̄_{lk})`
   —— `U_kŪ_k` 与 `V_kV̄_k` 各恰含一个 `h̄`，这是整条路线能走的原因；
4. `Zt = W_l·T^q`、`ZA`/`ZB`、`integral_Tq_pow_succ`：`E[T^{q+1}] = ∑_l w_l·E[D_lZ_{q,l}]`；
5. `sum_w_diag`：对角项 `= 2·Vq·T^q`（两个二重和交换指标后都等于 `Vq`）；
6. `norm_crossT_le`：交叉项 `≤ 4q·Vq·T^q`。两次 Cauchy–Schwarz——先在 `k`
   （`sq_Arow_le`，用 `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` 的加权版 `weighted_cauchy`），
   再对 `l` 配 `σ_l` 用 `sum_sg_mul_normSq`。关键观察：`‖W_l‖` 与 `‖D_lT‖/(2r²)`
   有**同一个**上界 `A_l = ∑_kσ_k(‖B_{kl}‖‖U_k‖ + ‖V_k‖‖B_{lk}‖)`，所以交叉项是 `σ_l·q·T^{q−1}·A_l²`；
7. `momTpow_succ_le` → `momTpow_le`：`E[T^{q+1}] ≤ (4q+2)E[VqT^q]`，再用 T82 的 `young_pow`
   （`K = 4q+2`）闭合，全程只有自然数次幂，不用 `rpow`、不用 Hölder。

蓝图节点 `lem:lde-quad-T` 现在带 `\leanok`（36 个 `\lean{}` 名字逐条 `#check` 通过），
paper-deltas **#64**。全量构建通过，公理审计 **6698 条声明**全部合规。

**`diag_bound_stochDom` 的四条假设**：`hLrow` ✔(T91)、`hLcol` ✔(T91)、`hLdiag` ✔(T92)、
`hLquad` —— 矩界已齐，**只差把矩翻成 `StochDom`**（`LDEQuad.lean` 文件头「What is not done
here」的第 2、3 条：为模型造一个 `RowChaos` 实例，再用 `StochDom.of_det`，因为 `ldeQuadRHS`
是随机控制）。这是下一张工单。

**T95 ✔**（`Gauss/LDEQuadInst.lean`，新建，零 sorry，**不碰 `Gauss/LDEQuad.lean`**）：
`LDEQuad.lean` 文件头「What is not done here」第 2 条（实例）做完了。

**我上一条 STATUS 里说的「全局有界性是结构性障碍」是错的，这里更正**：
`RowChaos.B` 确实要求**全局**有界连续，而 `greenMinor G i = G_kl − G_ki G_il / G_ii`
因 `G_ii` 无全局下界而无界（只有 `Im G_ii = Im z·‖Ge_i‖² > 0`）。但**换一边取就没事**：

```
B := minorRes = (H^{(i)} − z)⁻¹        -- 小方阵预解式，不是 greenMinor
```

* **全局有界 `|Im z|⁻¹`**：Hermitian 的子方阵还是 Hermitian，`norm_green_le` + `norm_apply_le_l2_opNorm`；
* **连续**：`continuous_green_of_isHermitian`（在本文件写的一般指标版；
  `Gauss/Hierarchy.lean` 的 `continuous_green_comp` 是它在 `d.Idx N` 上的特例，证明一字不差，
  **待合并**，归该文件负责人）；
* **只读 off-row 坐标**：`Hflow_submatrix_congr_offRowCoord`（T81 已有）。

而且两者**对每个 ω 相等**（`modelChaos_B_eq`）：`inv_minor_resolvent` 的两个边条件
（`H − z` 可逆、`G_ii ≠ 0`）在 `Im z ≠ 0` 时**无条件成立**——后者正是 T91 的
`green_diag_ne_zero`。所以这不是近似，是恒等。paper-deltas **#65**。

`co`/`eps` 直接用 T81 的 `rowCoord`/`rowSign`，`r = √u`，于是

```
modelChaos_h  : h_k = (H_u)_{ik}
modelChaos_sg : σ_k = u·S_{ik}
modelChaos_normSq_chaos : ‖Q‖² = ldeQuadLHS (Hflow) (green) (Sblk) u i
modelChaos_Vq           : Vq   = u²·ldeQuadRHS (Sblk) (green) i
integral_ldeQuadLHS_pow_le :
  E[(ldeQuadLHS)^p] ≤ ((2p−1)(4p−2))^p · u^{2p} · E[(ldeQuadRHS)^p]     （p ≥ 1，只要 0 ≤ u、Im z ≠ 0）
```

蓝图新节点 `lem:lde-quad-inst`。全量构建通过，公理审计 **6723 条声明**全部合规。

**下一步（`hLquad` 的最后一段）**：上面是矩不等式，而 `diag_bound_stochDom` 要的是
`StochDom P ldeQuadLHS ldeQuadRHS`，其控制 `ldeQuadRHS` 是**随机**的，
`stochDom_of_momentDom`（T73）只接受确定性控制。所以要走 `StochDom.of_det` 那条路
（`Green/EntryBound.lean` 里 `entry_bound_stochDom`/`diag_bound_stochDom` 本身就是这么用的），
或者先把 `ldeQuadRHS` 用好事件上的确定性控制夹住。这是下一张工单。

**T96 ✔**（`Gauss/LDEQuadDom.lean`，新建，零 sorry）：`diag_bound_stochDom` 的第四条假设
`hLquad` 落地。

```
stochDom_ldeQuad (hG : GaussIBP d) (hz : z.im ≠ 0) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
  StochDom (P d)
    (fun N i ω => ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) z) (Sblk (d.L N) (d.W N)) u i)
    (fun N i ω => ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i)
```

取 `z := zt E t`、`u := t` 就是 `diag_bound_stochDom` 的 `hLquad` 逐字形状。

**难点与解法**。T95 的矩不等式的控制 `ldeQuadRHS` 是**随机的**，`stochDom_of_momentDom`（T73）
只吃确定性控制；而 Markov 也不能直接用，因为阈值 `N^τ·ζ(ω)` 随 ω 变。解法是**归一化**：

1. 把矩阵整体除以 `(Vq + ε)^{1/2}`（`modelChaosEps`）。这个因子**与 (k,l) 无关**，所以
   混沌也被同样地除；它只读 off-row 坐标，所以 `B_free` 保住；而且它让矩阵**仍然全局有界**
   （`Bbd/√ε`）——这正是 `RowChaos` 要的。归一化后控制 `Vq/(Vq+ε) ≤ 1`，于是
   `E[(|Q|²/(Vq+ε))^p] ≤ A_p`，**常数与 ε 无关**（`mom_modelChaosEps_le`）；
2. 此时 Markov 的阈值是确定性的（`meas_lt_normSq_chaos_le_eps`）；
3. 去掉 ε 不用任何积分极限定理：
   `{|Q|² > λVq} = ⋃_n {|Q|² > λ(Vq + 1/(n+1))}` 是**递增并**，测度的下连续性直接给出
   `P{λVq < |Q|²} ≤ A_p/λ^p`（`meas_lt_normSq_chaos_le`）。**`{Vq = 0}` 不需要单独处理**
   ——它自动落在并集的补里（这比 T91 那边的 a.s. 论证省事）；
4. 最后 `StochDom.of_forall_le` 的 union bound（`LW ≤ N` 个格点）+ 取 `p` 大。
   `u = 0` 单独一支：那时 `h = 0`、`σ = 0`，混沌恒为 0（`chaos_modelChaos_zero`），坏事件是空集。

蓝图新节点 `lem:lde-quad-dom`。全量构建通过，公理审计 **6769 条声明**全部合规。

**`diag_bound_stochDom` 的四条假设现在全部落地**：

| | |
|---|---|
| `hLrow` | ✔ T91 `stochDom_ldeRow` |
| `hLcol` | ✔ T91 `stochDom_ldeCol` |
| `hLdiag` | ✔ T92 `stochDom_normSq_Hflow_diag` |
| `hLquad` | ✔ T96 `stochDom_ldeQuad` |

`entry_bound_stochDom`（(4.2)）的两条也齐了（T91）。**下一步**：把这四条喂进
`Green/EntryBound.lean` 的 `entry_bound_stochDom` / `diag_bound_stochDom`，得到 (4.2)(4.3)
对高斯模型的无假设版本——那是个纯粹的对接工单（需要核对 `zt E t` 的 `im ≠ 0`、
`0 ≤ t < 1` 与各处 `Sblk` 参数一致），**不碰 `Green/EntryBound.lean` 本身**，新开文件即可。

**T97 ✔**（`Gauss/EntryBoundGauss.lean`，新建，零 sorry，不碰 `Green/EntryBound.lean`）：
**Lemma 4.1 的 (4.2)(4.3) 对高斯流成立，不带任何大偏差假设。**

```
entry_bound_gauss (0 ≤ u) (u ≤ 1) (z.im ≠ 0) (‖m‖ = 1) (δ …) : StochDom (P d) …   -- (4.2)
diag_bound_gauss  (hG : GaussIBP d) (0 < κ ≤ 1) (|E| ≤ 2−κ) (0 ≤ t < 1) (δ …) : StochDom (P d) …  -- (4.3)
```

这是两半项目（确定性的 `Green/EntryBound.lean` 与随机层的 `Gauss/*`）**第一次合上**。
论文里四条 `[39, Lemma 3.3]` 的引用，现在都是定理：

| `EntryBound` 的假设 | 由谁卸掉 |
|---|---|
| `hLrow` | T91 `stochDom_ldeRow` |
| `hLcol` | T91 `stochDom_ldeCol` |
| `hLdiag` | T92 `stochDom_normSq_Hflow_diag` |
| `hLquad` | T96 `stochDom_ldeQuad` |

`(zt E t).im ≠ 0` 由 `zt_im_ne_zero`（`|E| ≤ 2−κ`、`t < 1`）给出。本文件一次编译通过，
没有新数学，纯对接。蓝图新节点 `lem:4.1-gauss`。全量构建通过，公理审计 **6771 条声明**全部合规。

**仍未卸的**：(4.5)（`norm_sq_green_diag_sub_le_blk` 那条）还带 `hFA`/`hIBP`
——`hFA` 已由 T88 卸掉，但 T88 的 STATUS 记了 (4.12) 本身有真实数学缺口
（T86 只迭代一阶，T94 正在做）。所以 (4.5) 的高斯版要等 T94。

**T98 ✔（维护 + 审计）**

1. **`docs/mathlib-api.md`** 新增一节「第二轮随机层（T91–T97）核实过的名字」，26 条。
   几个会绊人的：
   * `dotProduct_star_self_pos_iff` 在 ℂ 上要先 **`open scoped ComplexOrder`**，
     否则 `PartialOrder ℂ` / `StarOrderedRing ℂ` 合成不出来；
   * `hasFDerivAt_ringInverse` 与 `norm_apply_le_l2_opNorm` 在 `Matrix n n ℂ` 上要
     **`open scoped Matrix.Norms.L2Operator`**，否则 `NormedRing` 的实例路径对不上（报
     「`Semiring.toMonoid semiring` vs `NormedRing.toRing.toSemiring`」）；
   * **`Matrix.smul_mulVec`**，不是 `smul_mulVec_assoc`（后者不存在）；
   * **`HasDerivAt.fun_pow`**，不是 `.pow`（后者给 `Pi.pow`，`simp` 化不开）；
   * `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` 是 Cauchy–Schwarz 的**带权**形式
     （取 `r = σxy`、`f = σx²`、`g = σy²`）；无权版是 `sum_mul_sq_le_sq_mul_sq`。
   另记了三条方法论教训（全局有界字段的绕法、随机控制的归一化、`linear_combination` 系数
   按 `ring` 残项反推）。

2. **全库重复扫描**（T90 之后新增约 250 条声明）。**自己的文件里没有新重复**。
   新发现两处，归各自负责人：

| 重复项 | 位置 | 说明 |
|---|---|---|
| `mE_mul_smul_add_zt` / `mE_mul_add_zt` | `Gauss/IBP.lean`、`Green/EntryBound.lean` | 同一条 `m(E)·(t·m(E) + z_t) = −1` |
| `xiOf_mSigma_true_false` / `sigPM_xi` | `Hierarchy/KernelDecay.lean`、`Hierarchy/Step2.lean` | 同一条 `ξ` 的取值 |

   T90 列的四处（`ellHat_real_pos`、`cKerShort_nonneg`、`rpow_pow_eq`/`natCast_rpow_pow`、
   `cor35Const_nonneg`）**仍未合并**。另外 T95 记的
   `continuous_green_comp`（`Gauss/Hierarchy.lean`）是我 `continuous_green_of_isHermitian`
   的 `d.Idx N` 特例，证明一字不差，也待合并。

3. **审计**：`lake build RBM1D` 全量通过；公理审计 **6771 条声明**全部只含
   propext / Classical.choice / Quot.sound（故无 `sorryAx`）；全库 `grep sorry` 只剩两处
   **文档里的散文**（`Gauss/LDEQuad.lean:67`、`Gauss/FlucAvg.lean:79`），无真 `sorry`；
   蓝图 **1589 个 `\lean{}` 名字**逐条 `#check` 全部解析。

**T99 ✔（审计）：从 T97 的 (4.2)(4.3) 到 `Hierarchy/Step1.lean` 的 `Lemma41Flow`，还差什么**

`Lemma41Flow X E s t` 的形状是**界传递**：

```
(∀ Φ 确定性 ≥ 0)  1_{Ω_u}‖L_{u,(+,-),(a,b)}‖ ≺ Φ_u  ⟹  1_{Ω_u}(llMax_u)² ≺ Φ_u + W⁻¹
```
指标集是 `TimeIcc s t N × (ZMod L × ZMod L)`，即**对 `u ∈ [s_N, t_N]` 一致**。

逐条核对，缺口恰好三块（前两块机械，第三块是真障碍）：

**(A) 接口对齐（机械）。** 三处都对得上，但都要写出来：
* `X.Lval E N u ω (pmLoop a b) = gloop … ⟨[true,false],[a,b]⟩`，而
  `Lre H z a b = (gloop … ⟨[true,false],[a,b]⟩).re`；由 `Lre_eq`（`= W⁻²∑|G|²`，实且非负）
  可得 `‖Lval (pmLoop a b)‖ = Lre`（H Hermitian 时）。
* `goodEv X E N u = {llMax_u ≤ (Wℓη)^{-1/6}}` 与 `goodSet H z m δ N = {GoodEvent (green …) m (δ N)}`
  ——`GoodEvent G m δ = ∀ x y, ‖G x y − (x=y ? m : 0)‖ ≤ δ`，`llErr` 正是这个量，
  所以两者在 `δ N := (B.scale E N u)⁻¹^{1/6}` 下相同。**注意 `entry_bound_stochDom` 的 `δ` 只依赖 N，
  而 `goodEv` 的阈值还依赖 `u`** ——固定 `u` 时无碍，时间一致时要留意。
* `llMax` 是对 `Idx × Idx` 的 `iSup`；T97 给的是逐 `(i,j)` 的界。合成 `llMax²` 需要
  「多项式多个 `≺` 取 sup 仍 `≺`」——`StochDom.of_forall_le` 的标准用法。

**(B) 控制的形状（机械）。** T97 的控制是**随机**的（`∑∑Lre`、`Lmax`），
`Lemma41Flow` 要的是传递到**确定性** `Φ`。这正是它的假设 `1_Ω‖L‖ ≺ Φ` 的用处，
配 `StochDom.trans`（再加指标集上的求和/取 max）即可，只是指示函数的簿记要小心。

**(C) 时间一致性 —— 真障碍。** T97 是**固定 `u`、固定 `z`** 的。桥梁是
`stochDom_timeIcc_of_holder`（T75），它要求一个**逐 ω 一致**的 Hölder 模
`|Y_N(u,ω) − Y_N(u',ω)| ≤ N^K|u−u'|^γ`。而由预解式恒等式

```
‖G_u − G_{u'}‖ ≤ ‖G_u‖·‖H_u − H_{u'}‖·‖G_{u'}‖ ≤ η⁻²·|√u − √u'|·‖X‖
```
（`Gauss/Model.lean` 的 `norm_Hflow_sub` 已给出中间那一步），**Hölder 常数含 `‖X‖`，
而 `‖X‖` 逐 ω 无界** ——`‖X‖ ≺ 1` 正是 paper-deltas #49 里那个尚未证明的
`OpNormBound` 字段。所以 (C) 分成两张独立工单：

* 证 `‖X‖ ≺ 1`（矩/迹方法），卸掉 `OpNormBound`；
* 做一个 `stochDom_timeIcc_of_holder` 的变体，允许 Hölder 模只在**高概率事件**上成立
  （或常数本身被 `≺` 控制）。

据此新开三张工单（见 `docs/TASKS.md` T100/T101/T102），**T102（接口对齐 + 界传递）不依赖
(C)，可以立刻开工**；T100、T101 互相独立，合起来才解锁 `Lemma41Flow`。

**T102 进行中**（`Gauss/Lemma41Glue.lean`，新建，不碰 `Hierarchy/Step1.lean`、`Green/EntryBound.lean`）

**第一块 ✔（词典）**：两套语言对得上，逐条写出来了。

```
norm_gloop_pm_eq_Lre : ‖gloop L W H z ⟨[tt,ff],[a,b]⟩‖ = Lre H z a b      （H Hermitian）
Sample.llErr_eq      : llErr = ‖G i j − (i=j ? m(E) : 0)‖                  （= GoodEvent 的逐元素量）
Step1.goodEv_eq_setOf_goodEvent : goodEv X E N u = {ω | GoodEvent (G_u) m(E) (Wℓη)^{-1/6}}
Gauss.sample_Lval_pm, Gauss.goodEv_eq_goodSet                              （高斯实例，固定时刻）
```

`‖gloop‖ = Lre` 靠 `gloop_two_plus_minus_blocks`：这个 2-loop 的值是
`((W⁻²∑∑‖G‖² : ℝ) : ℂ)`，**实且非负**，所以范数就是实部。

**第二块 ✔（指示函数的传递）**：`entry_bound_stochDom`/`diag_bound_stochDom` 给的是
`1_Ω ξ ≺ ζ`，**控制 ζ 上没有指示函数**；而 `Lemma41Flow` 提供的是 `1_Ω ζ ≺ χ`。
两者仍可串联——**坏事件上左端为正，故 ω ∈ Ω，指示函数是白送的**：

```
StochDom.trans_indicator :
  1_A f ≺ g  →  1_A g ≺ h  →  (0 ≤ h)  →  1_A f ≺ h
```

证法是 `StochDom.of_subset_union`（两次 `τ/2`）。这条是通用的，将来可以下沉到
`Defs/StochDom.lean`（共享文件，先放在本文件里）。

**下一步（第三块）**：固定时刻的 `Lemma41Flow`——把 `entry_bound_gauss`（`i ≠ j`）与
`diag_bound_gauss`（`i = j`）的结论用 `llMax² = (⨆ llErr)²` 合成，控制经 `trans_indicator`
传到 `Φ + W⁻¹`。需要的额外输入：`δ_N = (Wℓη)^{-1/6} ≤ N^{-c₀}`（即对 scale 的多项式下界，
Step1 那边是 `Cond272` + `hreg`）。**时间一致性（T99 的 (C)）仍不在本工单范围内。**

（过程教训：这轮有一次 `lake build … | tail && git commit` 在**构建失败**时仍然提交了
——管道的退出码是 `tail` 的。单文件 `lake env lean` 通过**不等于**全量通过：
跨文件重名只有根文件 import 全部时才暴露，这次就是 `RBM.Gauss.sample_G` 与
`Gauss/Hierarchy.lean` 撞名。已 push 修复。）

### `RBM1D/Gauss/FlucIter.lean` — (4.12) 的 `2p` 阶迭代（T94，Claude Code 并行 agent）

**关键结论：`hsmall` 不可能被卸掉，因为它按字面是假的。** 它是关于 T87 那个界的**算术**陈述：
`(2p−1)ε_N B_N^{2p−1} + c_N^p p^{2p} B_N^{2p} ≤ C N^{εp} Φ_N^{2p}`；在目标 `Φ = Ψ²` 下，第一项 `Ψ^{2p+1}` 对目标 `Ψ^{4p}`，p=1 即 `Ψ³` vs `Ψ⁴`——**对任何预期尺度的参数都不成立**。
所以要换掉的是 **T87 的界本身**，而不是补一条假设。agent 在新文件里另起一条无 `hsmall` 的路线到 (4.12)/(4.5)，
**`FlucCount.lean`、`FlucAvg.lean`、`Green/EntryBound.lean` 一字未动**（工单硬性要求）。

**迭代怎么做的**：对「还剩几个 pivot」归纳（`norm_integral_prod_applyOps_le`）；状态是每个 slot 一个字 `List (Bool × Idx)`（`applyOps` 施加，head 最外层）。
「某指标仍只出现一次」由两处追踪：pivot 假设（T86 的 `hone`，现在对**一整个** pivot 集合）与不变量 `OpsOkOut`（字里的行两两不同、来自 `R` 之外的 slot、且异于本 slot 的行）。
单步：`Finset.prod_add` 在非 pivot slot 展开 `1 = Q + P`，全 `P` 项由 T86 的 `integral_mul_prod_eq_zero` 杀掉，其余每项多一个 `Q`。
**使这一切成立的新事实**：**`condRow_condRow_comm`——`E_k` 与 `E_κ` 对任意两行都交换**（无论是否共享 `H_{kκ}`）。
证法是把 `rowSplit` 推广成对任意坐标谓词的 `predSplit`，证 `measurePreserving_predSplit` 与 `predSplit_predSplit`，得 `condPred_condPred : E_q ∘ E_p = E_{p∪q}`。没有这条，pivot 因子最里层的 `Q_k` 活不过不断变长的字。
**残项求和**：单个 pivot 花 `(2M)^{n−1}` 买一个 `ρ`；满深度后 `ρ^{#lone}·B^n`。再由**计数** `two_mul_card_image_le_add_card_loneSlots`（`2·#image v ≤ n + #lone v`，T87 那条的加细）与 `sum_weighted_le`：
有 `a` 个 lone slot 的多重指标至多 `(n+a)/2` 个不同值，在 `c ≤ ρ²` 下其层权重 `≤ n^n ρ^{n−a}`，配上迭代买到的 `ρ^a`，**每一层都给出 `ρ^n`**。
结论 `integral_norm_flucAvg_pow_le_iter` ⟹ `stochDom_flucAvg_iter`：`≺ ρB`，在 `ρ, B ≍ Ψ` 时就是 **(4.12)**。

**当前状态**：(4.12) 除一条具名接口 `FlucGain` 外无假设；**(4.5) 还差 `hIBP`（T83，堵在 T70）与确定性控制 `ρB` 与论文随机控制 `Lmax` 的比较**（那是局部律，不属涨落平均）。
`FlucGain`（高阶小行展开：再作用 `m` 个 `Q_{κ_i}` 得 `ρ^m`）已证 `m = 0` 与 **`m = 1`**（`norm_qRow_flucDiag_le`：`Q_κ` 湮灭 `Z^{(κ)}_k`，后者与 `Z_k` 相差 T85 的 `ε`，故 `‖Q_κ Z_k‖ ≤ 2ε ≍ Ψ²`）；
**`m ≥ 2` 需要迭代小行 `G^{(κ₁κ₂)}` 及其 `≺ Ψ^{m+1}` 估计，仓库里还没有**。`flucGain_env` 是无条件的（无增益，`ρ = 2`）实例，故接口不空洞。paper-deltas #95。

**T102 ✔**（`Gauss/Lemma41Glue.lean`，零 sorry，不碰 `Hierarchy/Step1.lean`、`Green/EntryBound.lean`）：
**固定时刻的 `Lemma41Flow` 成立。**

```
stochDom_indicator_llMax_sq (hG) (0<κ≤1) (|E|≤2−κ) (0≤u<1) (δ 的两条) (0≤Φ) (LoopHyp d E u Φ) :
  StochDom (P d) (fun N _ ω => 1_{Ω_u} (llMax_u ω)²) (fun N _ _ => Φ N + W⁻¹)
```

即 `Lemma41Flow` **去掉时间量词**后的形状。T99 审计的 (A)(B) 两块全部做完：

| 块 | 结果 |
|---|---|
| 词典 | `norm_gloop_pm_eq_Lre`、`Sample.llErr_eq`、`Step1.goodEv_eq_setOf_goodEvent`、`Gauss.sample_Lval_pm`、`Gauss.goodEv_eq_goodSet` |
| 指示函数传递 | `StochDom.trans_indicator`（坏事件上左端为正 ⟹ ω ∈ Ω，控制上的指示函数白送）、`StochDom.control_mono` |
| 控制传递 | `stochDom_indicator_Lmax`（`sup'` 可达）、`card_sbSupport_le` + `sum_sum_Lre_le`（≤ 9·L^max）、`stochDom_indicator_entryControl` |
| 合成 | `stochDom_indicator_offdiag`（(4.2)）、`stochDom_indicator_diag`（(4.3)）、`stochDom_indicator_llMax_sq`（`llMax² > c` ⟹ 某个 `llErr > √c`，按 `i = j` 与否分到两边） |

两处小心得：
* `StochDom.of_subset` 要求**结论与前提的指标类型相同**；指标类型不同时用 `of_subset_union h h`
  （代价是 `D+1`，无所谓）。
* `Lmax` 是 `Finset.sup'`，用 `Finset.exists_mem_eq_sup'` 取到达点，就能把
  「`1_Ω L^max ≺ Φ`」归约到假设里逐对的 `1_Ω L^re_{ab} ≺ Φ`。

蓝图新节点 `lem:4.1-fixedtime`。全量构建通过，公理审计 **6937 条声明**全部合规。

**剩下的就只有时间一致性（T99 的 (C)）**：`Lemma41Flow` 的指标集是
`TimeIcc s t N × (ZMod L × ZMod L)`，要对 `u` 一致。缺口是 T100（`‖X‖ ≺ 1`）
与 T101（Hölder 模只在高概率事件上成立的 `stochDom_timeIcc_of_holder` 变体），两张都还空闲。

**T103 ✔（审计）：全库仍被携带的假设清点**

把「被假设、没被证」的东西分三类。定义性的 `Prop`（`GoodEvent`、`Crossing`、`FinDep`…）
不算，只算**接口假设**。

**(1) 已经卸掉（现在是定理）**

| 曾经的假设 | 由谁卸掉 |
|---|---|
| `MatrixStein` | `RBM.Gauss.matrixStein`（T70） |
| `EntryBound` 的 `hLrow`/`hLcol` | T91 |
| `EntryBound` 的 `hLdiag` | T92 |
| `EntryBound` 的 `hLquad` | T96 |
| `EntryBound` 的 `hFA`（签名层面） | T88（(4.12) 本身的缺口由 T94 在补） |
| `WardP` | `wardP_holds`（T60） |

**(2) 可卸、但没人在做 —— 只有一条，已开 T104**

`GaussIBP`（`Gauss/LDEQuad.lean` 的两个字段）。理由：

* `stein` 现在写成「`Tame`（多项式增长）」版本，而已证的 `matrixStein` 要求**全局有界**。
  但一维的 `RBM.integral_mul_gaussianReal`（`Gauss/Stein.lean:94`）**本来就只要三条可积性**，
  不要有界性——`SteinMatrix.matrixStein` 用的是它的有界特例
  `integral_mul_gaussianReal_of_bdd`。所以把同一条逐坐标 Fubini 论证换成
  「多项式增长 ⟹ 可积」即可，**不需要文件头设想的光滑截断**；
* `polyInt`（`P d` 的一切多项式矩有限）是初等高斯矩，`Gauss/LDEDiag.lean` 的
  `integrable_pow_coord` 已经是单坐标版本。

**这条一卸，T93/T95/T96/T97 整条链就没有任何携带假设了**
（`mom_le_momVpow`、`stochDom_ldeQuad`、`entry_bound_gauss`、`diag_bound_gauss`、
`stochDom_indicator_llMax_sq` 现在都带 `hG : GaussIBP d`）。

**(3) 真缺口，缺什么写明**

| 假设 | 缺什么 |
|---|---|
| `OpNormBound`（`‖X‖ ≺ 1`） | 迹/矩方法。T100 进行中 |
| `Lemma41Flow` | 只差**时间一致性**（T99 的 (C)）；固定时刻版已由 T102 证出。需 T100 + T101 |
| `LoopIto.second` / `EG` | cut-and-glue 的确定性代数，paper-deltas #52；矩路线里无法从 Itô 推出 |
| `Transfer.green` / `loop2` / `loop2_expect`（(2.39)(2.66)） | 需要 `H_u = √u X` 与论文 `H(z)` 的分布恒等，而 #49 明确不编码方差剖面，**结构性不可卸** |
| `Thm221.step`、`Steps.*`、`Lemma510`、`LKDecay`、`StepTwoClaim`、`Eq747`、`LoopScaling`、`NetLift`、`DBMUniversality`、`GreenComparison` | 论文 §5/§7 的主体，按工单表推进中 |

结论：**随机层这边可卸而未卸的只剩 `GaussIBP` 一条**（T104）；其余要么在做，要么是论文层面的主体工作，要么（`Transfer`）按矩路线的设计就卸不掉。

### `RBM1D/Gauss/DominationHolder.lean` — 高概率 Hölder 模的时间网（T101，Claude Code 并行 agent）

两种放宽都做了，且第二种由第一种**推出**：
**(a) 高概率形式** `stochDom_timeIcc_of_holder_hp`：`HighProb P Ξ` + `∀ᶠ N, ∀ ω ∈ Ξ N, …`（两处独立放宽：例外集与「终于」）。核心是 `stochDom_of_subset_highProb`（`badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ`，`RBM.StochDom.of_subset` 的高概率类比，且不需 `[IsFiniteMeasure P]`）。
**(b) `≺` 控制的常数** `stochDom_timeIcc_of_holder_dom`：`hR` 的类型**就是** `RBM.Gauss.OpNormBound.norm_X` 的类型——**T100 的 `‖X‖ ≺ 1` 可以零胶水插入**（取 `R N ω := ‖Xmat d N ω‖`）。归约：`{ω | R N ω ≤ N}` 是高概率事件，其上模是确定性的 `N^{K+1}|u−u'|^γ`。
**推广程度**：主定理严格强于两个前身——N-依赖区间 `[s_N,t_N]`（T75 的一般性，且 `T = 1` 放宽为任意 `T > 0`）**加** T73 的确定性控制 `Φ`（T75 只有 `Φ ≡ 1`）。T73 = `s ≡ 0, t ≡ T`；T75 = `Φ ≡ 1, T = 1`。
agent 在 scratch 里验证过：以 `Ξ ≡ univ` 可逐字复原 T73 的 `stochDom_Icc_of_holder`；`γ = 1/2`、`R = ‖X‖` 的实例对 `stochDom_timeIcc_one_of_holder_dom` 类型检查通过。

**可以据此卸掉逐点假设的下游**：`Step2Moment.MomentHyp.holder`（进而 `jS_stochDom`/(5.47)）；**T99 审计的阻塞项 (C)**（`Lemma41Flow` 的时间一致性那半）——预解式的模 `‖G_u − G_{u'}‖ ≤ η^{-2}|√u−√u'|·‖X‖` 正是形式 (b)（`γ = 1/2`，经 `abs_sqrt_sub_sqrt_le`），**余下的输入只剩 T100 的 `‖X‖ ≺ 1`**。
**注意重复**：因 `Gauss/` 不能 import `Hierarchy/`（Step2Moment 反向依赖 `Gauss.Envelope`），`netTime`/`netTime_mem`/`exists_netTime_close` 在此重证了一份（命名空间 `RBM.Gauss`，与 T75 的 `RBM.Step2Moment` 不冲突）。
**下次编辑 `Hierarchy/Step2Moment.lean` 时应删掉它那三条，改用这里的**；本单按协议未改动该文件。`…_one_of_holder_hp`/`…_one_of_holder_dom` 除模假设外与 T75 签名一致，是直接的替换件。paper-deltas #96。

**T104 ✔**（`Gauss/IBPPoly.lean`，新建，零 sorry）：**`GaussIBP` 卸掉了。**

```
gaussIBP (d : Dims) : GaussIBP d
```

T103 审计里说的「不需要光滑截断」是对的：`Gauss/LDEQuad.lean` 的文件头设想用
`χ_n(ω) = η(∑(ω c)²/n²)` 从有界版逼近，但**一维的 `RBM.integral_mul_gaussianReal`
（`Gauss/Stein.lean:94`）本来就只要三条可积性**，`SteinMatrix.matrixStein` 用的是它的有界特例
`integral_mul_gaussianReal_of_bdd`。所以把 `matrixStein` 的同一条逐坐标论证
（`P_map_update` 重采样 + Fubini）里的「全局有界」换成「多项式增长 ⟹ 可积」就行。三块：

1. **`polyInt`**（`integrable_polyW_pow`）：对坐标有限集归纳，`(a+b)^n ≤ 2^n(a^n+b^n)`
   （`add_pow_le_two_pow_mul`）+ 单坐标矩 `integrable_abs_pow_coord`（T92 的
   `integrable_pow_coord` 加绝对值）。
2. **一维 Stein 的可积性版**：`integral_mul_gaussianReal_int`（实）与
   `integral_mul_gaussianReal_complex_int`（复，且**不限制方差**，`var = 0` 时两端都为 0）。
   假设写成「对高斯**测度**可积」而不是「对**密度**可积」——后者是
   `Gauss/Stein.lean` 的原形状，转换用我在 T81 写的 `integrable_mul_gaussianPDFReal`。
3. **纤维化**：`polyW_upd_le`（换一个坐标最多把权重加 `|t|`）+ `norm_le_of_tame_upd`
   给出乘积测度上的控制 `C·2^n(polyW(p.1)^n + |p.2|^n)`，用 `Integrable.mul_prod` /
   `comp_fst` / `comp_snd` 拼出可积性，再用 `Integrable.prod_right_ae` 把可积性下放到纤维，
   `filter_upwards` 三条 a.e. 后逐纤维用第 2 块。

**后果**：`hG : GaussIBP d` 现在**处处可以直接填 `gaussIBP d`**。于是

```
mom_le_momVpow → stochDom_ldeQuad → diag_bound_gauss → stochDom_indicator_llMax_sq
```

整条链（T93/T95/T96/T97/T102）**没有任何携带假设**。签名我没动（保持接口稳定、避免和另一边
撞文件）；要无假设版本的，调用处写 `(gaussIBP d)` 即可。若要把 `hG` 从我这几个文件的签名里
删掉，可另开一张小工单。

蓝图新节点 `lem:gauss-ibp`。全量构建通过，公理审计 **6964 条声明**全部合规。

**T103 的「可卸未卸」清单现在是空的。**

**T105 ✔（维护）**：`hG : GaussIBP d` 已从**应用层四个文件**的签名里删掉：
`LDEQuadInst.lean`、`LDEQuadDom.lean`、`EntryBoundGauss.lean`、`Lemma41Glue.lean`。
于是下面这些现在**一个假设都不带**（除了模型本身的 `0 ≤ u`、`Im z ≠ 0` 之类）：

```
integral_ldeQuadLHS_pow_le, stochDom_ldeQuad, entry_bound_gauss, diag_bound_gauss,
stochDom_indicator_diag, stochDom_indicator_llMax_sq
```

**`Gauss/LDEQuadT.lean` 里的 `hG` 故意保留**：那一层是抽象 `RowChaos` 的机器，
`GaussIBP` 在那里正是被使用的接口，与 `Gauss/LDEQuad.lean`（别人的文件）的写法一致；
应用层调用时填 `(gaussIBP d)`。`Gauss/LDEQuad.lean` **一字未动**。

全量构建通过，公理审计 6964 条声明全部合规。

**T106 进行中**（`Gauss/FlowHolder.lean`，新建）：`u` 方向的 Hölder 模，**纯确定性**，
**不依赖 T100**（`‖X‖ ≺ 1` 只在把这里产出的常数喂给时间网时才用到）。

**第一块 ✔**：预解式恒等式，**矩阵与谱参数同时动**的版本。

```
green_sub_eq      : G_u − G_u' = G_u · ((H_u' − z_u') − (H_u − z_u)) · G_u'
norm_green_sub_le : ‖G_u − G_u'‖ ≤ ‖G_u‖ · (‖H_u − H_u'‖ + ‖z_u − z_u'‖) · ‖G_u'‖
```

（`Nonempty n` 是为了 `‖1‖ = 1`。）

**下一步**：代入 `‖G‖ ≤ η⁻¹`（`norm_green_le`）、`‖H_u − H_u'‖ = |√u−√u'|·‖X‖`
（`Gauss/Model.lean` 的 `norm_Hflow_sub`）、`|√u−√u'| ≤ |u−u'|^{1/2}`、
`|z_u − z_u'| = |η_u − η_u'| = |u−u'|·Im m(E)`（`etaT_eq`），得到

```
‖G_u − G_u'‖ ≤ η_t⁻² (‖X‖ + 1) · |u − u'|^{1/2}        （u, u' ∈ [0, t]）
```

再逐元素传到 `llErr`（`llMax` 的差 ≤ 算子范数差）与 `llMax²`
（`|a²−b²| = (a+b)|a−b|`，`llMax ≤ η⁻¹ + 1`）。配 T101 的 `≺`-常数版与 T100 即可关掉
`Lemma41Flow`。

### `RBM1D/Gauss/OpNorm.lean` — `‖X‖ ≺ 1` 的迹/矩路线（T100，Claude Code 并行 agent）

**缺口收窄，未完全合拢**：整条概率链已证，剩下的**恰好是走计数组合**，隔离成一条具名假设
`TraceMomentBound d : ∀ p, ∃ C > 0, ∀ᶠ N, E Tr(X^{2p}) ≤ C·N`（经 `trace_pow_eq_frobSq` 确认它真的是 `E Tr(X^{2p})` 而非更弱的东西）。
填 `OpNormBound` 的项是 **`opNormBound_of_traceMomentBound`**，其字段 `stochDom_norm_Xmat` 的类型**逐字**是 `OpNormBound.norm_X`，故 `Model.lean` 无需改动。
`p = 1` 已无条件证出（`traceMomentBound_one`，由 `∑_j S_ij = 1` 得 `E Tr(X²) = WL ≤ N`，常数 1）——**带状结构目前只在这里用到**。

**两处值得记的技术选择**：
1. **`‖A‖^{2q} ≤ Tr(A^{2q})` 绕开了谱定理**（Mathlib 没有「Hermitian 的算子范数 = 最大特征值绝对值」）：迭代 C\*-恒等式 `l2_opNorm_conjTranspose_mul_self` 得 `‖A^q‖ = ‖A‖^q`，**只对 `q = 2^m`** 成立，再配 op ≤ Frobenius。不构成限制——下游的 `q` 可以自由选。
2. **与 T73 的量词序不匹配，已桥接**：`MomentDom` 要 `ε` 在 `p` 外，迹方法给的是 `E‖X‖^{2p} ≤ C_p·N`，而 `εp < 1` 时 `N ≰ C N^{εp}`。用 `pow_le_add_inv_mul_pow`（`g^{2p} ≤ M^{2p} + M^{-2r} g^{2(p+r)}`，取 `M = N^{ε/2}`、`p+r = 2^m`、`m = p + ⌈1/ε⌉₊`）得 `E‖X‖^{2p} ≤ (1+C_q) N^{εp}`，直接喂 T73 的 `stochDom_one_of_momentDom`。

**`p ≥ 2` 被什么挡住**：需要 (a) 对 `{X_ij}` 的 Wick/Isserlis（或至少「独立对上的期望分解 + `E[z^m z̄^n] = 0`（m ≠ n）」，使只有每条边都重复的走留存），(b) 闭走计数（至多 `p+1` 个不同顶点、步长受带宽限制）。
**Mathlib 既无 Isserlis 也无闭走组合**，分解还得在 `Measure.infinitePi` 上从 `P_map_restrict` 造起——这是独立一单的体量，agent 没有伪造。
复用情况：高斯矩只用到 `RBM.integrable_pow_gaussianReal`（可积性）；`Stein.lean`/`LDEQuad.lean`/`LDEQuadT.lean` 给的是预解式二次型的条件/逐行混沌估计，**都不是**迹展开需要的 `X` 的 entry 矩，故无可复用。paper-deltas #49 已相应收窄。

## ⚠ HEAD 编译失败：`Gauss/FlowHolder.lean`（别人的 T106，2026-09-20）

`lake build RBM1D` 在 `RBM1D.Gauss.FlowHolder` 上失败（`2f1e01b`「T106 part 2」）：`181:89 unsolved goals`、`185/186 Function expected`、`202:15 don't know how to synthesize implicit argument E`。
**不是我这边的文件。** `RBM1D.Gauss.OpNorm` 与 `RBM1D.Gauss.DominationHolder` 单独 `lake build` 均为 exit 0。

**T106 第二、三块 ✔**（`Gauss/FlowHolder.lean`）：

```
abs_sqrt_sub_sqrt_le    : |√x − √y| ≤ √|x−y|
norm_zt_sub             : ‖z_u − z_u'‖ = |u − u'|          （因 z_t = E + (1−t)m(E)、‖m(E)‖ = 1）
norm_green_flow_sub_le  : ‖G_u − G_u'‖ ≤ η_u⁻¹·(|√u−√u'|·‖X‖ + |u−u'|)·η_u'⁻¹
abs_llErr_sub_le        : |llErr_u(ij) − llErr_u'(ij)| ≤ ‖G_u − G_u'‖
abs_llMax_sub_le        : |llMax_u − llMax_u'| ≤ ‖G_u − G_u'‖
llMax_le_inv_etaT       : llMax_u ≤ η_u⁻¹ + 1
abs_llMax_sq_sub_le     : |llMax_u² − llMax_u'²| ≤ (η_u⁻¹+η_u'⁻¹+2)·(上面那个界)
```

**谱参数那一半比想象中简单**：`zt E t = E + (1−t)·m(E)`，所以
`z_u − z_u' = (u'−u)·m(E)`，而 `‖m(E)‖ = 1`（`norm_mE`），于是 `‖z_u − z_u'‖ = |u−u'|`
——不需要碰 `etaT` 的表达式。

**下一步（最后一块）**：在 `[0, t]`（`t < 1`）上把两个 `η_u⁻¹` 统一放大成 `η_t⁻¹`
（`etaT` 对 u 反单调），并用 `|√u−√u'| ≤ |u−u'|^{1/2}`、`|u−u'| ≤ |u−u'|^{1/2}`
（`|u−u'| ≤ 1`）收成

```
|llMax_u² − llMax_u'²| ≤ (2η_t⁻¹+2)·η_t⁻²·(‖X‖+1)·|u−u'|^{1/2}
```

即 `stochDom_timeIcc_of_holder` 要的 `K(ω)·|u−u'|^γ`（γ = 1/2，`K(ω)` 与 `‖X‖` 成正比）。
之后配 T101 的 `≺`-常数版与 T100 的 `‖X‖ ≺ 1` 就能关掉 `Lemma41Flow`。

全量构建通过，公理审计 **7007 条声明**全部合规。

**T106 ✔**（`Gauss/FlowHolder.lean`，零 sorry）：**`u` 方向的 Hölder 模做完了，纯确定性。**

```
abs_llMax_sq_sub_le_holder (|E| < 2) (t < 1) (0 ≤ u,u' ≤ t) (|u−u'| ≤ 1) :
  |llMax_u² − llMax_u'²| ≤ (2η_t⁻¹+2)·η_t⁻²·(‖X‖+1)·|u−u'|^{1/2}
```

正是 `stochDom_timeIcc_of_holder`（T73/T75）与 T101 的高概率版要的 `K(ω)·|u−u'|^γ`，
γ = 1/2、`K(ω)` 与 `‖X‖` 成正比。**全程没用到 `‖X‖ ≺ 1`**——那只在把 `K(ω)` 喂给时间网时才需要。

几处记一下：
* **谱参数那一半只有一行**：`zt E t = E + (1−t)·m(E)` ⟹ `z_u − z_u' = (u'−u)·m(E)`，
  `‖m(E)‖ = 1`（`norm_mE`）⟹ `‖z_u − z_u'‖ = |u−u'|`。不必碰 `etaT` 的表达式。
* `|√x − √y| ≤ √|x−y|` **Mathlib 里没有**，自己证（比较平方：`(√x−√y)² ≤ x−y ⟺ y ≤ √(xy)`）。
* `inv_le_inv_of_le` 在这个版本里**不存在**；用 `one_div_le_one_div_of_le` 配 `← one_div`。
* `rwa [Real.sqrt_eq_rpow] at h` 会**把 `√u`、`√u'` 一起改掉**；要用
  `rwa [show Real.sqrt |u−u'| = … from Real.sqrt_eq_rpow _] at h` 定住实例。

蓝图新节点 `lem:flow-holder`。全量构建通过，公理审计 **7011 条声明**全部合规。

**`Lemma41Flow` 的三块现在**：固定时刻版 ✔（T102）、Hölder 模 ✔（T106）、
时间网桥 ✔（T101，另一边）。**只差 T100 的 `‖X‖ ≺ 1`**（另一边进行中）——
它一到，把 `K(ω) = (2η_t⁻¹+2)η_t⁻²(‖X‖+1)` 喂进 T101 的 `≺`-常数版即可收口。

**T107 —— 开工前的核对发现两处真障碍，工单重新划分（未写代码）**

原计划：把 T102（固定时刻）+ T106（Hölder 模）+ T101 的
`stochDom_timeIcc_of_holder_dom` 串起来关掉 `Lemma41Flow`。逐条对签名后，发现两处**结构性**问题。

**障碍一：`Green/EntryBound.lean` 的 Lemma 4.1 只对「固定的谱参数」陈述。**

```
entry_bound_stochDom … {z : ℂ} (hz : z.im ≠ 0) …
diag_bound_stochDom  … {E κ t : ℝ} …          -- z = zt E t，t 是一个固定实数
```

`z` 是一个**固定的复数**，连「随 N 变」都不行，更不要说「随指标集里的时间变」。
而 `Lemma41Flow` 的指标集是 `TimeIcc s t N × (ZMod L × ZMod L)`，
时间与谱参数都要随指标走。所以 **T102 的固定时刻版没法直接加时间指标**。

好消息是这**只是接口问题**：`StochDom.of_det`（`Green/EntryBound.lean:1378`）对指标类型
`U`、`V` 完全一般，而确定性内核 `norm_sq_green_le_blk`、`norm_sq_green_diag_sub_le_blk`
本来就是逐 `(ω, H, z)` 的。所以可以用**他们的确定性内核 + 自己的 `of_det` 调用**，
在自己的文件里重做一个带时间指标的版本。一个细节：`of_det` 的 `δ : ℕ → ℝ` 不含 `u`，
而 `goodEv` 的阈值 `(Wℓ_uη_u)^{-1/6}` 含 `u`；但 `scale` 对 `u` 反单调
（`flowScale_antitoneOn`），取 `δ N := (scale E N (t N))⁻¹^{1/6}` 即可一致地放大，
`goodEv_u ⊆ {GoodEvent G_u m δ_N}`，指示函数方向正确。

**障碍二：`Lemma41Flow` 的控制 `Φ N u` 依赖时间，而时间网桥要求控制只依赖 N。**

`stochDom_timeIcc_of_holder_dom`（T101）与 T75 的 `stochDom_timeIcc_of_holder`
都取 `Φ : ℕ → ℝ`。网论证把 `Y_u ≤ Y_v + mod` 从网点 `v` 传到任意 `u`，结论要的是
`Y_u ≤ N^τ(Φ_u + W⁻¹)`，而手上是 `Y_v ≤ N^{τ'}(Φ_v + W⁻¹)`——**差一个 `Φ_v ≤ N^ε Φ_u`**。
`W⁻¹` 那半没问题（`mod` 可以做到 `≤ N^{-D}`，而 `Φ_u + W⁻¹ ≥ W⁻¹ ≥ N⁻¹`），
问题只在 `Φ` 本身。`Lemma41Flow` 对**任意** `Φ ≥ 0` 量化，所以按字面**证不出来**。

Step1 实际传进去的是 `Φ N u = ℓ_u/ℓ_s · (Wℓ_uη_u)⁻¹`（`Step1.lean:704`），
它当然是缓变的；但「缓变」要与网距挂钩，而网距是桥内部选的。两条出路：
(a) 给桥加一个 `Φ` 的缓变假设（要改 T101 的文件，别人的）；
(b) 在自己的文件里重做网论证，把 `Φ N u` 一并处理。

**据此把 T107 拆成两张**（见 `docs/TASKS.md`）：T107 只做**带时间指标的 Lemma 4.1**
（障碍一，纯接口重做，可立刻开工）；T108 做最后的总装（障碍二 + T100）。

## T108 认领后释放（Claude Code，2026-09-20）

我认领了 T108 并派了 agent，**agent 因周额度上限（rate limit）在读文档阶段即中断，没有创建任何文件**——
`RBM1D/Gauss/Lemma41FlowGauss.lean` 不存在，`Gauss/DominationHolder.lean` 未被改动。工单已改回「空闲」，谁都可以接。

**接手时值得知道的一点**：STATUS 上面那条「障碍二」的路线 (a) 写着「要改 T101 的文件，别人的」——
**这句话过时了**：`Gauss/DominationHolder.lean` 就是本侧（Claude Code）T101 的文件，没有别人在编辑它，
所以路线 (a)（给桥加 `Φ` 的缓变假设，与现有五条 `stochDom_timeIcc_*` 并列新增、不动旧陈述）是通的，
不必走路线 (b) 重做网论证。Step1 实际传入的 `Φ N u = ℓ_u/ℓ_s · (Wℓ_uη_u)⁻¹`（`Step1.lean:704`）本身是缓变的。

### `RBM1D/Gauss/Lemma41FlowGauss.lean` — Lemma 4.1 沿流的总装（T108，Claude Code 并行 agent）

**`lemma41Flow` 已组装，且对 `Φ` 没有任何额外假设**——对**每个** `Φ N u ≥ 0` 成立，与 `Step1.Lemma41Flow` 的量化逐字一致。

**障碍二：既不用路线 (a) 也不用 (b)，实际是路线 (c)——根本不需要时间网。**
`Lemma41Flow` 是两个**本来就时间一致**的支配之间的传递（其假设是对 `TimeIcc × (ZMod L × ZMod L)` 的 `StochDom`）；
T102 那条链的每一步都是「在单个 `N`、`ω` 上关于失败事件的论断 + 对指标集的存在量词」，**对指标集是什么不敏感**。
于是全程把时间**放进指标集**就够了；只有当你从**固定时间**的 (4.2)/(4.3) 出发、事后再去做一致化，才需要网与 `Φ` 的缓变。Lean 证实了这一点：对任意 `Φ ≥ 0` 都类型检查通过。
**这说明 STATUS 上面那条「障碍二」的分析虽然正确，但前提（必须经由网）对本次总装并不成立。**

**路线 (a) 仍按要求交付**（`DominationHolder.lean` 末尾**纯新增**）：`stochDom_timeIcc_of_holder_slow_hp`/`_slow_dom`，`Φ : ℕ → ℝ → ℝ`，
缓变假设把**网距显式暴露**给调用方（`hδ : ∀ᶠ N, T/N^{(K+B+1)/γ} ≤ δ N`，证明里的网恰有 `⌈N^{(K+B+1)/γ}⌉₊+1` 个点），τ 预算三等分。
**T101 原有的五条陈述逐字未动**，且各自单独编译、公理干净（已逐条验证）。
**Step 1 的 `Φ` 已卸**：`step1Phi_eq` 证 `Φ N u = (ℓ_s·W·η_u)⁻¹`（`ℓ_u` 约掉），故 `Φ(N,v)/Φ(N,u) = (1−u)/(1−v)`；
`slow_step1Phi` 由单一边条件 `∀ᶠ N, δ N ≤ 1 − t N` 对每个 `ε > 0` 卸掉 `hslow`——即**网距小于到 u=1 奇点的距离**。

**T100 不是这里的假设**：`‖X‖ ≺ 1` 是 T107 背后**时间一致 LDE 估计**的输入，不是本传递的输入。
**T107 接口**：`EntryBoundFlow`/`DiagBoundFlow` 两个 `def`（(4.2)/(4.3) 前面加 `RBM.TimeIcc s t N` 到指标集，指示函数用时间冻结的 `flowDelta`），
字面上就是 `entry_bound_gauss`/`diag_bound_gauss` 放大指标集，T107 的 `of_det` 输出应当无胶水对上。
**T107 落地时要核对**：若它直接产出 `Step1.goodEv` 指示函数的形式，则 `goodEv_subset_goodSet_flow` 不再需要，假设可简化。
新增的 `..._slow_*` 桥目前**没有消费者**（因为总装不需要网），保留为通用工具与后备。paper-deltas #97。

## ⚠ HEAD 编译失败：`Gauss/IBP.lean` 与 `Gauss/FlucIter.lean` 的重名（2026-09-20，Cowork 值守发现）

```
error: RBM1D.lean:1:0: import RBM1D.Gauss.IBP failed,
  environment already contains 'RBM.Gauss.condRow_zero' from RBM1D.Gauss.FlucIter
```

`condRow_zero` 被声明了两次：

* `Gauss/FlucIter.lean:338`（T94，**已合并、有下游消费者** —— 同文件 421/425 行在用）
* `Gauss/IBP.lean:782`（T83，**在飞行中**）

**处理办法：后来的那个改名**，即 `Gauss/IBP.lean` 里那条。建议叫 `condRow_zero_apply`
或 `condRow_zero'`（它的陈述带 `(ω : Ω d)`，与 FlucIter 那条的形状不同，本来就该区分开）。
同文件 861 行的 `simp only [..., condRow_zero, ...]` 一起改。

**给 T83 接手人的提醒**：**单文件 `lake env lean` 查不出跨文件重名**——它只在全量 `lake build`
把根 `RBM1D.lean` 的 import 链拼起来时才炸。所以动了公共命名空间里的名字之后，
**收工前至少跑一次全量构建**，别只信单文件绿。

这一条同时说明 T90（全库重复扫描）那类维护单值得定期重跑。

### `RBM1D/Gauss/IBP.lean` — T83 交接的后三格已完成（Claude Code 并行 agent，2026-09-20）

**(a)(b)(c) 全部落地；`hIBP` 可在其冻结签名下卸掉**——已用 scratch 文件验证：把 `condExpDiag_stochDom_of_ibpRem` 喂进 `trace_green_sub_mul_Eblk_stochDom` 的 `hIBP` 槽，直接得到 (4.5) 的结论，**任何签名都没改**。
**(a)** `integral_Hflow_mul_green_diag : E[(H_u G)_{aa}] = −u Σ_k S_{ak} E[G_{aa}G_{kk}]`；组合核心 `sum_gvar_Bmat_sandwich_diag`——两个 tag 在**平方的非对角项**上贡献 `c_b² = ±1` 故**相消**，而 `c_b c̄_b = 1` 使每个 tag 各出一半的 `S_{xy}G_{xx}G_{yy}`，对角坐标（实 tag，`gvar = S`）补上 `S_{aa}G_{aa}²`。
**(b)** 没有重复造分析：`E_i` 本身就是对 `rowSplit` 复合后的 `P d`-积分，而 `rowSplit` 与「更新第 i 行的坐标」交换（`rowSplit_update`），故 `gaussIBP` 逐字适用；新增 `Tame.comp_rowSplit`（冻结非本行坐标后 tame 性保持）与 `condRow_coord_mul`。不碰第 i 行的坐标**逐点**掉出（`Bmat_mul_apply_diag_of_ne`），无需对指标集动手术。
**(c)** `condExpDiag_eq_sum_Sblk` 是 p.50 的式子且**无误差项**；误差全部进 `ibpRem`。

**唯一剩余缺口**：`condExpDiag_stochDom_of_ibpRem` 需 `‖ibpRem‖ ≺ Lmax`；`ibpRem_eq_add` 把它拆成论文的两个输入，`condExpDiag_stochDom_of_pieces` 分别接收：
`hprod`（局部律的平方 `E_i[(G_ii−m)(G_kk−m)] ≺ Lmax`）与 `hminor`（(4.9) 的替换 `E_i(G_kk−m) − (G_kk−m) ≺ Lmax`，T85）。两者都未证。
**`hminor` 还缺一块通用工具：「被 ≺ 支配的量取 `E_i` 后仍被 ≺ 支配」——这不是自动的，仓库里没有这条引理，是真正的下一张单**（我不写工单，留给 Jun/Cowork）。

**整合时踩到的一个坑（已修）**：新加的 `condRow_zero` 与我 T94 `FlucIter.lean` 里的同名声明冲突，`RBM1D.lean` 同时 import 两者即报
`environment already contains 'RBM.Gauss.condRow_zero'`。已把 `IBP.lean` 里的改名为 `condRow_zero_apply`（逐点形式）。
**教训**：并行 agent 各写各的文件时，`lake env lean 单文件` 绿**不能**保证全局无重名——整合时必须跑一次全量 `lake build`。paper-deltas #98。

### `RBM1D/Gauss/DistEq.lean` — (2.39)(2.66)(6.1) 三条转移（T111，Claude Code 并行 agent）

**三条全部成为定理，且全部落入「情形 A」——比规格预期的还强。**
不是「同一个 `ω` 的确定性重标度」，而是**随机变量的逐点相等**：矩路线用**一个固定的** `X`，`H_u = √u·X`，
标度与谱参数的平移恰好相消。由 (2.37) 有 `z_t^{(E)} = t^{1/2} z`，故 `H_t − z_t = t^{1/2}(X − z)`，于是 `t^{1/2} G_t^{(E)}(ω) = G(X(ω), z)` 逐点成立。
`Measure.map`、`gaussianReal_map_const_mul`、`infinitePi_map_pi` **一条都没用到**（规格里的「情形 B」路线完全不需要）。

- `RBM.Transfer` → **`transfer_gauss`**（是 `def`，因 `Transfer` 是数据），`Hband := Xmat`；`green`/`loop2`/`loop2_expect` 三个字段都是 `le_of_eq` 或 `integral_const_mul`。
- `RBM.TransferLoop1` → **`transferLoop1_gauss`**（长度 1 的同一恒等式：`t^{1/2} L_{t,+,a} = Tr G(z) E_a`，精确）。
- `RBM.LoopScaling` → **`loopScaling_gauss`**：`H_{t₂} = (t₂/t₁)^{1/2} H_{t₁}` 且 `z̃_{t₁} = (t₂/t₁)^{1/2} z_{t₁}`，故 `L_{t₂} = (t₁/t₂)^{n/2}·L_{t₁}` 逐点成立，`(t₁/t₂)^{n/2} ≤ 1` 收口。

`Flow/Consequences.lean`、`Flow/Hypotheses.lean`、`Loop/ContinuityAssembly.lean`、`Gauss/Model.lean` 的签名一律未改。
唯一新增假设：`loopScaling_gauss` 需 `0 < t₁ N` 与 `t₁ N ≤ t₂ N`（`RBM.LoopScaling` 本身未改；消费者 `RBM.lemma_5_1` 已自带 `0 < c ≤ t₁ N` 与 `t₁ N ≤ t₂ N`，白送）。
**注**：矩路线整体仍条件于 T69 的 `OpNormBound`（`‖X‖ ≺ 1`，T109 在做）与 `Dims` 的具体实例。paper-deltas #99。

### `RBM1D/Gauss/FlucIterHigh.lean` — 第 0 步结论：**增益是乘性的**（T110，Claude Code 并行 agent）

**全队标记为最高风险的那一单通过了。** `‖Q_{κ₂} Q_{κ₁} Z_k‖ ≲ Ψ³`，不是 `2Ψ²`。

**机制比预期的强：是恒等式，不是估计。** `Q_κ` 湮灭任何与第 κ 行严格独立的东西，且不同行的 `Q` 互相交换；
于是剥掉最外层的 `Q_κ`、把**整个小行族** `Y` 换成 `Δ_κ Y : S ↦ Y S − Y (S ∪ {κ})`，**什么都没损失**——被减掉的 `Y {κ}` 当场被杀。
迭代得到 **`applyOps_eq_applyOps_minorDiff`**：`applyOps L (Z_k) = applyOps L (Δ_{κ₁}⋯Δ_{κ_m} Z^{(·)}_k)`。
**m 次涨落并非各自独立作用，而是复合成 m 重小行差**——这正是乘性的来源。
`m = 2` 具体算完（`norm_minorDiff_pair_greenSetDiagCentered_le ≤ 10Ψ³`）：经 (4.9) 后二阶差是 `∅` 与 `{κ₂}` 两个层级上三元积 `G_{kκ₁}G_{κ₁k}/G_{κ₁κ₁}` 的差，
每个因子与其对应者相差 `Ψ²`，非对角是 `Ψ`，对角的逆是 `O(1)`，合计 `Ψ²·Ψ + Ψ·Ψ² + Ψ²·Ψ² ≍ Ψ³`；**加性的话只有 `Ψ²`**——多出来的那个 `Ψ` 正是第二个 `Q` 作用在第一次替换误差上赚到的。

**(4.12) 仍未完全无假设**，剩余输入是 `MinorDiffGain`（迭代小行差的**大小**，m ≥ 3）。但它**严格弱于**原来的 `FlucGain`：
**概率那一半已经卸干净**——其内容里不再有任何条件期望，只剩 Green 函数的小行与局部律。`m = 2` 已无条件。
按约束：`MinorDiffGain` 按**期望**陈述（逐点的 Ψ-尺度界是假的），**全程没有 `1_Ω`**（湮灭恒等式在任何截断之前使用，故 `E_κ[(1−E_κ)X]=0` 的障碍根本不出现）；`minorDiffGain_env` 是无增益（`ρ = 4`）的无条件实例，接口不空洞。
`m ≥ 3` 需要 `Δ_κ` 在 (4.9) 分解上的 Leibniz 演算（`Δ_κ(XY) = (Δ_κ X)Y + X^{(κ)}(Δ_κ Y)`、`Δ_κ(1/X) = (Δ_κ X)/(X X^{(κ)})`）逐层传播，单步的子类型搬运机器已经就位（`insertRowEquiv`、`greenSetMat_insert_apply`）——**这是自然的下一张单**（我不写工单）。paper-deltas #66。

### `RBM1D/Gauss/TraceMoment.lean` — `‖X‖ ≺ 1` 已完全证出（T109，Claude Code 并行 agent）

**paper-deltas #49 这个公开缺口关闭。** `traceMomentBound_gauss` 对**所有 p** 成立 ⟹ `stochDom_norm_Xmat_gauss`（`‖X‖ ≺ 1` 无条件）⟹ **`opNormBound_gauss : OpNormBound d`**。
`Gauss/Model.lean` 的 `OpNormBound` 与 `Gauss/OpNorm.lean` 的两个冻结接口一字未改——是**卸掉**，不是改写。**没有任何剩余假设。**

**第 0 步验过了，因子 2 完全对得上**：`integral_Xmat_pow_succ_diag : E[(X^{m+1})_{aa}] = Σ_{k+l=m−1} E[(Σ_j S_{aj}(X^k)_{jj})·(X^l)_{aa}]`。
路线即规格所述：`Xmat_eq_sum` 把 `X` 写成坐标和，逐坐标用 `gaussIBP.stein`（被积函数是 `Tame`），导数照抄 `IBP.lean` 的 `hasDerivAt_Hflow_update` 模式，坐标和由 `sum_gvar_Bmat_sandwich_apply` 塌缩。
**非对角对的两个 tag 各带 `gvar = S_ij/2`，其非对角贡献相消，活下来的 `2·S_ij/2 = S_ij` 恰好正确**，没有多余因子。
`p = 1` 体检通过：`m = 1` 时退化成 `E[(X²)_{aa}] = Σ_j S_{aj} = 1`，求和得 `E Tr(X²) = WL`，与 `traceMomentBound_one` 一致，`traceConst 1 = 1`。

**⚠ 规格里的收口方式实际不成立，agent 换了一个**：Cauchy–Schwarz 把次数 `k → 2k`，而递推里 `k` 跑到 `2p−2`，于是 `A_p` 依赖 `A_{2p−2}`——`p ≥ 3` 时不是良基的。
替代品同样不需要组合：列范数 `u_m(i) = Σ_r|(X^m)_{ri}|² = (X^{2m})_{ii}` 的**对数凸性** `u_m² ≤ u_{m−1}u_{m+1}`（对 `(X^{2m})_{ii} = ⟨X^{m−1}e_i, X^{m+1}e_i⟩` 用 Cauchy–Schwarz）加 `u_0 = 1`，
给出 `u_k^M ≤ u_M^k`（`pow_le_pow_of_logConvex`，除法-free 的离散证明），故 `‖(X^k)_{ii}‖ ≤ u_M(i)^{k/(2M)}`；再由加权 AM–GM，`k+l = 2M` 时两者之积被**凸组合**控制，**次数不再翻倍**。
配 `Σ_j S_{ij} = 1` 与对 M 的归纳得 `E[(X^{2M})_{ii}] ≤ C_M`（`C_0 = 1`、`C_{M+1} = (2M+1)C_M`，即 `(2M−1)!!`），对 `i` 与 `N` 一致；求和得 `E Tr(X^{2p}) ≤ C_p·N`。

**矩路线现在只剩一个公开前提**：`RBM.Gauss.Dims` 仍无实例（给出具体的 `W, L, c` 即可，唯一不平凡处是 (2.2) 的 `rpow` 估计）。paper-deltas #67。

### `RBM1D/Gauss/MinorDiffGain.lean` — m 重小行差的 Leibniz 演算（T113，Claude Code 并行 agent）

**估计在每一阶都有了，但 `MinorDiffGain` 按其现有定义仍未卸掉——(4.12) 不是无假设的。** 两条输入，文件里都具名：

1. **例外集**：全部条件于 `MinorGood d N u z ω Ψ`——(4.1) 加上**每个小行层级**上的 (4.2)(4.3)，且在**每个** ω 上。
   去掉它要拆积分、在坏事件上付 `η_t⁻¹`（在这里是合法的：`MinorDiffGain` 内部已无条件期望，不会有指示函数被乘进 `Q_κ`，文件里也确实没有引入），但需要仓库目前没有的那种形状的定量局部律。
2. **对 m 的一致性**：常数满足 `c_{m+1} = 16^m c_m^5`。**这不只是宽松**——倒数的 m 重差是对集合分拆的求和，即便最锐的版本也按 `m!C^m` 增长，
   **没有固定的 `ρ ≍ Ψ` 能对所有 `m ≤ N` 压住 `m!C^m Ψ^{m+1}`**。但**消费者根本不需要**：`2p` 阶矩展开只用到 `numQ (L i) ≤ 字长 ≤ 2p`。
   **所以有用的、也是已证的，是有界字长版本**（`integral_prod_applyOps_minorDiff_le`、`minorDiffGain_of_pointwise`）。
   **建议**：考虑给 `MinorDiffGain` 一个按字长有界的后继接口（agent 未建工单，我也不写）。

**已证的 Leibniz 规则（都是恒等式）**：`deltaFam_mul`、`deltaFam_inv_apply`（需两值非零）、`deltaFam_shiftFam`/`iterDeltaFam_shiftFam`（层级平移，子类型搬运只做一次）、
`deltaFam_gFam`（(4.9)：`Δ_κ G_{ab} = G_{aκ}G_{κb}(G_{κκ})⁻¹`，在**所有**层级含退化情形都成立）、`deltaFam_gInvFam`（五个原子，一次赚两个幂）。
**使归纳闭合的设计要点**：原子带一个基层级 `T`（`gFam a b T S = G^{(S∪T)}_{ab}`，指标被删时延拓为 0），于是这一类对层级平移封闭；而 `MinorDiffGain` 的 `Nodup`/新鲜性条件**正好**是分级所需要的。
**m=3 体检**：`norm_minorDiff_triple_le ≤ 2^91·Ψ⁴`；幂的阶梯 `Ψ²`(T85, m=1) → `10Ψ³`(T110, m=2) → `Ψ⁴`(此处) 对上了。
`FlucIterHigh`/`FlucIter`/`FlucCount`/`FlucAvg`/`EntryBound` 的签名一律未动，`MinorDiffGain` 的定义未改（被 `minorDiffGain_of_pointwise` 原样消费）。paper-deltas #68。

### `RBM1D/Gauss/CondDom.lean` — `≺` 在条件期望下的保持（T112，Claude Code 并行 agent）

**通用工具 `stochDom_condRow_of_envelope`**（本单的可复用产出，用的是仓库自己的 `RBM.StochDom` 与 `condRow`）：
`‖X‖ ≺ ζ` + 逐点确定性包络 `Env`（多项式增长）+ `N^{-B} ≺ χ` + **`CondStable`** ⟹ `‖E_k[X]‖ ≺ χ`。
数学内容就是工单那段「为什么不自动」所要求的两条：`lintegral_measure_rowSlice`（`∫ P(行切片) dP = P(S)`，经 T84 的 `measurePreserving_rowSplit` 做 Fubini）与其上的 Markov（`meas_measure_rowSlice_ge`），
再加 T77 式的好/坏事件分割 `norm_condRow_le_split`。

**第四条假设不可避免，这是本单真正的发现**：把 `E_k` 写成精确坐标积分后得到 `‖E_k[X](ω)‖ ≤ N^τ E_k[ζ](ω) + Env·P(切片)`——
**控制出现在分割点上**，所以诚实的结论是被 `E_k[ζ]` 界住而不是被 `ζ` 界住。打包成结构 `CondStable`（ζ 的行可积性 + `E_k[ζ] ≺ χ`）；
`CondStable.of_det`（确定性控制）与 `of_finDepOffRow`（控制读自小行）免费卸掉它，但 `χ = ζ = Lmax` 时不免费，需携带。

## ⚠ 发现冻结接口里的一处**假命题**：`condExpDiag_stochDom_of_pieces` 的 `hminor` 在对角处为假

`hminor` 在 `q.1 = q.2` 处断言 `E_i(G_ii − m) − (G_ii − m) ≺ Ψ²`，但该量正是 `−(1 − E_i)(G_ii − m)`，**尺度是 `Ψ` 而非 `Ψ²`**，且对角没有小行替身。
故 `condExpDiag_stochDom_of_pieces` **按原样喂不进去**。**修法完全在本文件内，没碰任何冻结签名**：
对角项在 `Σ_k S_ik·ibpRem(i,k)` 中带系数 `S_ii`，而事件上 `S_ii ≤ 2·Lmax`（`RBM.Sblk_le_Lmax`），`ibpRem` 有确定性包络 `(η_t⁻¹+1)²`；
于是用加权版 `norm_condExpDiag_sub_le_offdiag` 取代一致版，经 `condExpDiag_stochDom_of_offdiag` 得 **`condExpDiag_stochDom_of_localLaw`——`hIBP` 的冻结签名**。
**已按要求做编译验证**：`trace_green_sub_mul_Eblk_stochDom_of_localLaw` 把它塞进 `hIBP` 槽并编译通过（走的是 `condExpDiag_stochDom_of_offdiag`，不是 `condExpDiag_stochDom_of_pieces`）。

**剩余假设**：`hstabP`/`hstabM`（`E_i[Lmax] ≺ Lmax`——本路线暴露出的**真正新的概率输入**，属局部律类的比较而非涨落平均，**值得单独一张单**）；
`hloc`（(4.3) 去掉指示函数）；`hrepl`（T85 的 (4.9) 搬到 `greenMinorMat` 与控制 `Lmax`，需 `greenMinorMat = minorGreen` 的可逆性与 `Ψ² ≺ Lmax`）；`hΩ`(4.4) 与 `hG : GaussIBP`。
顺带证出：`measurable_Lmax`、`stochDom_rpow_neg_one_Lmax`（`N⁻¹ ≺ Lmax`），故 `N^{-B} ≺ χ` 那条**不用携带**。
又一次名字冲突（`norm_condRow_le` 与 `Gauss/FlucIter.lean` 重名），agent 自查时发现并改名为 `norm_condRow_le_const`——**单文件编译查不出跨文件重名，整合时必须跑全量 build**。paper-deltas #69、#70。

## T114 第 1 步：`Steps` 八字段对账（Claude Code，2026-09-21；**只做对账，未写 Lean**）

方法：scratchpad 下四个探针 + 一个负对照，`lake env lean` 对活的工作树编译（未碰任何仓库文件）。下面标 **[编译]** 的是探针验证过的，**[读码]** 的是只读代码得出的。

### 结论一句话：**八个字段全部逐字对上，零 `precomp_param`、零量词重排、零指标集改动、零类型类调整。**

探针 1 是一个字面的 `Steps X E s t where apriori := … sharpExpect := …`，每个字段都由裸应用填上，`EXIT=0` 无警告 **[编译]**；
负对照（把 Step 1 的 `weakLaw` 喂进 `localLaw` 槽）如期报错，说明探针确实在做类型检查 **[编译]**。
**真正的问题不在这八个字段，而在（i）各步定理的残余假设，（ii）`Thm221.step` 自身的一处假设强度不匹配。**

| 字段 | 来源 | 对上？ | 关键残余假设 |
|---|---|---|---|
| `apriori`(2.73) / `weakLaw`(2.74) | `Step1.step1` 的 `.1`/`.2` | **逐字** [编译] | `hreg`（**`Cond272` 推不出**，paper-delta #44；但可由 Step 2 的 `hregS` 推出，见下）；`Step1.Hyp` 四字段中 `scaling` = `Gauss.loopScaling_gauss`（T111）、`lemma41` = `Gauss.lemma41Flow`（T102/T108），**`lift` 与 `cont` 全树无生产者** |
| `localLaw`(2.75) / `aprioriDecay`(2.76) | `Step2.step2`（路线 A）**或** `Step2Moment.step2`（路线 B） | **两条路线都逐字** [编译] | A 需 T58；B 需 `MomentHyp.step`（STATUS 已记：今天供不出，T74/T76 那堵墙） |
| `sharpLoop`(2.77) | `Step3.flow_sharpLoop` | **逐字** [编译] | `h514` 由 `SumZeroDyn.lemma514_flow'` 卸；**`h0`/`h12` 全树无生产者** |
| `sharpLmK`(2.78) / `sharpDecay`(2.79) | `Step45.flow_steps45` 的 `.1`/`.2` | **逐字** [编译] | `h514` 要 `2 ≤ n`（严格强于 Step 3 的 `3 ≤ n`，由 `fun n hn => h514 n (by omega)` 转换 [编译]）；**`h1`/`h2`/`h548` 无生产者** |
| `sharpExpect`(2.80) | `Step6.sharpExpect_step6` | **逐字**（右端在**终点时刻**） [编译] | **`h5132` 字面就是 `(hb : Bounds X E s).expect`，无需搬运** [编译]；`hint1` = `Gauss.integrable_sample_Lval`；`DLK`/`DG` 是隐式且目标定不下来，总装要存在性地给出；`Step6.Hierarchy`/`FastDecayHyp`/`h5133`/`Eq527`/`hq11`/`hG`/`hq13` 无生产者 |

**两条经济性事实（都 [编译]，探针 4）**：`hregS` 同时蕴含 Step 1 的 `hreg`（经 `Step2.eventually_R4_le_scale` 取 `u := t`）**与** `Cond272`（经 `Step2.cond272_of_strict`）。
**故总装只需要一条正则性假设 `hregS`，`hc` 与 `hreg` 都可以去掉。**

### ⚠ 唯一的陈述级不匹配，需 Cowork 定夺：`0 ≤ s` vs `0 < s`

`Thm221.step`（`Flow/Hypotheses.lean:286`）给的是 `(∀ N, 0 ≤ s N)`，而 Steps 1–5 **全部**要求 `(∀ N, 0 < s N)`，只有 Step 6 接受 `0 ≤`。探针 3 复现为硬错误 **[编译]**：
`Application type mismatch: hs0 has type ∀ N, 0 ≤ s N but is expected to have type ∀ N, 0 < s N`。
**这不是 `precomp_param` 能搬的，是假设强度差。** 注意 `s` 是**序列**，所以「`s N = 0` 单独处理」不是能对 N 一致做的分情况；`Bounds_zero`/(2.67) 是 `s ≡ 0` 的基例。
**三条出路（我不替 Cowork 选）**：把五个 step 定理放宽到 `0 ≤ s`；或把 `Thm221.step` 收紧到 `0 < s`（一条 paper-delta）；或插值。
另记：`Thm221 X κ` 不带 `0 < κ`/`κ ≤ 1`，这两条要成为外层 `thm221_gauss` 的假设（只是记账，不是不匹配）。

### `Step2.Hyp` 的 `eG`/`mart` 与 T75 的关系：**两者是互斥的平行路线，不能混用**

`Step2Moment.lean` 里**没有任何**对 `Step2.Hyp`/`tau`/`stopTime`/`step_bound`/`self_improving`/`jS_highProb` 的引用（文档注释除外）**[读码+grep]**，
且 `Step2Moment.step2` 不带 `Step2.Hyp` 参数就产出 `Steps` 形状 **[编译]**。
`eG` **依赖 `H`**（其陈述里出现 `H.F`），**T58 定下 `F` 之前连陈述都写不出来**；`mart` 是**停止**鞅，依赖 `H.mart` 与停时。`MomentHyp` 的 15 个字段没有一个与二者一一对应。
T75 的替代关系是：`Hyp.cont`（高概率）→ `MomentHyp.cont`（逐 ω）；`Hyp.mart` + 自改进 → 单一字段 `MomentHyp.step`；Def 2.1(i) 的不可数并 → `stochDom_timeIcc_of_holder`（由 `holder`/`Kmod`/`gam` 喂）。`eG` 也被吸收进 `MomentHyp.step`。
**路线 B 假设更少**（不需 `Cond272`，只要 `hregS`），且 `holder` 由 T101 的 `stochDom_timeIcc_of_holder_dom` 卸掉 **[读码]**。

### T58 的消费点有**三处**（工单只写了两处），以及它必须交付的形状

1. `Step2.Hyp.H : SumZeroDyn.Hierarchy X E s t 0`——只有 `F`/`mart`/`duhamel` 被用到，但 `Hierarchy` 是结构，**八个字段都得给**。仅路线 A 需要。
2. **`SumZeroDyn.lemma514_flow'`——比工单说的「Step 3 的 `hyp_flow` 同理」分量重得多**：它要 `H : ∀ n, Hierarchy X E s t n`（**对所有 loop 长度**，不只 `n = 0`），并喂给 `sharpLoop`/`sharpLmK`/`sharpDecay`。
   **即：无论 Step 2 选哪条路线，T58 都在 Steps 3/4/5 的关键路径上**——工单正文没说这一点。其 `hLmK` **字面就是 `hB.LmK`**，无需搬运 **[编译]**。
3. `Step6.Hierarchy X E s t DLK DG`——**另一个对象**：无 ω、无鞅、无 `F`，漂移拆成 `DLK + DG`，是 (5.20) 在 `n = 2` 取期望**之后**的版本。**不是** `SumZeroDyn.Hierarchy` 的实例，不积分掉路径、不证 `E[mart] = 0` 就推不出来。**应告知 T58 这是第四项交付物。**

**形状要求**：TASKS 里 T58 的验收标准全写在 `LoopIdx` 一侧，**但每个消费者都在 `Fin n` 一侧**（`LoopArg L n = Fin n → ZMod L`；`SumZeroDyn.lkT` 里 `LoopData.idx (σ,a) = ⟨List.ofFn σ, List.ofFn a⟩` 已经把桥焊死在 `List.ofFn` 方向）。
**所以 T58 必须额外导出 `Fin n` 一侧的推论**（形如 `SumZeroDyn.lkT` + `Uker` + `xiOf (mSigma E) σ`），最低限度是给出 `∀ n, SumZeroDyn.Hierarchy X E s t n` 的项，其中
`F` 取 (5.15) 的漂移减去 `l_K = 2` 项（这样 `Lemma510` 才可证而非空洞）；`EE` 取 Def 5.4 的 `E⊗E`（**`Gauss.eeTens`/`eeRaw` 已经定义了这个对象，`toIdx`/`emart_Uker`/`quadVarPairs_Uker` 已经把它桥到 `Uker`，这一项最接近完成**）；`duhamel`=(5.20)、`duhamelQ`=(5.91)；`bdg`/`bdgQ`=(5.85)/(5.103)+BDG。
**必须转告 T58 的警告**（来自 `Gauss/DischargeBDG.lean:70ff`）：`duhamel` 可以**按定义造出来**从而对任意 `F` 成立，那会把全部内容压进 `bdg` 并使 `Lemma510` 为假。**只产出 `duhamel` 的交付物对 T114 毫无价值；绑定义务是三元组（`F` 具体、对它 `Lemma510` 可证、`bdg` 可证）。**

### 阻塞总装但**不属于**不匹配的缺口（全树无生产者）

按离完成的远近排序：`hs1`/`hs2`（Step 4 基例，Step45 文档说「可由 (4.5) 与 (2.76)+(2.72) 得出」但没证）→ `h0`/`h12`（文档说由 (2.73)(3.46) 与 (2.75)(2.76) 得出，但无引理；
**`h12` 在 `m = 2` 处有个坎**：`Step3.S … 2 l` 是对**全部四个** `σ ∈ {+,−}²` 取 max，而 (2.76) 只覆盖 `σ = (+,−)`，**其余电荷从哪来需要有人说明**）→ `h548`(5.48，T61 的遗留)
→ `Step1.Hyp.lift`/`cont` → Step 6 的七条随机层假设 → `SumZeroDyn.Lemma510`/`LKDecay`（其形状与 T59 的定理「对不上」，见 `SumZeroDyn.lean:62`）。

### 给 Cowork 的结论

八字段总装本身**不是问题**：八行字段赋值，今天就能编译。T114 实际要解决的是
**(a)** `Thm221.step` 的 `0 ≤ s` vs `0 < s`；**(b)** Step 2 选哪条路线；
**(c)** 从 Steps 1–2 的产出推导 `h0`/`h12`/`hs1`/`hs2`——**这块目前不属于任何工单，且与 T58 不同，它是纯确定性的记账，现在就能开工。**

### `RBM1D/Propagator/Rate.lean` — T1 完成（Claude Code 并行 agent，2026-09-21）

**先纠正一条本文件里过时的记载**：上面「T1 进展」一节说的**方向问题已经被 T1c 解决**（`RateComplex.lean`），
而「下一步」里要的 `1 − ‖ρ‖ ≍ |1−ξ|^{1/2}` 现在也有了。

**agent 查明：T1 的数学内容在开工前就已经齐了**，分散在两个文件里且都已被下游消费——
实 `ξ`：`rho_real_bounds`（`Decay.lean:411`，文件内用 6 次，`LongDiff.lean` 用 3 次）；
全体 `0 < ‖ξ‖ < 1`：T1c 的 `sq_one_sub_norm_rho_le`/`rho_complex_bounds`（`DiffComplex.lean` 已用 2 次）。
**Cowork 所说的「剩下的初等不等式」其实已被 T1c discharge 掉了。** 真正缺的只有三处**打包**：
(i) 全仓库没有任何 `≍` 形式的陈述（两条已有结果都是**平方**的，调用方想要的平方根形式不存在）；
(ii) `ellHat`（`Decay.lean:480`）只按 `‖1−ξ‖` 定义，**没有任何地方说它就是真正的衰减长度 `1/(1−‖ρ‖)` 截到 `L`**，每个消费者各自临时重推；
(iii) `ξ ≠ 0` 这条假设为什么必要，无人记载。

**新文件而非加进 `Decay.lean` 的理由**：`RateComplex.lean` **import** 了 `Decay.lean`，所以放在 `Decay.lean` 里的东西**用不了 T1c**，只会逼出重复证明。
`Rate.lean` import `RateComplex` 与 `DecayComplex`。七个名字均已全仓库 grep 查重。

主要结论：`one_sub_norm_rho_asymp`（`∃ c>0 ∃ C>0`，`c = 1/3`、`C = 2`）；
`ellHat_mul_one_sub_norm_rho_le` 与 `min_le_ellHat` 两条**双边**钉住 `ℓ̂ ≍ min(1/(1−‖ρ‖), L)`（绝对常数）；
**`norm_rho_pow_le_exp`**：`‖ρ‖^n ≤ e·exp(−n/(3ℓ̂))`（`n ≤ L`）——配上已有的 `norm_theta_apply_le_rho_pow` 就是**复 ξ 的 (2.52)，走闭式路线，不需要围道平移、不需要 Poisson 求和**（正是 CLAUDE.md 规定的路线）。

**可以据此简化的下游（本单未动，属别的文件）**：
`DecayComplex.lean` 的 `norm_Theta_apply_le_complex`/`_le_exists` 目前经 `Poisson.lean`+`Contour.lean` 到达复 (2.52)，常数是 `12π²/(1−e^{−c₀})+…`；
换成 `norm_rho_pow_le_exp` 可得同样结论、常数初等、依赖锥短得多（**Poisson 路线并不浪费——`Symbol.lean` 的 Fourier 形式 (3.48) 仍然要用——只是 (2.52) 不必依赖它**）。
`Decay.lean:577` 的 `norm_Theta_apply_le_of_real` 里内联重证的 `step3` 现在就是 `norm_rho_pow_le_exp`；`DiffComplex.lean` 的 `ellHat_mul_sqrt_le` 开头那段手工放缩就是 `sqrt_norm_one_sub_le_three_mul`。paper-deltas #71。

### `RBM1D/Hierarchy/StepGlue.lean` — T115：四条确定性缺口（Claude Code 并行 agent，2026-09-21）

## ⚠⚠ 第 0 步结论：**`m = 2` 的四电荷缺口是真的，而且缺在论文里，不在形式化里**（agent 查了 PDF 原文）

(5.76)（p.64）把 `Ξ^{(L−K)}_{t,m}` 定义成对**所有** `σ` 取 max；(2.76)（p.24）逐字写「`σ = (+,−)`」，§5.3（p.56）开篇也说「只看 `(+,−)`，本小节略去下标 σ」；
**p.70 却断言「由 (2.76)，`S(m,l)` 对任意 `l` 与 `m ≤ 2` 成立」**。`RBM.Steps.aprioriDecay` 与论文完全一致，所以缺的不是形式化。
四个电荷的来源：`(+,−)` 免费（`aprioriDecay_pm`）；`(−,+)` 由迹的循环性（已有的 `gloop_rotate`）归约；`(−,−)` 由共轭归约到 `(+,+)`；**`(+,+)` 在 Steps 1–2 里没有任何来源**。
**而且补不出来**：`S(2,l)` 在大 `l` 处要 `Ξ^{(L−K)}_{u,2} ≺ (Wℓ_sη_s)^{1/2}`，而 (2.73)+(2.59) 只给 `≺ R·A_u`、(2.75) 只给 `≺ A_u`——**都差整整一个 `A_u`**，正是 §5.3 单独硬论证的那个因子。
缺的输入已具名为 **`def RBM.StepGlue.AprioriDecayAll`**（四个电荷的版本，`(+,−)` 那半就在旁边证好），**没有被默默假设**。
**旁证**：Lemma 5.14 的证明（p.68）把 (5.96) 乃至整个 Step 3 的机器限制在**非常值** σ（「存在 k 使 σₖ = σₖ₊₁，即一对相反电荷」），**常值 σ 没有这样的对**——常值电荷在 §5 的**两处独立地**未被处理。**这需要 Jun 判断是补 §5.3 的论证还是改论文陈述。**

## 四条的状态

| | 状态 | 产出 |
|---|---|---|
| **`h0`** | **无条件证出** | `flow_S_zero`：由 (2.73)+(2.59)（经 `Step3.exists_norm_Kval_le`）。(2.73) 本身是 `max_{σ,a}` 界，故**覆盖全部电荷** |
| **`h12`** | `m=1` **无条件**，`m=2` 条件于 `AprioriDecayAll` | `flow_S_one`（**只用 (2.75)，不需要 (2.76)**）、`flow_S_two`、`flow_S_le_two` |
| **`hs2`** | 条件于 `AprioriDecayAll` + `hregS` | `flow_hs2`（经新证的 `eventually_R4_le_rpow_quarter`） |
| **`hs1`** | 条件于 `Eq45Flow` | `flow_hs1`：`Eq45Flow` + `Steps.sharpLoop 2`（(2.77) 逐字喂入） |

**编译验证（不是读签名）**：`flow_sharpLoop_glue` 与 `flow_steps45_glue` 把上面四条塞进 `Step3.flow_sharpLoop` 与 `Step45.flow_steps45` 的真实槽位，
**无强制转换、无 `convert`、无 `precomp_param`**，结论恰是 `Steps.sharpLoop`/`sharpLmK`/`sharpDecay` 的形状。两条已从 `example` 提升为文件里的定理。
`hregS` 是全程唯一的正则性假设（`Cond272` 内部由 `Step2.cond272_of_strict` 导出），未引入 `hc`/`hreg`。

**剩余**：`AprioriDecayAll`（**阻塞**，见上）；`Eq45Flow`（(4.5) 对 `u ∈ [s,t]` 一致——(4.5) 本身已证（`avg_bound_stochDom`），只差 p.51 的 `N^{-C}` 网连续性论证，与 `Step1.Lemma41Flow` 同一形状，**是形式化产物而非数学缺口**）。paper-deltas #72、#73。

### `RBM1D/Gauss/Step1Hyp.lean` — T116：`cont` 已卸，`lift` 归约（Claude Code 并行 agent，2026-09-21）

## 第 0 步结论：**`lift` 不能像 T108 的障碍那样绕开**

T108 的障碍之所以消失，是因为 `Lemma41Flow` 是两个**本已时间一致**的支配之间的传递，时间可以搭在指标集里。`NetLift` 结构上不同，差别在 `RBM.badSet`（`Defs/StochDom.lean:71`）：
**`StochDom` 把对指标集的并放在概率**里**。** 于是 `NetLift` 的假设只控制**每个 N 一个时刻**的 `P(A_{u(N)})`，而结论要 `P(⋃_{u ∈ [s_N,t_N]} A_u)`——不可数并。
**其中恰好一半是免费的**，已抽成定理：「每个 N 选一个时刻」本身就是一个序列，故失败界对**任意 N-依赖的选择** `θ(N)` 同时成立（`eventually_forall_measure_slice_le`，纯 `by_contra` + `Classical.choice`，不用网也不用连续性）。不免费的是把并放进 `P` 里——那要网。
**第二个独立发现**：即便有网，`lift` 对真实的族也不闭合——`Step1.loopInd` 带指示函数 `1(‖G_u‖_max ≤ 2)`，**它对 u 不连续**，网点上只能得到 `≤ 2 + o(1)`。（`Step1.lean` 的偏差清单已记过这一点。）故网引擎按**放宽形式**建：`netLift_of_relaxed`。

**`cont` 无条件卸掉**：`cont_gauss`，事件取全空间——`u ↦ ‖G_u − m‖_max` 对**每个样本**在 `[s_N,t_N]` 上连续，因为 `‖G_u − G_{u'}‖ ≤ η_t^{−2}(‖X‖+1)|u−u'|^{1/2}`。
假设只有 `|E| < 2`、`0 ≤ s N`、`t N < 1`；**不需要 `‖X‖ ≺ 1`**（常数是随机的但逐路径有限）。
**完整的 `Step1.Hyp` 现在存在**（已编译）：`step1Hyp_gauss` = `scaling`(T111) + `lemma41`(T108) + `cont`(新) + `lift`（唯一的随机层输入），外带 T107 的 `EntryBoundFlow`/`DiagBoundFlow`（仍无生产者）。

**`lift` 要闭合还缺四样**（按性质排）：(1) `‖L_{u,σ,a}‖` 对 u 的连续模——`gloop` 的望远镜估计，`Gauss/Envelope.lean` 只有包络与对**固定**核的差，都不是 u 的模；
(2) `Step1.aprioriRhs` 的缓变 `ζ(u') ≤ 2ζ(u)`，在指数 `n−1` 处要求网距小于 `c_n(1−t_N)`，即一条区制假设（`Φ` 层的计算已有：`step1Phi_eq` + `Lemma41FlowGauss.lean` 的缓变一节）；
(3) 多项式下界 `N^{−B} ≤ ζ`；(4) **Lemma 5.1 在阈值 `2 + o(1)` 处的版本——这是真正新的数学输入，且属 `Hierarchy/Step45.lean` 而非 `Gauss/`**。paper-deltas #74。

### `RBM1D/Gauss/CondStableInst.lean` — T119：`hIBP` 的局部律侧输入（Claude Code 并行 agent，2026-09-21）

**四条里三条卸掉，第八条只剩三条假设。** `trace_green_sub_mul_Eblk_stochDom_of_highProb` 只要 `hΩ`、`hFArow`、`hFAblk`——**从 8 条减到 3 条**。
编译验证：`condExpDiag_stochDom_of_highProb` 把四个槽全部填满（`hG := gaussIBP`，T104），**无 `convert`、无 `precomp_param`、无强制转换**，再喂进冻结的 `trace_green_sub_mul_Eblk_stochDom`。

- **`hloc` 卸掉**：`stochDom_normSq_green_diag_sub_Lmax`，就是 T112 预言的 `StochDom.of_indicator hΩ (diag_bound_gauss …)`；两边的指标类型无需强制转换即可合一。
- **`hrepl` 卸掉**：两点发现——(i) `greenMinorMat = minorGreen` 的识别**不需要事件也不需要额外假设**（`H_t` Hermitian、`Im z_t ≠ 0` ⟹ 行列式对每个 ω 都是单位）；(ii) 不去比较控制（`Ψ² ≺ L_max` 无生产者），而是**直接从 (4.2) 用控制 `L_max` 重做**。
- **`hstabP`/`hstabM` 卸掉，且 T112 对它的判断是错的**：`condStable_Lmax` 直接证出。关键是 **`Lmax_Hflow_le_inv_W`**——Ward 恒等式给出 `L_max ≤ η_t⁻²W⁻¹` **在全空间**成立，配 (4.1) 上的 `W⁻¹ ≤ 4L_max`；
  `t < 1` 是固定实数，`η_t` 与 N 无关，故 `L_max ≺ W⁻¹ ≺ L_max`。**`L^max` 本质上是确定性的，这根本不是局部律比较。**
- **`hΩ`(4.4) 未卸，全树无生产者**：已备好桥 `highProb_goodSet_of_stochDom`——由弱局部律 `‖G − m‖_max ≺ Ψ`（`MinorReplace` 已在用的形状）加多项式余量 `∀ᶠ N, N^τ Ψ_N ≤ δ_N` 即得。供给它就是 Step 1/2 的 (2.74)/(2.75)。

**⚠ 必须随 `L^max ≍ W⁻¹` 一起携带的警告**：上述论证**全部是固定时间的**。若 `t = t(N) → 1`（`Gauss/EntryBoundTime.lean`、`Gauss/Lemma41FlowGauss.lean` 所在、也是 §4 最终被使用的区制），
`η_t⁻²` 不再是常数，`stochDom_Lmax_inv_W` 作为 `≺` **失效**。agent 保留了一般接口 `LmaxRowProxy`（不读第 i 行的双边 proxy）+ `condStable_Lmax_of_rowProxy`，只是当前用常数 proxy `Λ_i := W⁻¹` 实例化；
**时间依赖区制下 proxy 要取小行的 `L^max`，那时比较才真的成为局部律输入。**
**剩余**：`hΩ`；`hFArow`/`hFAblk`（T88 的 `stochDom_flucAvg` 是确定性控制 `Ψ²`，`Ψ² → L_max` 的桥是另一件事）。paper-deltas #75、#76。

### `RBM1D/Gauss/Step6Hyp.lean` — T117：Step 6 七条假设的逐条勘察（Claude Code 并行 agent，2026-09-21）

| # | 假设 | 判定 | 依据 |
|---|---|---|---|
| 1 | `hH : Step6.Hierarchy` | **需新工作** | 即 **T58 的第四项交付物**。T76 的 `hasDerivAt_integral_Lval_hierarchy` **达不到**：那是**导数**陈述（`∂_v E[L]`），右端是 `primRhs`、不减 `K`、谱参数冻结；而 `Step6.Hierarchy` 是**积分形式**的 (5.20)@长度 2，用 `Uker` 写、漂移拆成 `DLK+DG`、且已取期望。缺口 = Duhamel + 漂移拆分 + 鞅项期望为零 |
| 2 | `hFD : FastDecayHyp` | **需新工作，且与 #1 绑定** | 它对 `DLK`/`DG` 量化，而这两者在 #1 产出前**根本不存在**，无法独立陈述 |
| 3 | `h5133` | 同上 | 对 `‖DLK‖` 的 `UnifDetDom` 界 |
| 4 | `h527 : Eq527` | **可达，已完成** | 见下 |
| 5 | `hq11` | **仅条件可达**，卡在一件缺失的**通用工具**上 | 由 `Steps.sharpLmK 1`（Step 4 的产出，Step 6 之前就有）**加一条一阶矩的反向桥** `\|Y\| ≺ Φ` + 确定性包络 ⟹ `∫\|Y\| ≺ Φ`。T77 的 `momentDom_of_stochDom` 只给**偶数矩** `∫\|Y\|^{2p}`，从不给 `∫\|Y\|`。该桥全仓库没有（已 grep） |
| 6 | `hG` | 需新工作，与 #1 绑定 | (5.134) 对 `DG` 的结构界 |
| 7 | `hq13` | 同 #5 | 经 `sharpLmK 1` 与 `sharpLmK 3` |

**已卸掉的**：`h527` = **(5.127)，且是精确恒等式——无误差项、无 `≺`、不带 `GaussIBP` 假设**（用的是 T104 已证的 `gaussIBP`）。
路线：`green_sub_smul_one_eq`(T83) 块平均 → 逐元素高斯分部积分 `integral_Hflow_mul_green_diag`(T83) → **块塌缩**（本单的承重新想法）：
因为 `Sblk L W i j = sbKre L (i.1−j.1)/W` **不依赖块内偏移**，`∑_k S_{pk} E[G_{pp}G_{kk}]`（**对角元**之积）**精确**塌成 `∑_b S^(B)_{ba} E[⟨GE_a⟩⟨GE_b⟩]`（**块平均**之积），无任何近似；再由 `∑_b S^(B)_{ba} = 1` 精确消掉 `m³` 项。
另卸 `hint2`（`int2_gauss`），并给出 `hq11`/`hq13` 的确定性第一步 `norm_quad11_le_integral`/`norm_quad13_le_integral`（对一般 `Sample B` 陈述，供将来造桥者直接用）。
**编译验证**：临时探针调用 `Step6.sharpExpect_step6 … hb.expect ?_ (eq527_gauss …) ?_ ?_ (integrable_sample_Lval …) (int2_gauss …) ?_`，恰好剩四个 `?_`——`eq527_gauss`/`int2_gauss`/`integrable_sample_Lval`/`hb.expect` 填的都是**真实槽位**且无搬运。探针已删。

**`sharpExpect_step6` 现状：7 条里还缺 6 条**（`hH`/`hFD`/`h5133`/`hq11`/`hG`/`hq13`）。

**agent 对拆单的建议（不是我写工单，是转述其结论）**：按**两个独立堵点**拆成两张，而不是拆六张。
**A：`hH`/`hFD`/`h5133`/`hG` 一张**——四者对 `DLK`/`DG` 量化，必须由造层级者存在性地产出，**其中三条在第一条完成前连陈述都写不出来**，不可分割；应路由给 **T58 作为第四项交付物**，并附上那条警告（按定义造出的 `duhamel` 会使 `Lemma510` 为假；绑定义务是三元组）。
**B：`hq11`/`hq13` 一张**——其真实内容是一件**属于 T77 `Gauss/Envelope.lean` 而非 Step-6 文件**的通用工具：一阶矩反向桥。
按 CLAUDE.md「造轮子之前先查」，agent **有意没有**在 `Step6Hyp.lean` 里就地造它（那会是个等着被重复的轮子）。B 的范围应是：(i) 给 T77 加 `unifDetDom_integral_of_stochDom`；(ii) 为 `lkErr` 之积供其两个输入（确定性包络 + 多项式下界）；(iii) 经 `norm_quad11_le_integral`/`norm_quad13_le_integral` 从 `Steps.sharpLmK` 收口。
**B 完全不依赖 T58，现在就能开工。** 一个勘察时发现的注意点：(ii) 需要 `η_u ≥ N^{-c}`，**这不是免费的**，来自 `Wℓ_uη_u ≥ 1`（由 (2.72) 推出），故该桥会带上这条假设。
**paper-deltas：本文件无新增**——(5.127) 与论文陈述完全一致；两条可积性是论文在 `‖G_u‖ ≤ η_u⁻¹` 下略去的 Lean 记账。

### `RBM1D/Hierarchy/ChargeReduce.lean` — T120：缺口从四个电荷收缩到一个（Claude Code 并行 agent，2026-09-21）

**三条归约全部走通**，而且我预先担心的两种失败模式都没出现：
* **共轭不移动谱参数**——`RBM.Gsig H z σ` 本身就把电荷编码成 `z ↦ conj z`，故 `Gsig_conjTranspose` 给出的是**同一个** `z_u` 上的 `(G_u(−))ᴴ = G_u(+)`；`K` 侧 `ξ = u·m(σ₁)m(σ₂)` 而 `u` 实，故 `conj(u·m(−)²) = u·m(+)²`。
  唯一需要新造的零件是 `conj (Θ_ξ)_{ab} = (Θ_{conj ξ})_{ab}`（由 `eq_Theta_of_mul` + `S^(B)` 元素为实的 `conj_SB_apply` 证出）——**已先 grep，仓库里原本没有任何 `Theta` 的共轭引理**。
* **循环性不需要拿不到的假设**——`L` 侧 `gloop_rotate` 是无条件的迹恒等式；`K` 侧 `kTwo_rotate` 要 `‖u·m(σ₁)m(σ₂)‖ < 1`，由已有的 `norm_mul_mSigma_lt_one` 从 `|E| ≤ 2`、`0 ≤ u`、`u < 1` 供给，**这三条在 `AprioriDecayAll` 的每个消费点都已具备**。

归约的**总代价**：`|E| ≤ 2`、`∀ N, 0 ≤ s N`、`∀ N, t N < 1`。没有新增任何东西。
**收口定理** `aprioriDecayAll_of_pp`：`Steps` + `AprioriDecayPP` ⟹ `StepGlue.AprioriDecayAll`；`(+,−)` 那半复用 T115 的 `aprioriDecay_pm`（未重复造），四路 case split 把 `(−,+)`/`(−,−)` 分别路由到两条归约。

**`K` 侧的结论：`(+,+)` 处的 `K` 并不缺**。`Band.Kval` 是定义，处处可用；Step 3 真正用的界 `Band.norm_Kval_two_le`（`Flow/Iteration.lean:380`）是对**任意** `I : LoopIdx`（`I.WF`、长度 2）陈述的，证明里把 `I` 拆成一般的 `⟨[s₁,s₂],[x,y]⟩`，**四个电荷全覆盖、无需改动、无额外假设**；`Step3.exists_norm_Kval_le` 同理；(2.73) 本身也是 `max_{σ,a}`。
**所以 `L − K` 在 `(+,+)` 处缺的，精确地只在 `L`（涨落）一侧。**

**agent 的一个观察（未形式化、未声称）**：`(+,+)` 处传播子的参数是 `ξ = u·m²`，`‖ξ‖ = u`，但只要 `|E|` 离 `±2` 有距离，`|1 − u m²|` 就离 0 有距离，故 `Θ_{u m²}` 的衰减长度是 `O(1)` 而非 `ℓ_u`——**这正是 `K_{(+,+)}` 无害、而困难全在涨落一侧的原因**。

## ⚠ 现在需要 Jun 裁的，精确到一条陈述

**`AprioriDecayPP`**：`|L_{u,(+,+),(a₁,a₂)} − K_{u,(+,+),(a₁,a₂)}| ≺ (η_s/η_u)⁴ (Wℓ_uη_u)^{−2}`，对 `u ∈ [s,t]` 与 `(a₁,a₂)` 一致。**除它之外什么都不缺。**
便宜的路子仍差整整一个 `A_u = Wℓ_uη_u`（T115：(2.73)+(2.59) 给 `≺ R·A_u`、(2.75) 给 `≺ A_u`，而大 `l` 处的 `S(2,l)` 要 `≺ (Wℓ_sη_s)^{1/2}`）——**这就是 §5.3 的那个因子**。
选择是：补一个 `(+,+)` 版的 §5.3 论证，还是改论文陈述。旁证仍是 Lemma 5.14 的证明（p.68）独立地排除了常值 σ。paper-deltas #72 已就地补充。

### `RBM1D/Gauss/Eq45Flow.lean` — T121：(4.5) 沿流一致化（Claude Code 并行 agent，2026-09-21）

**第 0 步判定：是 T108 的情形，不是 T116 的。** `Eq45Flow` 是两个**本已时间一致**的支配之间的传递——`u` 在假设与结论的 `≺` 指标集里都在；每一步都是关于单个 `(N, ω)` 的论断加上对指标集的存在量词，故**把时间放进指标集就够了：不用时间网、不用对 u 的连续性**。
与 `NetLift` 的区别很干净：那里假设只控制每个 `N` 一个时刻，而结论要 `badSet` 里对 `u ∈ [s_N,t_N]` 的并；这里根本不出现这种情况。
T116 的另外两个障碍也不存在——**`Eq45Flow` 完全没有指示函数**（故不连续的 `1(‖G_u‖_max ≤ 2)` 问题不会出现，放宽阈值的形式没必要），且 `Φ` 从不在两个时刻之间比较（不需要缓变）。
因此 T109 的 `‖X‖ ≺ 1`、T69 的 `|√u−√u'|·‖X‖`、T106 的预解式模、T101 的 Hölder 网**一个都没用上**。
`avg_bound_stochDom` 不能直接用（它把 `H` 与 `z_t` 里的 `t` 钉成同一个实数），但其证明是对确定性的 `norm_trace_green_sub_mul_Eblk_le` 做 `StochDom.of_det`，而后者对 `(N, ω, u)` 是逐点的——把那一步 `of_det` 在放大的指标集上重做即可。**未碰任何被消费的签名。**

**`Eq45Flow` 已卸**，条件是 (4.5) 的三个**带时间指标**的输入（与 T108 的 `EntryBoundFlow`/`DiagBoundFlow` 同构的接口）：`IBPFlow`（p.50 的高斯 IBP 式）、`FlucRowFlow`、`FlucBlkFlow`（两组系数的 (4.12)），外加 `0 < κ ≤ 1`、`|E| ≤ 2−κ`、`0 ≤ s N`、`t N < 1`。
**编译验证**：探针给出 `StepGlue.flow_hs1 … (eq45Flow_gauss …) h277 : StochDom … (Step3.flowXiLK … 1) (fun _ _ _ => 1)`——`eq45Flow_gauss` 填的是**真实的 `h45` 槽**，无强制转换、无 `convert`、无 `precomp_param`，结果正是 Step 4 的 `h1` 形状。
一条确定性的小发现：`lkErr_one_eq_norm_trace`——1-loop 的 `L − K` **等于** `‖⟨(G_u − m)E_a⟩‖`，对**两个电荷**都成立（`σ = −` 差一个复共轭，取范数后看不见）。这就是论文的单电荷 (4.5) 能覆盖 `LoopData L 1` 的原因。
`eq45Flow_of_inputs` 对**任意** `Sample B` 成立——传递本身与高斯无关。

**剩余**：三个输入未卸。`Lemma41Glue.trace_green_sub_mul_Eblk_stochDom` 与 T119 的 `CondStableInst` 只在**固定时刻**产出它们；把那些提升到流上是另一张单——**若那条路线走「固定时刻 + 网」而非「一开始就带时间指标」，T101 的网与 `‖X‖ ≺ 1` 就是在那里用**。paper-deltas #77。

## ✅ Jun 已裁 `AprioriDecayPP`（2026-09-21，Cowork 核对 PDF pp.64–72）

**论文不缺数学，走 (c)：收窄 p.70/p.72 的引用，(2.76) 陈述不改。** `(+,+)` 是非交错电荷（`σ₁ = σ₂`，(5.82)），
**Lemma 5.11（p.65）对 `n = 2` 同样适用**，(7.16) 情形 1 的演化核直接收缩；Lean 版已在 `SumZeroDyn.bound_nonAlt`。
缺的只是 `n = 2` 时 (5.83) 的自二次项 `Ξ_2·Ξ_2·A^{−1}` 的连续性自举（门槛 `A^{3/4}`，结论 `Ξ_2 ≺ A^{1/2} + R^{5/2}`，足够 `S(2,l)`；
再代一次得 `≺ R^{5/2}`，足够 `hs2`）。工单 **T122**；paper-deltas #72（原误编 #66 的重复行已删）。
**更正**：上文 T115、T120 两节的「旁证：Lemma 5.14（p.68）排除常值 σ」是误读——(5.96) 的「非常值」只出现在交错分支内部，常值 σ 走 Lemma 5.11。

### `RBM1D/Hierarchy/DecayBridge.lean` — T118 裁定：**两侧都不该改**（Claude Code 并行 agent，2026-09-21）

**`SumZeroDyn.lean:62` 那条注记的前提是错的**：两侧并非「形状对不上、必有一侧写错了」。
* **(a) 事件 vs `≺`**：`LKDecay` 是**忠于论文**的一侧——(5.75) 在论文里**本来就是** Def 2.1(i) 形式的概率界（p.63），其证明用的 (4.2) 本身也是高概率的；而 `Decay.lemma59` 的「事件上」形式是 T59 **有意的确定性内核**（`Decay.lean` 文件头自己写明，paper-delta #42），且它的 Deviations 一节**早就点名**了缺的那一步。**缺的是一个 wrapper，不是重塑。该 wrapper 现已写好并编译通过。**
* **(b) 抽象的 `F`/`EE`**：**根本不是形状不匹配**。`Lemma510` 约束的是 `Hierarchy` 的两个**无约束数据字段**，而 `Decay.lean` 界的是**具体**项；要接上就得**定义** `F`、`EE`——**那是 T58 的交付物**，不是 T118 的。

**决定性的不对称**：`F` 一旦具体，**`Lemma510` 是逐路径可证的**——它的 Ξ-输入不是假设，`Sample.xiLK` 本就**定义**为最小的这种界（`lkMax = ⨆ …`，`lkErr_le_lkMax` 已证），故 `Decay` 的假设 `‖D J‖ ≤ Φ A^{-|J|}` 对每个 ω 成立（取 `Φ := xiLK`）。`Lemma510` 一侧唯一真正随机的成分是衰减误差 `δ`。

**依赖计数（实测非猜测）**：`Hierarchy/Decay.lean` 的外部导入者 **0**（只有根文件 `RBM1D.lean`，全仓库没有任何 `RBM.Decay.*` 引用）——是叶子；`SumZeroDyn` 的两条占位符则被 **19 条签名**穿进 `lemma514_flow'`。**但成本不决定本案**：(a) 上 `Decay.lean` 没错，(b) 上两个定义都没错。

**⚠ fiat 风险（最重要的一条）**：`Gauss/DischargeBDG.lean:70ff` 警告 `duhamel` 可对**任意** `F` 按定义造出来。反过来读就是——**`Lemma510` 是防住这个 fiat 构造的唯一结构性护栏**（它说「这个 `F` 真的是 (5.15) 的漂移、且大小如 (5.77)」）。
**因此：把 `Lemma510` 弱化/重塑成「更好卸」是本工单上最危险的一步**，会让 fiat 的 `F` 更容易被合法化。安全方向是把 `F` **具体定义**成 `Decay` 的 `couplingLen + primBil + eG`，那时 `Lemma510` 变成可证且非平凡，内容正确地转移到 `duhamel`/`bdg`。
本文件**无 fiat 风险**：不加任何 `Hierarchy` 实例，不定义 `F`/`EE`/`mart`，只把 `LKDecay` 归约成关于 `X.Lval − B.Kval` 的**严格确定性逐路径命题**。

**已证**：`lkDecay_of_highProb`（wrapper：高概率的 `LKDecayEvent` ⟹ `SumZeroDyn.LKDecay`，**这把差异 (a) 作为陈述形状问题整个关掉了**）、`farInd_mul_le_of_loopDecay`（两种 Def 5.8 编码是同一个定义）、`mem_lkDecayEvent_of_loopDecay`、
**`loopDecay_lk_of_event`**——关键发现：这是**纯粹的重述**（`exact (Decay.lemma59 …).2`），因为 `X.Lval = gloop …` 与 `B.Kval = Kgen …` **按 `rfl` 成立**。**T59 的定理本来就是在讲 `LKDecay` 所讲的那个对象，什么都不需要翻译。**

**T74 的具体 `E⊗E` 改变了多少**：从「没有对象」变成「对象有了，还差一条恒等式与两个适配器」——仍缺 (i) `glueLoop = gloop (J k b b')`（T74 自己的 open item），(ii) `Gauss.eeTens : LoopIdx → LoopIdx → ℂ` 与 `Hierarchy.EE : … → LoopArg L ((n+2)+(n+2)) → ℂ` 的类型适配，(iii) **全仓库没有 `Band → Dims` 的转换**——每次 `Gauss → Hierarchy` 交接都会需要这块小管道。`F` 那一半 T74 没碰。

**给 Cowork/Jun 的建议**：(1) 不动 `Lemma510`/`LKDecay` 的形状，**唯一该做的改动是给 `LKDecay` 补上缺失的 `|L|` 一半**（见 paper-deltas #78，是补强，下游零成本）；(2) 不动 `Decay.lean`（叶子且按设计正确）；(3) 余下工作拆三张，**没有一张叫「调和两侧」**：(i) 把 `lkDecay_of_highProb` 的三个输入定量闭合 ⟹ 无条件的 `LKDecay`；(ii) `glueLoop = gloop` + `Band → Dims` 适配器 ⟹ 从 `Decay.norm_eTens_le` 解锁 `Lemma510.EE_le`；(iii) T58 的具体 `F` ⟹ `Lemma510` 其余部分（届时**逐路径**可证，但需要 `Ξ^{(L−K)}` 的先验多项式界——**此前无人记过**）。

### T123：一阶矩反向桥 + Step 6 的两条二次输入（Claude Code 并行 agent，2026-09-21）

**通用工具（加在 T77 的 `Gauss/Envelope.lean`，纯新增）**：`unifDetDom_integral_of_stochDom`——
`|Y| ≺ Φ` + 多项式增长的确定性包络 + `N^{-B} ≤ Φ` ⟹ **`UnifDetDom (∫|Y|) Φ`**（外加 `_of_nonneg` 变体）。
与 `momentDom_of_stochDom` 同一套好/坏事件分割，阈值取 `N^{τ/3}Φ`、例外指数 `D' = Kenv+B+1`；`UnifDetDom` 不容常数，故 `P(Ω)+1` 被 `N^{τ/3}` 吸收。
**两处有意的改进**：(a) **不需要 `Y` 的可测性**——分割跑在例外集的 `toMeasurable` 上，而其测度正是 Def 2.1(i) 已经界住的那个外测度；
(b) 包络取**「终于」形式** `∀ᶠ N, ∀ u ω, |Y| ≤ N^Kenv`，把 T77 的四个字段合并成一条，**严格更弱**，且是调用方真能证的（`∀ N` 在小 N 处不成立）。**未改动该文件任何既有签名。**

**`hq11`/`hq13` 已卸**：`quad11_unifDetDom`/`quad13_unifDetDom` 直接产出 `Step6` 要的 `UnifDetDom … (scale⁻¹)^2` / `^4`，
且对**任意 `Sample B`** 成立（不限高斯），输入是 `Steps`（即 `sharpLmK` 在 `n = 1, 3`）。
**编译验证**：探针把 `Step6.sharpExpect_step6` 实例化后**恰好剩四个具名目标** `hH`/`hFD`/`h5133`/`hG`——`hq11`/`hq13` 两个洞消失，无类型不匹配、无 `convert`、无强制转换。**剩下的四条全部绑在 T58 上**（`DLK`/`DG` 必须由造层级者存在性给出）。

**两条输入的实际情况与预期相反**：
* 控制的多项式下界**是免费的，已证出而非假设**（`N^{-(m+n)} ≤ (Wℓ_uη_u)^{-(m+n)}`，由 `ℓ_u ≤ L`、`η_u ≤ 1`、`W·L ≤ N`）；
* **不免费的是包络需要的 `η_u ≥ N^{-c}`**——作具名假设 `hη` 全程显式穿过（`lkErr_le_rpow` → `quad11/13_unifDetDom`），其出处（`Wℓ_uη_u ≥ 1` ← (2.72)）记在两处 docstring 里。
**小尾巴（未做，很便宜）**：`hint` 仍是假设——现成的 `integrable_sample_lkErr_mul` 是对**ℂ 值乘积**陈述的，而桥要的是 **ℝ 值**的 `lkErr · lkErr`；为保持对一般 `Sample` 的普适性没有就地特化。
paper-deltas：**无新增**（本单没有任何 Lean 陈述偏离论文）。

### `RBM1D/Gauss/Eq45FlowInputs.lean` — T124：三个输入「到网为止」已卸（Claude Code 并行 agent，2026-09-21）

**第 0 步判定：三个全是 T116 的情形，网不可避免。** T121/T108 的论证讲的是**传递**一个假设里本就带时间的支配，那里指标集是惰性的；**生产**一个则相反——把指标集放大成 `TimeIcc × V` 就等于把不可数的 `∃ u` 放进 `P` 里（`badSet`）。
**证据不是说辞**：每个固定时刻的生产者都经过一个**结构上要求 `Fintype` 指标**的步骤——`stochDom_flucAvg_*` 经 `stochDom_of_momentDom`（其 `hcard` 是对 `Fintype.card` 的多项式界），`condExpDiag_stochDom_of_highProb` 经 `stochDom_condRow_of_envelope`（带 `[∀ N, Fintype (U N)]`）。而 `TimeIcc` 是 `ℝ` 的子类型，矩+Markov 在它上面做不了。
于是 `‖X‖ ≺ 1`（T109）与 T101 的网机器**正是在这里**用上——与 T121 的预判一致。

**T101 的五条网定理全部要求控制是确定性的**（`Φ : ℕ → ℝ` 或 `ℕ → ℝ → ℝ`），而 (4.5) 的控制是 `L^max_u(ω)`——**既随机又依赖时间**，一条都用不上。agent 补了缺的引擎：`UnifDomIcc` + **`stochDom_timeIcc_of_unifDom`**（带随机且时间依赖控制的网提升）。
控制侧的输入全部**无条件证出**：`highProb_flowNetEvent`（后半就是 T109）、`rpow_neg_le_Lmax_flow`（`N^{-2} ≤ L^max_u`，即 `hζlow`）、以及**新的确定性模 `Lmax_flow_le_add`**：`L^max_v ≤ L^max_u + (η_u⁻¹+η_v⁻¹)‖G_u−G_v‖`，由它得 `Lmax_flow_slow_of_net`。
三个生产者 `ibpFlow_of_unifDom`/`flucRowFlow_of_unifDom`/`flucBlkFlow_of_unifDom` **逐字**产出 `IBPFlow`/`FlucRowFlow`/`FlucBlkFlow`（`exact`，无 `convert`、无强制转换），`eq45Flow_of_unifDom` 喂进冻结的 `eq45Flow_gauss` 得到 `StepGlue.Eq45Flow`——**这就是所要的探针，已类型检查通过**；其结论与 T121 已验证能填 `flow_hs1` 的 `h45` 槽是同一个项，故下游检查自动沿用。

**T119 的固定时间警告已正面处理**：从夹逼 `W⁻¹/4 ≤ L^max_u ≤ η⁻²W⁻¹` 推缓变要付 `4η_v⁻²`，在 `t_N → 1` 时是多项式大——**所以没有用 `stochDom_Lmax_inv_W`**，只用了**下半边**（在流的好事件上对每个时刻都成立），缓变本身走真正的模。代价是一条显式可查的假设 `hfine`，与网距条件相容。**因此不需要 `LmaxRowProxy`**——本文件从不对 `u` 一致地做 `L^max ≍ W⁻¹` 的比较。

**`Eq45Flow` 仍非无条件**，余下三类：(1) **`hΩ`**——(4.4) 在**每个** `u ∈ [s,t]` 上成立，即 T119 留下的那个 `hΩ` 的 u-一致版（它本身也是一条网命题）；
(2) **三个 `hfix`**（固定时刻的输入作 `UnifDomIcc`）——**注意这些即便在固定时刻也还没有**：`stochDom_flucAvg_*` 仍带未卸的 `hsmall`（`FlucBound` 参数的**尺寸**；唯一无条件的实例 `stochDom_flucAvg_blockAvg_env` 控制是常数），`condExpDiag_stochDom_of_highProb` 仍带 `hΩ`；
(3) **三个 `hHol`**（`u` 的模）——Green 函数那半是 T106 的 `norm_green_flow_sub_le`，而 **`condExpDiag` 那半是真正新的估计**，且**不是逐点模的推论**，因为随机常数 `‖X‖` 落在行积分内部。paper-deltas #79。

### `RBM1D/Hierarchy/Step2PP.lean` — T122：常值电荷经 Lemma 5.11 `n = 2` 解决（Claude Code 并行 agent，2026-09-21）

**⚠ 撤回一条此前的记载**：上面 T115、T120 两节写的「旁证：Lemma 5.14（p.68）排除常值 σ」是**误读**——「非常值」只出现在 (5.96) 的**交错**分支内部。
`StepGlue.lean` 的文件头与 `AprioriDecayAll` 的 docstring 已由 agent 就地加了 Correction 说明；`ChargeReduce.lean` 的头里没有这句话（已核对全文）。

**第 0 步的决定：挂在事件/逐路径层，既不是 `≺`-前缀层，也不是矩层。** 用 `RBM.le_of_bootstrap_prefix`，但**在高概率事件内逐路径跑**——正是 Step 2 路线 A（`Step2.jS_highProb`）对 `(+,−)` 已经在做的事。
* **工单设想的 (a)（在前缀 `[s,v]` 上重新实例化 `Lemma514`）确实行不通**，工单自己的预判是对的：`Step3.Lemma514` 的假设与结论都是 `≺` 陈述（关于 `N → ∞` 的序列），而连续归纳要的是**每个固定 N** 上同一条路径取值之间的蕴含。前缀限制本身免费（`Cond272` 可限制），但没有东西可被自举。
* **(b)（矩层，`Step2Moment` 那套）不需要**：`u ↦ Ξ^{(L−K)}_{u,2}(ω)` 是有限个连续函数的 max，**对每个 ω 都连续**。于是改进可假设在事件上、归纳逐路径跑、再用并界推回 `≺`——**比造 `MomentHypPP` 严格便宜**（不需控制收敛、不需 Hölder 网），而且这就是论文 §5.3 自己的结构。

**`AprioriDecayPP` 没被卸掉，这条路线也卸不掉它**（paper-deltas #80：它严格强于 (5.83)@n=2 能给的）。
**但它的所有消费者现在都不再需要它**：`flow_sharpLoop_glue_of`/`flow_steps45_glue_of`（及 `…_flowAs` 特化）直接产出 `Steps.sharpLoop`/`sharpLmK`/`sharpDecay` 的字面形状——探针做了类型指定验证，**无 `convert`、无 `precomp_param`、无强制转换**；第二遍 (5.83)（用 `Ξ_{u,1} ≺ 1`）**不需要第二次自举**，与工单预期一致。`ChargeReduce.aprioriDecayAll_of_pp` 一字未动。

**剩余假设**：`BootPP.step`——Lemma 5.11 在 `n = 2` 的**事件（停止）形式**，即 `Step2.Hyp.mart` 的类比物。
它的 `≺` 层影子 `xiLK_two_improve` **已在本文件证出**，所以被假设的东西是看得见的；推出 `step` 需要把 `SumZeroDyn.Hierarchy.bdg` 用到停止鞅上——与 Step 2 路线 A 是同一批随机层工作。
下游不变：`h514`、`StepGlue.Eq45Flow`、`Step45.FlowEq548`、`hregS`、`Steps`。（小注：`xiLK_two_le` 与 `RBM.Step3.xiLK_two_le` 同名不同命名空间，无碍。）

### T125：`Step1.Hyp.lift` 已闭合，`Step1.Hyp` 完整（Claude Code 并行 agent，2026-09-21）

**第 0 步结论：阈值 `2` 只是证明常数，推广走通了——于是 T116 标为「真正新的数学输入」的第 (4) 项根本不是新数学。**
`2` 只出现在三处浅层：事件 `gmaxEvent` 的定义、`continuity_recursion` 的假设 `hY1`、以及 `lemma_5_1` 证明里用 `loopMax_one_le` 卸 `hY1`。它**只通过基例 (5.6)** 进入 §6 的归纳，从不碰 (6.4)、(6.10)–(6.13) 或最后的 `X ≺ A + A^{1/2}X^{1/2}`。
agent 没有复制粘贴，而是**从现有 `C₀ = 2` 的机器重标度推出**推广版：取 `λ = 2/(C₀+2) ≤ 1`，`Y_n ↦ λ^n Y_n`、`T_n ↦ λ^n T_n`——指数 `2l+1` 与 `2(m−l)−1` 相加为 `2m`，故 (6.4)(6.13) **不变**，而 `Y₁ ≤ C₀` 变成 `Y₁ ≤ 2`。**§6 一行都没有重证。**
新增（`Loop/ContinuityAssembly.lean`，纯追加）：`continuity_recursion_thr`、`gmaxEventThr`（+ `gmaxEvent_eq_thr` 在 `C = 2` 处为 `rfl`、`gmaxEventThr_mono`）、`lemma_5_1_thr`、`lemma_5_1'_thr`。

**四项全部卸掉**（`Gauss/Step1Hyp.lean`，纯追加）：
(1) `u` 的模——`norm_gchain_sub_le` 是对 `gchain` 的确定性望远镜估计，`norm_Gsig_sub_le_green_sub`（`G(−) = G(+)ᴴ`）让**两个电荷一次处理完**，不需要另写共轭预解式的估计；高斯形式 `norm_Lval_sub_le_sqrt`。
(2) 缓变——承重的观察是 **`aprioriRhs_eq`：两个 `ℓ_u` 相消，(2.73) 右端只通过 `η_u` 依赖时间**，于是缓变塌成 Bernoulli（`pow_one_sub_le_two_mul`）。
(3) 多项式下界 `rpow_neg_le_aprioriRhs`（由 `ℓ_s·W·η_u ≤ W·L ≤ N`）。
(4) `eq58_seq_thr`（把 `lemma_5_1'` 换成 `lemma_5_1'_thr`），**固定阈值 `C₀ = 3`**，不是 `2 + o(1)`。

**`lift` 已闭合**：`netLift_gauss`（用 T116 的 `netLift_of_relaxed`，事件取 `{‖X‖ ≤ N}` 即 T109 的 `‖X‖ ≺ 1`，网距 `N^{−A}`，`A = 2(c(n+1)+n+3)`）。
**两个完整的 `Step1.Hyp` 生产者**，其中要紧的是 **`step1Hyp_gauss_of_scale`**：`rpow_neg_one_le_one_sub_of_scale_ge` 表明区制假设是**免费的**——`N^c ≤ Wℓ_tη_t` 配 `Wℓ_t ≤ WL ≤ N` 给出 `η_t ≥ N^{c−1} ≥ N^{−1}`，而 `η_t ≤ 1 − t_N`（因 `Im m ≤ 1`）；**而 `N^c ≤ Wℓ_tη_t` 本来就是 `Step1.step1` 的假设**。
于是 `step1Hyp_gauss_of_scale` 在**恰好是 `Step1.step1` 已有的那组假设**下造出完整的 `Step1.Hyp`，**随机层输入 `hlift` 消失且没有任何未生产的东西顶替它**；只余 T107 的 `EntryBoundFlow`/`DiagBoundFlow`。

**一处可回收的重复（留给将来允许改那两个文件的工单）**：`eq58_seq_thr` 与 `Step1.eq58_seq` 重复约 50 行，`lemma_5_1_thr` 与 `lemma_5_1` 重复约 130 行；
若允许改 `Hierarchy/Step1.lean` 与 `Loop/ContinuityAssembly.lean`，应把旧的定义成新的在 `C₀ = 2`/`C = 2` 处的特例并删掉重复。paper-deltas #74 已改写为已解决，另加 #81、#82。

### T131：T123 的可积性尾巴已收（Claude Code 并行 agent，2026-09-21）

`integrable_sample_lkErr_mul_real`（ℝ 值版，由 ℂ 值的 `integrable_sample_lkErr_mul` 经 `Integrable.norm` + `norm_mul` 一行得出——`Sample.lkErr` 按定义就展开成 `‖Lval − Kval‖`，陈述不用改写），
据此给出 **`quad11_unifDetDom_gauss`/`quad13_unifDetDom_gauss`**：与一般版签名相同但**去掉了 `hint`**。一般 `Sample B` 版逐字未动，仍带 `hint`（T123 有意保留的普适性）。
一个放置上的判断：`FirstMoment` 节绑了 section variable `Ω`，会遮蔽高斯的 `RBM.Gauss.Ω d`，故两条特化另起一节。paper-deltas 无新增。

### `RBM1D/Gauss/GoodSetFlow.lean` — T130：(4.4) 的 u-一致版（Claude Code 并行 agent，2026-09-21）

**给 T126 对接用的确切陈述**：`highProb_goodSetFlow_of_localLaw : … → HighProb (P d) (goodSetFlow d E s t δ)`——
结论**逐字**就是 T124 的 `hΩ` 类型，可直接喂；若 T126 想要 `≺` 形式而非事件，中间结果 `stochDom_timeIcc_localLaw` 更合适。
输入的弱局部律写成 `LocalLawUnifIcc d E s t Ψ`（即 `UnifDomIcc` 形式的 (2.74)/(2.75)）。

**`hΩ` 已有生产者**，条件只有：`hll`（弱局部律，Steps 1/2 的 (2.74)/(2.75)，工单说明不在此单范围）、`hmargin`（T119 那条桥的多项式余量）、以及两条纯确定性的区制边条件 `hKbig`/`hΨlow`（网的代价，非新数学）。
核心是 `stochDom_timeIcc_localLaw`：**把弱局部律的时间搬进 `≺` 的指标集**——用 T124 的引擎（`γ = 1/2`、事件 `{‖X‖ ≤ N}`、网距取引擎自带的最小值，故**不需要额外的 `hδ` 假设**）。

**`t_N → 1` 的坑在这里不咬人，而且不是碰巧**：弱局部律的控制 `Ψ_N` 是**确定性且不依赖时间**的，故引擎的 `hslow` 退化成 `Ψ_N ≤ N^ε Ψ_N`。
**全文件没有出现 `L^max`**，`stochDom_Lmax_inv_W` 一次都没被提及；`η_{t_N}` 只出现在**确定性** Hölder 常数里（单边，`K` 自由）。
另：**这里没有指示函数不连续的问题**（`GoodEvent` 是闭条件），故 T116 的 `netLift_of_relaxed` 不需要。
**探针验证**：`eq45Flow_of_unifDom (hΩ := highProb_goodSetFlow_of_localLaw …)` 以及 `ibpFlow_of_unifDom`/`flucRowFlow_of_unifDom`/`flucBlkFlow_of_unifDom` 用同一具名参数全部 elaborate，无强制转换、无 `convert`。paper-deltas #83。

### `RBM1D/Hierarchy/EEBridge.lean` — T127：三块管道全部打通（Claude Code 并行 agent，2026-09-21）

**(a) `glueLoop = gloop` 已证，T74 的遗留项关闭。** 它需要的共轭事实**确实成立**，而 `ChargeReduce` 的 `Gsig_conjTranspose` 正是缺的那一步。新恒等式
`Gsig_mul_conjTranspose_prodList_mul`：`G_σ · (prodList …)ᴴ · E_c = prodList … (rflip t l c)`——**共轭把链反转并翻转每个电荷**，
所以 `E⊗E` 里共轭后的第二个因子**确实是**反着读的 σ̄-loop。**这把 T74「读作复共轭」的约定从「采用」升级成「证明」**（paper-deltas #84 已更新）。
`Decay.norm_eTens_le` 对其抽象粘合**假设**的三条性质，对具体的 `glueIdx` **全部证出**（`glueIdx_wf`、长度 `2n+2`、含 `b`、含锚点）；
agent 还用 `#eval` 在一个具体 3-loop 上核对：电荷 `[F,T,T,F,T,F,F,T]`、标号 `[2,3,1,2,4,1,0,3]`、长度 8 = 2·3+2——切边在两半各出现一次、后半反转且翻转电荷，正是 (5.23)。
**(b)** `leftArg`/`rightArg`（`SumZeroDyn.QQ` 与 `bdg` 字段已在用的那个 `Fin.castAdd`/`natAdd` 拆分）+ T74 的 `toIdx` ⟹ `eeField`，其类型**逐字**是 `Hierarchy.EE` 的（探针已验）。
**(c) `RBM.Band.toDims`**——全仓库缺的那块管道，逐字段对应，四条投影都是 `rfl`。**通用基础设施，以后每次 `Gauss → Hierarchy` 交接都能用。**

**`Lemma510.EE_le` 现在逐路径可得**（`norm_eeField_le` 与其被积函数/控制对逐字一致），但**作为 `≺` 陈述还差一步，agent 没有伪造**：
`≺` 的过渡要吸收 `N^τ` 前因子（免费）**与**一个可加项 `m·W·L·N^{-D}`，后者需要**控制的多项式下界**——`StochDom.of_det` 没有可加余量、`Step1.stochDom_of_highProb` 要求无前因子的界。
**这是真缺口而非记账**，形状同 T123/T125 的 `rpow_neg_le_aprioriRhs`，值得单独一张单；agent 刻意没在本文件里造通用吸收引理（按「造轮子之前先查」，它该在 `Defs/StochDom.lean`）。
**无 fiat 风险**：不造 `Hierarchy` 实例、不定义任何字段、不弱化 `Lemma510`/`LKDecay`；装上 `eeField` 仍要拖着 `duhamel`/`bdg`，T118 指出的护栏完好。

### T128：(4.5) 的固定时刻输入（同一批 agent）

**两条涨落平均的输入已卸，走的是 T94 的迭代路线而非已被证伪的 `hsmall` 路线**：`unifDomIcc_flucRow_condExpDiag`/`unifDomIcc_flucBlk_condExpDiag`，
归约到一条假设——`FlucGain` 在 `ρ ≤ 1` 处、对 `u` 一致。`flucRowFlow_of_gain`/`flucBlkFlow_of_gain` 以 `exact` 填进 T124 的槽（`y = condExpDiag`，与 IBP 槽一致）。
底下三件新机器：`UnifDomIcc.trans`；**`unifDomIcc_of_moment`——Markov 这里不需要任何基数假设**（`UnifDomIcc` 是逐指标**且逐时刻**地界住失败概率，对 `u` 的并只由网来取；故需要对 `u` 一致的只有 `N` 上的阈值，而 T94 的矩界是逐 `(N,u)` 的确定性不等式，其唯一的 `∀ᶠ N` 部分根本不提时间）；
**`unifDomIcc_const_Lmax`——T88/T119 留下的 `Ψ² → L^max` 桥**：在流的好事件上只用到**下半边** `W⁻¹/4 ≤ L^max_u`（对每个时刻都成立且不花 `η⁻¹`），故给定 `hΦW` 后该桥是免费的。
**`hfixIBP` 未卸**，缺的环节精确为：`CondStableInst.condExpDiag_stochDom_of_highProb` 的 `UnifDomIcc` 版——它在固定 `t` 处是 `StochDom`，其 `∀ᶠ N` 阈值不知道对 `t` 一致（整条链 `stochDom_condRow_of_envelope`/`condStable_Lmax`/`stochDom_normSq_green_diag_sub_Lmax` 都是先定 `t` 再量化 `N`），且仍带该时刻的 `hΩ`（→ T130）。
与涨落平均那侧不同，**这里没有单一的逐 `(N,u)` 确定性估计可供重新量化**，要一致化就得重跑那条链，而那些文件不在本单可改范围。
**还有一处接口缺口**：`FlucGain` 在 `ρ ≍ Ψ` 处仍非定理——T113 只证了**有界字长**形式，而 `norm_integral_prod_epsHom_flucDiag_le`/`integral_norm_flucAvg_pow_le_iter` 却对**所有**字消费 `FlucGain`，尽管它们实际构造的字长 ≤ `2p`。
**补上这个「按字长分级的 gain 接口」是 `Gauss/FlucIter.lean` 的一张单**（不是本单能改的文件）。paper-deltas #85。

### `RBM1D/Hierarchy/LKDecayQuant.lean` — T126：`LKDecay` 定量闭合（Claude Code 并行 agent，2026-09-21）

**`lkDecay_of_flowInputs : |E| < 2 → 0 ≤ s → t < 1 → FlowInputs → SumZeroDyn.LKDecay`**——即 **`LKDecay` 在 T130 的输入之外无条件**，没有别的假设。
探针 `lemma514_flow_of_flowInputs` 把它以 `exact` 填进 `SumZeroDyn.lemma514_flow'` 的 `hdec` 槽，无 `convert`、无强制转换。

**(1)(2) 两条定量输入都闭合了。** 半径取 `ℓ = ℓ_u·N^{τ/2}`（`radius_le`），误差两半各自成引理（`term1_le`/`term2_le`）。
**这里需要一件仓库里没有的分析输入**：`Decay.cKdecay` 的**多项式上界** `cKdecay_le_bound`（`cKexp m = m + 2m² + 1`），由 `cor35Const_le_bound` 经 `2/(1−e^{−λ}) ≤ 4/λ` 得出。
**一个值得记的结构性事实**：衰减指数对 `u` **一致**有下界，靠的是一个两边都有利的二分（`ℓ̂(u) = min((1−u)^{-1/2}, L)`）——
`L√(1−u) < 1` 时 `ℓ_u = L`，而目标半径 `ℓ_u N^τ` 已超过环的直径，**陈述本身是空的**（`loopDecay_of_half_lt`）；
`1 ≤ L√(1−u)` 时 `ℓ_u√(1−u) = 1` **恰好**成立，故 `cor35Rate(1−u)·2m(ℓ+2) ≥ (c₀/2)N^{τ/2}` **与 `u` 无关**，同时 `1−u ≥ N^{-2}` 使 `cKdecay` 保持多项式。

**(3) 按指示作具名假设 `FlowInputs`**：它把 T130 负责的 `GoodEvent` 高概率一致性，与 `LDERow`/`LDECol`/(2.76) 的条款打包成**同一个事件**，外加数值束 `Φ_N√(ε_N) ≤ N^{-D'}`（paper-deltas #86）。
**`LDecay`（(5.75) 的 `|L|` 半）也顺手出来了**，按 Cowork 的裁定作**独立谓词**、不并进 `LKDecay`；确实是同一个证明——`Decay.lemma59` 返回合取，两条结论取自同一事件的 `.1`/`.2`。`SumZeroDyn.LKDecay` 一字未动。paper-deltas #78 已改写。

### `RBM1D/Gauss/CondExpMod.lean` — T129：`condExpDiag` 的 u-模（Claude Code 并行 agent，2026-09-21）

**第 0 步：随机常数路线成立，常数就是 `E_k[‖X‖]`，且 `E_k[‖X‖] ≺ 1`（`stochDom_condRow_norm_Xmat`，对 `k` 一致）。**
模本身 `norm_condExpDiag_flow_sub_le` **除 `|E| < 2`、`u,v < 1` 外无任何假设**。

**但走的不是 T112 的路，这是本单最有意思的一点**：`stochDom_condRow_of_envelope` **用不了**——它要被支配量有**确定性包络**，而 `‖X‖` 没有（高斯坐标无界）。
替代它的是「**`E_k` 只重采一行**」这个结构事实：`X(rowSplit k ω ω')` 与 `X(ω)` 只在第 k 行/列不同，于是
`‖X(σ)−X(ω)‖² ≤ 2·rowFrobSq_k(ω') + 2·rowFrobSq_k(ω)`，其中 `ω` 那半**逐点确定性**（`rowFrobSq_k(ω) ≤ 2‖X(ω)‖²`），`ω'` 那半有**精确期望** `≤ ∑_j S_{kj} + ∑_i S_{ik} = 2`；
平方根用 `x ≤ (1+x²)/2` 去掉，不需要 `∫√· ≤ √∫·`。
**关键细节**：`rowFrobSq_k(ω) ≤ 2‖X‖²` 用的是**锐的** `∑_i |M_{ik}|² ≤ ‖M‖²`（由 `(MᴴM)_{kk}` 加 C\*-恒等式证出）——**粗的 Frobenius 界会多花一个 `N`，`≺ 1` 就没了**。
于是 `E_k[‖X‖]` 被 `‖X(ω)‖` 的**逐点**多项式支配，T109 一条就够，**完全绕开 T112**。

**T124 的引擎接受随机 Hölder 常数，不需要新引擎**：`stochDom_timeIcc_of_unifDom` 的 `hHol` 虽写成确定性 `N^K`，但限制在高概率事件 `Ξ` 上，而 T124 取的 `Ξ = flowNetEvent` 已含 `{‖X‖ ≤ N}`——
其 docstring 本来就预见了这种用法。交付的 `norm_condExpDiag_flow_sub_le_rpow` 就是 `hHol` 的形状（指数 `1/2`、常数 `N^K`、在 `flowNetEvent` 上），代价是一条区制假设（paper-deltas #87）。
**未做（有意）**：没有组装 `ibpFlow_of_unifDom` 的完整 `hHolIBP`——那要混入 Green 函数那半与 `u·m²·∑_k S_{ik}(G_{kk}−m)` 的前因子，而 T128 正在改那个文件、拥有其形状；
组装方法（三角不等式 + 两个额外项，总常数 `η⁻²(2N²+2N+9/2) + η⁻¹ + 1`）写在 `norm_condExpDiag_flow_sub_le_rpow` 的 docstring 里。

## T132 第 0 步：矩 Duhamel 的消费者清单、接口草案与评估（Claude Code，2026-09-21；**未写任何 repo 文件，等 Cowork 审**）

**建议：Proceed with modifications（开工，但按下面五条改规格）。** 三个 scratchpad 探针把最可疑的分析前置都验成了正面结果。

### 1. 消费者清单（穷尽，非抽样）
全仓库 `duhamel|bdg` 的非注释命中只有 8 处，其中 4 处是 `Hierarchy` 的字段声明本身，**真正的使用点只有 5 个**：
`SumZeroDyn.bound_nonAlt`(duhamel，逐路径)、`bound_qGood`(duhamelQ，逐路径)、`term1M`(bdg)、`termM`(bdgQ)、`Step2.step_bound`(duhamel@n=0)；
外加 `mart_of_QV` 一个已经把 `bdg` 形状抽象成参数的泛化点。传递下游：`lemma514_flow(')` → `LKDecayQuant.lemma514_flow_of_flowInputs`；`Step2.jS_highProb` → `jS_stochDom`/`aprioriDecay`/`step2`。

**重要的否定结果：血缘半径很小。** `Step3.Lemma514` 的全部下游（`hyp_flow`/`flow_sharpLoop`/`flow_steps45`/`StepGlue`/`Step2PP`/`Thm221`）都把 `Lemma514` 当**谓词假设**、对 `Hierarchy` 完全参数化；`Steps` 的两个字段同理。
**只要带撇路线重新生产出 `Lemma514` 与那两个字段，下游一行都不用改。** 另有 7 条只碰 `H.F`/`H.EE` 的定理在带撇结构里**逐字存活**。
**现成先例**：`Step2Moment.MomentHyp` 已经是本单想做的事在 `n = 2` 上的成品（无停时、无鞅），其文件头明写唯一补不上的就是 `step` 字段，理由逐字是本单要解决的那条——**T132 的产出应当直接落成 `MomentHyp.step`，而不是另造带撇的 `step_bound`。**

### 2. 接口草案（已编译验证）
`MomentDuhamel` 对**一般 `Sample B`** 陈述：保留 `F`/`EE`（类型不变 ⟹ **`Lemma510` 一字不改可复用**），**删去 `mart`/`martQ` 两个数据字段**，四条 Prop 合并成两条不等式。
**Gauss → Band 的交接全是 `rfl`**（`band.P`/`sample.H`/`band.Idx`/`sample.Lval` 四条已逐条编译验证），故高斯生产者可无摩擦实例化。
**一个意外的好消息**：原以为最硬的前置 `∂_u U_{u,v}` 是**免费的**——`edgeKer` 里跑动时间只出现在 `1 − (sξ)S^{(B)}` 中、是**仿射**的，于是 `Uker` 对 `u` 是仿射因子之积。agent 已把 `hasDerivAt_edgeKer` **零 sorry 证出**（无假设、不需要 ODE、不需要 `Propagator/Deriv.lean`）。

### 3. 评估
**(a) fiat 护栏：原地不动，但可以加固到严格优于现状。** 带撇接口在草案形态下同样可被 fiat 满足（取 `F` 巨大即可），`Lemma510.F_le` 仍是唯一护栏——与 T74/T118 一致。
但有一处真实改善：T74 那个具体手柄是「取 `mart :=` 残差 ⟹ `duhamel` 对任意 `F` 成立」，而**带撇结构没有 `mart` 字段，这个手柄消失**；剩下的钝 fiat 被 `Lemma510.F_le` 正面挡住。
**净效果：护栏覆盖率从「两个数据字段只管住一个」变成「一个数据字段全管住」**（旧接口里 `mart` 的 fiat 是 `Lemma510` 管不到的）。
**(b) T74 障碍 2（残差路径依赖）——真正被克服**：带撇路线**从不构造** `∫U∘F(H_u)du` 再去求导，而是对 `u ↦ E|Φ(u,H_u)|^{2p}` 求导，其中 `Φ(u,·)` 是**单时刻矩阵的函数**；路径积分只在**结论**里作为微分不等式的积分出现。代价转移到「`Ψ` 对 `(u,M)` 联合 `C²`」。
**(c) T74 障碍 3（无漂移）——被溶解而非转移**：不再需要 `𝓛F = 0`，漂移项保留成结论里的积分项；而 `MomentGronwall.genMomentPt_le` **本来就带着那一项**，`DischargeBDG` 只是把它扔了。**这是全案最便宜的一块。**
**(d) 模型无关性：部分为真，工单措辞偏强。** 生成元恒等式只用一时刻边缘律（**paper-delta #49 从负债变成资产**），但其证明用 Stein 恒等式，非高斯 entry 分布要加累积量修正——所以是「对同一一时刻边缘律的不同流无关」，**不是「对模型无关」**。
接口后果：带撇件**不能替换**一般消费者，只能**实例化**它们（生成元只活在 `Dims`/`MatrixStein` 上）。

### 4. 五条修改建议
1. **把 T134 的逐点漂移恒等式作为 `MomentDuhamel` 的必需字段**——它在**定义层钉死 `F`**，使 `Lemma510` 从「防伪造约定」升级为「关于确定对象的命题」，正是 T118 裁定里那条安全方向的接口化版本，**而且旧接口做不到**（其 `duhamel` 是积分形式、残差路径依赖，钉不死 `F`）。**不加这条，本单收益只剩记账整洁。**
2. 结构陈述在一般 `Sample B` 上，高斯卸载单独一节（必要时按 CLAUDE.md 下沉到 `Defs/`）。
3. 结论取 `e^{p(2p−1)(v−s)}` 形状而非工单字面的 `2∫ + (C∫)^{1/2}`——后者对应 `y' ≤ a + b/y`，**不是** Mathlib `gronwallBound` 的形状，要自写比较引理；改用现成的 `momentIntegral_le_exp` 零损失，记一条 paper-delta 即可。
4. 不做带撇的 `bound_nonAlt`/`bound_qGood`/`step_bound`，带撇件直接输出 `≺` 结论，把「逐路径 → `≺`」两段合成一段。
5. **三块无主缺口写进工单**：`(z,M)` 联合 `C²` 的预解式（补进 T134 规格，其工单文字里没有）、参数积分的 `u`-一致控制（T133 给的是固定 `u` 的界）、`Lp` 的可积性字段。

### 5. 依赖标注
`momentDuhamel(Q)` 的**陈述**与 `term1M'`/`termQ'` 的推出**不依赖 T133/T134**，现在就能落地；**高斯卸载**依赖两者，且需 T134 额外补 `(z,M)` 联合 `C²`；`∂_u Uker` 不依赖任何人、已证。
**若只做一半**：结构 + 两条带撇消费者 + `∂_u Uker` 可先行落地并编译通过，高斯卸载留作 T132b。

### `RBM1D/Gauss/LoopC2.lean` — T133：T76 的 `TestFun` 缺口已补（Claude Code 并行 agent，2026-09-21）

**缺的确实只有 Leibniz 那一步。** 新的二阶乘积法则 `fderiv2_clm_apply_apply` 是**真正 Fréchet 的**（用 `hasDerivAt_dir2'` + `HasDerivAt.clm_apply` 的线导数装置证出，不是逐线版），
由它得 `bddC2C_clm_apply` ⟹ **`BddC2` 对乘积封闭**（常数 `C₀ = a₀b₀`、`C₁ = a₀b₁+a₁b₀`、`C₂ = a₀b₂+2a₁b₁+a₂b₀`），矩阵乘法是其实例；另对 CLM 复合、常数、求和封闭。
载体是新的定量类 `BddC2C F C₀ C₁ C₂`（把 T72 `BddC2` 的三个存在量词具名化，且取值于任意实赋范空间，以覆盖矩阵值的部分积），两个方向的转换都有，故 T72 的 `TestFun.of_bddC2` 原样可用。
**预解式的 Fréchet `C²` 其实早就在了**（T72 的 `contDiff_resH` 等本来就是 Fréchet 的、在全空间上、经 `hermCLM`），`bddC2C_resH` 只是打包：`‖G‖ ≤ η⁻¹`、`‖DG‖ ≤ η⁻²`、`‖D²G‖ ≤ 2η⁻³`。

**loop 的导数界**：`n` 个因子的 `foldr` 积满足 `(Bⁿ, nBⁿ, n²Bⁿ)`——**归纳精确、无松弛、对因子个数无任何限制**（常数只是按 `n²Bⁿ` 增长）。
`bddC2_loopObs` 取 `B = 2(1+η⁻¹)³` 落成 `η⁻¹` 的显式幂。**`TestFun` 已由探针验证**：`testFun_loopObs_of_im_le` 填上 T76 那个 hook 的三个空字段；
端到端的 `hasDerivAt_momentIntegral … (testFun_momentFun_loopObs …)` 也编译通过——即 `d/du E|L_{σ,a}(H_u)|^{2p} = E[𝓛(|L|^{2p})]` **除 `MatrixStein`（T70）外假设全部卸掉**。
`(U∘(L−K))_a` 同样拿到（`ukerObs`/`bddC2_ukerObs`/`testFun_ukerObs`）——因为 (5.17) 的系数**不依赖 `H`**，它就是 loop 的有限 ℂ-线性组合加常数。
**一处继承来的多余假设**：`testFun_loopObs_of_im_le` 带 `1 ≤ I.a.length`，**不是本单的界需要的**，而是仓库里 `testFun_loopObs` 的 `bdd₀` 字段（即 (5.2)）自带的；`bddC2_loopObs` 与整条 Uker 链**没有**长度假设。paper-deltas #100（原误编 #88，与 Jun 的模型裁决撞号，Cowork 改）。

### `RBM1D/Gauss/LoopIto.lean` — T134：动 `z_u` 已解决，且 (2.47) 的 `G̃` 升级为定理（Claude Code 并行 agent，2026-09-21）

**先纠正工单的一处混同**：`LoopIto.second` 是**cut-and-glue 代数**（`½ Σ S_ij ∂_ij∂_ji L` 的 Leibniz 计算），而 `(∂_u+𝓛)(L−K) = Θ∘(L−K)+F` 是 (5.12)–(5.15)，**由前者推出**。本单证的是后者与缺的分析胶水，**不是** `second` 本身。

**额外项确实出现，而且被精确命名——T76 的猜测是对的**：
**`eGterm_sub_eGterm`：`∂_u L_{σ,a}(M, z_u) = eGterm[G − m] − eGterm[G]`**，即**动 `z_u` 贡献的恰好是 (2.47) 的 `−m(σ_k)` 减项**。
机制：`∂_z(H−z)⁻¹ = G²`、`ż_u = −m`，故第 `k` 个 slot 变成 `−m(σ_k)G(σ_k)²`；再由 `⟨E_a⟩ = 1`、`Σ_a S^(B)_{ab} = 1`、`W Σ_b E_b = 1`，那个加倍的 `G(σ_k)` 恰是 Def 2.10(1) 的 `W Σ_b L_{G^{(b)}_k}`。
**对 T76 的后果：`LoopIto.second` 今后只需在冻结形式下证明（`EG := eGterm … 0 …`，用 `G` 而非 `G̃`），`G̃` 是白送的。剩余义务因此变小。**
`(L−K)` 那一侧没有重造轮子——`primBil`/`primRhs_sub`（(5.12)–(5.15)）**在 `Hierarchy/Dynamics.lean` 里已有**，本单只是装配。

**动 `z` 已闭合，`ContDiff.comp` 确实够用**：`hasDerivAt_comp_diag`（由联合 `HasFDerivAt` 得 `d/du f(u,u)`，**全程不碰「偏导连续 ⟹ 可微」**）；
`contDiffAt_green_comp → … → contDiffAt_gloop_flow` 走 `contDiffAt_ringInverse ∘ Real.contDiffAt_sqrt ∘ 仿射 z_w` 加列表归纳；
`hasDerivAt_integral_gloop_zt` **不带额外假设**（`zMotion` 的包络是确定性的，控制函数就是常数）。
终点 `hasDerivAt_sample_ELval_hierarchy`：被求导的函数**字面就是** `(sample d).ELval E N v I`、**两个参数同时动**，漂移为 `∫(Ẽ[G−m] + primRhs L_u)`——**T76 的「未做项」就此关闭**，只欠一条具名输入。
**一处值得记的坑**：T71 的 `hasDerivAt_lineInverse` 在此**不可用**（要求沿整条直线可逆，而 `u ↦ z_u` 在 `u = 1` 撞实轴），`hasDerivAt_green_path` 局部重做。

**剩余假设**：`LoopIto`（cut-and-glue，仍欠，但只需冻结形式）；`MatrixStein`（T70）；`TestFun`（**T133 已交**）；
以及**唯一的新假设** `hjoint`——逐 ω 就是本单已证的 `contDiffAt_gloop_flow`，缺的是**对 `z` 在球上一致**的联合导数控制，**即 T133 的 `bdd₁`/`bdd₂` 加强成对 `z` 一致的版本**（这就是 T133 该补交的精确形状）。
**未做**：`LoopIto.second` 本身；(5.19) 的 `primBilLen 2 = ThetaOp`；`hjoint` 的卸载。paper-deltas #52 已改写，另加 #89。

### T137：按字长分级的 gain 接口（Claude Code 并行 agent，2026-09-21）

**`FlucGainUpTo … M`** = `FlucGain` 加一条 `(L i).length ≤ M`；`FlucGain.upTo` 表明**无分级蕴含每个分级**，故 `flucGain_env` 仍是每一档的非空性见证。**`FlucGain` 本身一字未动。**
**使这件事变便宜的结构性事实**：`OpsOkOut.length_le`——归纳不变量本来就说「字母来自 `R` 之外**互不相同**的 slot」，故**字长自动小于 `#ι`**；
于是整个迭代不需要穿任何长度记账，分级版就是旧证明把 gain 假设限制到 `≤ #ι`，并在**唯一用到它的基例**处把该限制卸掉。
消费者全链重derive（`…_graded` 后缀）直到 `trace_green_sub_mul_Eblk_stochDom_iter_graded`，结论逐字不变。

**T113 端到端接上了**（探针 `t137/thread.lean`，`exit 0`）：`flucGainUpTo_of_minorDiff` = `flucGain_of_minorDiffGain` 的证明体加一条长度假设穿过，随后在 `M = 2p`（`hM := le_rfl`）处喂给分级消费者，**不再残留任何 `FlucGain`**。
**一处被 import 方向挡住、而非被数学挡住的**：该桥用到 `minorDiff`/`applyOps_eq_applyOps_minorDiff`，它们在 `FlucIterHigh.lean`（反向 import `FlucIter`），故 8 行的桥只能放在 `Gauss/FlucIterHigh.lean`——本单只许改一个文件，所以它目前只存在于探针里。**这是个很小的后续。**

**⚠ 一个值得记的发现：当前威力是 `Ψ·η_t⁻¹` 而非 `Ψ²`。** 原因是 T113 的 `B` 取的是确定性包络 `2(η_t⁻¹+1)`，因为其空字分支用 `norm_flucDiagSet_le_env`；
而根因在 **`MinorGood`（`MinorDiffGain.lean:436`）带 (4.1) 与 (4.3)，但不带 (4.2)**——没有 `‖G^{(S)}_{aa} − m‖ ≤ Ψ` 这个字段，`m = 0` 那一档就改进不到 `B ≍ Ψ`。
**补上该字段并在空字分支使用它，就是把这条现已打通的路线做到 (4.12) 论文尺寸的下一步**（是对 `MinorDiffGain.lean` 的编辑，自然的下一张单）。paper-deltas #85 已更新，另加 #100。

### T138：`FlowInputs` 被拆解，`LKDecay` 只剩三条实质假设（Claude Code 并行 agent，2026-09-21）

**`lkDecay_of_inputs`**：由 `|E| < 2`、`0 ≤ s N`、`t N < 1` 加**三条实质假设**给出 `SumZeroDyn.LKDecay`——**`FlowInputs` 本身不再出现**。

| 条款 | 新名 | 状态 |
|---|---|---|
| (4.4) 好事件（每个 `u`） | `FlowGoodEv` | 假设 `hΩ`，但**就是 T130 的定理**（见下），即 Steps 1/2 的弱局部律 |
| `LDERow`/`LDECol`（每个 `u`） | `FlowLDE` → `LDEFlowDom` | 假设 `hlde`——**对 `u` 一致这一版确实还开着** |
| (2.76) 在半径 `ℓ_u·N^{τ/2}` 的定量形式 | `FlowDec` | **已证**（`highProb_flowDec_of_aprioriDecay`） |
| 数值束 | `flowNum_choice` | **已证** |

**本单的实质新工作是 (2.76) 那条**：`highProb_flowDec_of_aprioriDecay` **逐字消费 `RBM.Steps.aprioriDecay`**（Step 2 的交付物，本来就带 `u` 指标）。
`L^re ≤ |L−K| + |K|`；`|L−K|` 半边用 `Steps.aprioriDecay`（取 `D = 30+2c`）、profile 界 `exp(−N^{τ/4})`、由 (2.2) 得的 `W^{-D} ≤ N^{-D/2}`，以及**已证而非假设**的前因子界 `prefactor_le`（两个 `Im m` 在 `η_s/η_u = (1−s)/(1−u)` 里相消）；`|K|` 半边用 `Decay.loopDecay_Kgen`@长度 2 加本文件已有的 `term2_le`，走同一个 `ℓ̂(u)` 二分。

**T130 的产出无需适配即可对接**：`Gauss.goodSetFlow ⊆ FlowGoodEv` 是 `fun ω hω u => hω u u.2`，`(Gauss.band d).P = Gauss.P d` 是 `rfl`；探针验证了 T130 → `hΩ` 端到端。
**为什么 LDE 那半没做出来**：T130 用的网引擎需要控制的多项式下界 `N^{-B} ≤ ζ`，而 (4.2) 的控制 `ldeRowRHS` 是小行 Green 元素平方和，**没有这种下界（它可以为零）**——已记进 `LDEFlowDom` 的 docstring。固定时刻的生产者 `Gauss.stochDom_ldeRow`/`stochDom_ldeCol` 恰是删掉 `TimeIcc` 因子的同一陈述。
**分层选择**：没有给 `LKDecayQuant.lean` 加 `Gauss` 的 import——高斯侧的对接只在探针里验证，以免 `Hierarchy` 依赖 `Gauss`。paper-deltas #91（#86 的附录）。

### T135：`≺` 的可加余量吸收 + `EE_le`（Claude Code 并行 agent，2026-09-21）

**通用引理进了 `Defs/StochDom.lean`**（纯新增，未重排未重述任何既有内容）：核心算术 `le_rpow_mul_of_le_add_rpow_neg`，加两个形式——
`StochDom.of_add_le`（控制扰动型，供 `of_det` 那条路）与 **`StochDom.of_highProb_add_rpow_neg`**（高概率型，`EE_le` 用的就是它），外加 `HighProb.of_eventually_univ` 让**确定性**下界也能喂进同一条引理。
**两处设计值得记**：高概率型里的**下界本身只是一个事件**而非确定性的 `∀ᶠ N`——这正是**随机**控制（`Ξ^{(L)}`）所要求的，T123/T125 的确定性情形是其退化特例；且 `b` 与 `D` 之间**不设关系**，证明自己在 `(τ/2, |b|+1)` 处实例化。

**`EEBridge.stochDom_norm_eeField` 字面就是 `Lemma510.EE_le`**（取 `H.EE := eeField`），探针以**裸 `:=`** 闭合该字段类型（无 `convert`、无强制转换），两种写法都验了（直接写 `eeField`，以及经抽象 `H` 加 `hH : H.EE = eeField`）。
假设只有：常设区制 + **(2.72)**、`eeDecayEvent`（(5.77) 的衰减输入）、`xiLowEvent`（`Ξ^{(L)}` 的高概率多项式下界）。
**没有自造区制假设**：`1 ≤ Wℓ_uη_u` 用的是**已有的** `SumZeroDyn.flow_crude`（agent 说它先写了一版推导，grep 后发现已有便丢弃了——「造轮子之前先查」）。

**多项式下界一半已证一半携带**：确定性那半由 `ℓ_u ≤ L`、`η_u ≤ 1`、`W·L ≤ N` 证出（同 `Gauss.rpow_neg_le_aprioriRhs`）；
随机那半（`Ξ^{(L)}` 的下界）需要 `Im G_{xx} ≥ η/(‖H−E‖²+η²)` 即 `‖H‖` 的界，而对**一般 `Sample B`**（entry 无界）只能高概率地有（`‖X‖ ≺ 1` 是 T109，且只在 `Gauss/`），故归约成**最弱可用形式**携带。
**无 fiat 风险**：不造 `Hierarchy`、不定义 `F`/`EE`/`mart`，`Lemma510`/`LKDecay` 逐字节未动；且 `hxi` 是**假设**，弱的 `C` 不会削弱结论（结论是固定的 `EE_le`）。
**未做**：`H.EE := eeField` 的安装（T58）；`EE_decay`（另一字段）；`eeDecayEvent` 与 `xiLowEvent` 的生产者（前者是粘合 `(2m+2)`-loop 版的 `Decay.lemma59`，该放 `LKDecayQuant.lean`）。
`StochDom.of_add_le` 已证但暂无消费者，是为确定性那条路留的。paper-deltas #92。

### T132a：矩 Duhamel 的结构与收口（Claude Code 并行 agent，2026-09-21）

**⚠ 先记一次我（协调者）的转述错误，供以后参考。** 我给 agent 的指令里写「收口用 `momentIntegral_le_exp` 的 `e^{p(2p−1)(v−s)}` 形状，per your recommendation #3」——
**这是错的**：Cowork 在 `docs/TASKS.md:2530` 的审查里**明确退回了修改 3**，理由是它会**丢一个 `η` 的幂**（Young + 常系数 Grönwall 给出的非齐次项是 `∫‖U∘F‖_{2p}^{2p}`，而论文要 `(∫‖U∘F‖_{2p})^{2p}`；在 `‖U∘F‖ ≍ Φ/η_u` 时开 `2p` 次方后差 `η_t^{−1}`），并给了「积分 + 取上确界」的四步配方。
**agent 按工单执行、没按我的转述执行，并复核确认 Cowork 是对的。这是正确的处置。** 我转述前没有重读工单的审查段。

**交付**：`Analysis/MomentClosing.lean`（纯实分析，Cowork 四步配方拆成四条可复用引理，**不用任何 ODE 比较定理**；`le_two_mul_add_sqrt_of_sq_le` 证完发现 `0 ≤ A` 可以去掉；
`integral_sqrt_mul_le` 是**唯一**让上确界进入积分、从而使右端与 `u` 无关的地方；**不假设 `ψ` 可微**，假设取积分形，好让 T132b 用 FTC 接上）；
`Gauss/MomentDuhamel.lean`（`∂_u U` 已落地、零假设、不依赖传播子 ODE；确定性层 `lkFun`（无 ω）与 `genLK`（只用方差剖面，故在一般 `Band` 上有定义）；带撇结构 `Hyp`）。
**修改 1 已兑现且可验证**：**`Hyp.F_unique` 已证**——`F` 在定义层被钉死。`Lemma510` 逐字复用（探针 `rw [← hFeq]; exact h510.F_le`，无 `convert`）。

**⚠ agent 自己纠正的一处第 0 步误判**：它原打算让带撇消费者直接给出**对 `u` 一致**的 `≺`，写到一半被类型系统拦下——`stochDom_of_momentDom` 要求 `[∀ N, Fintype (U N)]`，而 `TimeIcc` 是 `ℝ` 的子类型。
故 `stochDom_of_momentDuhamel` **只能在固定时刻给出 `≺`**，时间一致性必须走 T124 的网引擎。**这不是矩路线的缺陷**——`Hierarchy.bdg` 的时间一致性也是**靠假设**拿到的。已写进 docstring。

**未做（工单第 4 项）**：`Step3.Lemma514` 的带撇再生产。`stochDom_of_momentDuhamel` 把它归约成具名假设 `hrhs`（`U` 核估计 + `Lemma510` ⟹ 右端三项的 `‖·‖_{2p}` 界）；
填它要把 `SumZeroDyn` 的 `term1F`/`termI1`/`QV1_stochDom` 那套 `stochDom_of_logBound` 机器做出矩版本，体量与 `lemma514_flow` 相当，agent 本轮预算内做不完，**没有硬凑**。
另两项有意留给 T132b：收口引理与 `Hyp` 的内部接线（需 Hölder 步，而那要生成元恒等式）、`momentDuhamelQ` 的消费者。paper-deltas #93。

### `RBM1D/Gauss/CondStableFlow.lean` — T136：`hfixIBP` 已卸（Claude Code 并行 agent，2026-09-21）

**`unifDomIcc_condExpDiag_flow` 就是 `eq45Flow_of_unifDom` 的 `hfixIBP` 槽**（`y = condExpDiag`）。
假设里 **`hloc`/`hrepl`/`hstabP`/`hstabM` 全部消失**——不需要一致版的 `CondStable`，也不需要 `LmaxRowProxy`。
剩下的是 `hll`（u-一致的弱局部律，**与 T130 要的是同一条**，无新数学输入）、`hΩ`（T130）、`hΨW`（即论文的 `Ψ² ≍ W⁻¹`，与 T128 的 `hΦW` 同一条）、`hEnv`（常设区制）加记账项。

**卡住的不是 `∀ᶠ N` 的记账，而是控制的选择。** 在 `UnifDomIcc` 层根本不取对指标的并，故移植过来的 `unifDomIcc_condRow_of_envelope` **完全不需要基数假设**（与 T128 在 `unifDomIcc_of_moment` 处发现的是同一现象）。
真正的障碍是 T119 那条链把每个 `E_i[·]` 都用随机的 `L^max` 支配，因而需要 `E_i[L^max] ≺ L^max`，而后者经 `L^max ≍ W⁻¹` 证出、代价 `η_t⁻²`。
**agent 换成全程用确定性控制 `Ψ²` 重跑该链**——对它 `E_i` 是恒等（`condRowReal_const`），故 `CondStable` **退化掉**；`L^max` 只在最后一行、且只用其**下半边** `W⁻¹ ≤ 4L^max`（在流的好事件上对每个 `u` 成立、不花 `η` 的幂）。
于是 `hloc` 直接从 `hll` 读出，`hrepl` 由 (4.9) 重做、两个非对角因子都取自 `hll`。

**`t_N → 1` 的坑两个方向都守住了**：`L^max ≍ W⁻¹` **从不**对 `u` 一致使用，`LmaxRowProxy` 一次未用；`η_{t_N}` 只出现在**确定性包络**里乘以例外概率，多项式大小被 `Kenv` 吸收。
固定时刻的证明里唯一把 `η` 当作 `≺` 的**乘性常数**的地方（对角项 `k = i`，常数 `(η_t⁻¹+1)²`，在 `t_N → 1` 时多项式大）被替换成 `unifDomIcc_ibpRem_diag`（`ibpRem(i,i) ≺ 1`，控制取常数 1），够用是因为其系数 `S_{ii} ≤ 2L^max`。

**探针**：`eq45Flow_of_unifDom_ibp`（填 `hfixIBP`）与 **`eq45Flow_of_localLaw_gain`（三个 `hfix` 全部供齐）**，都以 `exact` 式应用、无 `convert`、无强制转换。
**`Eq45Flow` 仍非无条件，但剩下的已不再是固定时刻的估计**：三条 `u`-模（T129 给了 `condExpDiag` 那半并在 docstring 里写了组装配方，Green 那半是 T106）、`FlucGain` 在 `ρ ≍ Ψ`（堵在 T137 的分级接口）、`hll`（Steps 1/2）、`hΩ`（T130 由 `hll` 产出）、以及数值/区制条件。paper-deltas #94。

## ⚠ Cowork 审计 T132a（2026-09-21 04:55）：两处审查意见未落实 → T145

04:25 的中途抽查（`docs/TASKS.md` T132 规格下「Cowork 中途抽查 T132a」）要求提交前改两处：`Hyp.EE` 钉死为 T127 的 `eeField`；`drift` 只对 Hermitian `M` 量化。
68e7f61 提交的 `Gauss/MomentDuhamel.lean` **两处都没有**（`git grep eeField\|IsHermitian` 为空）。收口引理与 `F_unique` 是对的。
不是返工：`Hyp` 刚建、无外部消费者，改结构即可。开 **T145**（最高优先级）。另开 **T146**：`hrhs` 先试「逐时刻 `≺` + 确定性包络 ⟹ 矩」（T77）的桥，而不是把 `stochDom_of_logBound` 整套做矩版。

### T139：paper-deltas 编号去重（Claude Code，2026-09-21）

`61`–`65` 与 `90` 各有两行。**第一组保持原号**（T81/T91–T93/T95，STATUS 1592/1648/1666/1741/1767 的引用不动）；
**第二组改编**：T94→**95**、T101→**96**、T108→**97**、T83→**98**、T111→**99**，T137 的 `90`→**100**。
**与工单的一处偏差**：工单写「改编 `91`–`95`」，但 `91`–`94` 已被后来的行占用（当时最大号是 94），故顺延到 95–100。
STATUS 里指向第二组的 7 处引用（1988/2073/2295/2332/2347/2856/2890）已按上下文逐条改正；`RBM1D/**/*.lean` 的 docstring 里没有对这些号的引用（已 grep）。现全表无重号。

### T145：修补 `MomentDuhamel.Hyp` 的两处缺陷（Claude Code 并行 agent，2026-09-21）

**缺陷 1（`EE` 是无约束数据字段）——取了比工单更强的选项：字段直接删除，不是加约束。**
`E ⊗ E` 现在是**定义** `eeFun`（T127 的张量读成 `(u, M)` 的函数），`eeFun_H` 与 `EEpath_eq_eeField` 都是 `rfl`。
**T135 的 `stochDom_norm_eeField` 随即以裸应用闭合 `Lemma510.EE_le`**（探针验证，无 `convert`、无强制转换）。
**缺陷 2（`drift` 对所有矩阵量化）**：改为只对 Hermitian `M`；`genLK` 的 docstring 注明 `∂_ij∂_ji` 是沿 Hermitian 方向的二阶导（即 (2.34) 的生成元）。
`F_unique` 加 `hM` 后证明不变，并新增 **`F_unique_flow`**——这是「限制不花代价」的承重检查：沿流由 `Sample.hermitian` 卸掉边条件，**T132b 不损失任何东西**。

## fiat 审计（本单真正的验收标准）：**没有字段还能被 fiat 满足**

数据字段现在只剩 `F` 与 `cMD`，审计结论已写进模块 docstring：
* **`F`** 被 `drift` 在**每个** Hermitian `M`、每个 `u ∈ [s_N,t_N]` 处钉死——而这恰好就是 `momentDuhamel(Q)` 求值 `F` 的全部参数（矩阵总是 `X.H N u ω`，由 `Sample.hermitian` 为 Hermitian；时间总在 `[s_N,v] ⊆ [s_N,t_N]`）。**不存在既自由又被用到的参数**；且 `∃ dv, HasDerivAt …` 本身是义务，无法靠挑 `F` 绕过。
* **`cMD : ℕ → ℝ`** 是唯一残留的自由度，agent 判断它**确实**无害而非仅仅「相信无害」：(a) 类型上它只能依赖 `p`、**不能依赖 `N`**，而与 `N` 无关的常数是 `≺` 免费吸收的；(b) 同一个 `H.cMD p` 也出现在唯一消费者 `stochDom_of_momentDuhamel` 的 `hrhs` 里，故放大它同时把消费者的义务变难——**这一对是闭合的**。
  **存档一句**：没有任何东西把 `cMD` 与其 docstring 所提的 `sqrt_le_of_integral_le` 的 `C_p/p` 绑定，约束它的只有 `cMD_nonneg`。
* 其余字段都是关于 `Hyp` 之前就已固定的对象的 `Prop`。唯一剩下的空洞路径是退化窗口 `t_N < s_N`，与仓库里每个带时间的接口相同。paper-deltas #101、#102。

### T142：(4.12) 做到论文尺寸 `Ψ²`（Claude Code 并行 agent，2026-09-21）

**探针在 `MinorDiffGain.lean` 内部（对活源码而非可能过期的 olean）验证**：`≺ 6Ψ²`，对 `u` 一致，**控制里不再有任何 `η_t⁻¹`**；`stochDom_flucAvg_Sblk_iter_graded` 与 `2p`-矩形式同样成立。此前是 `2Ψ·(2(η_t⁻¹+1) + Ψ)`。
机制正如 T137 的诊断：`B` 从 `2(η_t⁻¹+1) + 2·minorDiffC M·Ψ` 降到 `2Ψ + 2·minorDiffC M·Ψ`，`ρ = 2Ψ` 不变；**只有空字那一支改了**（新的 `norm_flucDiagSet_le` 取代 `norm_flucDiagSet_le_env`）。

**新字段对消费者的代价：零。** `MinorGood` **逐字节未动**，8 个既有消费者全不受影响、没有任何陈述被弱化；新增 `MinorGood'` 继承它并加 (4.2)（见 paper-deltas #103），锐链在需要演算处用 `.toMinorGood`。
**而且生产者的代价是负的**：`minorGood'_of_local_law` 表明 `Ψ ≤ 1/2` 时 (4.2)+(4.3)+可逆性就给出整个 `MinorGood'`，(4.1) 由 `|m_E| = 1` 推出——**供给方要给的比以前更少**。

**T137 那个「8 行桥该放 `FlucIterHigh.lean`」的判断只对了一半**：探针里的桥用到 `MinorGood` 与 `integral_prod_applyOps_minorDiff_le`，两者都在 `MinorDiffGain.lean`，而该文件**import** `FlucIterHigh.lean`，故放不进去。
能放进去的是**无 import 依赖的那一半**（`MinorDiffGainUpTo`、`MinorDiffGain.upTo`、`flucGainUpTo_of_minorDiffGainUpTo`），具体的桥落在 `MinorDiffGain.lean`（旧强度与锐强度各一条）。**`Gauss/FlucIter.lean` 一行都不用改**，其 `_graded` 消费者原样接受新 gain。

**剩余**：`MinorGood'` 本身的生产（例外集，仍是对**每个**样本点的假设，需要仓库没有的那种形状的定量局部律——与 T113/T137 时相同）；无分级的 `MinorDiffGain` 在 `ρ ≍ Ψ` 处仍非定理，但**消费者只需要分级形式**。
**下游待办**：paper-deltas #85 的 `hΦW`（`4·W·ρB ≤ N^τ`）是把包络尺寸的确定性控制换成 (4.5) 随机控制的装置，现在 `ρB ≍ Ψ²` 了，该数值桥要在 `Eq45FlowInputs.lean` 里重推（本单未碰该文件）。

### `RBM1D/Gauss/LDEFlow.lean` — T143：把卡点搬出引擎（Claude Code 并行 agent，2026-09-21）

**T138 记的卡点（(4.2) 的控制可以为零、没有多项式下界）被绕开了，办法是改引擎而不是改陈述**：
T124 引擎里的 `hζlow` **只用于吸收网误差**，于是 agent 用吸收步骤**实际需要**的那条**相对**比较（网距处 `ξ(u) ≤ ξ(v) + ζ(u)` 且 `ζ(v) ≤ 2ζ(u)`）取代「模 + 下界」，**全程不出现任何下界**。
`close_of_holder_of_low` 证明**旧引擎是新引擎的特例**——没有交换掉任何东西。

**固定时刻的输入因此成了无条件定理**（`unifDomIcc_ldeRow`/`_ldeCol`）：**又一次 T128 式的消解**——`UnifDomIcc` 不取对指标集的并，故高斯行和的矩界（常数 `2(2p−1)!!`，与时间无关）直接喂 `unifDomIcc_of_moment`，**不需要基数假设、不需要好事件**；退化纤维 `ζ = 0` 逐 `(N,u,q)` 处理，与固定时刻时相同。

**剩下的 `LDENetClose` 不是记账，agent 说清了为什么没有硬凑**：经 Cauchy–Schwarz 与行独立性后 `ξ(u)/ζ(u) = u|⟨g,w(u)⟩|²`，`w(u)` 是小行 Green 列在 `S`-加权带范数下的单位化；对 `u` 一致即沿曲线 `{w(u)}` 的高斯上确界。
在整个球面上取粗的 sup 得 `≍ W`——**亏整整一个 `N` 的幂**；用链式论证则要求曲线长度多项式有界，即 `‖∂_u ĉ(u)‖ ≤ N^K‖ĉ(u)‖` **限制在 `i` 的带内**。
预解式的导数在**全**范数下给出这一点，但 `‖G^{(i)}e_j‖ ≍ η^{-1/2}`，而带内那部分在 `i, j` 相距远时是指数小的——**把前者换成后者，需要的是小行 Green 函数的非对角衰减，即 (2.76)/(4.3) 那个输入**。已记进模块 docstring，是独立的一张单。

**`LKDecay` 仍是三条实质假设**（探针端到端验证）：`hΩ`（T130）、`hdecay`（= `Steps.aprioriDecay`，Step 2）、以及取代 `LDEFlowDom` 的 `LDENetClose`。
**这笔交易是**：把一条「对时间一致的概率性假设」换成了「高概率事件上逐 ω 的逐点假设」。`ldeFlowDom_of_close` 以裸 `:=` 闭合 `LDEFlowDom` 并直接喂进 `lkDecay_of_inputs`。paper-deltas #104。

### T141：`hjoint` 已卸，T134 的余项只剩两条（Claude Code 并行 agent，2026-09-21）

**`z`-一致性确实是免费的**（agent 直说了，没有粉饰）：T133 的常数全由 `η`、loop 长度与 `Fintype.card` 构成，谱参数只经假设 `η ≤ |z.im|` 进入，故球版都是一行。
**但那并不是 T134 真正需要的——这是本单的实质发现**：`hjoint` 讲的是 `(v,w) ↦ ∫ L(H_v, z_w)` 的**联合**导数（流时间 × 谱时间），不是 T133 界住的矩阵导数；
T133 的常数**不能直接复用**（`v`-导数是 `D_M L[∂_v H_v]`，而 `∂_v H_v = (2√v)⁻¹X(ω)` 对 `ω` 无界），且 T133 根本没有 `z`-导数的界。真正的工作是从头搭联合界。

**`hjoint` 已卸**：`differentiableAt_integral_gloop_flow`，其假设**恰好是 T134 两条定理已经携带的那些**，**没有引入任何新假设**；`LoopIto.lean` 一字未动（探针 `t141/probe.lean` 验证）。
**关键手法（界是确定性的，不需要 `‖X‖` 的任何矩）**：`green_mul_self_mul_green`（`G M G = G + ζG²`）——因为 `∂_v H_v = (2v)⁻¹H_v`，**流的方向就是矩阵本身**，预解式把它吸收掉，
于是控制函数是**常数**，`integrable_const` 收口，避开了朴素路线所需的 `‖Xmat‖` 全部矩与多项式可积性。
另两件可复用的机器：`BddC1On`（一阶、集合局部化版的 `BddC2C`，对乘积封闭，`foldr` 又是一次归纳）；
**`ω ↦ fderiv` 的可测性在没有导数公式的情况下拿到**——`ℝ×ℝ` 上的泛函由两个坐标值决定，而每个坐标值是差商的逐点极限（`clm_prod_eq_smulRight` + `measurable_deriv_of_hasDerivAt_zero`），
绕开了 `(ℝ×ℝ) →L[ℝ] ℂ` 没有 `MeasurableSpace`/`BorelSpace` 实例这一点。
**注**：T134 的 `contDiffAt_gloop_flow` 只在**对角线 `(u,u)`** 上陈述，供不出邻域上的可微性，这就是非对角版必须在此重做的原因。

**T134 的余项现在精确地只剩两条**：`MatrixStein`（T70）与 `LoopIto.second` 的冻结形式（**T140**）。`TestFun` 由 T133 供给。paper-deltas：**无新增**（球半径内部收缩到 `min ε (u/2)` 纯属证明手段）。

### T144：T135 携带的两条输入都产出了（Claude Code 并行 agent，2026-09-21）

**(a) `eeDecayEvent`——关键发现是不需要任何新估计。** `Sample.Lval` **按定义就是**流的 `gloop`，而 T126 的 `highProb_loopDecay_pair` 本来就对**每个** loop 长度 `m` 给出 Def 5.8 的衰减，
故粘合后的长度 `2(n+2)+2` 只是它的一个实例；新增的一节只是把它重述成 `gloop` 的形状。
**刻意不 import `EEBridge`**（那会拖进 `Gauss/DischargeBDG`，破坏 T138 的 `Hierarchy ⊬ Gauss` 分层）；`GLoopDecayEvent … = EEBridge.eeDecayEvent …` **按 `rfl` 成立**，两侧只在探针里相遇。

**(b) `xiLowEvent`——已产出，且除常设区制与 (2.72) 外无任何假设**；唯一的概率输入是 T109 的 `‖X‖ ≺ 1`（无条件），只在 `τ = 1/2` 一个指数处用到。
**T135 草图的那条路没走通，这是本单的实质发现**（见 paper-deltas #105）：它需要 PSD 的幂平均不等式，Mathlib 没有可用形式。
改走**对标号求和**：`∑_a L_{σ,a} = W^{-m} Tr(∏_i G(σ_i))`，一条迹就从下方界住最大值；交错电荷处 `G` 与 `Gᴴ` 交换，迹化为 `∑_{x,y}|(G^k)_{xy}|²`，显然为正。**谱、PSD 序、Cauchy–Schwarz 全避开。**
确定性内核 `inv_le_loopMax` 对**任意** Hermitian `H`（`H − z` 可逆）成立，`rpow_neg_le_xiL` 则对一般 `Sample B` 成立。

**`EE_le` 现在还差什么**：从「两条携带假设 + `FlowInputs` + T58」变成「**`FlowInputs` + T58**」。
其一是 `H.EE` 仍是 `SumZeroDyn.Hierarchy` 的无约束字段（T58 的决定；**注意 T145 已在 `MomentDuhamel` 那边把对应字段删掉了，但 `SumZeroDyn` 一侧仍未动**）——探针 C 表明一旦有 `H.EE = eeField`，该字段立刻闭合；
其二是 `FlowInputs` 自身的余项（T130 的 `hΩ`/弱局部律、`LDEFlowDom`、(2.76)）。`Lemma510` 的另外三个字段未动。

### T140：cut-and-glue 冻结形式已证；(5.19) 暴露出论文的一处笔误（Claude Code 并行 agent，2026-09-21）

**1. `LoopIto.second`（冻结形式）逐字证出，无边界项。** `loopIto_second_frozen` + `loopItoFrozen`——**T76 的那条假设现在是定理**。
路线：`coordD2_loopObs_eq` → `insB`/`dblB`/`ins2B` 归并 → **`sumSblk_half_wirtPair`**（收缩 `½∑S_ij⟨ABCB⟩ = ½W∑⟨AE_a⟩S^(B)_{ab}⟨CE_b⟩`，**这正是 Def 2.10 的 `E_a` 的来源**）→ 字典 `insB E_b = cutGlue`、`ins2B = (cutGlueL, cutGlueR)`。
**收益已在文件内兑现**（不只是探针）：`hasDerivAt_sample_ELval_hierarchy_gauss` 把 T134 的终点重述，**去掉三条假设**（`hito`、`hEG`、`TestFun`）。
**Lemma 2.11 的矩形式现在只剩 `MatrixStein`（T70）与 `hjoint`（T141，已卸）** —— 即只剩 T70。

## ⚠ 2. (5.19)：`primBilLen 2 = ThetaOp` **按字面为假**，两个独立原因（见 paper-deltas #106、#107）

**(a) 左端错**：`primBilLen … 2` 只是回绕切 `(1,n)` 一项，其余 `n−1` 个相邻切在 `Decay.primBilLenR` 里；正确的左端是对称化的 (5.14)，即 `Decay.couplingLen L W 2 K D I`。
**(b) 核错——这是论文的笔误**：恒等式**强制**核为 `ξ_i·Θ^{(B)}_{tξ_i}·S^(B)`，而 (5.16)（以及逐字转写它的 `RBM.ThetaOp`）没有那个 `S^(B)`。
**两条独立佐证**：论文自己的 Example 2.16（p.21）写的核**带** `S^(B)`；且 `∂_t U_{s,t,σ} = Θ_{t,σ}∘U_{s,t,σ}` 经 (5.18) 也强制它。
已证的是更正后的版本 `couplingLen_two_eq_thetaGenLoop`（配 `thetaGenLoop`），并附 `thetaGenLoop_three` 作指标自检——**逐字复现 Example 2.16 的三项展开**。
**`RBM.ThetaOp` 未改**：19 条签名经过它，属冻结接口，该由 Cowork 决定。**而且这个疏漏是良性的**：`sum_Theta_mul_SB_row` 表明 `S^(B)` 行随机，故 `sum_ThetaOp_row`、`SumZero_ThetaOp` 与所有 ℓ^∞ 界**原样成立**，**只有恒等式 (5.19) 本身不成立**。
顺带把 STATUS 里一直挂着的 `LoopIdx ↔ LoopArg` 桥补上了（`thetaGenLoop_ofFn`、`set_ofFn_eq_ofFn_update`）。

## Cowork 裁定：(5.16) 漏 `S^(B)`（T140，paper-deltas #106/#107；2026-09-21 07:35）

**核实**：p.53 (5.16) 写 `(Θ_{t,σ}∘A)_a = Σ_i Σ_{b_i} [m_i m_{i+1}/(1 − t m_i m_{i+1} S^(B))]_{a_i b_i} A_{a(i)}`；而 (5.18) 对 `t` 求导给出生成元 `ξ Θ_{tξ} S^(B)`，
Example 2.16（p.20–21）的核也写作 `m₁m₂(Θ_{tm₁m₂}·S^(B))`。**agent 是对的：(5.16) 漏了右乘的 `S^(B)`，是笔误**，论文其余处都用对了。
**处理**：
* **论文**：按「小错误可自行修改」修正 (5.16)，p.53 补一个 `S^(B)`，零陈述改动——记为论文改动预算第 7 条。
* **Lean**：`RBM.ThetaOp`（冻结，5 个文件引用）**不改**；其 docstring 由下一张碰到它的单补一句「按字面转写 (5.16)，缺 `S^(B)`；生成元请用 `SumZeroDyn.genS` / `thetaGenLoop`」。
  既有结论不受影响（`sum_Theta_mul_SB_row`：`S^(B)` 行随机，ℓ^∞ 界与 sum-zero 原样成立），且 `SumZeroDyn.genS` 与 T132a 的 `drift` 字段**早已用的是带 `S^(B)` 的正确核**。


## Jun 裁定并落地：`RBM.ThetaOp` 已按更正后的 (5.16) 重定义（2026-09-21，Claude Code 并行 agent）

上一节 Cowork 的裁定是「论文改、Lean 不改」；**Jun 随后决定 Lean 一并改，31 处引用一起改**。已完成并推送。

**新定义**（`RBM1D/Hierarchy/Kernel.lean`，名字不变，只换核）：

```lean
fun a => ∑ i : Fin n, ∑ c : ZMod L,
  (ξ i * (Theta L (t * ξ i) * SB L) (a i) c) * A (Function.update a i c)
```

**没有一条定理被削弱或删除。** `S^(B)` 行随机，所以 `Hierarchy/SumZero.lean` 里
`sum_ThetaOp_row` 的值、`Psum_ThetaOp_succ_term` 的常数、`norm_Psum_ThetaOp_le` 的界**逐字不变**；
`SumZero_ThetaOp`、`commQT`、`SumZero_commQT` 以及整个 `Psum`/`vartheta`/`Qop`/`TwoSlot` 块
**连证明都没动**。只有四条把核写开的展开引理需要按新核重新陈述（是忠实重述，不是弱化）。
`SumZeroDyn.lean` 与 `Gauss/DischargeBDG.lean` 无数学改动。

**新增**（放在 `Hierarchy/Kernel.lean`，让 `Hierarchy/` 不必再向 `Gauss/` 借）：
`RBM.Theta_mul_SB_transpose`、`RBM.sum_Theta_mul_SB_row`、`RBM.sum_norm_Theta_mul_SB_row_le`。

**副产物**：`Gauss.thetaGenOp` 与 `SumZeroDyn.genS` 现在与 `ThetaOp` **按 `rfl` 相等**
（`Gauss.thetaGenOp_eq_ThetaOp`，机器验过）。两者都保留：前者是 (5.19) 的 `LoopIdx` 桥
（`thetaGenLoop_ofFn`、`smul_thetaGenOp_eq`）所用的陈述名，后者是 `genOp` 的实例、
`Q_t` 的估计都是对它陈述的。`thetaGenLoop` 不冗余——它是 `LoopIdx` 两表表示，类型不同。

**验证**：`lake build RBM1D` exit=0、0 errors、3797 jobs；公理审计 **8452** 条声明全部落在
`[propext, Classical.choice, Quot.sound]`。四个文件的 olean 均新于源文件。

**上一节（Cowork 07:35 裁定）中「Lean 不改、docstring 补一句」的处置已作废**，paper-deltas #106 同步重写。

## 蓝图解析器：`]` 吞节点的 bug 第三次发生，已从根上修掉

`lem:lde-quad-T` 的标题是 `$\mathbb E[T^p]\le C_p\,\mathbb E[V_q^p]$`，含 `]`，
于是 `\begin{lemma}[...]\label{...}` 的正则匹配不上，**整个节点连同 36 个 `\lean` 名字被静默丢弃**，
而「all 2165 names exist」照样打印绿色——只有一个悬空的 `\uses{lem:lde-quad-T}` 露出马脚。

`scripts/blueprint_preview.py` 两处修改：① 标题改为**惰性**匹配到「后面真的跟着 `\label` 的那个 `]`」；
② `parse` 直接数 `\begin{...}` 环境的个数，与产出的节点数不符就**报错退出**。
丢节点再也躲不进「名字全部存在」后面了。节点数 161 → 162，名字数 2165 → 2201
（找回的那个节点本来就已形式化，别无变化）。

## T147：总装还差什么（自上而下的精确清单，2026-09-21，Claude Code 并行 agent）

方法：七个 scratch 探针，全部用 `lake env lean` 编译过（树是绿的）。下面标 **[探针]** 的是编译验证过的，
标 **[读码]** 的是读代码 + grep 得到的。没有新建或修改任何仓库文件。

### 0. 两个跟数学无关、但目前让总装根本不可能的拦路石

**0a. `Steps` 当假设用是循环的——纯记账，无主，挡住一切。**
`RBM.Steps`（`Flow/Hypotheses.lean:294`）是 8 个字段的包。**生产**它后面字段的那些 glue 定理，把**整个包**当假设收。
**[探针 P2]** `Step2PP.flow_sharpLoop_glue_flowAs` 在喂进一个四个 sharp 字段全是 `sorry` 的 `Steps` 时照样编译——
即「要证 `sharpLoop` 必须先有 `sharpLoop`」。Step 6 同样（**[探针 P5]**：`quad11/13_unifDetDom_gauss` 收 `hsteps : Steps`，而 Step 6 生产 `sharpExpect`）。
**[读码]** 全树只取了 5 个投影（`apriori`、`localLaw`、`aprioriDecay`、`sharpLoop 2`、`sharpLmK 1/3`），
依赖序 1→2→3→4/5→6 **是无环的，循环只在打包上**。
**修法：约 8 条签名里把 `hSteps : Steps X E s t` 换成用到的那几个字段。零新数学。这是清单上杠杆最大的一项。**

**0b. `Thm221.step` 的 `0 ≤ s` vs `0 < s` 仍然在，而且是承重的。**
**[探针 P3]** `mkSteps` 只要 `0 ≤ s` 时，`Bounds_of_Steps` 恰好填满 `Thm221.step`（零 sorry）；要 `0 < s` 时是硬错误。
躲不掉：`Bounds_of_Thm221`（`Flow/Iteration.lean:282`）沿 `u₀ ≡ 0` 的网格用 `hT.step`，`s ≡ 0` 真的出现。
**好消息是它很浅**：`hs0` 全部经 `Band.scale_pos` → `one_le_ellHat`，而 `0 ≤ t` 版 **[探针 P4]** 用现成的
`RBM.one_le_ellHat_of_nonneg`（`Flow/Scales.lean:416`）五行就出来。属记账，无主。

### 1. Theorem 2.2：没有总装，且不只是记账
`Delocalization.lean` 只有确定性内核，`sq_norm_eigenvector_le_of_norm_green_le` **[读码] 除 `Test/Sanity.lean` 的公理打印外无任何消费者**。
缺的是「Thm 2.3 在 `z = λ_k + iη` ⟹ `‖G_xx‖ ≤ C` 高概率 ⟹ (2.10)」，两个超出记账的障碍：谱参数是**随机的**（`λ_k(ω)`），
而 `localSemicircleLaw_of_Thm221` 是对确定性列 `z : ℕ → ℂ` 陈述的；且 `SpecSeq` 把能量钉成与 `N` 无关，`E` 方向没有一致性。
要改 `Bounds`/`Thm221` 的接口（`N` 依赖的能量）加覆盖论证。paper-delta #5。**无主、无工单。**

### 2. Theorem 2.3 / 2.4：已完全归约到 `Thm221` ✅
**[探针 P6a] 零 sorry 编译**：`Transfer`、`TransferLoop1` 在矩路线模型上**是定理**（`Gauss.transfer_gauss`、`transferLoop1_gauss`，T111）。
STATUS 早前几节仍把它们列为待办输入，**那是过时的**。

### 3. Theorem 2.5：`Thm221` + 两个可积性槽 ✅⚠
**[探针 P6b] 零 sorry**。`hint_pp`/`hint_pm` **[读码]** 可由 `Gauss.integrable_gloop_Hflow` 在 `u = 1` 处 + `gloop_pm_eq`/`gloop_pp_eq` 卸掉。记账，无主，便宜。

### 4. Theorem 2.6：三个假设，两个按设计是外部文献，一个是本文的开放数学
`DBMUniversality`、`GreenComparison` 是外部引用（设计如此）；**`StepTwoClaim`（即 (2.23)）是本文自己的数学**，要 (2.25)–(2.33)。**无主。**
QUE 那一半已形式化，但压在 `RBM.Eq747`（T65 的占位符）上，**无生产者**。

### 5. `Thm221 ← Steps` 与六步

**T58 有四项交付物**（T114 当时找到三项，Step 6 那项是第四）：① `SumZeroDyn.Hierarchy … 0`（Step 2 路线 A）；
② `∀ n, Hierarchy` + `∀ n, Lemma510`（Lemma 5.14，**不论 Step 2 走哪条路都在关键路径上**）；③ `Fin n` 侧的推论；
④ `Step6.Hierarchy` + `FastDecayHyp`——**是另一个对象**（无 ω、无鞅、漂移拆成 `DLK + DG`、已经在期望里）。
**[读码] 全树没有任何 `SumZeroDyn.Hierarchy` 实例，也没有任何 `Step6.Hierarchy` 实例。**

* **Step 1**：`Step1.Hyp` 四个字段现已全部由 `Gauss.step1Hyp_gauss_of_scale` 在 `step1` 自己的假设下供给。
  **仍携带**：`EntryBoundFlow`/`DiagBoundFlow`（(4.2)/(4.3) 的 `TimeIcc` 版），**无生产者**——这是 T107。
  **审计发现**：它们的定时版建在 `stochDom_ldeRow/Col` 上，而 T148 的 `LDENetClose` 正是这两条的 `u`-一致版。
  **T107 与 T143/T148 缺的是同一个输入**，规划时值得合并。
* **Step 2**：两条互斥路线**都开着**。路线 A 的 `Step2.Hyp` **无生产者**，其 `eG` 的陈述提到 `H.F`，**T58 钉死 `F` 之前连陈述都写不出**；
  路线 B 的 `MomentHyp` **无生产者**，硬字段是 `step`（T132c）。
* **Steps 3/4/5**：入口 `Step2PP.flow_*_glue_flowAs` 的 `h0/h12/h1/h2` 都已卸。剩：
  `h514` ← T58 ②③；其中 `Lemma510.EE_le` 是**已证但没接线**（`EEBridge.stochDom_norm_eeField` 一个裸 `:=` 就闭合，
  **只要 `SumZeroDyn.Hierarchy.EE` 像 T145 钉 `MomentDuhamel` 那样钉住**——那边钉了，这边**还是无约束数据字段**）；
  `hdec` ← `LKDecayQuant.lkDecay_of_inputs`，`hΩ`✅`hdecay`✅，只差 `LDENetClose`（T148）；
  `hΘ` ← `BootPP`，**`BootPP` 无生产者，无工单**；`h548 : Step45.FlowEq548` **无生产者、无工单**（T61 余留）。
  `eq45Flow_of_localLaw_gain` 内部余留：三个时间 Hölder 模 `hHolIBP/hHolRow/hHolBlk`（T129 + T106 有料，组装没做）；
  **`hg : FlucGain` 是接口错配**——T137/T142 做的是**分级**的 `FlucGainUpTo`，而消费者要**不分级**的那个，两边没桥；
  `hΨW`/`hΦW` 要按 `ρB ≍ Ψ²` 重算；`hll : LocalLawUnifIcc` **已证但没接线**：**[探针 P7]** 由 `Steps.localLaw` +
  `Step3.Scales.le_A` 十行 `measure_mono` 即得（这正是 `GoodSetFlow.lean` docstring 里说「(2.74)/(2.75) 给的就是它」的那句，**从没接过**）。
  矩路线的替代 `stochDom_of_momentDuhamel` **[读码]** 只给**固定终点 `v`** 的 `≺`，时间一致性仍得走 T124 的网，
  故**今天它严格落后于 T58**。
* **Step 6**：**[探针 P5]** 高斯模型下 `sharpExpect_step6` 只剩五个洞，全是裸应用、无 `convert`：`h5132` = `hB.expect` 逐字✅，
  `h527`✅(T117)、`hq11/hq13`✅(T123+T131)、`hint2`✅；`hint1` **[探针 P5b]** 由 `Gauss.integrable_sample_Lval` 取 `η := etaT E u` 闭合，**只是没接**；
  `hH`/`hFD`/`h5133`/`hG` 四个全部量化 `DLK`/`DG`，**无生产者 = T58 ④**。

### 6. 三个桶

**(a) 真正开放的数学**：T58（四项，Steps 2–6 全在其关键路径上；且 `DischargeBDG.lean:70ff` 记的约束仍在：
`duhamel` 按定义造出来会让 `Lemma510` 为假，交付物是三元组「具体的 `F` + 对它可证的 `Lemma510` + 可证的 `bdg`」）；
`BootPP.step`（无工单）；`Step45.FlowEq548`（无工单）；`LDENetClose`（T148，同时解锁 T107）；
`MomentHyp.step`（T132c，若走路线 B）；`StepTwoClaim`（无工单）；Theorem 2.2 的概率一半（无工单）。

**(b) 纯记账、必须有人做**：① 拆 `Steps` 包（挡住全部总装，**应最先做**）；② `0 < s` 放宽到 `0 ≤ s`；
③ 由 T129 + T106 组装三个 Hölder 模；④ 把 `eq45Flow_of_localLaw_gain` 搬到**分级**的 `FlucGainUpTo` 接口并按 `ρB ≍ Ψ²` 重算 `hΦW`/`hΨW`；
⑤ 落地 T142 那条只存在于探针里的分级桥 `flucGainUpTo_of_minorDiff`。

**(c) 别处已卸、只是没接线**（全部有探针或逐字依据）：`hll`、Step 6 的 `hint1`、`0 ≤ t` 的 `Band.scale_pos`、
`Transfer`/`TransferLoop1`、Step 6 的 `h5132`/`hq11`/`hq13`/`h527`/`hint2`、Thm 2.5 的两个可积性、`Lemma510.EE_le`、`Step1.Hyp` 四字段。

### 7. 到绿色 `Thm221` 的最短路径（供估算）
① §0a + §0b 的记账（解开整个证明的形状）→ ② 接线 (c)（零新数学）→ ③ 选 Step 2 的路线（**A 与 B 今天都落在 T58 后面**）→
④ T58 无论如何都绕不过（Steps 3/4/5 与 6 都要）→ ⑤ `BootPP.step`、`FlowEq548`、`LDENetClose`（顺带给 T107）、Hölder 模、分级 `FlucGain` 的改接。
**②和⑤与 T58 无关，可并行。**

## Cowork 审 T147（2026-09-21 07:50）

**清单质量很高，全盘采纳**，据此开 T149–T153，并重排优先级（TASKS 顶部）。三点裁定：
1. **T58 在矩路线下被拆分替代**：① 路线 A 放弃；②③ 由 T146 经矩 Duhamel 重新生产 `Lemma514`（审计说「今天落后于 T58」是指 `stochDom_of_momentDuhamel` 只给固定终点，T146 规格本就要求走 T124 的网）；④ 由 T152 走一阶的带时间生成元恒等式。
2. **(5.48) `FlowEq548` 并入 T132c 的交付**（同一论证的副产品）；**`BootPP.step` 已在 T132c 规格里**（审计写「无工单」是因为它读的是修订前的规格）。
3. **`RBM.ThetaOp` 已被改成带 `S^(B)` 的更正核**（d31e1d4，类型未变、全量绿、ℓ^∞ 与 sum-zero 引理原样成立）——这推翻了我 07:33「不改」的裁定，**我接受**：Lean 定义与更正后的论文一致更好。
**需 Jun 定范围**：Theorem 2.6 的 `StepTwoClaim`（(2.23)，需 (2.25)–(2.33)）与 QUE 的 `Eq747` 是否在本轮范围内（此前计划 §7.2 不碰）。


## T146：`hrhs` 三项全部卸掉（`Gauss/MomentDuhamelRhs.lean`，589 行，2026-09-21）

**第 0 步的判断是对的：`stochDom_of_logBound`/`term1F`/`termI1`/`QV1_stochDom` 那套机器不需要重做。**
理由是矩形式让三个因子**分开**：① 核是确定性的，用 Minkowski 从范数里提出来；
② 剩下的是**只对张量**的 `‖·‖_{2p}` 界，正是 T77 的反向桥；③ 时间积分是逐 `u` 的界，**完全不需要可积性**。
（`≺` 那套之所以逼出 `stochDom_of_logBound` 的写法，是因为它把核 + 张量 + 时间积分**捆在同一个高概率事件上**估。）

关键声明：`momNorm_le_of_le_weighted_sum`（带确定性权的 Minkowski；因为 `momNorm` 是裸的 `(∫|Y|^q)^{1/q}`
而非 `eLpNorm`，只能从 Jensen `ConvexOn.map_sum_le` 走）；**`momNorm_Uker_apply_le`**（Lemma 7.1 的矩形式，
常数与 `norm_Uker_apply_le` 同为 `C^n`）；`intervalIntegral_le_of_le_const`（无可积性假设：不可积时
Bochner 积分为 `0`，界平凡成立——这就避开了证 `u ↦ ‖·‖_{2p}` 可测）；`MomNormDom` + 两条桥；**`hrhs_of_moment_inputs`**。

**两个设计上的要点值得记住**：
* `momNorm_Uker_apply_le` 里对标号的 sup **必须留在矩的外面**。放进去要付 `(#LoopArg)^{1/(2p)} ≈ N^{Ccard/(2p)}`，
  **对固定的 `p` 没有任何 `N^{ε/2}` 吸得掉**。
* 该定理是用 `edgeKer` 的行和陈述的，**与 `ThetaOp` 无关**——所以并行进行的 `S^(B)` 更正碰不到它。
* `MomentDom` **不要求 `Fintype`**（只有回程的 `stochDom_of_momentDom` 要），所以**指标里可以带时间**：
  `hrhs` 本身**不需要 T124 的网引擎**。

**留作假设的三项**（边界划得很干净）：`hinit`/`hFmom` 归约到带**确定性**控制的 `≺`，而 `Lemma510.F_le` 的控制是
**随机的**（`xiRhs`），差的那一步正是 `SumZeroDyn.F_stochDom` 逐路径做的 `Ξ ≺ 1` 替换。
**`hEEmom` 是 `p` 阶矩范数，不是 `2p`**：T77 的桥只出偶数阶，要从 T135 的 `stochDom_norm_eeField` 喂进来
就得有 **Lyapunov `‖·‖_p ≤ ‖·‖_{2p}`——仓库里没有**。agent 没有在一个项估计内部临时造它（对的判断），
**这是唯一真正缺的引理**，它应该放在 `momNorm` 旁边。

**⚠ 顺带查出 `Gauss/MomentDuhamel.lean` 的一处括号错误**（T132a/T145 的文件，未动）：见 paper-deltas #108。
`Hyp.momentDuhamel`/`momentDuhamelQ`/`hrhs` 里 `∫` 的被积式向右延伸，**(5.24) 的第三项实际落在了时间积分内部**。
T146 按它实际 elaborate 的样子证明，因此能复合；**修法是一对括号，但要等 T132b 落地再动**——那两个字段正在被卸。

## T132b：带时间的生成元恒等式证出；但查出 `genLK` 多了一个 `W`（`Gauss/MomentDuhamelGauss.lean`，499 行，2026-09-21）

**1. 带显式时间依赖的生成元恒等式，完整走通。**
`hasDerivAt_integral_Psi_pairs`：`d/du E[Ψ(u, H_u)] = E[∂₁Ψ] + ½ ∑_{ij} S_ij E[∂_ij∂_ji Ψ]`。
T71 的 `hasDerivAt_integral_Phi_pairs` 就是 `Ψ v = Φ` 的特例。配套：`timeD1`、`fderiv_uncurry_apply`
（联合导数拆成 `a·∂₁Ψ + ∂_M Ψ[B]`——**两个槽唯一相互作用的地方**）、`hasDerivAt_Psi_Hflow`、`TestFunT`(+`slice`)。
`TestFunT` 是**时间局部化**的，窗口不是装饰：`Ψ` 的每个界都是 `(Im z_u)⁻¹ = ((1−u)Im m_E)⁻¹` 的幂。
探针验证过该类**非空**，且在 `Ψ(u,M) = u` 上恒等式重现 `d/du ∫u dP = 1`。

**2. `(z,M)` 联合 `C²`：不需要二阶的 `BddC1On` 类比。** `resH` 是 `Ring.inverse ∘ ((u,M) ↦ (M+Mᴴ)/2 − z_u)`，
内层映射在 `z` 为 `C²` 时联合 `C^∞`，而 `contDiffAt_ringInverse` 在单位处是 `C^∞`——就是 `contDiff_resH`
的证明把 `M` 换成序对，**T141 的 `BddC1On` 没用上**。（集合局部化的二阶**有界**类只在要造 loop 观测量的
具体 `TestFunT` 实例时才需要，那部分没做。）

### ⚠⚠ 查出的缺陷：`MomentDuhamel.genLK` 多带一个 `W⁻¹`

`genLK` 把 `∂_ij∂_ji` 的权重写成 `Sblk (B.L N) (B.W N) i j / B.W N`。但
**`RBM.Sblk L W i j = sbKre L (i.1 − j.1) / W` 本身就是方差 `E|X_ij|²`**（逐字等于 `Gauss.gvar`，
见 `gvar_diag`/`gvar_offDiag`），它正是 `hasDerivAt_integral_Phi_pairs`、`genD` 和 T140 的
`sumSblk_half_wirtPair` 里用的权重。agent 把这件事做成了**定理**而不是断言：

```
RBM.Gauss.W_mul_genLK_eq :  W · genLK = ½ ∑_{ij} Sblk_ij · wirtSecond(lkFun)
```

即 **`genLK = W⁻¹ · 𝓛`**。（`genLK` 的 docstring 说「只有方差剖面 `S^{(B)}/W` 进来」——
写它的时候把 `Sblk` 当成了不带 `/W` 的 `S^{(B)}`。）

**代价不是 `drift` 变得不可证。** `drift` 读作 `∃ dv, HasDerivAt … dv u ∧ dv + genLK = genS + F`，
`F` 是**数据**字段，取 `F := dv + genLK − genS` 就卸掉了，真正的义务只有 `u`-导数存在。
**真正的损害是：这样钉死的 `F` 与 (5.15) 的 `F` 差了 `(W⁻¹ − 1)·𝓛(L−K)`，量级就是 `𝓛(L−K)` 本身。**
T145 的 fiat 审计结论「`F` 被 `drift` 钉死」仍然成立，**但钉死的是 (5.15) 没有命名的那个对象**，
于是 `SumZeroDyn.Lemma510` 会在估计错的东西。**修法是一个 token**（删掉 `/ (B.W N : ℝ)`）。

### ⚠ 第二处：`Hyp.integrable` 对 `u` 过度量化
`integrable_lkT_pow` 已证（带 `(zt Ev u).im ≠ 0`），**但它闭合不了字段**，唯一原因是
`Hyp.integrable` 把 `u` 量化在**整个 `ℝ`** 上而不是 `[s N, t N]`。`u = 1` 时谱参数是实的，不存在确定性包络。
**这与 T145 从 `drift` 上删掉的过度量化是同一类问题。**

### 未完成（边界）
`momentDuhamel`/`momentDuhamelQ` 整条链（T72 `genMomentPt_le` → 代入 drift → Hölder → T132a `sqrt_le_of_integral_le`）
都挂在 `drift` 上，被上面的缺陷堵住。`drift` 本身还缺两个生产者：`u ↦ B.Kval E N u I` 的时间可微性（仓库里没有），
以及固定 Hermitian `M` 时 `u ↦ gloop(M, z_u, I)` 的可微性（在 `Gauss/LoopIto.lean`，当时是**在飞行中**的文件，未碰）。
`Ψ = |U∘(L−K)|^{2p}` 的具体 `TestFunT` 实例要 `ℝ × Matrix` 上的联合二阶**有界**演算（T133 `BddC2C` 的时间版），未做。

**`ThetaOp` 暴露：无。** 本文件没有任何声明提到 `ThetaOp`/`genS`/hierarchy 核，并行的 `S^(B)` 更正只让它重编译。

## T132c 第 0 步：指数表（2026-09-21，Claude Code 并行 agent，只读审计，未写 Lean）

判据先说清楚：设系数为 `A^{−α}R^β`（`R := η_s/η_t ≥ 1`，`A := Wℓ_tη_t`）。在 `hregS`（`StepGlue.lean:186`，
即带 `N^c` 增益的 (2.72)）下 `A^{−α}R^β ≤ N^{−cα}` **当且仅当 `β ≤ 30α`**。
**裸 `Cond272` 下表里没有一行能过**——`s = t` 时 (2.72) 只给 `A ≥ 1`，没有任何 `A` 的多项式下界。
所以差别只在「吃掉多少 `N^c`」。下面用 `β* := β/α`，可直接与 30 比。

| 出处 | `J*` 幂（前→后） | 系数 | `β*` | 判决 |
|---|---|---|---|---|
| (5.40) 主项 (p.57) | 2 → 1 | `A^{−1}R^6` | **6** | 余量 `A^{−4/5}` |
| (5.41) 第一项 (p.58) | 0 | `A^0R^3` | — | 加性常数，无条件 |
| **(5.41) 第二项 (p.58)** | 3 → 1 | `A^{−1/3}R^{10}` | **30** | **恰在边界，零余量** |
| 同上，先用 (2.73) 降幂 | 3 → **1** | `A^{−1/2}R^{11/4}` | **5.5** | 余量 `A^{−49/120}` |
| 同上次主项 | 3 → **3/2** | `A^{−1}R^{9/2}` | **4.5** | 舒服 |
| (5.42) 第二项 (p.58) | 3 → 1 | 二次变差 `A^{−1/3}R^8`，**开方后** `A^{−1/6}R^2` | **12** | 余量 `A^{−1/10}` |
| `BootPP` `n=2` 自平方 | 2 → 1 | `A^{−1/2}R^{1/2}` | **1** | 已由 `Step2PP.harith_flowAs` 从 `hregS` 证掉 |

**Cowork 草算的三个数全对**（`A^{−1}R^6`、`A^{−1/3}R^8`、(5.41) 的 `10/30 = 1/3` 恰在边界）。

### ⭐ 这张表**已经编译在仓库里**了
`Step2.phi`（`Step2.lean:727`）与 `Step2.phi_arith`（`:953`）就是它的 Lean 版：
`hA : x^17R^10 ≤ A`（(5.40)，锐的是 `x^15R^6`）、`hq : q ≤ R`、**`hα : α(x^24R^10) ≤ 1` ⟺ `x^72R^30 ≤ A`**（(5.41)，**一分不剩**）、`hε`。
`Step2.lean` 文件头第 73–75 行早就写明「(2.72) 单独用时 `(J*)³(Wℓη)^{−1/3}` 项**恰好临界**，`≺` 的损失无处安放」。

### 由此得到的修正：**线性化不改变指数预算**
工单说「线性化的代价是 `(η_s/η_t)` 的幂要重算」——**不用重算，指数完全不变**（`Λ³` 与 `Λ²·J*` 给同一个上界，
对应 `phi_arith` 的 `t5`）。线性化买到的是**纯结构性**的收益：把「`q` 阶结论要 `3q` 阶假设」变成同阶闭合。
换言之第 0 步**不会产出新的门槛约束**，(5.41) 的边界性从一开始就在那里。

### (2.73) 降幂：成立，落到 `J*` 的**一次**（次主项 3/2 次）
两处 `(1 + J*A^{−1})` 的来源核实无误（(5.52) 经 (4.5)；(5.57)/(5.58) 经 (4.2)）。换成 (2.73) 后
`Ξ^{(L)}_{u,2} ≺ r`、`|G_{xy}| ≺ r^{1/2}A_u^{−1/2}`（`r := ℓ_u/ℓ_s`），(5.41) 第二项变为
`(1/η_u)(η_u/η_v)^2[r^{3/2}A_u^{−1/2}J*_u + rA_u^{−1}(J*_u)^{3/2}]`，`β*` 从 **30 掉到 5.5**。
**工单猜的「一次或二次」不对：是 1 与 3/2。** 降幂后全表瓶颈变成 (5.40) 的 `β* = 6`。
**代价必须说**：(5.35) 的显式形式就把 `A^{−1/3}(J*)³` 焊死了，`Step2.Hyp.eG`（`Step2.lean:1256`）逐字抄的是它，
所以 (2.73) 路线要重述 `eG`，连带 `phi`/`phi_arith`/`step_bound` 出带撇版——**这是重证 (5.35) 的远程部分，不是引用一条现成引理**。

### ⇒ **不需要动 (2.72) 的 30。** Jun 预授权的 50/100 不启用。
（备案：若要保留 (5.41) 的字面形状**且**放弃 `N^c` 增益，最小可用指数 > 30；不建议。）

### 顺带发现的一条锐化（备选，非必需）
`Step2.lean` 把 `∫_s^v (1/η_u)(η_u/η_v)^2 du` 放成「长度 × 上确界」。门槛 `Λ(u)` 随 `u` 单增，被积函数由 `u = v` 端主导，
**锐算回收 2 个幂**：(5.41) 的 `β` 从 10 掉到 8，`β* = 24 < 30`。这是一条**不用 (2.73)、也不抬 30**就能脱离边界的路，
但要重写 `phi`/`phi_arith`/`step_bound` 的积分估计，比 (2.73) 路线工作量大。

### ⚠ 光滑截断方案：三个真实缺口（如实报告）
`(∂_u+𝓛)Φ̃` 展开后逐项核对：
* **`ΣS|∂J|²` 数学上有、Lean 里没有。** 光滑 max 的权重满足 `Σw_i ≤ M^{1/r} = O(1)`，于是它归约到 `ΣS|∂(L−K)|²`，
  **那正是 `E⊗E`，即 (5.36)/(5.42)**。但 `EEBridge.norm_eeField_le`（`EEBridge.lean:568`）给的是 Lemma 5.10 的**粗形式**
  （`Ξ^{(L)}_{2n+2}A^{−2n}η^{−1}`），**没有 `T_{u,D}²` 归一化、没有空间衰减**。(5.36) 本身在仓库里**不存在**——
  `Step2.lean:78` 明说它「只经停时鞅假设 `Hyp.mart` 进入」，**而矩路线恰恰不能用停时鞅**。
  → **缺口 1：截断路线要先把 (5.36) 立成独立的逐点估计。**
* **T133 的 `C²` 界覆盖不了缺口项——工单这条假设不成立。** `LoopC2.lean` 给的是 `BddC2C` 常数 `B = 2(1+η⁻¹)³` 外加 `W·L`，
  文件自己写着「常数不最优……确定性多项式，够控制收敛用」。**没有 `T_{u,D}` 归一化、没有衰减、量级差 `A^{O(1)}`。**
  → **缺口 2**：T133 给的是生成元恒等式与控制收敛所需的那一半，不是量化那一半。
* **`(∂_u+𝓛)J` 缺三块**：光滑 max 的链式法则 + 权重和界（纯初等，小）；`∂_u log T_{u,D}`（`∂_u[−(ℓ/ℓ_u)^{1/2}]` 对 `ℓ` **不一致有界**，
  但**符号有利**可直接丢，`W^{−D}` 地板区要单独处理；仓库里关于 `∂_u T_{u,D}` 什么都没有）；
  以及 `(∂_u+𝓛)(L−K) = F` 本身——`SumZeroDyn.Hierarchy` 被 T118 禁用，**只能来自 T132b 的带时间生成元恒等式**
  （**该恒等式此刻已经落地**，见上一节 `hasDerivAt_integral_Psi_pairs`）。
* **工单漏了一项**：门槛 `Θ_u` 依赖 `u`，故 `(∂_u+𝓛)χ` 里还有 `−χ'(J/Θ)Θ̇_u/Θ_u`，`Θ̇_u/Θ_u = 4m/η_u`，与其它漂移项同阶、无害，但三项分解里没有它。
* **第 3 步的「无阶数上升」只在概率层面去截断时成立。** 在矩层面用 `E|Φ|^{2p}1_bad ≤ N^{2pK}P(bad)` 去截断，
  需要 `q ≳ 2p(K+δ)/δ` 阶矩——**阶数还是升了**，只是倍数从 3 变成 `(K+δ)/δ`。出路是工单自己的第 4 步（穿越论证 + 时间网），
  所需工具库里**有**：`MomentHyp.holder`（`Step2Moment.lean:373`）+ `stochDom_timeIcc_of_holder`（`:504`）。

### 工单里另外两处说错的
* 「真正内禀的只有 (5.34)/(5.50) 的 `J*²`」**不准确**：(5.36) 的 Case 2(1a) 有内禀 `(J*)²`、Case 2(1b) 有内禀 `(J*)³`
  （(5.67)/(5.72)，p.62–63），来自 (5.31) + 尾函数衰减，**(2.73) 换不掉**；(5.35) 的 Case 2 ((5.61)) 有内禀 `(J*)^{3/2}`
  （三个尾函数的乘积是凑出 `T(|a₁−a₂|)` 全幂所必需的，替掉任何一个就缺 `T^{1/2}`）。
  它们都带 `A^{−1}`、(5.42) 还过一次开方，**全部安全**，但「只有一处内禀」会让实现者低估。
* (5.42) 的 `A^{−1/3}R^8` 是**二次变差**层面的，**开方后**真实约束是 `R^{12} ≤ A`，比表面宽。

## Cowork 审 T132b / T146 / T132c 第 0 步（2026-09-21 08:10）

**T132c 指数表：全盘采纳。** 30 不动（`hregS` 的 `N^c` 增益 + (2.73) 降幂后 `β* = 5.5`）；Jun 预授权的 50/100 不启用。
线性化不改指数预算、只改结构（同阶闭合）——agent 这一更正是对的，我原话「`(η_s/η_t)` 的幂要重算」不准确。
**更重要的是 agent 查出 Lemma 5.7 只证了一半**：(5.34) 是定理，**(5.35) 只是 `Step2.Hyp.eG` 假设、(5.36) 只经停时鞅假设进入**。
不论 Step 2 走哪条路线，这两条都得立成定理——开 **T155**（(5.35)）、**T156**（(5.36)）。截断方案的另两个缺口开 **T158**；收尾改为概率层面的穿越论证 + 时间网。
内禀超线性不止 (5.50) 一处（(5.36) Case 2 有 `(J*)²`/`(J*)³`，(5.35) Case 2 有 `(J*)^{3/2}`），全都带 `A^{−1}`，安全。
**T132b/T146 查出的 `MomentDuhamel.Hyp` 三处缺陷**（`genLK` 多 `/W`、`integrable` 过度量化、`∫` 括号）+ 缺 Lyapunov → **T154**。`genLK` 那一处我在 T132a 抽查时漏看了。


## T148：`LDENetClose` **按字面不可证**——证明了它等价于一个为假的下界（`Gauss/LDENetClose.lean`，992 行，2026-09-21）

工单的第 0 步（条件化 + 不单位化 + 加地板）**走通了**，但终点不是把 `LDENetClose` 卸掉，而是把缺口**收缩成一条具名的、可判定为假的输入**。

**`ldeNetClose_of_lower_bound`**：在（现已是定理的）确定性模之下，`LDENetClose` **等价于**
控制的多项式下界 `N^{−B} ≤ ζ(u)`，对 `u` 与非对角对一致。
**而这个下界是假的**：`ζ(u) = ∑_{k∈band(i)} S_{ik}|G^{(i)}_{kj}(u)|²` 对带距 `d(i,j)` 是**指数小**的——
这正是 (2.76)/(4.3) 的内容。**所以 `LDENetClose` 隐含地要求比「T143 把引擎重写以摆脱的那个下界」严格更强的东西。**

**无条件证出来的（地板版）**：
* `abs_ldeRow_flow_sub_le`/`abs_ldeCol_flow_sub_le`——**(4.2) 两侧沿流的确定性 Hölder-1/2 模**，
  `≤ 6R^10(|√u−√v| + |u−v|)`（`R` 同时界住 `η_u⁻¹`、`|Idx|`、`‖X‖`；指数 10 故意不最优）。
* `stochDom_ldeRow_flow_floor`/`stochDom_ldeCol_flow_floor`/`ldeFlowDom_floor`——
  **(4.2) 对 `u ∈ [s_N,t_N]` 与对非对角对一致，带一个加性地板**：对每个 `B ≥ 0`，`ldeRowLHS(u) ≺ ldeRowRHS(u) + N^{−B}`。
  假设只有 `|E| < 2`、`0 ≤ s_N ≤ t_N < 1` 与确定性区制界 `N^{−K} ≤ η_{t_N}`。
  **不要 `LDENetClose`、不要 `‖X‖ ≤ N`（T109，本就无条件）以外的好事件、不要非对角衰减、不要局部律。**
  网距 `δ_N = (N^{−(10K+12+B)})²`；定时输入是 T143 无条件的 `unifDomIcc_ldeRow/_ldeCol`，经新增的 `UnifDomIcc.mono_control` 放松。

**地板吸不掉。** T135 的 `of_highProb_add_rpow_neg` 要的是**同一个**多项式下界。
**所以消费者要改形状**：`Hierarchy/LKDecayQuant.LDEFlowDom` 需带 `+ N^{−B}` 重述（`Hierarchy/` 的改动，按协议未做）。
探针 B（临时、import `LKDecayQuant`）端到端验证过：`LKDecay` 仍然只携带三条实质假设
（`hΩ`、`hdecay`，以及**代替 `LDENetClose` 的** `hlow` + `hΞ`/`hΞX`）——**数量没变，但第三条现在是一条显式可判的不等式**，
而不是一个两分句的网比较。

**缺的工具不是高斯过程工具**（与工单的备案相反）：多项式规模的网上做并界已经打赢 `e^{−N^{2τ}}` 的尾，T143 的引擎做的就是这件事。
**缺的是相对模 `‖∂_u ĉ(u)‖ ≤ N^K‖ĉ(u)‖`**——分子要小方阵 Green 列的非对角衰减（仓库**没有**：`Green/Minor.lean` 与
`Gauss/MinorReplace.lean` 只有逐元界 `≤ η⁻¹` 与 `GoodEvent`-条件下的 `Ψ` 界），分母还要 `‖ĉ(u)‖` 对 `u` 一致的**下界**，
即 `u ↦ G^{(i)}_{·j}(u)` 的反集中——**仓库和论文里都没有**（论文这一步的连续性论证是隐式的）。记 paper-deltas #111。

**小偏差**：模是**逐元素**证的（`norm_green_sub_apply_le_of_entries`），多付两个 `|Idx|` 因子，
因为仓库没有主子矩阵的 `ℓ²→ℓ²` 算子范数界。

## `MomentDuhamel.lean` 的三处缺陷全部修复（2026-09-21）

接 T132b（`genLK` 的 `W`、`integrable` 的过度量化）与 T146（paper-deltas #108 的括号）。
`lake build RBM1D` exit=0，公理审计通过；只动了 `MomentDuhamel.lean`、`MomentDuhamelRhs.lean`、`MomentDuhamelGauss.lean`。

1. **`genLK` 的 `/ W` 删掉了**，docstring 重写（原文「只有方差剖面 `S^{(B)}/W` 进来」正是误读的根源，现在明写
   `Sblk L W i j` **本身就是** `E|X_ij|²`）。下游 `Gauss.W_mul_genLK_eq` 随之作废，改为 **`Gauss.genLK_eq`**（证明是 `rfl`，已编译）。
2. **`Hyp.integrable` 按窗口量化**（`s N ≤ u → u ≤ t N →`），与 T145 对 `drift` 的处理逐字一致。
   调用点两处；其中 `hrhs_of_moment_inputs` 原来拿不到 `s N ≤ t N`（`v` 与 `t` 无关系），
   故**新增假设 `hvt : ∀ N, v N ≤ t N`**——不增加负担，唯一的消费者 `stochDom_of_momentDuhamel` 本就有 `hv2`；
   探针验证 `hrhs_of_moment_inputs` 仍可**裸应用**填进 `hrhs` 槽。
3. **括号修好了**，`pp.parens` 复核为三项/五项真和、无嵌套。**T146 预测的多余因子确实掉了出来**：
   `hnum` 第三个被加项由 `2 * ((v−s) * (…)^{1/2})` 变成 `(…)^{1/2}`。

**因此 STATUS 上一节（T132b）里关于这两处缺陷的描述已过时**：T132b 现在只剩两条矩不等式与高斯实例本身，
外加它自己报告的两个缺生产者（`u ↦ Kval` 的时间可微性、固定 Hermitian `M` 时 `u ↦ gloop` 的可微性）。

## T154(4)：Lyapunov 落地，`hEEmom` 的阶数落差不再是障碍（2026-09-21）

T146 报「唯一真正缺的引理」是 Lyapunov `‖·‖_p ≤ ‖·‖_{2p}`。现已证出，且**不是裸手 Jensen/Hölder**：

* **桥** `MomentDuhamel.momNorm_eq_eLpNorm_toReal`：`momNorm P r Y = (eLpNorm Y r P).toReal`，
  **不需要可积性**——`|Y|^r` 不可积时 Bochner 积分为 `0`、lintegral 为 `∞`，两边同为 `0`。
* **Lyapunov** `MomentDuhamel.momNorm_le_momNorm_of_exponent_le`：`p ≠ 0 → p ≤ q → Integrable (|Y|^q) → momNorm P p Y ≤ momNorm P q Y`（`[IsProbabilityMeasure P]`）。

**假设是最弱的那一组**：`p = 0` 时左边恒为 `1`、命题假；没有 `q` 阶可积性时右边被 `integral_undef` 打成 `0`、命题也假；
而**不需要 `Y` 的可测性假设**——`momNorm` 只看 `|Y| = (|Y|^q)^{1/q}`，`|Y|^q` 的可测性已含在 `Integrable` 里。
`Hyp.integrable` 对每个阶数都给，消费者全能满足。

核心 Mathlib 引理是 `MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le`，**它本身不要求可测性**——
所以 T146 担心的「桥会需要消费者给不出的可积性侧条件」没有发生。

**接线通了**：`Gauss.hEEmom_of_momNorm_two_mul` 让 `hrhs_of_moment_inputs` 的 `hEEmom` 由 `2p` 阶界直接得出，
**常数 `C` 与控制 `ΦE` 原样不变**，可积性用的就是该定理已经在收的 `hintEE`，调用方零额外代价。
于是 `hEEmom` 现在只差**输入**——把 T135 的 `stochDom_norm_eeField` 变成 `MomentDom` 要的确定性包络，那是 T157 的范围。

## ⚠ Theorem 2.6 的保真缺口（Cowork 分析，2026-09-21；**暂不开单**，Jun：先做六步）

`Flow/Universality.lean` 的 `OUFlow` 只记路径（Hermitian、`H_0 = H`），**未钉死分布**。取常值流 `H_t ≡ H`：
`Claim223`/`StepTwoClaim` 平凡成立（差为 0），`GreenComparison` 的结论平凡，而 **`DBMUniversality F` 恰好就是 (2.18)**——
`theorem2_6_of_steps` 实际上假设了结论。**任何人不得用常值流或其他 fiat 流去「卸」这些假设。**
修法（六步完成后开单）：钉死 `H_t := e^{−t/2}H + (1−e^{−t})^{1/2}G`（`G` 为独立 GUE）；[51] 与 [37]/[70] 写成**对任意满足前提的模型**成立的一般形式，前提（能量窗一致的局部律等）由我们证；
(2.25)（[70] Lemma 4.18）用带时间生成元恒等式自证（高斯情形是等式），(2.31)、`η Im m` 单调性自证。完整分析在项目文档 `claude/theorem-2.6-analysis.md`。


## T151：分级 `FlucGain` 的改接——**三件事里有两件是「已经不是问题了」**（`Gauss/Eq45FlowInputs.lean`，2026-09-21）

**1. 消费者搬到分级接口：数学上完成。** `eq45Flow_of_localLaw_gain` 对 `hg` 的全部用法只有两处
（`unifDomIcc_flucRow_condExpDiag` 与 `unifDomIcc_flucBlk_condExpDiag`），都经 `integral_norm_flucAvg_pow_le_iter`
在**字长 ≤ 2p** 处用——**所以工单说的「只需 `M = 2p`」是对的**。
但分级接口还多要一样东西：`FlucGainUpTo` 的 `B` 允许随 grade 变（T142 的确实变），而 `UnifDomIcc` 的控制必须与 `p` 无关。
对齐办法就是 T137 在 `momentDom_flucAvg_iter_graded` 里用的因子分解 `Bp p N ≤ Kp p * Bm N`
（`Kp p` 与 `N` 无关，被 `unifDomIcc_of_moment` 本来就允许依赖 `p` 的常数吞掉）；
**在 T142 的参数下这个分解取等**（`Kp p = 2 + 2·minorDiffC(2p)`、`Bm = Ψ`），**不花任何代价**。
落地：`unifDomIcc_flucAvg_iter'` 及两个权重特例、`unifDomIcc_flucRow/flucBlk_condExpDiag'`（**结论与不带撇的逐字相同**）、
`flucRowFlow_of_gain'`/`flucBlkFlow_of_gain'`。不带撇的版本一字未动。

**⚠ 只剩一个文件边界问题**：`eq45Flow_of_localLaw_gain` 在 `CondStableFlow.lean`，而 `CondStableFlow` import `Eq45FlowInputs`，
方向反了，带撇消费者写不进生产者那个文件。**但它只有三行**——中间层 `eq45Flow_of_unifDom_ibp`（`CondStableFlow.lean:1097`）
本来就把两个槽当**裸 `UnifDomIcc` 假设**收，生产者原样插进去即可。**已落地**：`eq45Flow_of_localLaw_gain'`（`CondStableFlow.lean:1240`，纯新增，不带撇版一字节未动），
`lake env lean` exit 0、零 warning，公理干净，证明体是裸应用、无 `convert` 无强制转换，**结论一字未弱**（仍是 `StepGlue.Eq45Flow`）。
假设表的净变化：`hg` 换成分级形式；`hpos`/`hρ1`/`hcρ3`/`hcρ1`/`hΦW` 五条换成 `hKp`/`hBK`/`hΨpos`/`hΨhalf`/`hΨW'` 五条，
其中 **`hΦW` 整条消失**、两条 `hcρ` 合成一条 `W⁻¹ ≤ 4Ψ²`。

**2. `flucGainUpTo_of_minorDiff` 早就是定理了——T147 审计的 §6(b)⑤「只存在于探针里」是过时的。**
那是 T137 时代的状态；**T142 已经落地**：`MinorDiffGain.lean:1239` `flucGainUpTo_of_minorDiff`、
`:1249` `flucGainUpTo_of_minorDiff'`（锐强度 `B = 2Ψ + 2·minorDiffC M·Ψ`、`ρ = 2Ψ`），
无 import 依赖的那半（`MinorDiffGainUpTo`、`flucGainUpTo_of_minorDiffGainUpTo`）在 `FlucIterHigh.lean:898/917`。
**所以 `FlucIterHigh.lean` 没有可做的事，一行未动。** 从 `MinorGood'` 到 `Eq45Flow` 的链现在是通的，
只剩上面那三行的位置问题与 `MinorGood'` 自身的生产者（仍是 T142 记的开放项）。

**3. `hΦW`/`hΨW` 重算：`hΦW` 整条消失。** T142 把控制降到 `ρB = 2Ψ·Ψ = 2Ψ²`，于是
`flucPhiW_of_psiW` 由 `hΨW` 一次 `τ/2` 劈分即得——**`hΦW` 不再是消费者的假设**；
两条 `hcρ`（`(3W)⁻¹ ≤ ρ²` 与 `W⁻¹ ≤ ρ²`）在 `ρ = 2Ψ` 下合并成一条。
打包成 `unifDomIcc_flucRow/flucBlk_condExpDiag_psi`，签名里只剩 `hΨW`、`hΨpos`、`hΨhalf`、`hΨlow`。
**T142 说的「对生产者是负代价」在消费者侧同样成立：这次重算是净删假设，不是替换。**

**据此更正 T147 审计的两条**：§6(b)⑤ 应删除（桥已落地）；§6(b)④ 的「重算 `hΦW`/`hΨW`」实际结果是 `hΦW` 被消掉。

## Jun 的裁定：外部输入的边界（2026-09-21，永久规则）

1. **全项目唯一允许的外部输入是 Theorem 2.6 Step 1 的 [51] 主定理**，且必须**逐字**按其陈述写成假设（量化在所有满足其前提的模型上），**不得编造「类似的结论」作为 input**。
2. **最终的 Lean 报告必须写明：Universality 部分用到了外部 input，其余全部是独立完整的 Lean。**
3. 其余全部自证：Step 2 的相关函数比较（[37] Thm 15.3 + [70] Prop 4.17，**不再作假设**）、(2.25)（[70] Lemma 4.18）、(2.31)（[70] Lemma 4.20）、§7.2。
现有的 `RBM.DBMUniversality`（特化到我们的流、跳过前提）与 `RBM.GreenComparison`（外部假设）**都不符合这条规则**，Theorem 2.6 开单时要替换/卸掉。
**附带发现（待 Jun 判断）**：[51] 的 Theorem 2.2 字面上是实对称模型（`V + √t·GOE`），而本文的矩阵是复 Hermitian；β = 2 似乎在 [51] §8 处理。详见项目文档 `claude/theorem-2.6-analysis.md` §7。


## T155：(5.35) 从假设变成定理（`Hierarchy/Lemma57.lean`，1066 行，2026-09-21）

pp.59–61 全链证出，`lake env lean` exit=0，六条主结论 `#print axioms` 只有三条标准公理。

| 论文 display | Lean |
|---|---|
| 近场 `b`-求和切分 (5.53)+(5.54) | `card_zdist_le`、`sum_le_split_one` |
| 远场 Case 1/Case 2 切分 | `sum_le_split_two`（Case 1 至多 `4ℓ*_u+4` 个格点） |
| (5.58)+(5.31)+(5.32) ⇒ Case 1 逐点 | `case1_pointwise`（论文的 "WLOG" 拆成 `a₁`/`a₂` 两个对称假设，**两支都证**） |
| (5.60)+(4.2)+(5.31) ⇒ (5.61) | `case2_pointwise` |
| (5.62) 的求和核 | **`sum_sqrt_tailT_mul_le`**（新造的轮子，见下） |
| (5.55)/(5.63)/(5.35) | `eG_near_le`、`sum_far_le`、**`eG_le`** → `eG_le_paper`（形状 1）、`eG_le_reduced`（形状 2） |
| (5.60) **从 3-loop 定义证出** | `gloop_three_expand` + `norm_gloop_three_le`，**无常数损失** |

**新造的轮子（已先查过）**：`sum_sqrt_tailT_mul_le`，即
`∑_b √(T(‖a₁−b‖))·√(T(‖a₂−b‖)) ≤ (168ℓ_uA_u⁻¹ + L√(W^{−D}))·√(T(‖a₁−a₂‖))`——
论文 `∫₀^a exp(−√((a−x)/2) − √(x/2) + √(a/2))dx ≤ C` 的离散版。
仓库里**只有全指数版** `sum_tailT_mul_tailT_le`，半指数版没有、也用不上全指数版。

### 形状 2 的远场括号**逐字落实了 T132c 第 0 步的预言**
```
cFar · (r·√r·(√A)⁻¹·J)  +  169 · (r·A⁻¹·(J·√J))
```
即 `r^{3/2}A^{−1/2}·J* + r·A⁻¹·(J*)^{3/2}`——主项 `J*` **一次**、次主项 **3/2** 次。指数表的结论完全对上。
（**但近场项是 `r³` 不是 `r²`**，指数表只算了远场，这条是新的，记 paper-deltas #112 ④。）

### Case 2 的 `(J*)^{3/2}` 不可降——**确认，不是驳回**
(5.61) 是三条 `G` 边各出一个 `√(J*·T)`。降幂只能把其中一条换成 (2.73) 的 `√(rA⁻¹)`（不带尾函数）：
换掉 `a₁–a₂` 边则 `sum_far_le` 前置的 `√(T₁₂)` 没了、**缺 `T^{1/2}`**；换掉 `a₁–b` 或 `a₂–b` 边则 `T₁₂` 一点都拿不到，更糟。
这在 Lean 里**结构性可见**：Case 2 分支写成 `J√J·√T₁₂·∑_b(√T₁ᵦ√T₂ᵦ) ≤ J√J·√T₁₂·C·√T₁₂ = J√J·C·T₁₂`，
`√T₁₂·√T₁₂ = T₁₂` 这一步就是全部理由。

### 留作假设的（边界清楚）
* **(5.51)/(5.52)** 是假设 `hEG`——**仓库里 `E^{(G)}` 根本没有定义**，`Step2.Hyp.eG` 的左端是抽象的 `H.F − eLL`，(5.51) 的展开无处可接。
* **(5.56)/(5.58) 的 Schwarz 步**是假设 `h558a/h558b`（逐字抄 (5.58)）。已验证它可从 `gloop_three_expand` +
  `gloop_two_plus_minus_blocks`（`∑_{x₁,x₂}|G|² = W²L_{(+,−)}`）+ AM–GM 证出、常数 1/2，但没做（时间给了保 Case 2 落地）。
  **这是最值得接的下一步。**
* (4.2)/(4.5)/(2.73)/(2.74)/(5.31) 按工单许可作假设；**(5.32) 是证的**（走已有的 `tailT_sub_le`）。

### ⚠ 重复劳动（「造轮子之前先查」又漏了一次）
`Lemma57.inv_sq_le_tailT`（`C = 1`）与已有的 `Step45.inv_sq_le_tailT`（`C = 6`）是**同一条引理的两个常数版本**，
两个文件互不 import，所以谁也查不到谁。**建议下沉到 `Analysis/StretchedExp.lean` 做成带参数 `C` 的一条。**

### 与 `Step2.Hyp.eG` 的对接
`eG` 用的 `B.scale E N u`、`tT B E N D u ℓ`、`jS` 与本文件的写法**定义相等**，`eG_le_paper` 的结论逐项对得上 `eG` 的右端。
真正的接线缺口只有上面的 (5.51)/(5.52) 与 `H.F − eLL` 的关系。`Step2.lean` 的签名未动。

## T149：拆 `Steps` 包 + `0 ≤ s`（2026-09-21，Claude Code）

**全量 `lake build RBM1D` exit=0**，`axiom audit: 8667 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]`。
`Steps` 结构**一个字段都没动**；所有改动要么是**新增声明**，要么是**放宽假设**（单调加强），没有改过任何结论。

### (a) 打包上的循环已解开

`Flow/Hypotheses.lean` 新增 5 个 `def`，**逐字**等于 `Steps` 里被投影到的那五个字段
（探针验证 `h.apriori : AprioriFlow …` 等五条都是 `:=` 直给，定义相等）：

`AprioriFlow`（2.73）、`LocalLawFlow`（2.75）、`AprioriDecayFlow`（2.76）、
`SharpLoopFlow`（2.77）、`SharpLmKFlow`（2.78）。

先用 `grep` 复核了 T147 的投影清单，**全树确实只有那 5 个投影**（另加 `Flow/Hypotheses.lean`
自己的 `BoundsCore_of_Steps`/`Bounds_of_Steps`，它们是合法的消费者）。

带撇版（**旧签名全部保留，改成一行推论，所以两边不会走样**）：

* `Hierarchy/StepGlue.lean`：`flow_S_zero'`、`flow_lkErr_one_le'`、`flow_S_one'`、
  `aprioriDecay_pm'`、`flow_S_le_two'`、`flow_sharpLoop_glue'`、`flow_steps45_glue'`
* `Hierarchy/ChargeReduce.lean`：`aprioriDecayAll_of_pp'`
* `Hierarchy/Step2PP.lean`：`flow_xiL_apriori_le'`、`flow_xiLK_one_le'`、`xiLK_two_improve_of'`、
  `xiLK_two_improve'`、`flow_S_le_two_of'`、`flow_hs2_of'`、`flow_sharpLoop_glue_of'`、
  `flow_steps45_glue_of'`、`flow_sharpLoop_glue_flowAs'`、`flow_steps45_glue_flowAs'`
* `Gauss/Step6Hyp.lean`：`quad11_unifDetDom'`、`quad13_unifDetDom'`、
  `quad11_unifDetDom_gauss'`、`quad13_unifDetDom_gauss'`

### 验收探针（scratchpad，不入库）：**两个都过，公理干净**

1. `steps_of_inputs`：按 1→2→3→4/5→6 的依赖序串起来，**结论是 `Steps X E s t`，假设里没有
   `Steps`**。链条是 `Step1.step1` → `Step2.step2` → `Step2PP.flow_sharpLoop_glue_flowAs'` →
   `Step2PP.flow_steps45_glue_flowAs'` → `Gauss.quad11/13_unifDetDom'` →
   `Step6.sharpExpect_step6`。携带的假设都是随机层接口或别处的工单
   （`Step1.Hyp`、`Step2.Hyp`、`hΘ`（由 `Step2PP.xiLK_two_le` 从 `BootPP` + `hB.LmK 2` 生产，
   也不是 `Steps` 的字段）、`Lemma514`、`Eq45Flow`、`FlowEq548`、`Step6.Hierarchy`/`FastDecayHyp`
   等），**没有一个是 `Steps` 的字段**。
2. `steps_of_inputs_nonneg`：同一条链在 `hs0 : ∀ N, 0 ≤ s N` 下，把 Step 2 的两个输出
   （`LocalLawFlow`、`AprioriDecayFlow`）当假设收——1、3、4、5、6 **全部在 `0 ≤ s` 下走通**。

### (b) `0 ≤ s`：走到了 Step 2 的门口就停住，原因不是记账

`Band.scale_pos'`（`0 ≤ t`）已落地，`Band.scale_pos` 成了它的一行推论。顺带把两条传播子引理
**就地放宽**（只动假设）：`RBM.one_le_ellHat`（`Propagator/Decay.lean`）与
`RBM.etaT_mul_ellHat_le`（`Loop/KBound.lean`）现在收 `0 ≤ t`——证明本来就不用严格正性。

`hs0 : 0 ≤ s N` 现在成立于：`Step1`（全部，含 `inv_W_le_inv_scale`、`norm_Lval_le_of_le_half`）、
`Step3`、`Step45`、`StepGlue`、`Step2PP`、`ChargeReduce`、`Step2Moment`、`EEBridge`、
`LKDecayQuant`（除 `lemma514_flow_of_flowInputs`）、`SumZeroDyn.flow_crude`、
`Gauss/XiLow`、`Gauss/Step1Hyp`、`Gauss/Lemma41FlowGauss`、`Gauss/Step6Hyp`（含
`lkErr_le_rpow`、`lkErr_loopData_le_rpow`）、`Step2.localLaw`/`eventually_step_facts`。

**仍然需要 `0 < s` 的，且 T147 §0b 低估了它**：

* `Step2.jS_highProb` → `jS_stochDom` → `Step2.aprioriDecay` → **`Step2.step2`**。
  底在 `Step2.step_bound`，它用 `RBM.norm_Uker_flow`（要 `0 < v`）。
* `SumZeroDyn` 的 `integral_term_stochDom`、`termI1`、`QV_Q_stochDom`（以及它们的下游
  `termI2/I3/I4`、`termM`、`lemma514_flow`），底在 `integral_term_le`、
  `norm_Uker_sumZero_scale_le`、`norm_Uker_fastDecay_le_sumZero`，这三条又都要
  `norm_edgeKer_sub_one_sub_le` → **`norm_Theta_mul_sub_le`**，而 `Propagator/` 里
  `Θ_t` 的一阶/二阶差分估计**整族只对 `0 < t` 证过**（`ρ(t)` 那套闭式）。
  因此 `SumZeroDyn.lean` 整个文件**原样退回**（`git checkout`），只有 `flow_crude` 放宽了。
* `Flow/Hypotheses.BoundsCore.stochDom_norm_Lval`：它走 `norm_Kgen_le`（要 `0 < t`）。
  **无消费者**——`0 ≤ t` 的版本是 `Flow/Iteration.stochDom_norm_Lval_of_LmK`，早就有了。

**结论**：`0 ≤ s` 在**总装层面**（Steps 1、3、4、5、6 + 全部 glue）是通的；要让
`Thm221.step` 在 `s ≡ 0` 处真的可填，还差的不是记账，而是把 `Propagator/Decay.lean` 的
`Θ_t` 差分估计（`norm_Theta_sub_shift_le`、`norm_Theta_second_diff_le` 一族）延拓到 `t = 0`。
`t = 0` 处 `Θ_0 = I`，界本身平凡为真，但现有证明全部经过 `ρ(t)`，要单独分情况。
**这值得单开一张工单**（估计：`Propagator/Decay.lean` + `LongDiff.lean` 的 `ht0` 一族，
再加 `KernelDecay.lean` 的三条 `Uker` 引理）。

## T160：带地板的 (4.2) 接上了，**`LKDecay` 现在只剩两条实质假设**（`Hierarchy/LKDecayQuant.lean`，2026-09-21）

新增 `LKDecayQuant.LDEFlowDom'`（旧的 `LDEFlowDom` 一字未动）：T148 的 `Gauss.ldeFlowDom_floor` 的逐字形状，
**外加对地板指数 `Bex` 的全称量化**——地板必须**在消费者选定目标指数之后**再选，这是它被吸收的关键。

**地板不是被「吸收引理」消掉的**，而是顺着 (4.10)→(4.11)→(4.2)→Lemma 5.9 推下去的：
**它进入的位置与 (2.76) 的误差 `δ₂` 完全相同**（同一个括号里的加项）。于是新证了一条平行链，
全部是**新增**声明（`Green/EntryBound.lean` 与 `Hierarchy/Decay.lean` 一个字没碰）：
`LDERowFloor`/`LDEColFloor`、`norm_sq_green_le_{row,col,two_sided,blk,of_far}_floor`、
`loopDecay_gloop_of_event_floor`、`lemma59_floor`，以及 `FlowGoodSet'`/`FlowInputs'`/`FlowLDE'` 那一整套带撇版。

地板取成**与 (2.76) 误差同一个 `ε_N`**，所以 `FlowInputs'` 与 `FlowInputs` 唯一的差别是数值束由
`Φ√ε ≤ N^{−D'}` 变成 `Φ√(2ε) ≤ N^{−D'}`；`flowNum_choice'` 照样满足（多付一个 `N^{−2}`）。
**`lkDecay_of_inputs'` 的结论是原样的 `SumZeroDyn.LKDecay`，不带任何地板——地板没有传到下游，`LKDecay` 的消费者一个都不用改。**

**探针验证**（`ProbeT160.lean`，import `Gauss.LDENetClose` + `Hierarchy.LKDecayQuant`，exit=0、公理干净）：
`hlow`/`hΞ`/`hΞX` **全部消失**，`LDENetClose` 不再出现，`LKDecay` 只剩 `hΩ`（T130）与 `hdecay`（`Steps.aprioriDecay`）。
`LDEFlowDom'` 由 `ldeFlowDom_floor` 以**裸 `fun`** 填满，无 `convert`。

**一处必须说清楚的代价**：`ldeFlowDom_floor` 比原来的 `lkDecay_of_inputs` 多要三条**确定性区制条件**——
`hst : ∀ N, s N ≤ t N`、`hK : 0 ≤ K`、`hη : ∀ᶠ N, N^{−K} ≤ η_{t_N}`。它们是确定性的、属于区制本身
（消费者本来就有 `s ≤ t`），不是概率性假设，但签名里确实多了三个参数，**转派时别说成「零代价」**。

**`B ≥ 2D·log W/log N + 1` 的算术成立**（`N^{−2D log W/log N} = W^{−2D}`），且由 `W·L ≤ N`、`L ≥ 3` 得
`log W/log N ≤ 1`，所以 `B = 2D+1` 就够，Cowork 的式子是安全放大版。**但落地时没用到它**——
地板落进 (2.76) 那条本来就自由的误差预算里，不需要下游的 `W^{−D}` 地板来兜。
**Cowork 的判断（地板无害）对，理由比他说的更强。**

### 据此收紧 T148 那节与 paper-deltas #111 的措辞
「地板吸不掉、消费者要改形状」应读成：**形状只在 `LDEFlowDom` 这一层改**（新增 `LDEFlowDom'`），
`FlowInputs'` 只把数值束从 `Φ√ε` 换成 `Φ√(2ε)`，**`SumZeroDyn.LKDecay` 的陈述未变，下游零改动**。

### T107 的现状与计划（只报告，未动 `Lemma41FlowGauss.lean`）

**T107 确实早已停滞，而且目标文件 `RBM1D/Gauss/EntryBoundTime.lean` 从未存在过**
（`git log --all` 对该路径为空，全仓只有三处 docstring 指向它）。

* **`EntryBoundFlow` 能用同一个输入解掉，而且地板是白送吸收的**：它唯一的消费者
  `stochDom_indicator_offdiag_flow` 立刻把它与 `stochDom_indicator_entryControl_flow` 复合，
  而后者的控制带**无条件的** `W⁻¹`；由 `W·L ≤ N`、`L ≥ 3` 得 `N^{−1} ≤ W⁻¹`，取 `Bex := 1` 即可。
  只需一条约 15 行的常数吸收小引理，**`lemma41Flow`/`Step1.Lemma41Flow` 的陈述一个字都不用改**。
* **⚠ `DiagBoundFlow` 有一个真缺口，不能同法接上**：`diag_bound_stochDom` 除 row/col 外还要
  **`hLquad`（(4.7) 的二次型 LDE）** 与 `hLdiag`，而 **T148 只交付了 row 和 col 的带地板时间一致版**——
  `Gauss/LDENetClose.lean` 里没有任何 `ldeQuad`。补它需要 `stochDom_ldeQuad_flow_floor`
  与 `norm_sq_green_diag_sub_le_blk` 的带地板版，**是一张独立工单的量**，不该塞进 T107 的「纯接口重做」。

### 结构建议（待定）
本单新证的 6 条确定性带地板核是**纯矩阵引理、与 `Hierarchy/` 无关**，现在住在 `RBM.LKDecayQuant` 里。
`Gauss/` 可以 import `Hierarchy/`（已有五处先例），所以技术上能直接复用；但更干净的是
**下沉到新建的 `RBM1D/Green/EntryBoundFloor.lean`**，让 `LKDecayQuant` 与将来的 `Gauss/EntryBoundTime.lean` 都从那里取。

## T157：`hrhs` 的三项输入全部卸掉（`Gauss/MomentDuhamelRhs.lean`，649 → 894 行，2026-09-21）

`hrhs_of_moment_inputs` **一个字没动**，新增 6 条声明。

**两条通用步骤**
* `MomNormDom.control_mono`——关键的顺序发现：**`Lemma510` 的控制带时间 `u`，而 `hrhs` 要的控制不带**。
  正确做法是**先**用带时间的控制过 T77 的桥，**之后**在矩的层面放宽。这样就**不需要 `≺` 层面的控制单调性**
  （`Gauss.StochDom.control_mono` 在 `Gauss/Lemma41Glue.lean`，不在本文件的 import 闭包里；没有为它新加 import，也没有重证）。
* `stochDom_control_det`：`Y ≺ d·Ξ`（`d` 确定性）+ `Ξ ≺ Ψ` ⟹ `Y ≺ d·Ψ`。
  **这正是 `SumZeroDyn.F_stochDom` 对漂移做的那一步**，抽出来是因为 `E⊗E` 没有对应定理。

**三项输入**
1. **`hinit`**（`hinit_of_stochDom`）：`≺` 输入是 **`BoundsCore.LmK (n+2)` 逐字**——(2.68) 的控制本来就是确定性的
   `(Wℓ_sη_s)^{−(n+2)}`，**这一项从来就没有随机控制问题**。可积性取自 `Hyp.integrable`，调用方零额外代价。
2. **`hFmom`**（`hFmom_of_stochDom`）：`hdom` 的控制写成 `fun N p _ => g N (p.1 : ℝ)`，
   **`SumZeroDyn.F_stochDom` 的结论逐字落进去**。唯一新增的实质假设是
   `hgle : ∀ N u, s N ≤ u → u ≤ v N → g N u ≤ ΦF N`（把带时间的控制在窗口上取一致上界；窗口可短于 `[s_N,t_N]`）。
3. **`hEEmom` 的输入**：两步。`stochDom_norm_eeFun_det` 收 **`EEBridge.stochDom_norm_eeField` 逐字**
   （控制带随机因子 `Ξ^{(L)}_{u,2(n+2)+2}`）加 `hxiL`（就是 `xiRhs_stochDom` 收的那个 `hY`，换到回路长 `2(n+2)+2`），
   输出确定性控制并顺带把 `eeField` 换成 `eeFun`；再接 T154 的 Lyapunov 产出 `p` 阶矩的 `hEEmom` 槽。

**合成全部探针验证过**（exit=0，已删）：三者一起填满 `hrhs_of_moment_inputs` 的三个槽。

### 剩下什么（边界诚实）
* 三条新引理仍收 **T77 反向桥的侧条件**（可测性、确定性包络及其多项式增长、控制的多项式**下界**）。
  这些是**模型层事实**、不是关于 hierarchy 的陈述，仓库里都有对应件
  （`Gauss.integrable_lkT_pow`、`norm_gloop_sub_le_det`、`det_envelope_le_rpow`、`EEBridge.rpow_neg_le_eeControl`），接上是另一单。
* **`hFmom` 那条链的最后一环仍在文件外**：`hFmom_of_stochDom` 本身不需要 `Hierarchy`，但**要用 `F_stochDom` 生产 `hdom`**，
  调用方就得有一个 `SumZeroDyn.Hierarchy` 且其 `F` 等于 `Hyp.Fpath`——**T118 禁止实例化 `Hierarchy`**。
  这一环没有被绕过也没有被伪造：`hdom` 留成假设，形状与 `F_stochDom` 的结论完全一致。**它指向 T58/T163。**
* `momentDuhamelQ`（五项 `Q_t` 路线）依旧无消费者，不需要卸。

## Theorem 2.6 外部输入：方案 (A)（Jun 2026-09-21，Cowork 逐字核对后定）

**问题**：[51] Theorem 2.2（`paper/1609.09011v3.pdf`）字面只陈述 β = 1——§2 首句「W be a standard GOE matrix」，(2.9) 比较 `p_GOE`，§3 起的证明是 β = 1 的 DBM (3.1)；§8「General β-ensembles」是带势的不变 β-系综（Theorem 2.4），与矩阵模型 `V + √t·W` 无关。全文只有摘要声称「classical values of β … GOE/GUE」。我们的矩阵是复 Hermitian。

**方案 (B) 核对（`paper/0905.4176v2.pdf`，[51] 的参考文献 [35]：Erdős–Péché–Ramírez–Schlein–Yau, CPAM 63 (2010)）——不可用**，三条理由，任一条都致命：
1. **主定理不适用**：Theorem 1.1/1.2 是 i.i.d. 复 Wigner 矩阵、矩阵元分布满足 (1.5)(1.6)(1.8)（`C⁶` 光滑、高斯尾）。能套到一般初值上的只有 **Proposition 3.3**（辅助命题）。
2. **Prop. 3.3 是关于显式密度 `q_S(x; y)`（(3.5)）的陈述，不是关于矩阵模型的**：「`Ĥ + aV` 的特征值密度等于 `q_S`」来自 [13]（Johansson）的 Proposition 1.1（HCIZ 型公式）。要把 Prop. 3.3 接到我们的矩阵上，**必须再引一条外部结果**，违反「唯一外部输入」。
3. **前提 `𝒴_N`（(3.8)）要全能量域的局部律**：`sup_{Im z ≥ η} |N⁻¹Σ_j (z − y_j)⁻¹ − m_sc(z)| ≤ N^{−λ/4}`，其中 `η = η₀ t √(1−u²)`、`t = N^{−1+λ}`，**上确界取遍所有 `Re z`**（原文 (3.9) 的注：「after taking the supremum over all energies」）；另要 `sup_j |y_j| ≤ K`。论文 Theorem 2.3 只到 `|E| ≤ 2 − κ`，带状矩阵的谱边局部律在论文之外。

对照 [51] Theorem 2.2 的前提——`(g,G)`-正则只要求**局部窗口** `|E| ≤ G` 内 `c ≤ Im m_V ≤ C`（`g ≤ η ≤ 10`）加 `‖V‖ ≤ N^{C_V}`，结论直接是矩阵模型 `H_t` 的 `k` 点相关函数——与体区局部律严丝合缝。

**裁定 (A)**：唯一外部假设 = **[51] Theorem 2.2 逐字，只把 (2.1) 的 GOE 与 (2.9) 的 `p_GOE` 换成 GUE**；最终 Lean 报告写明「[51] 正文陈述 β = 1，此处使用其摘要所声称的 β = 2 版本」。已写入 `CLAUDE.md`「外部输入的边界」。Theorem 2.6 仍暂缓开单。

## T162 + T156：(5.58) 立成定理、(5.36) 立成独立逐点估计（`Hierarchy/Lemma57.lean` 1066 → 1942 行，2026-09-21）

### T162 前半：(5.58) 的 Schwarz 步已是定理
从 `gloop` 的定义一路打到 `case1_pointwise` 吃的形状：`norm_mul_three_le`（AM–GM，常数 1/2）、
块权 `blkW`、`sum_block_ite_real`（**从已有的 ℂ 版取实部导出，没有重证**）、
`sum_blkW_normSq`/`_conj`（`W⁻²∑_{x∈I_b,y∈I_a}|G_{xy}|² = L_{(+,−),(a,b)}`，后者走 `Gsig_conjTranspose`）、
**(5.56)** `norm_gloop_three_le_schwarz`、3-loop 旋转 `gloop_rot1`、**(5.58)** 的两个对称分支 `gloop_h558a/b`（+ 去掉无害 ½ 的带撇版）。

**验收达成**：`eG_le_paper`/`eG_le_reduced` 现在是关于具体 `RBM.gloop` 的定理，**假设表里没有 `h558a`/`h558b`**，
取而代之的是 (5.57) 的两个取向 `h557C`/`h557R`。抽象版保留，改名 `eG_le_paper_of_schwarz`/`eG_le_reduced_of_schwarz`；
master `eG_le` 原样不动。
**一处必要的内部调整**：`h558a/b` 里 2-loop 的**取向**改成 loop 展开真正产出的那个——
`L_{(+,−),(a,b)}` 在一般（非实对称）`H` 下**不对称**。

### T162 后半：`inv_sq_le_tailT` 去重完成
`Analysis/StretchedExp.lean` 新增 `RBM.inv_sq_le_tailT`（`C` 作参数）；`Step45.inv_sq_le_tailT`（`C = 6`）与
`Lemma57.inv_sq_le_tailT`（`C = 1`）都改成一行推论，**两个旧名和旧陈述一字未改**。

### T156：(5.36) 立成独立逐点估计
`ee_near_le`（(5.64) Case 1，近段吃 (2.73) 的 `n = 6`，远段留显式余项）、`case2a_pointwise`/`case2b_pointwise`
（(5.67)+(5.71)/(5.72)）、`sum_ee_far_le`/`ee_far_le`、**`ee_le`/`ee_le_paper`**。
(5.72) 的卷积直接用仓库已有的 `sum_tailT_mul_tailT_le`——**这次没造新轮子**。

### ⚠ 更正 T132c 审计的一条：「(5.36) 的内禀项都带 `A^{−1}`」**只对了一半**
内禀性本身**确认**（Case 2(1a) 的 `(J*)²`、2(1b) 的 `(J*)³` 都换不掉，理由与 (5.61) 同构、在 Lean 里结构性可见：
(1a) 的四条 `G` 边分成两对、每对出一个 `J*T`，左端要 `T²` 归一化，两个尾函数缺一不可；
(1b) 的 `(G†E_bG)_{x₁x₁'} ≺ J*T(‖b−a₁‖)` 提供第三个尾函数，正是卷积凑出第二个 `T(‖a₁−a₂‖)` 所必需）。
**但幂次不对**：过完 (5.22) 的 `W∑_b` 之后，
* **Case 2(1a) 是 `A^{−1/2}` 不是 `A^{−1}`**：`η_u^{−1}(ℓ_u/ℓ_s)^{3/2}A_u^{−1/2}(J*)²`，
  来自 (5.66) 的 `(4\text{-loop})^{1/2} = (ℓ_u/ℓ_s)^{3/2}A_u^{−3/2}` 乘上 `Wℓ*_u = (A/η_u)(log W)^{3/2}`。
  **这正是 (5.36) 自己写的 `(Wη_uℓ_u)^{−1/2}`。**
* Case 2(1b) 确实是 `A^{−1}`：`36η_t^{−1}A_t^{−1}(J*)³`。

不影响安全性（(5.36) 本来就声明 `A^{−1/2}`），但**指数表若按「都带 `A^{−1}`」算 `β*` 会偏乐观半格**。

### 未完成（如实报告）
* **`hsym` 未卸**（paper-deltas #113 ②）——需要 (5.22) 的 `k = 2` 项，属另一张单。
* **(5.65)/(5.66) 的 Cauchy–Schwarz 步仍是假设 `h566`**：要 6-loop 的逐元展开（`gloop_three_expand` 的 6 元版）
  + `G†E_bG` 的块结构。这轮把 3-loop 那一层（(5.56)/(5.58)/(5.60)）打穿了，**6-loop 那一层没动**。
* `h572`（`(G†E_bG)_{x₁x₁'} ≤ max_{y∈I_b}|G_{x₁y}||G_{x₁'y}|`）仍是假设。
* `eG_le`/`ee_le` 到 `Step2.Hyp.eG` / `Hyp.mart` 的接线没做；(5.51)/(5.22) 与 `H.F − eLL` 的关系仍是老缺口（T163）。

## T161：`Θ_t` 差分估计延拓到 `t = 0`，`Step2.step2` 在 `0 ≤ s` 下打通（2026-09-21，Claude Code）

**全量 `lake build RBM1D` exit=0、`errors: 0`**，`axiom audit: 8805 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]`。
**没有改过任何结论**：全部改动要么是新增声明，要么是把 `0 < t` / `0 < s` 放宽成 `0 ≤ t` / `0 ≤ s`（单调加强）。

### 第 0 步（工单要求的依赖清点）：**矩路线一条都不需要**

`Hierarchy/Step2Moment.lean` 的 `jS_stochDom` / `aprioriDecay_of_jS` / `aprioriDecay` / `step2`
**签名里本来就是 `hs0 : ∀ N, 0 ≤ s N`**。它们走 `MomentHyp`（矩输入束）+ `stochDom_timeIcc_of_holder`，
**完全不经过 `step_bound` / `norm_Uker_flow` / `Θ_t` 差分**。所以「矩路线需要放宽哪些」的答案是**空集**。

真正卡住的是**旧的逐路径路线**，链条只有一条、而且很短：

```
Step2.step2 → Step2.aprioriDecay → jS_stochDom → jS_highProb → Step2.step_bound
            → RBM.norm_Uker_flow → norm_Uker_le_of_tail → norm_Uker_tail_le_ellStar
            → norm_Uker_tail_le → norm_edgeKer_one_sub_one_le → norm_Theta_apply_le_of_real
```

**底只有一条**：`Propagator/Decay.lean` 的 `norm_Theta_apply_le_of_real`（(2.52) 实参数版，经 `ρ(t)`）。
中间各层的 `0 < t` 全是顺着传下来的，只有三处真用到严格正性：`abs_of_pos`（→ `abs_of_nonneg`）、
`B.scale_pos`（→ T149 已有的 `scale_pos'`）、以及 `(t:ℂ)*ξ ≠ 0`（复数版 (2.53) 的 `hξ0`）。

### 验收：**过了**（scratchpad `T161Probe.lean`，不入库）

`steps_of_inputs`（= T149 探针的逐字同一条链 1→2→3→4/5→6，结论 `Steps X E s t`）现在收
`hs0 : ∀ N, 0 ≤ s N`，**Step 2 的两个输出由 `Step2.step2` 现场生产、不再当假设收**，
`#print axioms` 只有 `[propext, Classical.choice, Quot.sound]`。T149 (b) 的缺口到此闭合。

### 改动清单

**新增（带撇版，旧签名一字未动、成为一行推论；`Propagator/Decay.lean`）**
`norm_Theta_apply_le_of_real'`、`norm_Theta_sub_shift_le'`、`norm_Theta_second_diff_le'`、
`norm_Theta_second_diff_le_inv_dist'`，外加三条 `ξ = 0` 的支撑引理
`ellHat_zero`（`ℓ̂(0) = 1`）、`norm_Theta_zero_sub_shift_le`、`norm_Theta_zero_second_diff_le`。

**新增（`Propagator/DiffComplex.lean`，去掉 `hξ0 : ξ ≠ 0`）**
`norm_Theta_sub_shift_le_complex'`、`norm_Theta_second_diff_le_complex'`、
`norm_Theta_second_diff_le_inv_dist_complex'`。

**新增（`Propagator/LongDiff.lean`，`ht0` 一族）**
`sum_norm_Theta_zero_shift`、`norm_Theta_sub_shift_le_uniform'`、`norm_Theta_second_diff_le_three'`、
`sum_norm_Theta_sub_shift_le'`、`sum_norm_Theta_second_diff_le'`。

**就地放宽（只动假设，调用点全在同文件内，已逐一核对无外部调用者）**
* `Hierarchy/KernelDecay.lean`：`norm_edgeKer_one_sub_one_le`、`norm_Uker_tail_le`、
  `norm_Uker_tail_le_ellStar`、`norm_Uker_tail_le_sigma`、`norm_Theta_mul_sub_le`、
  `norm_edgeKer_sub_one_sub_le`、`norm_Uker_fastDecay_le_sumZero`、
  `norm_Uker_fastDecay_le_sumZero_sigma`（`0 < t` → `0 ≤ t`）
* `Hierarchy/Step2.lean`：`norm_Uker_le_of_tail`、`norm_Uker_flow`（`0 < v` → `0 ≤ v`）；
  `step_bound`（`0 < s N` → `0 ≤ s N`）；`jS_highProb`、`jS_stochDom`、`aprioriDecay`、`step2`
  （`∀ N, 0 < s N` → `∀ N, 0 ≤ s N`）
* `Hierarchy/SumZeroDyn.lean`：`norm_Uker_sumZero_scale_le`、`integral_term_le`（`0 < v` → `0 ≤ v`）

**下沉**：`Theta_zero : Theta L 0 = 1` 从 `Loop/Primitive.lean` 移到 `Propagator/Basic.lean`
（同名同签名同命名空间，`Loop/` 的六处使用者不受影响）——`Propagator/` 不能 import `Loop/`。

### 没做完的：`SumZeroDyn` 的流层扫尾**被持有中的文件挡住**

`SumZeroDyn` 的两条底（`norm_Uker_sumZero_scale_le`、`integral_term_le`）已经放宽，
但它上面还有 22 条 `hs0 : ∀ N, 0 < s N` 的流层签名（`integral_term_stochDom`、`termI1`–`termI4`、
`termM`、`termP`、`QV_Q_stochDom`、`F_stochDom`、`EE_stochDom`、`mart_of_QV`、`QV1_stochDom`、
`bound_qGood`、`bound_nonAlt`、`lemma514_flow`/`lemma514_flow'` 等）。这一串**全是机械的**
（`(hs0 N).trans_le` → `.trans`、`B.scale_pos` → `scale_pos'`），但终点
`SumZeroDyn.lemma514_flow'` 的**唯一外部调用者是 `Hierarchy/LKDecayQuant.lean:608`**
（`lemma514_flow_of_flowInputs`），该文件当前由别的 agent 持有，按协议没动。
在那之前扫这 22 条签名没有可观测收益，所以**整串原样保留**。
工单已声明旧路线「顺带即可」，且 `SumZeroDyn.Hierarchy` 带 fiat 风险、终将被矩路线替换。

### 顺带发现（未动）
`Propagator/Edges.lean` 的 `norm_Theta_long_edge_le`、`sum_norm_Theta_long_edge_le`（(3.35)/(3.36) 长边）
也只对 `0 < t` 证过，底是 `norm_Theta_apply_le_of_real` 与 `sum_norm_Theta_row_of_real`。
前者现在有带撇版可直接用；后者要另配 `t = 0` 支。不在 T161 的清单里，没动。

## T150：四条接线全部落地（2026-09-21）

1. **`hll : LocalLawUnifIcc`**（`Gauss/GoodSetFlow.lean` 追加）：通用的
   `unifDomIcc_of_stochDom_timeIcc`（证明就是探针 P7 那句 `measure_mono`——把 `(⟨u,hu⟩, a)` 塞进 `badSet` 的存在量词）
   + `localLawUnifIcc_of_localLawFlow`（桥接用 `llErr_eq`）+ `le_inv_rpow_half_of_scales`（由 `Step3.Scales.le_A` 给出时间无关上界，
   规范取 `Ψ N = (R²·As^{3/4})^{-1/2}`）+ 合成版 `localLawUnifIcc_of_localLawFlow_scales` / `localLawUnifIcc_of_steps`。
   **既有签名未改。**
2. **Step 6 的 `hint1`**：`Gauss.int1_gauss`（`integrable_sample_Lval` 取 `η := etaT E v`；`oneLoop` 的 `WF` 与长度条件都是 `rfl`/`le_rfl`）。
3. **Thm 2.5 的 `hint_pp`/`hint_pm`**：**新文件 `Gauss/Thm25Gauss.lean`**——全树没有同时 import `Flow/Universality`（`trGG`）
   与 `Gauss/Hierarchy`（`integrable_gloop_Hflow`）的文件，塞进 `DistEq` 会让一大片子树的依赖闭包变重。
   产出 `Hflow_one`、`integrable_trGG_Xmat`/`_trGGs_Xmat`、`int_pp/pm_thm25_gauss`，以及
   **`theorem2_5_gauss`：高斯模型的 Theorem 2.5，唯一剩下的假设是 `RBM.Thm221 (sample d) κ`。**
4. **三个时间 Hölder 模**（`Gauss/CondStableFlow.lean` 追加 `section Holder`）：T129 的 docstring 描述的组装方式**原样可行**，
   没有一处需要新估计。`wFluc`/`wDiag` + `norm_wFluc_sub_le`/`norm_wDiag_sub_le`（`∑|c_k| ≤ 1` 合成 T106 的 Green 模与 `condExpDiag` 模）
   ⟹ `holFluc_of_inputs` ⟹ `holRow_of_inputs`/`holBlk_of_inputs`；`holIBP_of_inputs` 另走 `‖uA_u − vA_v‖ ≤ |u|‖A_u−A_v‖ + |u−v|‖A_v‖`。
   **唯一的新假设 `HolConst` 是 regime 条件**（`η_{t_N}⁻¹ ≤ N^c`，来自 (2.72)），与 `Step1Hyp` 已携带的 `hη` 同类。
   三条的结论逐字就是槽位形状，**与消费者无关**，`eq45Flow_of_localLaw_gain` 与分级版 `'` 都能直接吃。

## T161：`Θ_t` 延拓到 `t = 0`；**矩路线一条都不需要**（2026-09-21）

### 第 0 步的答案是空集
`Step2Moment` 的 `jS_stochDom`/`aprioriDecay`/`step2` **签名里本来就是 `0 ≤ s N`**——它们走 `MomentHyp` +
`stochDom_timeIcc_of_holder`，**完全不经过 `step_bound`/`norm_Uker_flow`/`Θ_t` 差分**。
卡住的只有**旧逐路径路线**，链条短而唯一：
`Step2.step2 → aprioriDecay → jS_stochDom → jS_highProb → step_bound → norm_Uker_flow → norm_Uker_le_of_tail
→ norm_Uker_tail_le_ellStar → norm_Uker_tail_le → norm_edgeKer_one_sub_one_le → norm_Theta_apply_le_of_real`。
**底只有一条**（`Propagator/Decay.lean` 的 `norm_Theta_apply_le_of_real`）；中间各层的 `0 < t` 全是传下来的，
真用到严格正性的只有三处：`abs_of_pos`、`B.scale_pos`（换 T149 的 `scale_pos'`）、`(t:ℂ)*ξ ≠ 0`。

### 验收：过了
T149 探针逐字同一条链现在只收 `hs0 : ∀ N, 0 ≤ s N`，**Step 2 的两个输出由 `Step2.step2` 现场生产、不再当假设收**。
**T149 (b) 的缺口闭合。**

新增带撇版覆盖 `Propagator/Decay.lean`、`DiffComplex.lean`（顺带去掉 `hξ0 : ξ ≠ 0`）、`LongDiff.lean`；
就地放宽 `Hierarchy/KernelDecay.lean` 七条、`Hierarchy/Step2.lean` 七条、`SumZeroDyn` 两条（调用点全在同文件内，已 grep 核对）。
`Theta_zero` 从 `Loop/Primitive.lean` 下沉到 `Propagator/Basic.lean`（`Propagator/` 不能 import `Loop/`），六处使用者不受影响。

### 余留（未做，理由明确）
* `SumZeroDyn` 流层还有 **22 条 `0 < s`**（`termI1–I4`、`termM`、`QV_Q_stochDom`、`lemma514_flow'` 等），两条底已放宽、
  剩下全是机械替换；但终点 `lemma514_flow'` 的**唯一外部调用者 `LKDecayQuant.lean:608` 当时是持有中的文件**，
  在那之前扫这 22 条没有可观测收益。
* `Propagator/Edges.lean` 的 `norm_Theta_long_edge_le`/`sum_norm_Theta_long_edge_le`（(3.35)/(3.36)）同样只对 `0 < t` 证过；
  前者可直接用带撇版接，后者还要给 `sum_norm_Theta_row_of_real` 配 `t = 0` 支。不在本单清单内。

## ⚠⚠ T164 第 0 步：`MinorGood'` 按字面**是假命题**，`MinorDiffGain` 整支悬空（只读审计，2026-09-21）

### 反例（三条支撑引理已编译验证）
`Ω d := Coord d → ℝ`，所以 `ω = fun _ => 0` 是合法样本点。取 `E = 0`：
`Hflow d N u 0 = 0` ⟹ `G^{(S)}_{aa} = −z_u⁻¹`，而 `z_u = (1−u)i`、`m_E = i`，故
**`‖G^{(S)}_{aa} − m‖ = u/(1−u)`，与 `N` 无关**。
`MinorGood'` 的 `diag_sub_le` 要它 `≤ Ψ`，而链条自带 `hΨhalf : 2Ψ ≤ 1`，于是 **`u ≤ 1/3`**。
**只要 `u > 1/3` 这条假设就是假的**——而 Theorem 2.21 Step 2 的区制正是 `t > s ≥ 1/2`、`t → 1`。
一般 `E`：`−1/z_u = m_E` 当且仅当 `u = 0`，**对任何 `u > 0` 都有一个不随 `N` 变小的固定缺口**。

**不是零测例外**：`green` 在 `ω` 上连续、level-`N` 的 `G` 只依赖有限多个坐标，`{|ω_c| ≤ ε}` 有正测度，
所以把 `∀ ω` 换成 `∀ᵐ ω` **同样假**。
**不带撇的 `MinorGood` 一样不可满足**（`inv_le` 要 `|G^{(S)}_{aa}| ≥ 1/2`，取 `X = c·I`、`c` 大即破），
所以 **T113 的 `η⁻¹` 包络版 `integral_prod_applyOps_minorDiff_le` 也站在假假设上**——
这不只是 T142 锐版本的问题，**是整个 `MinorDiffGain` 分支的问题**。

论文的对应做法是 **(4.2)(4.3) 都带 `1_Ω` 且是 `≺`**，从不声称逐点形式。

### 论文里根本没有 `|S| ≥ 2` 的小行估计
全文 grep：`G^{(i)}` 的每一处都是**单行**，且每一处都立刻用 **(4.9)** 把上标消掉。
论文只提供①层级 0 的界 (4.2)(4.3)，②层级抬升**一步**的恒等式 (4.9)。
迭代到 `|S| = m` 是**我们的构造**（论文允许，但没写，常数与条件得自己定，应记 paper-delta）。

### 正面发现：层级 0 已经完全就位，抬升是纯确定性的
* **`det` 是白送的定理**（探针编译过）：`isUnit_det_sub_smul_one` + `(Hflow …).submatrix` 的 Hermitian 性，
  **不需要任何好事件、任何层级限制**。今天它却是 `MinorGood` 的一个 `hdet` 参数往上传，四处签名可以直接删掉。
* **层级 0 恰好就是 `GoodEvent`**：`norm_offdiag_le`/`norm_diag_sub_le` 逐字就是 `off_le`/`diag_sub_le` 在 `S = ∅` 的实例，
  而 `HighProb (P d) (goodSetFlow …)` 是**已证定理** `highProb_goodSetFlow_of_localLaw`——**正是论文 (4.1) 的 `Ω(t,c)`**。
* **抬升的归纳纯代数、不需要新概率**：`gEnt_insert`（`MinorDiffGain.lean:537`）已经是 (4.9) 在一般层级 `S` 上的恒等式；
  递推 `Ψ_{j+1} ≤ Ψ_j + 2Ψ_j²`，在 `Ψ ≤ 1/4`、`8MΨ ≤ 1` 下给 `Ψ_j ≤ 2Ψ`（`j ≤ M`），`inv_le` 随归纳一起走。
* `|S| > M` 不可能（`Ψ_j ≲ 2^jΨ`）**也不需要**：实际到达的层级 `card ≤ 字长 ≤ M = 2p`。
  障碍纯粹是 `DiffBd`（`MinorDiffGain.lean:243`）**对 `S` 无界量化**。
* **穿过 `E_k` 的工具仓库已经有了**：`Gauss.norm_condRow_le_split`（`CondDom.lean:164`）与
  `meas_measure_rowSlice_ge`（`:147`，Fubini + Markov，把无条件的 `P(Bad)` 换成**行条件概率**的小性），
  `CondStableFlow.lean:285–320` 已是现成用例。**这比无条件高概率严格强，而这一步仓库做过。**

### 循环性：绿灯
`eq45Flow_of_localLaw_gain'` **本来就同时带着** `hll` 与 `hΩ`，生产者消费同一个假设是**删假设、不是加假设**。
但为对齐论文的逻辑顺序，生产者应消费 `goodSetFlow`（= `Ω(t,c)`，阈值粗）而不是 (2.75) 本身。
**尺度记账**：`highProb_goodSetFlow_of_localLaw` 要 `N^τΨ ≤ δ` 的余量，所以高概率拿到的是 `GoodEvent … (N^τΨ)`；
产出的 Ψ 是 `Ψ' = N^τΨ`，下游 `hΨW`/`hΨlow`/`hΨhalf`/`hΨW'` 都是 τ-柔性的，自洽——**每次应用损一个 `N^τ`，正是 `≺` 允许的**。

### 建议的后续（三张单 + 两条顺手活）——**待 Jun / Cowork 定，本节不开单**
* **L1**（纯确定性，新文件，今天就能绿）：`MinorGoodLe`（带层级预算 `S.card ≤ M`）+
  `minorGoodLe_of_goodEvent : GoodEvent … Ψ ⟹ MinorGoodLe … (2Ψ) M`。依赖方向 `Green/EntryBound → FlucIterHigh → 新文件`，
  **`MinorDiffGain.lean` 一行不动**。
* **L2**（机械，约 500 行，需独占 `MinorDiffGain.lean`）：给 `DiffBd` 加层级预算，消费点换成 `MinorGoodLe`。
* **L3**（真正的墙）：把 `MinorDiffGain` 事件条件化——`hgood : ∀ ω ∉ Bad, …` 加 `hslice`（行条件概率）。
  ⚠ **`MinorDiffGain.lean` 文件头「`MinorDiffGain` 里已经没有条件期望，所以拆积分是合法的」这句话不对**：
  `flucDiagSet` 就是 `qRow`，`applyOps` 还会再叠 `E_κ`。正确工具是 `norm_condRow_le_split`。
* 顺手一：把 `det` 从假设变成定理，删四处签名。
* 顺手二：**(4.2)/(4.3) 在 Lean 里标反了**——`MinorDiffGain.lean:471` 把 `off_le` 标成 (4.3)、`:517` 把 `diag_sub_le` 标成 (4.2)，
  论文里 (4.2) 是一般 entry、(4.3) 是对角 centered，正好相反；`paper-deltas.md` #103 与 `content.tex:1935` 一路沿用了反标。
  纯文档层面，不影响证明。另：`diag_ne`/`inv_le` 被标成 (4.1)，但论文的 (4.1) 是**事件 `Ω(t,c)` 的定义**，
  `|G_ii| = O(1)` 是它的推论、论文没编号。

## ⭐ T163：(5.35) 的 fiat 洞堵上了——`E^{(G̃)}` 是定义，`F` 由恒等式钉死（`Hierarchy/EGDef.lean`，734 行，2026-09-21）

`lake build RBM1D` exit=0，公理审计 **8846** 条。

**1. 定义**：`EGDef.eGpm` 逐字抄 p.59 (5.51)，写成 `Gsig`/`Eblk`/`SB`/`gloop` 的显式表达式，**是 `def`、不是结构字段**；
`eGpm_eq_eGterm` 证明它逐字等于 (2.47) 的 `Gauss.eGterm`——也就是 `generator_add_zMotion_gauss` 放进漂移里的那个 `Ẽ`。

**2. 恒等式，逐项对账，没有第三项**（`F_eq_eGpm_add_quadGlue`）：
```
H.F N u M ![true,false] ![a₁,a₂] = eGpm … + primBil … (gloop − Kval) …
```
即 **(5.51) 的 `E^{(G̃)}` + (5.49) 的 `E^{((L−K)×(L−K))}`**，`H.F` 由 `Hyp.drift` 钉死（`Hyp.F_unique`）。
「有没有别的项」是**证出来的否**：`couplingLen_two_of_len_two` 表明长度 2 时唯一的切割是 `(k,l) = (1,2)`、
两个子 loop 长度都是 2，故整个耦合就等于它的 `l_K = 2` 分量，**`∑_{l_K>2}` 是空和**；再由 (5.19) 该分量 `= Θ_{u,σ}∘(L−K)`，
而那正是 `Hyp.drift` 左端已有的 `SumZeroDyn.genS`（桥 `genS_eq_thetaGenLoop`）。

途中补上两块**原本缺失的胶水**（T132b 会直接用上）：
* `genLK_eq_split`：`MomentDuhamel.genLK`（对**裸** `gloop` 求矩阵二阶导）`= eGterm 0 + primRhs(gloop)`。
  此前仓库只有 `loopIto_second_frozen`，它是对 `loopObs`（预合成 Hermitian 投影 `hermCLM`）说的，**两者不是同一个函数**。
  桥是新证的通用引理 `fderiv2_comp_clm`（CLM `T` 固定基点与方向时 `∂²(Ψ∘T) = ∂²Ψ`）+ `contDiffAt_gloop_matrix` + `coordD2_sub_const`。
* `hasDerivAt_Kval_two`：`B.Kval` 在 2-loop 上满足 (2.48)。

**3. (5.52) 过了**：`norm_eGpm_le`（`S^{(B)}` 列和为 1）+ `eGpm_le_reduced`——**(5.35) 形状 2 直接作用在 `‖eGpm …‖` 上**。

**4. fiat 审计**：(5.35) 左端每个量要么是**定义**（`eGpm`、`primBil`、`mSigma`），要么是**被恒等式钉死**（`H.F`），
**没有一个可自由赋值的结构字段**，**全程没有 `SumZeroDyn.Hierarchy` 的实例**（T118 遵守）。
值得记一笔的非洞项：`Gm` 是继承自 `eG_le_reduced` 的辅助控制函数，只出现在假设里、**不出现在结论**，是调用者必须提供的见证。

**两条 paper-delta**：#116（原编 #114，与 Cowork 的 [51] β = 2 条撞号，09:58 改号；(5.51) 的两个下标次序印反了，实际是 `(a₂,b₂,a₁)`；同一条共轭关系正是「`+ c.c.`」的严格含义）、
#117（原编 #115；`+ c.c.` 的那个 2 在锐不等式里要显式安置为 `hκ : 2κ ≤ ℓ_u/ℓ_s`）。

## T153 第 0 步：固定 `E` 的假设**在 `Thm221` 以上完全是参数化的**（只读调查 + 编译探针，2026-09-21）

**结论**：`Flow/` 层把 `E : ℝ` 换成 `E : ℕ → ℝ`，**证明脚本一个字都不用改**——探针把
`BoundsCore`/`Bounds`/`Cond272`/`Thm221`/`Bounds_zero`/`Bounds.congr`/`eventually_flow_grid`/`Bounds_of_Thm221`
全部按 `E N` 重述，逐字照抄原证明，`lake env lean` exit=0、0 sorry。
一致性的来源在读码里也看得见：`Flow/Scales.lean:326` `flow_grid_2_72` 是 `∃ W₀, ∀ W … ∀ E, |E| ≤ 2−κ → …`，
**`W₀` 在 `E` 之前选定、常数只含 `κ`**；`Flow/Iteration.lean:234` 同样把 `τ'`、`n₀` 选在 `E` 前，
其 `filter_upwards` 用的四个 `∀ᶠ N` 事实**一个都不含 `E`**。

**⭐ 副作用：`SpecSeq` 的能量切片条件可以直接删掉。** `lemE_eq : ∀ N, lemE (z N) = E`（`Flow/Consequences.lean:162`）
是唯一的切片约束，它的五个消费者全是**逐 `N`** 用的；换成 `E : ℕ → ℝ` 后取 `E N := lemE (z N)`，
**`lemE_eq` 变成 `rfl`、条件消失**。探针把 `SpecSeqN` + `localLaw_of_boundsN` + `localLaw_prob_of_Thm221N`
（(2.3) 对**任意**谱参数列）整条编出来了。**这直接销掉 paper-deltas #38 与 #5 的一半。**

**而且只有 `Bounds`/`Thm221` 一家卡着**：`Transfer`/`TransferLoop1` 的字段写的本来就是 `X.G (lemE (z N)) N …`，
能量已随 `N` 走；`Flow/Universality.lean` 的 `Band.queZ (τ) (E : ℕ → ℝ)` 也早就是 `N` 依赖的。
`Thm221` 今天**没有生产者**（全树只作假设出现），且 `Thm221.step` 已经是 `∀ E : ℝ, |E| ≤ 2−κ → …`，
换成 `∀ E : ℕ → ℝ` 是**严格加强**，代价全部落在将来的六步生产者身上，今天不破坏任何东西。

### 一处真实的非一致（负面发现）
`∀ E → ∃ C`（`C` 可依赖 `E`）全树 35 处；与能量有关的一支同根同源，链条
`Flow/Iteration.norm_Kval_le ← KBound.norm_Kgen_le ← norm_Kpi_le ← sum_norm_innerId_le ← norm_Kpi_empty_*_le
← SumZero.sum_zero ← **SumZero.norm_Alayer_le**`，根在 `Loop/SumZero.lean:842` 的 `ι = (mE E).im`。
**但不是障碍**：`|E| ≤ 2−k ⟹ (mE E).im ≥ √(2k)/2`（`Flow/Scales.lean:315`），
且 `Loop/SumZero.lean` 经 `Loop/WardKgen.lean:9` **已经传递 import 了 `Propagator/Edges`**，把 `∃ C` 提到 `∀ E` 之前即可，
**不需要搬文件**。这一支的消费者是 (2.61) 与 Steps 内部，**不在 `Bounds_of_Thm221` 的路径上**。
⚠ 余下 34 处 `∀E ∃C` **未逐条核**，是本报告的已知盲区。

### 路线判定：**(ii) 单独走不通，必须接在 (i) 后面**
要「以 ≥ 1−N^{−D} 的概率对网上所有能量同时成立」，必须把能量塞进 `StochDom` 的指标集
（现在只有 `(x,y)`，能量在概率**外面**）——按 STATUS 的老结论这是 **T116 情形：生产必须用网**。
而网点 `E_j(N)` **本来就是 `N` 依赖的能量**，所以 **(ii) 的输入恰好是 (i) 的输出**。

**引擎现成且可一字不改复用**：`Gauss.stochDom_reindex_of_forall_seq`（`Gauss/Step1Hyp.lean:269`，
docstring 明说 generic、非高斯特有）+ `StochDom.of_forall_le`；而 **`RBM.TimeIcc s t N` 就是 `↥(Set.Icc (s N) (t N))`**，
取 `s ≡ −2+κ`、`t ≡ 2−κ` 它**就是能量区间**。探针已编出 `localLaw_energy_seq` 与 `localLaw_net_of_Thm221N`
（网上一致、并集在 `P` 里面），exit=0、0 sorry。
从网点到随机点 `λ_k(ω)` 的最后一跳也编过：`‖G(z)_{ij} − G(w)_{ij}‖ ≤ ‖z−w‖η⁻²`
（`green_sub_green` + `norm_green_le` + `norm_apply_le_l2_opNorm`）。
**不需要任何概率型连续性模（T101/T106 都用不上）**——随机点的 `ω` 依赖在好事件上逐点处理即可。

### 改动量
**(i) 建议走新文件**（探针已是骨架，约 170 行全绿）：`BoundsCoreN`/`BoundsN`/`Cond272N`/`Thm221N` 及其五条引理
+ `SpecSeqN` + `localLaw_of_boundsN`/`localLaw_prob_of_Thm221N`，再加 `Thm221N → Thm221`（常数列特化，一行）保证向后兼容，
**0 个现有签名改动**。就地泛化更干净但要动 `Bounds`/`BoundsCore` 9 个文件、`Cond272` 14 个文件，**与并行车道正面冲突**，
建议等六步定型后再合并。
**(ii)** 约 150–250 行、无新数学；网点构造用已有的 `Gauss/Domination.netSize/netPt/exists_netPt_close/card_net_le`。
⚠ `stochDom_reindex_of_forall_seq` 现住在 `Gauss/Step1Hyp.lean`，让 `Delocalization.lean` 依赖 `Gauss/` **方向不对**，
按 CLAUDE.md 应**下沉到 `RBM1D/Defs/`**（它本来就 generic）。

### 做完之后还剩
`Thm221N` 依然无生产者（负担转嫁给六步）；**谱边缘**——局部律只在 `|E| ≤ 2−κ` 上有，(2.10) 对边缘的 `λ_k` 要么排除、
要么另记一条 paper-delta，**论文 Theorem 2.2 的措辞待确认**；特征值编号沿用 #5；
`norm_apply_le_l2_opNorm` 要 `[Nonempty n]`，`Band.Idx N` 的实例待确认。

## ⚠ T152：Step 6 的四个洞里**两个是空洞**；另发现高斯漂移恒等式在 `v = 0` 处不可满足（`Gauss/Step6HierarchyGauss.lean`，557 行，2026-09-21）

> **⚠ 后续更正（T182，2026-09-21）**：本节「`DLK`/`DG` 的拆分在 Lean 里毫无代价可省」**只对恒等式成立，对 size estimate 不成立**——单张量下 `eG` 那半比 (5.133) 恰好弱一个 `A`，该因子只能从期望的抵消 (5.134) 拿回。(5.133) 请用 `Gauss/Step6DriftSplit.lean` 的双张量版。

`lake build RBM1D` exit=0，审计 **8864** 条。

### 产出
**1. `Uker` 的常数变易演算（树里原先完全没有这块）**：
`edgeKer_mul_Theta_mul_SB`（全部内容就是 `(1−vξS)Θ_{vξ} = 1` + 交换性）、`Uker_ThetaOp_eq`（配对合重标 `sum_update_reindex`）、
**`hasDerivAt_Uker_thetaOp`：`∂_v U_{v,t} = −U_{v,t}∘Θ_v`**（符号有独立交叉验证：`n = 1` 退化成 T132a 已证的 `hasDerivAt_edgeKer`）、
`hasDerivAt_Uker_path`、**`Uker_duhamel`** 与 **`Uker_duhamel_Ioo`**、`integral_ThetaOp`。
T132a 的 `hasDerivAt_Uker_apply` 是**把张量冻住**求导、积不出层级；这一节补的正是这个缺口。
**2. `hH` 的生产者**（全树第一个）：`Step6.hierarchy_of_hasDerivAt` / `..._Ioo`。

### ⚠ fiat 审计：四个洞里两个是空洞，且**做成了定理**
| 字段 | 结论 |
|---|---|
| `DLK`/`DG` | **自由数据**（`DriftTensor` 是纯数据，`sharpExpect_step6` 对它们全称量化） |
| `hH` | **可 fiat**：取 `DG = 0`、`DLK_v := (∂_v − Θ_v)E(L−K)_v`，只要路径 `C¹`，用本文件的 `Uker_duhamel` 就按定义成立。**所以单独交付 `hH` 一文不值。** |
| `hG` | **完全空洞**，已编译证明 `hG_zero_right`：`DG = 0`、`Cg = 0` 即满足。`hG` 只有在 `DG` 被先钉死成论文的 `E E^{(G)}` 之后才有约束力 |
| `hFD` 的 `DG` 半边 | **空洞**（`fastDecay_zero`） |
| `hFD` 的 `DLK` 半边、`h5133` | **唯一有内容的两条**，未做 |

**最实用的一条结论，已编译成 `sharpExpect_step6_single`**：
**论文把漂移拆成 `DLK`/`DG` 在 Lean 里毫无代价可省**——`driftBound_of_5133` 与 `driftBound_of_5134` 给出的是**同一个**界
`η_v⁻¹(Wℓ_vη_v)⁻³`。于是 Step 6 的四个洞塌缩成**单张量 `D` 上的三条义务**：层级恒等式 + `D` 的快衰减 + (5.133)。
**后续接手的人不必再构造两个张量。**

### ⚠ 新发现的硬障碍：高斯漂移恒等式在 `v = 0` 处**不可满足**
所有路线都要经过沿 `H_v = √v·X` 的链式法则，而 `hasDerivAt_Psi_Hflow` / `hasDerivAt_integral_Psi` /
`hasDerivAt_sample_ELval_hierarchy_gauss` **全部**带 `0 < u`；偏偏 **Step 6 是 Theorem 2.21 里唯一接受 `0 ≤ s` 的一步**。
所以闭区间版的 `hderiv` 在 `s N = 0` 时不可满足——**这就是为什么本单额外做了 `_Ioo` 版本**（开区间要导数、闭区间只要连续），
**接手的人应当用 `_Ioo` 版本**。这是 T149/T161 那条 `0 ≤ s` vs `0 < s` 的缝从**解析侧**的又一次撞击。

### 未做
* **高斯侧的期望漂移恒等式（`hderiv` 的输入）不是拼装活**：逐路径的 (5.15) 是 T140 的 `hasDerivAt_sub_prim_thetaGen`，
  微分号下求导是 `hasDerivAt_sample_ELval_hierarchy_gauss`（仍挂 `MatrixStein`(T70) 与 T141 的 `hjoint`）。
  但 **`primRhs` 对回路值是二次的，`E[primRhs(L_v)] ≠ primRhs(E L_v)`**，取期望这一步真的会生出 `E[primBil(L−K,L−K)]`
  ——正是论文的 `E E^{((L−K)×(L−K))}`。**纯线性的那一半已做掉**（`integral_ThetaOp`），二次的那一半是剩余工作。
* `h5133` 与 `hFD` 是 size estimate，依赖上一条把 `D` 定成论文的对象之后才谈得上。
* **没有捏造 `DLK`/`DG` 的具体定义**——在上一条没有之前定义它们只是摆样子，反而会掩盖 `hH` 可 fiat 这件事。

## ⭐ T58/T118(iii)：`F` 在**一般回路长度**上被具体钉死（`Hierarchy/DriftDef.lean`，473 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **8899** 条。

### 第 0 步：`Lemma510` 四个字段的归属
结构性前提要先说清楚：`SumZeroDyn.Lemma510` 的参数是 `SumZeroDyn.Hierarchy`，而 **T118 禁止实例化它**。
所以**「`Lemma510` 作为结构被生产出来」在矩路线下永远不会发生——这不是缺口，是设计**
（`Hierarchy` 的 `mart`/`martQ`/`duhamel`/`bdg` 就是 fiat 的那一半）。
有意义的读法是把四个字段的**陈述**用 `MomentDuhamel.Hyp.Fpath` 与 `EEpath` 代入（类型逐字相同）：

| 字段 | `F` 具体化之后 |
|---|---|
| `F_decay` | **解锁，本单已给出确定性内核** `fastDecay_driftF`（Definition 5.8 的衰减逐项证出，半径统一到 `2ℓ+1`）。剩下只是把 `FastDecay → StochDom` 接上已有的高概率输入，**没有新数学** |
| `F_le` | **解锁但不免费**：三项各自对上 `Decay` 的一条界，但 `xiRhs` 右端与 `Decay` 的形状之间还有一整段 Ξ-记账（T165 第 (2) 项），本单未做 |
| `EE_le` / `EE_decay` | **与 `F` 无关**（T127/T135/T144）；`≺` 版仍缺一条控制的多项式下界 |

### 主结论：长度 2 的恒等式**确实推广，且只多一项**
```
F_{u,σ,a} = Ẽ_{u,σ,a} + ∑_{l_K ≥ 3} [K ∼ (L−K)]^{l_K}_{u,σ,a} + E^{((L−K)×(L−K))}_{u,σ,a}
```
`DriftDef.driftF` 是 `def`（不是结构字段），由 `drift_split_gen`/`F_eq_driftF` **证出**（走 `Hyp.F_unique`），不是按定义造的。
逐项对账：`∂_u gloop(z_u) = eGterm(mSigma E) − eGterm 0`；`genLK = eGterm 0 + primRhs(gloop)`（T163 的 `genLK_eq_split` 本来就是一般长度的）；
`∂_u Kval = primRhs(Kval)`（`hasDerivAt_Kgen_all`——**这是 T163 当时卡在长度 2 的唯一原因**，它只有 `hasDerivAt_Kval_two`）；
`primRhs_sub` 分成三项；`Decay.sum_couplingLen` 分级，`l_K = 2` 那支由 (5.19) 等于 `genS`。
**`eGterm 0` 精确抵消，没有第三项、没有余项。** `n = 0` 时求和为空，与 T163 的结论逐字一致——`E^{(G)}` 全仓库仍只有一套。

### 两条**本来缺失**的桥（这才是让 `Decay` 的界能用上的东西）
* **`eGterm_eq_eG`**：`Gauss.eGterm … = Decay.eG …`。此前 (5.77) 第 3 行（`Decay.norm_eG_le`、`fastDecay_eG`）说的是 `Decay.eG`，
  而漂移里的是 `Gauss.eGterm`，**两者之前没有桥，一直在说不同的函数**。桥的内容是 `Kgen_one`（`K` 在 1-loop 上等于 `m(σ)`）+ `trace_Eblk`。
* **`sum_couplingLen_erase_two`**：(5.15) 留下的 `∑_{l_K ≠ 2}` **等于**论文的 `∑_{l_K > 2}`，且上界截到 `l_K ≤ n`。
  上下两侧都是定理（`two_le_length_cutGlueL/R`、`length_cutGlueL/R_le`），**不是约定**。
  这正是 `Decay.norm_couplingLen_le`（前提 `3 ≤ l_K`）能逐项套用的前提。

### fiat 审计
`driftF` 是 `def`，三个加项全部 unfold 到 `M` 在 `z_u` 处的 Green 函数与 `Kgen`，**无任何可自由赋值的结构字段**；
`F_eq_driftF` 的左端由 `Hyp.drift` 钉死，证明走 `HasDerivAt.unique` + `add_left_cancel`；
**全程无 `SumZeroDyn.Hierarchy` 实例**。**可满足性已验**：`Fpath_eq_driftF_of_lt_one` 在 `|E| < 2`、`0 ≤ u < 1` 下卸掉两个副条件，
**恒等式在流真正活动的区制里非空**。`fastDecay_driftF` 的假设就是 Lemma 5.9 的输出，不是凭空谓词。

**无新 paper-delta**：`∑_{l_K>2}` 的范围是证出来的而非假设的；`Gauss.eGterm` 与 `Decay.eG` 是同一对象。
`F_le` 的 Ξ-记账留给 T165，本单已把它需要的三座桥全部铺好。

## T158：截断方案的定量导数界（`Gauss/CutoffBounds.lean`，734 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **8965** 条。namespace `RBM.Cutoff`。

**1. 光滑 max 与权重和界（工单的「初等一半」，全部证完）**：`smoothMax`/`cutWeight`、`le_smoothMax`/`smoothMax_le`、
**`rpow_card_le_exp_one`（`r ≥ log(card ι) ⟹ (card ι)^{1/r} ≤ e`——这就是 `r ≍ log N` 给出 `O(1)` 的那一步）**、
`sum_cutWeight_le`（走 Hölder，仓库里没有现成的，用 Mathlib 的 `Real.inner_le_weight_mul_Lp_of_nonneg`）、
`hasDerivAt_smoothMax`（链式法则是**定理**，不是假设）。
**自带锐性自检**：一条 `example` 证明 `a ≡ 1`、`ι = Fin 2` 时 `∑ cutWeight = 2^{1/r}` **取等**——`cutWeight` 的指数抄错会当场编译失败。

**2. `∑S|∂J|²` 以 `T_{u,D}` 归一化**：加权 Cauchy–Schwarz → `sum_cutWeight_quadForm_le`；
`W^{−D}` 地板把**不正比于 `T²` 的加性余项**吸收进 `T²` 归一化（代价 `W^{2D}`）；
`ee_shape` 把 T156 的 `ee_le`/`ee_le_paper` 的结论形状重排成 `B·T² + R`；
合起来 `∑ₓ Sₓ(∂ₓJ)² ≤ (card ι)^{2/r}(B + R·W^{2D})`。

**3. `∂_u T_{u,D}`**：第二项对 `ℓ` **确实不一致有界**，但 `ℓ'_u ≥ 0` 时符号有利可丢，得到**对 `ℓ` 一致**的
`−∂_u log T ≤ 2(∂_u log A_u)₊`。**`W^{−D}` 地板区的「单独处理」结论是：它不需要单独处理**——
地板与 `u` 无关故对 `T'` 贡献 0，只通过 `0 ≤ W^{−D} ⟹ (T−W^{−D})/T ≤ 1` 进入，同一条界就覆盖。

**4. 门槛的时间依赖（工单原先漏的那一项）**：`Θ̇_u/Θ_u = 4m/η_u`（`hasDerivAt_threshold`），
缺口上 `J/Θ ∈ [1,2]` ⟹ 该项 `≤ 8C_χ m/η_u`，**与其它漂移项同为 `η_u^{−1}` 阶**。

**5. 额外做掉的二阶导**：`hasDerivAt_deriv_smoothMax` 给出**恒等式**，第三项符号非正可丢，`aᵢ ≥ 1`（(5.28) 的 `J ≥ 1`）
⟹ `≤ (r−1)κb² + κc`。**光滑化的二阶代价恰好是一个 `r − 1 ≍ log N`，即 `N^{o(1)}`。**

### 边界（如实）
* **(5.36) 是按「形状」接的，不是直接 `apply Lemma57.ee_le`**——后者自带 `h273/h564/h566/h572/hsym` 一串假设，
  属调用方（T167 钉死 `eeFun` 之后）。提供的是 `ee_shape` + `sum_cutWeight_quadForm_tailT_le`，**接线是平凡的 `linarith`，但尚未接上**。
* **二阶是一维方向导数**，不是 Fréchet Hessian。对 `𝓛 = ½∑S_{ij}∂_{ij}∂_{ji}` 够用（它是方向二阶导之和），
  若下游要 Fréchet 形式还需一层包装。
* **没有构造具体的 `C²` 截断 `χ`**：所有关于 `χ` 的陈述都以 `HasDerivAt χ dχ ·` + `|dχ| ≤ C_χ` 为假设，
  **文件里没有一条 `∀ ω` 的逐点量化**（刻意按 T164 的教训避开）。~~`ContDiffBump` 可作见证，未落 Lean~~ **→ 更正（T175）：Mathlib 的 `ContDiffBump`/`smoothTransition` 不能作为**定量**见证（两者都只有 `nonneg`/`le_one`/`ContDiff`，**没有导数公式、没有导数界**），已改用五次 Hermite 截断。**
* 去截断（概率层面的穿越论证 + 时间网）不在本文件，按设计属 `MomentHyp.holder` + `stochDom_timeIcc_of_holder`。
* 已按提醒**避开** T133 的 `BddC2C` 常数（无 `T_{u,D}` 归一化、差 `A^{O(1)}`），文件头写明它不能当缺口界用。
* **指数预算未重算**：本文件只给「每一步的损失是什么」（`e`、`e²`、`r−1`、`W^{2D}`、`8C_χm/η`）。
  T156 的更正（Case 2(1a) 是 `A^{−1/2}`）与 T155 的近场 `r³` **仍需在 T132c 实现前合并重算 `β*` 表**。

## T169：`MinorGoodLe` 落地——层级 0 的好事件迭代到 `|S| ≤ M`（`Gauss/MinorGoodLe.lean`，335 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **8986** 条。

**可满足性先行检查（按 T164 的教训，工单要求的第一件事）**：语句形状合法且非空洞。
`ω` 只作为「假设与结论共同读取的那一个点」出现（`GoodEvent … ω ⟹ MinorGoodLe … ω`），**没有任何 `∀ ω` 量化**；
T164 的反例在这里表现为**前提不成立**，不构成矛盾。
**并且把「非空洞」变成了定理**：逆向的 `MinorGoodLe.goodEvent` 证明它在层级 0 逐字蕴含 `GoodEvent`（对任意预算，含 `M = 0`）。
所以结论既不弱到平凡、也不强到不可满足——它恰好是把 (4.1) 从 1 层推到 `M+1` 层，代价是常数 2。

**归纳真正需要的常数**：不变量是「对 `S.card ≤ M`，`‖G^{(S)}_{ab}‖ ≤ Ψ + 8|S|Ψ²`（`a ≠ b`）且对角 centered 同」。
一步 (4.9) 的代价 `2Ψ_j² ≤ 8Ψ²` **正好等于不变量每步的增量，递推自封闭、不需要任何余量**。
`8MΨ ≤ 1` **是紧的**，只用于这一条；`Ψ ≤ 1/4` 只用于 `inv_le`/`diag_ne`。**工单给的三条常数原样够用，没加码也没放宽。**

**两处必要的新增**：`gEnt_insert_of_ne`——现有的 `gEnt_insert` 吃**整个** `MinorGood`（所有层级），
而归纳步只在层级 `S` 上有信息，**用不了**，所以重证了只吃 `hdet` 与 `gEnt κ κ S ≠ 0` 的版本；
以及第五个字段 `diag_ne`（对齐 `MinorGood` 的字段表，T170 用 `gEnt_insert` 时直接需要，白送）。
`det` 确如 T164 所说是白送的定理（`isUnit_det_Hflow_submatrix_sub`），**无好事件、无层级限制**。

### ⚠ 留给 T170 的两件事
* **依赖会成环**：本文件 `import Gauss.MinorDiffGain`（为复用 `gEnt`），而 T170 要让 `MinorDiffGain` 的消费点改吃 `MinorGoodLe`。
  届时要么把 `gEnt` 及其基本引理**下沉**到 `FlucIterHigh.lean` 或 `Defs/`，要么 T170 走 `MinorDiffGain` 之后的新文件。**待定。**
* T169 的第 (2)(3) 项（删 `MinorDiffGain.lean` 四处签名的 `hdet` 参数、(4.2)/(4.3) 标签更正及 `paper-deltas` #103 / `content.tex:1935` 同步）
  **都要改本文件之外的文件，未做**。
* 给 T171 的线索：`goodSetFlow`（`Eq45FlowInputs.lean:278`）**逐字就是** `∀ u ∈ Icc, GoodEvent …`，
  所以桥是一行 `fun hω => minorGoodLe_of_goodEvent_flow … (hω u hu)`；只是要多引一个 import，依赖方向待定。

## ⭐⭐ T172：全仓库「逐点 ∀ω 假设」可满足性扫描（只读审计 + 两条新编译反例，2026-09-21）

**覆盖**：`RBM1D/**/*.lean` 共 145 个文件，六条检索（`∀…ω` 含不等号的 64 行逐行分类；43 个结构逐条读；
`(ω : Ω` 限定到结构/`Prop`；`∀ᵐ`；端点型 `HasDerivAt`；多行 binder 与别名绑定）。
**声明的盲区**：`Hierarchy/GUEPhase.lean` 只看签名未查实例化路径；`MomentHyp.holder`/`env_le` 给的是数学论证非编译证明。

### 一句话结论
**逐点 `∀ω` 这个坑，全仓库只塌了 `MinorGood`/`MinorGood'` 一处，而且是死胡同（无下游消费者）。**
第二处 `FlucBound` **不是塌方而是天花板**：可满足，但 `B` 有绝对下界，所以 (4.12) 走不通那条接口。
其余 40 余处要么是非负性/可测性，要么界是自由参数并配了已证的包络实例，要么本来就是正确写法。
**`∀ᵐ ω` 形状在仓库里根本不存在**（9 处 `∀ᵐ` 全是证明内部的 `have`）。

### 反例 1：`MinorGood`（不带撇）为假，**与 `Ψ` 无关**——比 T164 的结论强
`not_minorGood_forall`（已编译）：取 `ω = Function.update 0 ⟨N,k,k,true⟩ 40`，则
`Hflow = diagonal(20·1_{i=k})`、`G^{(∅)}_{kk} = (20 − i/2)⁻¹`，故 `‖(G^{(∅)}_{kk})⁻¹‖ ≥ 20 > 2`，**字段 `inv_le` 直接垮**。
**`inv_le` 根本不提 `Ψ`，所以没有任何 `Ψ` 能救**，也不需要链条自带的 `2Ψ ≤ 1`；对每个 `u > 0` 取 `R` 够大即可
（`u = 0` 是唯一例外）。又因 `MinorGood'` 是 `extends MinorGood`，**带撇的一支被它蕴含**。

**爆炸半径 = 0（好消息）**：`∀ω, MinorGood(')` 出现在 `MinorDiffGain.lean` 的 8 条定理假设里，
而查全树**这 8 条在该文件之外只被 docstring 提到，没有一处实际 `apply`**——下游实际跑的是包络版
`norm_flucDiagSet_le_env`。所以这是**死胡同，不是污染链**。

### ⚠ 反例 2（新发现）：`FlucBound` 的 `B ≥ 64/65`，**(4.12) 的 `B ≍ Ψ` 不是「还没证」而是不可能**
`le_B_of_flucBound`（已编译）：**两点法**。取 `ω₀ = 0` 与 `ω₈ = Function.update 0 ⟨N,k,k,true⟩ 8`，
两者**只在行 `k` 的坐标上不同**，故 `rowSplit d N k ω₈ ω' = rowSplit d N k ω₀ ω'`，
**条件期望 `E_k` 在两点取同一个值**（编译引理 `rowSplit_omR`、`condRow_greenDiagCentered_omR`）。
于是 `Z_k(ω₈) − Z_k(ω₀) = G_kk(ω₈) − G_kk(ω₀)`，虚部 `−128/65`，而 `flucDiag_le` 要求 `≤ 2B`。
**结论 `B ≥ 64/65`，对一切 `d`、`N`、`k` 成立。**

`FlucAvg.lean:427–434` 的 docstring 只说「确定性包络给不出 `Ψ` 大小的 `B`」；
现在知道的是**没有任何东西能给出**——`hsmall` 在 `Φ = Ψ²`、`Wℓη ≥ N^c` 的区制下代入 `B ≥ 64/65` 即不成立。
所以 `stochDom_flucAvg` 系列**本身不是空真**（`Φ` 自由且有真实例），但**它们在 `Φ = Ψ²` 处的实例化不可满足**。
**正确形状**：`B`、`ε` 必须挂在事件上（`1_Ω` 进 `E_k`，用 `Gauss.norm_condRow_le_split` / `meas_measure_rowSlice_ge`），
或整条改成 `≺`。这与 T164 给 `MinorDiffGain` 的 L3 是同一处方。

### 两个正面样板（值得当模板抄）
* `Loop/ContinuityAssembly.lean:1117`：消费者把 `Y` 取成 **`1_Ω · loopMax`**，(5.6) 的门槛在指示函数里，于是 `hY1 : ∀N u ω, Y 1 ≤ 2` 是**证出来的**。
* `Green/EntryBound.of_det`：`(∀v, A ≤ ΦB) → …`，**事件当假设而不是当结论**。

### 其余判定
六步主链（`Thm221`/`Bounds`/`Steps`/`Transfer`/`BootPP`/`Lemma510`/`Step1.Hyp`/`Step2.Hyp`）**全是 `StochDom`/`HighProb`/`UnifDetDom`，没有逐点假设**。
`TestFun`/`TestFunT`/`MatrixStein` 等量化的是**矩阵/函数**不是样本点。
`SumZeroDyn.Hierarchy.duhamel/duhamelQ` **不是空真而是 fiat**（`mart` 自由字段取残差即满足）——T118 的禁令是对的。
端点型只有 `Step6.hierarchy_of_hasDerivAt` / `Uker_duhamel` 在 `s N = 0` 不可满足，**但爆炸半径为 0**（T152 已给 `_Ioo` 版，且无外部消费者）。

## T173：Step 6 的单张量漂移钉死（`Gauss/Step6HierarchyGauss.lean` 557 → 905 行，2026-09-21）

> **⚠ 后续更正（T182，2026-09-21）**：本节「`DLK`/`DG` 的拆分在 Lean 里毫无代价可省」**只对恒等式成立，对 size estimate 不成立**——单张量下 `eG` 那半比 (5.133) 恰好弱一个 `A`，该因子只能从期望的抵消 (5.134) 拿回。(5.133) 请用 `Gauss/Step6DriftSplit.lean` 的双张量版。

单文件 `lake env lean` exit=0（全量构建此刻红在 `MinorDiffGain.lean`——T170 的 agent 正在改那个文件，与本单无关）。

**(1) 钉死单张量：落地。**
```lean
noncomputable def driftE (X : Sample B) (E : ℝ) : Step6.DriftTensor B :=
  fun N v σ a => ∫ ω, DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a ∂B.P
```
**是 `def`，不是字段**；被积函数是 T58 的 `driftF`（本身已 unfold 到 Green 函数与 `Kgen`）。
**与 `E[Fpath]` 的等价是定理而非定义**（`driftE_eq_integral_Fpath`，走 `Fpath_eq_driftF_of_lt_one` → `Hyp.F_unique`）。
`sharpExpect_step6_driftE` 把 `Step6.sharpExpect_step6_single` 的 `D` 槽填满，
**陈述里没有任何自由张量变量**——T152 警告的那条 fiat 路径被堵死。

**(2) 期望形漂移恒等式（开区间）：落地。**
`eGterm_add_primRhs_sub_eq` 把 `drift_split_gen` 里**纯代数的一半**剥出来（去掉时间导数后不再需要 `M` Hermitian、
不再需要 `Im z_u ≠ 0`）；`hasDerivAt_lkT_thetaOp_driftE` 给出 `∂_v E(L−K)_v = Θ_v∘E(L−K)_v + driftE`。
**T152 指出的二次半边确实出现并被正确安置**：线性半边走 `integral_ThetaOp`，
二次半边 `E[primBil(L−K,L−K)]` **不能与期望交换，原样留在 `driftF` 的第三个加项里**——即论文的 `E E^{((L−K)×(L−K))}`，
**所以 `D` 里装的就是论文装的东西**。
`hierarchy_driftE` 经 T152 的 **`_Ioo` 版**交出 `Step6.Hierarchy … (driftE X E) 0`（`0 < v` 由 `hs0` + `Ioo` 左端自动得到）；
第二张量取 `0`，其 `Uker` 积分项由新证的 `Uker_zero` 化为常值 0（合法性来自 T152 的 `hG_zero_right`/`fastDecay_zero`）。

**(3) `hFD` 的 `DLK` 半边与 `h5133`：未落地，只落地了「取期望不是障碍」。**
`fastDecay_integral`/`fastDecay_driftE`（逐路径一致快衰减 ⟹ 期望快衰减）配上 `DriftDef.fastDecay_driftF`，
把 `hFD` 的有内容半边归约为 Lemma 5.9 的确定性输入、**没有随机步**；
`norm_driftE_le_integral` 把 (5.133) 归约为 `F` 的**一阶矩**界。
**短的是**：`Decay` 给的是逐项 `≺` 形状，要变成 `UnifDetDom` 形状还差整段 Ξ-记账（**正是 T165 的第 (2) 项**）＋好集外包络的一阶矩记账。
**没有为了凑出 `h5133` 去改 `D` 的定义。**

**fiat 审计**：`driftE` 无任何可赋值结构字段；`hierarchy_driftE` 的假设全是关于**已确定对象**的命题
（`hcont`/`hintL`/`hintF`/`hEL`/`hintU`，**都没证，是调用方义务**）。
**可满足性**：`hEL` 在高斯模型上正是 T140 的结论，但那条仍挂 `MatrixStein`(T70) 与 `hjoint`(T141)，
且**自带 `0 < u`**——这就是必须走 `_Ioo` 的原因，与 T152 的发现一致。

## T170：`DiffBd` 加层级预算，消费点改吃 `MinorGoodLe`（2026-09-21）

`lake build RBM1D` exit=0，审计 8986 → **9042**。改动落在 `Gauss/FlucIterHigh.lean`（+36）、
`Gauss/MinorDiffGain.lean`（+671/−223）、`Gauss/MinorGoodLe.lean`（+7）。

**解环**：`gEnt` 及三条基本引理整块从 `MinorDiffGain.lean` **下沉到 `FlucIterHigh.lean`**，名字与签名逐字不变、同命名空间，
下游无感；import 方向随之翻转（`MinorGoodLe` 只 import `FlucIterHigh`，`MinorDiffGain` import `MinorGoodLe`）。

**预算的确切形式**：`DiffBd Ψ I M n c p Y` 的量词加 `S.card + l.length ≤ M`。闭包性质的记账是本单最实质的设计决定：
* `DiffBd.delta` / `.shift` **各花掉一格**（`M+1 → M`）。**不用 ℕ 截断减法**——`M = 0` 时那是假命题；
  `mul` 的 `κ :: l'` 分支里由 `hcard` 直接 `obtain ⟨M', rfl⟩`，因为 `M = 0` 时该分支前提本身不成立。
* `DiffBd.mul` 预算不变（Leibniz 两支各花一格，正好是乘积自己那次差分已付的），需要新的 `DiffBd.mono_M`。
* `diffBd_atom` 的不变量是 **`B + T.card ≤ M`**（`B` 是估计自身的预算，`T` 是原子的基层级）：
  一次差分花 `B` 一格，一次 shift 把一行从 `B` 挪进 `T`，**和守恒**。

**两件必需品**：`iterDeltaFam_congr`（迭代差分只读 `card ≤ S.card + l.length` 的层级）与 `DiffBd.congr`。
**这是绕不开的**——`MinorGoodLe` 只在预算内成立，`deltaFam_gFam` 那种 `funext` **全局族等式再也拿不到**，
必须降级成逐点版（`deltaFam_gFam_apply` 等，都带层级条件），于是 `rw` 路线整条作废。

**⭐ 关键核对：预算够用，没有偷偷抬高。** `norm_minorDiff_greenSetDiagCentered_le` 需要的恰好是 `(κ :: l).length ≤ M`，
而 `integral_prod_applyOps_minorDiff_le` 里 `numQ (L i) ≤ (L i).length ≤ M` 本来就有。
**所以字长预算与层级预算可以是同一个 `M`，签名里没有多出第二个预算参数**，也没有任何消费点要求预算外的层级。
13 个消费点全部改吃 `MinorGoodLe`；四个桥的名字保持不变。旧链（`MinorGood(')` 等）原样保留但已无人依赖，
新增 `MinorGood'.toMinorGoodLe` 把「这次改动只是减弱前提」写成定理。

**顺手三项**：删 `hdet`（本文件实际只有**三处**，不是工单说的四处；代价是各自多一个 `hz : z.im ≠ 0`）；
**(4.2)/(4.3) 的标签全文对调**（模块头、两个字段注释、8 处正文；`MinorGoodLe.lean` 原本就是对的）；
**删掉文件头那句假话**（「`MinorDiffGain` 里已无条件期望，所以拆积分是合法的」），
改成明写 `flucDiagSet` **就是** `qRow`、`applyOps` 还在上面叠 `E_κ`、指示函数乘进去过不了 `Q_κ`，修法归 T171。

**有点顶的地方（留给后来人）**：`shift` 也要花预算，所以 **`M` 与 `n` 不能合并成一个参数**；
`diffBd_atom` 的 gInv 分支若照搬 `hD.shift κ`，`B` 会多掉一格导致归纳不闭合，须改走 `ih` 在基层级 `insert κ T` 上的实例。

## ⭐ T165：(5.77) 第 1–3 行对**钉死的漂移**立成定理，`hFmom` 全链打通（`Hierarchy/DriftBound.lean`，881 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9074** 条。

`norm_driftF_le`（逐点 (5.77)）→ `norm_Hyp_F_le`（同式对 `MomentDuhamel.Hyp.F`，经 T58 的 `Fpath_eq_driftF_of_lt_one`，
**不是按定义造的 `F`**）→ `stochDom_norm_driftF`（`≺` 版，**控制是确定性的**）→ `stochDom_det_of_xiRhs`
（`SumZeroDyn.F_stochDom` 的带撇版，**不要 `Hierarchy`、不要 `Lemma510`**）→ **`hdom_of_driftInputs`**
（结论与 `F_stochDom` **逐字一致**）→ **`hFmom_of_driftInputs`**（由 `Gauss.hFmom_of_stochDom` 一次 bare application 合上）。

**最后这条编译通过本身就是验收探针**：调用链里**不再出现 T157 留下的 `hdom` 缺口、任何 `Lemma510` 字段、或 `SumZeroDyn.Hierarchy` 实例**。

### Ξ-记账
关键恒等式只有一条：**`W(ℓ+1)/A ≤ (Krad+2)/η_u`**（`Decay.mul_add_one_div_le`）——**(5.77) 里所有 `η_u^{−1}` 都从这里来**。
`m = n+2`：`∑_{l_K=3}^{m} couplingLen` 取 `Φ = ∑_{k∈Ico 1 m} Ξ^{(L−K)}_{u,k}`（常数 `4e m²·n·C_K`）；
`primBil(L−K)(L−K)` 取 `Φ = ∑_{k∈Icc 2 m} Ξ_kΞ_{m−k+2}A⁻¹`（常数 `2e m²`）；`eG` 取 `Ξ^{(L−K)}_{u,1}·Ξ^{(L)}_{u,m+1}`（常数 `2e m C1`）。
合并用 `m ≥ 2 ⟹ 2m ≤ 4m²`；误差侧 `xiSum` 同时支配两项。

### 两个必须记录的发现
1. **(5.77) 第 3 行短一个因子 `Ξ^{(L−K)}_{u,1}`** → paper-deltas #121（原编 #119，撞号已改）。论文默认它 `≲ 1`（(2.68) 单圈）才丢掉，
   但**它既不是常数也不在 `xiRhs` 里，无法从另外两行推出**，故 Lean 侧显式列为假设。
2. **⚠ `Decay.norm_couplingLen_le` 的 `hD` 假设过强，长度 0 处会炸**：它要求 `‖(L−K)_J‖ ≤ Φ·A^{−|J|}` 对**所有** `|J| < m`，
   含 `|J| = 0`；而 `L_∅ = ⟨1⟩ = L·W`、`K_∅ = 0`，于是逼出 `Φ ≥ LW`，**主项直接废掉**。
   耦合本身根本看不到这种圈（cut-and-glue 两边长度都 ≥ 2）。本单用 `dTrunc`（长度 < 2 处置零）+ `couplingLen_dTrunc` 绕过，
   **没有改 `Decay.lean`**；**要收紧只需把 `hD` 改成 `2 ≤ J.length → …`，`dTrunc` 那一段就能删掉。**

### 还剩什么
`DriftInputs` 仍是假设而非定理——它装的是 Lemma 5.9 的衰减与 Step 3 的计数，**都不涉及漂移**，由别处产出
（`Decay.lemma59` / Step 3）。这是下一环，不在 T165 范围内。

## T167：(5.36) 接到钉死的 `E⊗E`，(5.22) 的展开补齐（`Hierarchy/EEDef.lean`，新文件 485 行，2026-09-21）

`lake env lean RBM1D/Hierarchy/EEDef.lean` **exit=0**、0 sorry、0 axiom；
`#print axioms`（跑完已删）对 11 条声明全部只含 `propext / Classical.choice / Quot.sound`。
另改动两处纯文档：`Hierarchy/Lemma57.lean` 偏差表第 9 条（它说的「展开不在仓库里」现在过时了，已改写；
文件重编 exit=0），和 `blueprint/src/content.tex` 新增节点 `lem:5.7c`。

### 为什么开新文件
`Lemma57.lean` 只 import `Analysis/StretchedExp` + `Loop/GLoop`，是纯确定性算术层；
把接线写进去会让它 import `Gauss/MomentDuhamel`（整个 Gauss 栈），方向反了。
新文件 `Hierarchy/EEDef.lean` 同时 import 两边，与 T163 的 `EGDef.lean` 同构。

### ⭐ 关键发现：(5.22) 的展开**本来就在仓库里**
`Lemma57.lean` 偏差表第 9 条写「`E⊗E ≤ W ∑_b L^{(1)}(b)` 的展开本身不在仓库里」——**是错的**。
T74 的 `Gauss.eeEdge_eq_sum_SB` 经 T127 的 `EEBridge.eeEdge_eq_sum_gloop` 就是 (5.22)，
`Gauss.eeTens` 又本来就是 `eeEdge` 对 `k ∈ range I.length` 的和。于是

* `EEDef.glueSum` / `EEDef.eeL6`：把 `L^{(1)}(b)` 写成**定义** `∑_k ∑_{b'} ‖S^{(B)}_{bb'}‖·‖L_{glue(I,I',k,b,b')}‖`；
* `EEDef.norm_eeTens_le_W_sum`：`‖E⊗E‖ ≤ W ∑_b L^{(1)}(b)` 是定理（三角不等式 + 一次 `Finset.sum_comm`）。

### 接到钉死的对象
`EEDef.norm_EEpath_le_W_sum` / `norm_eeField_le_W_sum` / `norm_eeFun_le_W_sum` 三条同一件事
（`EEpath = eeField = eeFun ∘ X.H`，都是 `rfl`）。由此
**`EEDef.ee_le_EEpath` / `ee_le_paper_EEpath` 的左端是 `‖MomentDuhamel.EEpath X E n N u ω σ c‖`**，
`hEE`、`hL6`、`1 ≤ W` 三条假设全部卸掉（后者由 `B.W_pos`），`L^{(1)}` 不再是参数。
`ee_le_EEpath_labels` 进一步把 `a₁ a₂` 钉成 loop 自己的前两个标号（`lab₁ c = leftArg c 0`、`lab₂ c = leftArg c 1`，
`n = 0` 即 2-loop），于是 (5.36) 左端的归一化 `T_{u,D}(‖a₁−a₂‖)` 也不是自由选择。

### 仍是假设的六条（逐条给了理由，写在文件 docstring 里）
`h273`（(2.73) 的 `n = 6`）、`h564`（远 `b` 的显式余项 ρ）、`h42sq`（(4.2)/(4.5)+(5.31)）——都是别处的输入；
**`h566`**（(5.65)/(5.66) 的 Cauchy–Schwarz）——要 6-loop 逐元展开，T156 只打穿了 3-loop 层，**没动**；
**`h572`**——初等但没做；
**`hsym`**——paper-deltas #113 ②：论文的「by symmetry」是 (5.22) 的 `k=1`/`k=2` 对称，
不是 `k=1` 项内部的重标号，**已证不可能从 `k=1` 项推出**，本单**不尝试**。

### 可满足性自检（按「先查可满足再证」的要求，已在 Lean 里证出）
`EEDef.ee_hyp_consistent`：对任意 `X,E,N,u,ω,σ,c,a₁,a₂` 显式给出见证
`ℓu = ℓs = 1`、`D = 0`、`ηu = (W(1+S))⁻¹`（`S = ∑_b eeL6 b`，于是 `A_u = (1+S)⁻¹`、(2.73) 预算 `A_u^{-5} = (1+S)^5 ≥ S`）、
`J = μ = 1+S`、`ρ = S`、`Gsq` 取 (4.2) 的等号，六条假设**同时成立**。
关键是 `D = 0` 时 `tailT` 的地板 `W^{-0} = 1`，四个 `tailT` 因子都 `≥ 1`。
这不是论文的区制（那里 `A_u → ∞`），只用来排除「把 `L^{(1)}` 钉成具体量之后假设组自相矛盾 ⇒ 结论空洞」这一失效模式
（T172 在 `MinorGood` 上抓到过的正是这个）。

### fiat 审计
左端每一个量都是定义：`EEpath`(T145) = `eeField`(T127) = `eeArg` = `Gauss.eeTens`（Def 5.4），
在流自己的 `X.H N u ω` 与 `z_u` 上取值；右端 `eeL6` 也是定义；两者之间是定理不是假设。
**陈述里没有任何结构字段**，**全程没有 `SumZeroDyn.Hierarchy` 实例**（T118 遵守）。
调用者仍需提供的见证 `Gsq`、`μ`、`ρ` 只出现在假设里（master 形状的结论里还留 `Gsq`、`μ`，
与 T163 `eG_le_reduced` 的 `Gm` 同性质；`ee_le_paper_EEpath` 把 `μ` 消掉了）。

### 下一步
`h566` 需要 `gloop_three_expand` 的 6 元版 + `G†E_bG` 的块结构；
`hsym` 需要 (5.22) 的 `k=2` 项（仓库里没有），两者都可以在不改 `EEDef.lean` 的前提下单独补。

## ⭐ T171：`MinorDiffGain` 事件条件化落地——外加一堵**可编译证明**的墙（`Gauss/MinorDiffCond.lean`，726 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9150** 条。

### ⚠ 结论一：T164 建议的 `hslice` 形状**本身不可满足**
建议的签名 `hslice : ∀ κ ω, (P d).real (rowSlice d N κ Bad ω) ≤ ε` **又是一条 `∀ω` 假设，且对真正的好事件为假**：
把某一行 `j ≠ κ` 的对角坐标冻结成大数 `R`，则 `|G_jj − m| ≈ 1 > Ψ` **与行 `κ` 的取值无关**，于是 `rowSlice κ Bad ω = univ`、概率为 1。
（这就是 T172 的 `not_minorGood_forall` 换一行的版本。）**Markov 救不了**：`meas_measure_rowSlice_ge` 只能说「截面大的 `ω` 少」，
而把这些 `ω` 并进 `Bad` 之后**新集合的截面又变了，循环**。

**正确形状是逐层的塔**：`badStep`/`badTower` + `BadFamily`（`slice` 被 `ω ∉ Bad (j+1)` 挡着，**在典范构造里按定义成立、不是 fiat**）。
`badFamily_badTower` 对任意可测 `S` **无条件产出** 一个 `BadFamily`。
代价 `meas_badTower_le`：**每个字母损一个 `(ε + #行)/ε = N^{O(1)}`**，字长有界时 `≺` 允许。

### 核心工具与主定理
`norm_applyOps_le_badFamily`：对字归纳，每个 `E_κ` 用 `Gauss.norm_condRow_le_split`（取 `f := 1`），`Q_κ` 补一次三角不等式。
**没有把指示函数乘进被积函数。** 结构化简的关键：`flucDiagSet = qRow k (greenSetDiagCentered)` 且 `Δ` 与 `Q_k` 交换
（`minorDiff_flucDiagSet_eq`），于是整个因子等于**单个字**作用在**确定性**族上，好事件只在那一个确定性族上逐点使用。

主定理 `integral_prod_applyOps_minorDiff_le_on` 与它的 `goodSetFlow` 版，**假设表里没有任何对所有 `ω` 量化的好事件假设**；
后者的假设**全是数值条件**，概率输入只有 `goodSetFlow`（= 论文 (4.1) 的 `Ω(t,c)`）。
条件化的代价显式：`condEnv`、`condCost`（**加在常数 `B` 上，增益 `ρ = 2Ψ` 一点没退化**）、以及加性余项 `condEnv^{#ι}·P(Bad_{M+1})`。
`goodSetFlow` 的可测性缺口用 `toMeasurable` 取可测包解决（外测度下包与补集测度相等），**没有留窟窿**。

### ⚠⚠ 结论二：`MinorDiffGainUpTo` 在 `B ≍ Ψ` 处不可满足——**与 T172 的天花板同一堵墙**
`integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo`（已编译）：取 `ι = Fin n`、全部 `L i = []`，得
**`MinorDiffGainUpTo` 的 `B` 支配 `Z_k` 的每一个 `L^n` 范数**，`n → ∞` 即支配 `‖Z_k‖_∞`；
而 T172 的两点法给出 `‖Z_k‖_∞ ≥ 64/65`。**故 `B ≍ Ψ` 不可满足**——`minorDiffGainUpTo_of_minorGood'` 是真定理但**前提假**，死胡同。

**推论**：加性余项 `condEnv^{#ι}P(Bad)` **不是这条证明的赘生物，它吸收不进 `MinorDiffGainUpTo`**
（`condEnv ≍ η_u⁻¹ > B`，`#ι` 无界时必然超出）。**根因是 `MinorDiffGainUpTo` 的 `ι` 没有基数预算。**

### 还短的那一步（未做，要改 `FlucIter.lean`/`FlucIterHigh.lean`）
给 `FlucGainUpTo`/`MinorDiffGainUpTo` 加**第二个预算 `#ι ≤ n`**。有了它余项就能吸收：
`#ι ≤ n`、`∑q ≤ nM`、`B₀ ≤ 1`、`2Ψ ≤ 1`、`1 ≤ condEnv` 时
`condEnv^{#ι}P(Bad) ≤ condEnv^n P(Bad) ≤ B₀^n(2Ψ)^{nM} ≤ B₀^{#ι}(2Ψ)^{∑q}`，总界 `≤ (2B₀)^{#ι}(2Ψ)^{∑q}`。
而 `2p` 阶矩展开里 `#ι ≤ 2p` **本来就成立**（与 `OpsOkOut.length_le` 同源）。本文件的 `..._le_on` 可直接喂它。

**未编译的部分（如实）**：`hslice` 不可满足是论证 + 据此改了接口形状，**不是编译证明**
（T172 的反例当时只在探针里、未入库，从零搭要另开一单）。

## ⭐ T174：指数表重算（只读，2026-09-21）——**30 够，不动；但旧审计有两处算错**

`β*` 全部从**已编译的 Lean 陈述**与论文原文重推，未沿用旧审计的数字。
判据：`hregS` 逐字是 `N^c(η_s/η_t)^{30} ≤ A_t`，系数 `A^{−α}R^β` 可过 **当且仅当 `β* := β/α ≤ 30`**。
`r := ℓ_u/ℓ_s ≤ √R` 是**定理**（`Step3.ellHat_le_sqrt_mul`），不是假设。

### 块 I：`phi` 各项（预算 `C x²R⁴`）
`(5.40)` → `β* = 6`；**`(5.41)` 远场（论文字面 `A^{−1/3}(J*)³`）→ `β* = 30`，R 余量为零**（与更正前一样恰在边界）；
(2.73) 降幂后 → 主项 **5.5**、次项 **4.5**；近场 shape 1 是 `r²`、shape 2 是 T155 更正的 `r³`（两者都是 α = 0，不占预算）。

### 块 II：(5.42)/(5.44) 二次变差（预算 `M_m²R⁴`）
* 近场 `(η_u/η_t)⁴r⁵` → `β = 0`，**R 余量为零**。
* **⚠ 旧审计这里算错了，而且比「半格」严重得多**：旧审计按 `A^{−1}` 算，(5.36)→(5.42) 的吸收有 `A^{−2/3}` 可花、`β* = 6`；
  实际 `ee_le` 的 Case 2(1a) 是 `cFar2·J²·(Aμ)`，由 (2.73) `n=4` 得 `Aμ = r^{3/2}A^{−1/2}`，**只剩 `A^{−1/6}` 可花 ⇒ `β*` 从 6 跳到 28.5**。
  **论文 (5.36) 自己写的就是 `A^{−1/2}`，所以不是论文错，是旧审计算错。**
* 开方不改变判决（α、β 同时减半），**唯一不被开方摊薄的就是那个吸收步**——它发生在积分与开方之前，这正是它成为全表第二紧的原因。

### 结论：**30 够，Jun 预授权的 50/100 不启用**
最大的两个 `β*` 是 **30**（(5.41) 远场，论文字面）与 **28.5**（那个吸收步），都 `≤ 30`。

### 三条有实现后果的建议（比门槛本身重要）
1. **那个吸收步整行可以删掉**：`ee_le_paper` 已经把 `A^{−1/2}` 编译出来了，**不做论文那步 `−1/2 → −1/3` 的吸收**，
   瓶颈从 28.5 降到 **17.5**（用 `ee_le` 不合并的两项形）。**零成本**——`ee_le` 本来就是两项形，是 `ee_le_paper` 主动并成 `(J*)³` 的。
2. **生产 `Hyp.mart` 时，近场那一项必须「先乘后取 sup」**：`∫η_u^{−1}(η_u/η_v)^4r^5du` 的被积函数 `= η_v^{−4}η_s^{5/2}η_u^{1/2}` 在 `u = s` 取最大，
   乘 `(v−s) ≤ η_s` 得 `R^4` **恰好等于预算**；按 `phi` 现在的「`R^4 × sup r^5`」粗算会**超预算 `R^{2.5}`**。
3. **#113 ③ 的 `(ℓ_u/ℓ_s)^{3/2}` 能被吸收，(5.36) 的陈述不用改**：在 (5.44) 的积分里它是免费的
   （`∫η_u^{−1}(η_u/η_v)^4r^k du` 只要 `k < 8` 结果都是 `R^4`——**这正是论文 (5.44) 写 `(η_s/η_t)^4` 的原因**）；
   即便按粗算也只值 `R^{3/4}`，把那行推到 28.5，仍 `≤ 30`。

### 截断（T158）的 `N^{o(1)}` 代价落点
唯一的真交互：**`r−1 ≍ log N`（光滑化的二阶代价）落在 `β* = 30` 那一行，而该行 R 余量为零**，
所以 `log N` 只能从 `N^c` 增益里出，要求 `δ` **严格小于 `c/9`**——`phi_arith` 文档头写的 `δ ≤ c/24` 已经留够。
`e²` 落在块 II 的 α = 0 行，由 `M_m` 的常数吸收；`W^{2D}` 与 A/R 正交，但 `D ≥ 60` 要按 `WLρ·W^{2D}` 重选。

### `phi_arith` 还对不对：**分两种走法**
* **走论文字面 shape 1：假设表一字不改。** T155 的 `r³` 只在 shape 2；T156 的更正**根本不进 `phi`**
  （它在 `Hyp.mart` 里，`phi_arith` 看到的只是 BDG 完的常数）。唯一新增的 `hJA : J* ≤ A_u`（#112 ③）
  **由 `phi_arith` 自己的 `hA` 免费推出**（`J* ≤ Λ = x⁸R⁴ ≤ x^{17}R^{10} ≤ A`）——**这一路不需要 Jun 拍板。**
* **走 shape 2（把 30 挪到 5.5）：`phi`/`phi_arith`/`Hyp.eG` 三处签名要一起改。**
  **改法已在 scratchpad 编译验证**：`phi_arith'` 把 `hq : q ≤ R` 放松成 `q ≤ R²`，**证明骨架与常数 `cStep` 都不变**
  （t4 恰好取等）——所以 **T155 的 `r³` 只是一处假设的放松，不是重证**；`phi_arith2` 是 shape 2 的完整算术。

### 一处未能复现（如实）
旧审计 `BootPP` 那行的 `β* = 1` 从 `harith_flowAs` 的陈述复现不出来：`Step3.flowR = r ≤ √R`（不是 `R`），
三项分别要 `R^5/R^4/R^4 ≤ A`，最坏 **`β* = 5`**。无论 1 还是 5 都不影响结论。

## T166：(4.7) 二次型 LDE 的带地板时间一致版 + (4.3) 的确定性带地板链（2026-09-21）

`lake build RBM1D` exit=0，审计 **9189** 条。`Gauss/LDENetClose.lean` 992 → 1684 行（纯新增，旧声明一字未动）；
新建 `Green/EntryBoundFloor.lean`（794 行）。

**主交付 `stochDom_ldeQuad_flow_floor`**：假设表与 T148 的 row/col 版**逐字相同**（`|E|<2`、`0 ≤ s ≤ t < 1`、`N^{−K} ≤ η_{t_N}`），
**没有额外概率输入**。配方原样复用 T148 的「网点高斯尾 + 并界 / 网点之间确定性 Hölder / 不单位化 / 地板」。
模同样是**逐元**证的：二次型比行和多一个 `H` 因子与一重求和，指数 `10 → 14`、常数 `6 → 28`。
唯一的缺口是新证的桥 `greenMinor_eq_greenMinorMat`（`k,l ≠ i` 时 (4.9) 的 `greenMinor` 就是小方阵预解式的元素）。
另外 `unifDomIcc_ldeQuad` 无条件（Hanson–Wright 的常数与时间无关，`UnifDomIcc` 不取指标并集，故**基数假设也一并掉了**）。

**`Green/EntryBoundFloor.lean` 的关键观察**：地板只经 `LDE*Floor` 进入，而 (4.11) 以下每一步都由「界住 `∑∑S|G|²S` 与 `S_{ij}` 的 `Λ`」
参数化——**只要多要一条 `fl ≤ Λ`，所有带地板陈述与无地板版形状完全相同，只是常数翻倍**（162→324、…、4320→8280）；
块模型里取 `Λ = 2·L^max + fl` 自动满足。`hLdiag` **没有加地板**——其生产者 `stochDom_normSq_Hflow_diag` 本来就无条件。

### `DiagBoundFlow` 的现状：墙倒了，剩下全是 `Gauss/` 侧的接线
`diag_bound_stochDom_floor_idx`（时间进指标集的版本）就是 `DiagBoundFlow` 要的形状，`hLrow`/`hLcol`/`hLquad` 三条**结论逐字吻合**。
还缺三件，**没有新数学**：
1. **`hLdiag` 的带时间版**——仓库只有固定 `u` 的。数学上白送（`‖H_{u,ii}‖² = u‖X_ii‖² ≤ ‖X_ii‖²`，控制与 `u` 无关），
   但要写在 `Gauss/`。**T160 说「可以直接用」在控制这一侧对，在指标并集这一侧还欠一步。**
2. **地板落地**：控制是 `L^max + N^{−B}` 而 `DiagBoundFlow` 要裸 `L^max`。唯一消费者 `stochDom_indicator_diag_flow`
   立刻与无条件的 `W⁻¹` 复合，取 `B := 1` 即吸收——**与 T160 给 `EntryBoundFlow` 记的那条约 15 行引理是同一条**。
   所以 `Step1.Lemma41Flow` 的结论拿得到，但中间 `def` 本身拿不到，**需要一个 `DiagBoundFlow'`**（与 `LDEFlowDom'` 同手法）。
3. `hδ`：`entry_bound_stochDom` 一侧本来就需要同一条，不是新负担。

**没有出现 T148/T172 那种「目标本身为假」的情况**——二次型的模确实闭合，每一步都编译过，没有任何因子短缺。

### ⚠ 下沉内核：被迫重证了六条
`norm_sq_green_offdiag_le_floor` 依赖 `norm_sq_green_le_two_sided_floor`，而后者住在 `Hierarchy/LKDecayQuant.lean`，
**`Green/` 不能 import `Hierarchy/`**。所以在新文件里重证了 T160 六条中的六条（加新的 `LDEQuadFloor`）。
命名空间 `RBM` 与 `RBM.LKDecayQuant` 的副本全名不同、不冲突。
**`LKDecayQuant` 里的重复副本应删除并改指到这里，由该文件的所有者做。**

## Jun 裁定：论文 (5.36) 第二项补因子 `(ℓ_u/ℓ_s)^{3/2}`（2026-09-21 11:05）

T156 发现、Cowork 对照原文核实：(5.67) 之后那行（「Next, applying (2.73) on L term in (5.66), together with (5.67) we obtain that」）与 (5.71) 都带 `(ℓ_u/ℓ_s)^{3/2}`，乘 (5.22) 的 `W∑_b` 后情形 (1a) 贡献 `η_u^{−1}(ℓ_u/ℓ_s)^{3/2}(Wη_uℓ_u)^{−1/2}(J*)²`，而 (5.36) 第二项 `η_t^{−1}(Wη_uℓ_u)^{−1/2}(J*)³` 在 `u` 近 `t` 时盖不住它。
Jun：「你理解的正确，这个地方补上这个 factor（可能当时忙乱了）」。**论文改动**：(5.36) 第二项乘 `(ℓ_u/ℓ_s)^{3/2}`（paper-deltas #113 ③、论文改动预算第 13 条）。**Lean 不改**（`ee_le_paper` 已带该因子）；T174 按补正后的 (5.36) 算指数表。
另：页码约定写入 `CLAUDE.md`——以编号为准，仓库页码 ≠ Jun 手上版本的页码。

## ⭐ T176：六步循环剩余具名假设的**当前**清单（只读审计，6 个编译探针，2026-09-21）

**从 `Bounds X E s` 到 `Steps X E s t` 现在只差 10 条具名假设**（探针 P1 编译通过，公理干净）。
链条 `Step1.step1 → Step2Moment.step2 → Step2PP.flow_sharpLoop_glue_flowAs' → flow_steps45_glue_flowAs' → sharpExpect_step6_driftE`，
**假设里没有 `Steps`、没有 `Step2.Hyp`、没有 `SumZeroDyn.Hierarchy`、没有自由张量**，且**全程只收 `hs0 : ∀ N, 0 ≤ s N`**。

| # | 假设 | 状态 |
|---|---|---|
| 1–2 | `EntryBoundFlow` / `DiagBoundFlow` | 在飞（T107；T166 已推倒 `ldeQuad` 的墙，剩 `hLdiag` 带时间版 + `DiagBoundFlow'`） |
| 3–4 | `MomentHyp` / `hΘ`（`BootPP`） | 在飞（T132c 一张单同交 3 条） |
| **5** | **`h514 : Lemma514`** | 🔴 **无主，且在 T118 禁用的 fiat 路线上** |
| 6 | `Eq45Flow` | 生产者已在（探针 P4），但其 `hg` 不可满足，见下 |
| 7 | `FlowEq548` | 在飞（T132c） |
| 8–10 | `hH` / `hFD` / `h5133` | `hH` 部分；`hFD` 已归约到 Lemma 5.9；🔴 **`h5133` 的 Ξ-记账无主** |

### ⚠⚠ 一条 T147 没写、今天才浮出来的接口错配（探针 P2/P3）
**`Thm221.step` 只收 `Cond272`（裸 (2.72)），而六步全链要的是带 `N^c` 增益的 `hregS`。**
`Cond272` 严格更弱——paper-deltas #47/#54/#73 记过这条偏差，**但没人记它把 `Thm221` 的陈述变成了不可证**。
`eventually_flow_grid` 也只产出裸 (2.72)，所以 `Bounds_of_Thm221` 一侧同样对不上。
**好消息（探针 P3 编译通过）**：`gridT_step_2_72_gain` 证明 p.24 的网格**能带任意增益 `g`**，
而 `flow_grid_2_72` 的证明内部本来就有 `g = Im m·W^{τ/2−30τ'}`（由 `60τ' < τ` 是 `W` 的正幂）。
**结论：纯记账 + 一条 `eventually_flow_grid'` + 一个 `Thm221'` 字段，零新数学，但目前无人负责，且它挡在总装的最后一米上。**

### ⚠ 另一处：同一堵墙就在**活路径**上，比 T171 说的高一层（探针 P5）
`integral_pow_norm_flucDiag_le_of_flucGainUpTo`（已编译）：**`FlucGainUpTo` 自己的 `B` 就支配 `Z_k` 的每一个 `L^n` 范数**
——而 `FlucGainUpTo` 正是 `eq45Flow_of_localLaw_gain'` 在 `hg` 槽吃的接口。配上 `‖Z_k‖_∞ ≥ 64/65`，
**`hg` + `hBK : Bp ≤ Kp·Ψ` 在 `Ψ → 0` 时不可满足**。
→ **修基数预算的那张单必须把 `FlucGainUpTo` 一并写进规格**，只点名 `MinorDiffGainUpTo` 会修了下层、上层接口仍然塌。

### T147 条目的时效性
* §0a **`Steps` 打包循环**：**已解**（探针 P1 的结论是 `Steps` 而假设里没有 `Steps`）。
* §0b **`0 ≤ s`**：**已闭合**。⚠ 但 `lemma514_flow'` 仍要 `0 < s N`——若 `h514` 回到 SumZeroDyn 路线，**这条缝会重新裂开**。
* §6(c) 九处「已卸未接」：**八处已接**；唯一未接的 `Lemma510.EE_le` **已成死项**（它只喂被 T118 禁用的 `lemma514_flow'`）。
* §6(b)④⑤：均已过时（T151）。
* **「T58 是瓶颈」：部分过时，但换了个更糟的形状。** ①④ 已解决，**但 ②③（`Lemma514`）并没有被 T146 重新生产**
  ——T146 交付的是 `hrhs`。`stochDom_of_momentDuhamel` 只给**固定终点**的 `≺`，且其 `Hyp` 本身**也无生产者**。
  **⚠ TASKS 顶部「②③ → T146（完成）」是错的：`Lemma514` 现在无主。**

### fiat 审计：活路径上只剩一处冲突
`Hyp.F`、`EEpath`、`E^{(G̃)}`、Step 6 的漂移张量**全部钉死**；`MomentHyp` 的数据字段**不可 fiat**
（`bnd_poly` 强制 `bnd(2p) ≤ CN^{εp}` 对每个 ε）；`BootPP.target` 形式上自由但消费者只吃 `Θ = flowAs^{1/2}`，
**单独「交付一个 `BootPP`」一文不值**。
🔴 **唯一的 fiat 冲突是 `SumZeroDyn.Hierarchy`**（`F/EE/mart/martQ` 全自由），**而它是 `h514` 的唯一入口**。

### 顺带纠正一条过时记载（探针 P6）
STATUS 的 T173 节写「`hEL` 仍挂 `MatrixStein`(T70) 与 `hjoint`(T141)」——**T70/T141 都已落地**
（`Gauss.matrixStein` 是定理、`differentiableAt_integral_gloop_flow` 已有），`hEL` 在高斯模型上**已经可以产出**。

### 最短路径（2、4、5、6 可四路并行；1 可立刻单独做完）
1. 🔴 `hregS` vs `Cond272` 的接口修复（无主，纯记账）—— **不做的话前面所有工作都接不到 `Thm221` 上**。
2. 🔴 `h514` 换成矩路线版（无主）——唯一落在 T118 禁令上的一条，**今天最大的一块**。
3. T132c（在飞，一单交 3 条）。 4. 基数预算（含 `FlucGainUpTo`）。 5. T107 + T160(2)。 6. Step 6 收尾 + `h5133` 的 Ξ-记账。

### 声明的盲区
`hcont`/`hintF`/`hintU` 与 `MomentHyp` 的 `cont/holder/env_le/meas` 只 grep 未构造；
`‖Z_k‖_∞ ≥ 64/65` 是 T171/T172 的结论、**两条反例当时都只在探针里未入库**，本次未重跑，
且 `L^n → L^∞` 那一步需要 `ω ↦ Z_k(ω)` 的连续性，**T171 没有写出这一步**；
`hregS` 能否从强化后的网格真正推出，P3 只证了「网格步能带任意增益」，**最后一段是读证明得出的、未编译**。

## T107：`EntryBoundFlow` 接上了——**(4.2) 已从 `Step1.Hyp` 的假设表里消失**（`Gauss/EntryBoundTime.lean`，501 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9206** 条。`Gauss/Lemma41FlowGauss.lean` **一个字没动**（新增全在新文件）。

**先回答 T166 那个警告：row/col 侧确实有同样的缺口，而且更严重**——`Green/EntryBoundFloor.lean` 里
**只有对角版的指标加宽** `diag_bound_stochDom_floor_idx`，**没有 (4.2) 的对应物**。本单补了
`Gauss.entry_bound_stochDom_floor_idx`（确定性内核直接取 T166 的 `norm_sq_green_le_blk_floor`，**没有重证任何东西**）。
**建议下沉到 `Green/EntryBoundFloor.lean` 与对角版并排。**
**控制侧则确实逐字对上**：`stochDom_ldeRow/ldeCol_flow_floor` 塞进槽位零改写、`exact` 直接过。

**产出** `entryBoundFlow_floor : EntryBoundFlow' d E s t (fun N => 2·N^{−B})`——`EntryBoundFlow` 的陈述逐字不变、
控制多一项地板，**无任何大偏差假设**，其余全是与 T148/T166 同一批的区制条件。
（无地板的 `EntryBoundFlow` **没有也不可能被证出来**——那正是 T148 判定为假的形状。）

**四条下游陈述真的逐字不变，而且是编译验证的不是目测**：用 `have : h1 = h2 := rfl` 探针（`Prop` 相等要求两侧 defeq）
对 `stochDom_indicator_offdiag_flow`、`stochDom_indicator_llMax_sq_flow`、`lemma41Flow`、`Step1.Lemma41Flow` **四条全过**。

**地板代价为零，按 T160 的估计兑现**：与无条件的 `W⁻¹` 复合，由 `3W ≤ WL ≤ N` 取 `B := 1`。
（实际比估的 15 行多些：吸收引理 ~25 行、`3W ≤ N` ~15 行、`offdiag'` ~35 行。）

**额外落地（零新增假设）**：`step1Hyp_gauss_of_scale'` 与原版**结论与假设逐字相同，只是删掉了 `hEntry`**
（同样 `rfl` 验证）——两条区制输入都能从 `step1` 自带的 `N^c ≤ Wℓ_tη_t` **免费推出**。
**于是 (4.2) 已从 `Step1.Hyp` 的假设表里彻底消失，那里只剩 `DiagBoundFlow`。**

`LKDecayQuant.lean` 的八条重复副本仍在；本单只用 `Green/` 那一套，**既没让它们更好删、也没挡着删**。

---

# 待 Jun 定夺（Claude Code 汇总，2026-09-21）

> **约定（Jun 2026-09-21）**：Jun 不在 Claude Code 界面回复。凡需他裁定的，Claude Code 写在这一节里，由 Cowork 与他讨论。
> 本节只列**需要裁定**的，不列进度；裁定后由 Cowork 开单，Claude Code 不写工单。

## D1 ~~⭐ `Thm221.step` 收的是裸 `Cond272`~~ —— **Lean 侧已解决（T179），只剩论文措辞**
**已落地**：新增 `Cond272'`（= `hregS` 逐字）与 `Thm221'`（`c` 量化在 `step` 内部），旧的 `Cond272`/`Thm221` 一字未动；
**T176 未编译的那一段（`g ≥ N^c`）现已编译**，且比预估短——直接用 (2.2) 的 `W ≥ N^{1/2+c_B}`，不必绕 `B.dim`。产出 `c = min(τ,1)/32`。
下游补了带撇版（`Flow/Thm221Gain.lean`），**结论逐字不变（`rfl` 探针验证）**；`Thm221` 在整条装配里**只从 `SpecSeq.bounds` 一处进入**。
**⚠ 一条要记住的约束**：网格给的 `c` 有上界 ≈ `τ/16`，**不能要多大给多大**，所以 `Thm221'` 必须对任意小的 `c > 0` 成立（现有生产者满足，已验）。
**仍待裁定（只剩这一条）**：论文侧 (2.72) 是否相应写成带增益形——**Lean 侧不需要**，paper-delta #125 已足。
（~~备选：走 (2.73) 降幂的 shape 2 后 T174 表里所有行 `β* < 30` 严格成立，裸 (2.72) 其实也够~~ —— **T186 已推翻后半句**：`β* < 30` 只解决 `R` 的幂，解决不了 `≺` 的 `N^δ`，那需要 `A_t` 的多项式下界，而裸 (2.72) 在 `s = t` 处只给 `A_t ≥ 1` 且 `A_t = 1` 可取（已编译反例 `RBM.exists_cond272_not_rpow_le_scale`）。可达的最强形是 `Cond272Reg` = (2.72) 逐字 + Step 1 本来就带的 `N^c ≤ A_t`。见本文档 T186 节。）

<details><summary>原始条目（存档）</summary>

## D1（原文）`Thm221.step` 收的是裸 `Cond272`，而全链要带 `N^c` 增益的 `hregS`（T176，探针 P2/P3）
`Cond272`（`Flow/Hypotheses.lean:290`）等价于去掉 `N^c`，**严格更弱**；六步全链（`hregS`，`Step2PP.lean:575`）要的是带增益版。
paper-deltas #47/#54/#73 记过这条偏差，**但没人记它把 `Thm221` 的陈述变成了不可证**；`eventually_flow_grid`
（`Flow/Iteration.lean:238`）也只产出裸 (2.72)，所以 `Bounds_of_Thm221` 一侧同样对不上。
**这挡在总装的最后一米上，且目前无人负责。**
* 已验证（探针 P3，编译通过）：`gridT_step_2_72_gain` 证明 p.24 的网格**能带任意增益 `g`**，
  而 `flow_grid_2_72`（`Scales.lean:326`）的证明内部本来就有 `g = Im m·W^{τ/2−30τ'}`（由 `60τ' < τ` 是 `W` 的正幂）。
* **未验证**：把 `g ≥ N^c` 那一段（要 `W ≥ √(N/2)`）接起来——P3 没编译这一步，是读证明得出的。
* **代价评估**：一条新的 `eventually_flow_grid'` + 一个 `Thm221'` 字段，零新数学。
* **要定的**：(a) 就地改 `Thm221`/`Cond272`，还是加带撇版；(b) 论文侧 (2.72) 是否相应写成带增益形（还是只在 Lean 记 delta）。

</details>

## D9 ⭐ `TestFun`/`TestFunT` 对**所有**矩阵量化，而矩 Duhamel 的 `Ψ` 只在 Hermitian 集上合格（T180）
`Hyp.momentDuhamel`/`momentDuhamelQ` 的最后一步要 T132b 的 `hasDerivAt_integral_Psi_pairs`，它收 `Gauss.TestFunT`。
但 `Ψ(u,M) = |(U_{u,v}∘(L−K)(u,M))_a|^{2p}` **不在该类里**：`bdd₀/₁/₂` 对所有矩阵量化而 `(M−z_u)⁻¹` 在非 Hermitian `M` 上无界；
`TestFunT.slice` 要全局 `ContDiff ℝ 2`，而在奇异的非 Hermitian `M` 处 `Ψ` 连连续都不是。**在 Hermitian 集上两条都成立**，
而整个论证本来就待在那里（流是 Hermitian，流值之间的线段也是）。**两条路，需裁定**：
* **(i)** 把 `TestFun`/`TestFunT` 从 `∀ M` 放松到 `∀ M, M.IsHermitian →`——**就是 T145 对 `Hyp.drift` 做过的同一处修补**；
  代价是把 `hasDerivAt_integral_Psi` 的控制收敛改写到流上重证。
* **(ii)** 截断 `Ψ`，即 T158 的光滑截断方案，连带「三个真实缺口」。
**agent 的判断（我同意）**：`Hyp.momentDuhamel` 是**结构性**不等式（右端摆着 `F` 与 `E⊗E`），
**本身不需要截断给的尺寸估计**，只需要生成元恒等式 + Hölder。**所以 (i) 若可行，代价明显小于 (ii)。**
⚠ 这是第五次撞上「字段对所有矩阵/所有样本点过度量化」（T145、T132b、T154、T164/T172，现在 T180）。

## D13 ⚠⚠ **裁定反转：裸 `Cond272` 不够**（T186，编译反例）（原编 D12，与 Cowork 的 D12 撞号，16:10 改为 D13）
Jun 12:10 选 (a)「论文 (2.72) 陈述不改」，依据是 T174/T132c 的「走 (2.73) 降幂后每行 `β* < 30` 严格成立」。
**那一半是对的，但由此推出「所以裸 (2.72) 也够」不成立**——`hregS` 的 `N^c` 有**两个**用处，此前只核了第一个：
① 压住 `R = η_s/η_t` 的幂（这个确实由 `β* < 30` 白送）；
② **给 `A_t = Wℓ_tη_t` 一个多项式下界**，好把 `≺` 的 `N^δ` 吃掉（`phi_arith` 的 `hA`）。**裸 (2.72) 对 ② 一点都不给。**
取 `s = t`，(2.72) 逐字就是 `1 ≤ A_t`，而 **`A_t = 1` 确实取得到**（已编译：`exists_flowScale_eq_one`、
`eventually_exists_scale_eq_one`、`exists_cond272_not_rpow_le_scale`——后者给出逐字满足 (2.72) 的时间列，其上 `N^c ≤ A_t` 对任何 `c > 0` 失败）。
**这不是 Lean 写宽了**：论文 p.24 的 Theorem 2.21 假设表确实只有 (2.68)–(2.72)，多项式下界是**应用时**由网格 `t ≤ 1−N^{−1+τ}` 给的。
**可达的最强形 `Cond272Reg` = (2.72) 逐字 + Step 1 本来就带的 `hreg`**，代价只有 **δ 预算减半**（`δ ≤ c/4` vs 带增益的 `δ ≤ c/2`）。
**要定的**：论文是否在 (2.72) 后补一句「`Wℓ_tη_t ≥ N^c`」（paper-deltas #132 的建议），还是保持原样、由 Lean 侧用 `Cond272Reg` 承接。
**附带印证**：论文字面 shape 1 的边条件在该判据下逼出 `N^δ` 零余量，**说明 Jun 选 (a)「(5.41) 必须走 (2.73) 降幂」是必要的**，否则连 `Cond272Reg` 都不够。

## D2 ~~⭐ 基数预算的工单必须把 `FlucGainUpTo` 一并写进规格~~ → **已办（T177，2026-09-21）**

> 两层都加了预算（`FlucGainUpTo'`/`MinorDiffGainUpTo'`），两条反例已入库，(4.12)→`Eq45Flow`
> 整条链在 `MinorDiffCond.lean` 里按预算版重建、只读文件一个字没动。详见本文档末尾的 T177 节。
> **仍未验证的那条照旧**：`‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步（需 `ω ↦ Z_k(ω)` 连续性）没入库。
> 下面是原始条目，保留备查。

### （原始条目，T171 + T176，探针 P5）
T171 已编译证明 `MinorDiffGainUpTo` 在 `B ≍ Ψ` 处不可满足（其 `B` 支配 `Z_k` 的所有 `L^n` 范数，配 `‖Z_k‖_∞ ≥ 64/65`）。
**T176 的探针 P5 表明同一堵墙高一层、且在活路径上**：`FlucGainUpTo` 自己的 `B` 也支配所有 `L^n` 范数，
而 `FlucGainUpTo` 正是 `eq45Flow_of_localLaw_gain'`（`CondStableFlow.lean:1246`）在 `hg` 槽吃的接口。
**只点名 `MinorDiffGainUpTo` 会修了下层、上层接口仍然塌。**
* 修法已写清（T171 §「还短的那一步」）：加第二个预算 `#ι ≤ n`；`2p` 阶矩展开里 `#ι ≤ 2p` 本来就成立。
* **未验证**：`‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步需要 `ω ↦ Z_k(ω)` 的连续性，**T171 没有写出来**；
  两条反例当时只在探针里、未入库。**若要把这堵墙当定论，应先补这一步。**

## D3 ⭐ `Lemma514`（`h514`）现在无主，且唯一入口落在 T118 禁用的 fiat 路线上（T176）
工单表顶部此前写「T58 的 ②③ → T146（完成）」——**是错的**，T146 交付的是 `hrhs`。
全树 `Lemma514` 只有 `SumZeroDyn.lemma514_flow/'`，**三者都收 `H : ∀ n, SumZeroDyn.Hierarchy`**，
而 `Hierarchy` 的 `F/EE/mart/martQ` 全是自由数据（T118/T172 判定，禁止实例化）。
**这是活路径上仅剩的一处 fiat 冲突，也是目前最大的一块。**
* 矩路线替代要走 `MomentDuhamel.Hyp` → `stochDom_of_momentDuhamel` → T124 网 → `Lemma514` 形状，
  但 `Hyp` 的 `momentDuhamel`/`momentDuhamelQ`/`drift` 三条**自己还没有生产者**（T132b 余项：
  `u ↦ Kval` 的时间可微性、固定 Hermitian `M` 时 `u ↦ gloop` 的可微性）。
* ⚠ 附带：`lemma514_flow'` 仍要 `0 < s N`。**若 `h514` 回到 SumZeroDyn 路线，T161 刚闭合的 `0 ≤ s` 缝会重新裂开。**
* **要定的**：是补 T132b 的余项走矩路线，还是另想办法。

## D4 (5.35) 的第一项需要论文没写的 `J* ≤ A_u`（T155，paper-deltas #112 ③）
(5.55) 明写 `(1+(J*)²A⁻¹)` 而 (5.35) 第一项不带 `J*`，中间那步要 `r² ≤ J*·A^{2/3}`，**不自动成立**。
在论文上下文里 `J* ≤ A_u` 总成立，只是从没写出来。**要定的**：论文是否补这半句。
（**Lean 侧不需要裁定**：走论文字面 shape 1 时，该条件由 `phi_arith` 自己的 `hA` 免费推出——T174 已核。）

## D5 (5.77) 第 3 行短一个因子 `Ξ^{(L−K)}_{u,1}`（T165，paper-deltas #119）
`Decay.norm_eG_le` 出来的是 `Ξ^{(L−K)}_{u,1}·Ξ^{(L)}_{u,m+1}`，而 (5.77) 第 3 行写的是**裸的** `Ξ^{(L)}_{u,m+1}`。
论文默认它 `≲ 1`（(2.68) 单圈）才丢掉，**但它既不是常数也不在 `xiRhs` 里，从另外两行推不出来**。
**要定的**：论文补一个因子，还是补一句「由 (2.68) 该量 `≲ 1`」。

## D6 Theorem 2.2 的谱边缘措辞（T153）
局部律只在 `|E| ≤ 2−κ` 上有；(2.10) 对体内特征值成立，**边缘的 `λ_k` 要么排除、要么记一条 paper-delta**。
**要定的**：论文 Theorem 2.2 怎么措辞（审计时为省预算没翻 PDF，落地前需确认）。
附带路线判定（**已定，不需裁定**）：`Flow/` 层固定 `E` 纯参数化，(ii) 的输入恰是 (i) 的输出，故顺序只能是 (i) → (ii)。
**要定的只有**：(i) 走新文件（0 个现有签名改动）还是就地泛化（更干净，但要动 `Cond272` 的 14 个文件，与并行车道冲突）。

## D7 两处「仓库里的重复副本该由谁删」
* `Hierarchy/LKDecayQuant.lean` 有八条带地板内核与 `Green/EntryBoundFloor.lean`（T166）重复；
  `Green/` 不能 import `Hierarchy/` 是重复的成因，反方向可以，改指即可。
* `Gauss.entry_bound_stochDom_floor_idx`（T107）应与 `diag_bound_stochDom_floor_idx` 并排下沉到 `Green/EntryBoundFloor.lean`。
**要定的**：并进哪张单（都要独占那两个文件）。

## D8 `Decay.norm_couplingLen_le` 的 `hD` 假设写宽了（T165）
它要求 `‖(L−K)_J‖ ≤ Φ·A^{−|J|}` 对**所有** `|J| < m`，含 `|J| = 0`；而 `L_∅ = LW`、`K_∅ = 0`，**逼出 `Φ ≥ LW`、主项直接废掉**。
耦合本身看不到这种圈（cut-and-glue 两边长度都 ≥ 2）。T165 用 `dTrunc` 绕过、**未改 `Decay.lean`**。
**要定的**：是否开一张单把 `hD` 收紧成 `2 ≤ J.length → …`（那样 `dTrunc` 那一段就能删掉）。

## D10 ⭐ 是否允许新建 `Gauss/MomentDuhamelCut.lean`（截断版矩 Duhamel 接口）（T132c）
T132c 交付了 `BootPP.step` 与 (5.48) 的化归，但**两者的余项与 `MomentHyp.step` 的替代路径都压在同一个前提上**：
**带截断的矩 Duhamel**——`χ(Ξ₂/Θ)` 在支撑上把自二次项线性化，且在前缀事件上截断与未截断的 loop 重合。
现有 `MomentDuhamel.Hyp` 没有截断版本，而 `Gauss/MomentDuhamel*.lean` 对实现 agent 是只读的。
**要定的**：(a) 新建 `Gauss/MomentDuhamelCut.lean` 作截断版接口（不动现有文件），还是 (b) 就地扩展 `Hyp`。
**附带一条已证的事实**：`MomentHyp.step` 按**冻结形状不可证**，两条阻塞都编译成了定理
（`bnd_poly` 不允许 `bnd` 带 `N` 的幂，而 `J*` 的并集界每阶要付 `L² ≍ N²`；矩层去截断的余项不小于门槛本身，
压下去要把阶数乘 `(K+δ)/δ`，流上是天文数字）。**规格本来就写的是「`step` 冻结、新增 `MomentHypCut`」，所以这不是推翻规格、是确认它。**

## D11 `hfar`：(5.48) 唯一缺的东西要不要改 `Step2.step_bound`（T132c）
(5.39)/(5.41)/(5.44) 的三个指示函数必须**带过** one-step bound，而 `Step2.step_bound` 把它们全丢了。
**要定的**：改 `Step2.step_bound`（冻结签名，需带撇版），还是在矩路线上重做一份带指示的 step bound。

## T168：Lemma 3.2 的组合模型（`Loop/CanonicalPartition.lean`，815 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9309** 条。蓝图里最后一个「引用未证」节点现在是**部分形式化**（**没有加 `\leanok`**）。

**建模步**（唯一一处，已写进文件头、`IsCanonicalTree` 与蓝图节点）：典范划分 **:=** 它的树 `Γ`——
有限带叶标树、叶子恰为 `a_0..a_{n−1}`、内点度 `≥ 3`、**每条边恰落在 `n` 条区域路径中的两条上**。
平面性条款不是随手写的：已证它等价于 **`leafSide_eq_Ico`（每条边的叶侧是循环区间）**，这也是整份文件的枢纽。

**⭐ 小规模自检：跑了，但在 Lean 外面跑的——理由充分。**
`Sep` 的判定走 Mathlib 的 `finsetWalkLength` 枚举，**实测 9 点树的无环性 `decide` 就要 85 秒**，平面性还要贵一个量级，
不能放进仓库。改为 Python 穷举（Prüfer 枚举 + 按叶标同构去重 + 平面性过滤）：

| n | 模型里的树数 | `|TSP n|` |
|---|---|---|
| 3–7 | 1, 3, 11, 45, 197 | 1, 3, 11, 45, 197 |

**完全对上**（小 Schröder 数），且 `n = 3..7` 上 Lemma 3.2 的 (1)(2)(3) 对该模型逐条成立；
Figure 4 的树算出 `F = {{1,4},{4,6}}`，与论文字面一致。**模型没有抄错。**
Lean 里留了 `RBM.figure_four`（`decide`）作为可编译的锚点。

**证了**：(0) `R_i ∩ R_j ∈ E(Γ)`（`edge_unique_of_paired`——**真正用到内点度 `≥ 3` 的地方**）、
(1) `F(Γ)` 无交叉（`crossingFree_FGamma`、`FGamma_mem_TSP`）。
支撑件：`exists_leaf_sep`（有限树的每条分支都够到一个叶标点，按分支大小强归纳）、`sep_unique_neighbor`、
`quadrant_empty`（两条不同边的劈分相容：四象限有一个空）、`interval_of_two_cycChange`。

**没证**：实现性（每个无交叉 `F*` 都是某个 `F(Γ)`）、唯一性、等价 II 与同构一致、像**恰为** `TSP n`（只证了 `⊆`）。
**所以 `Loop/Crossing.lean` 的 `TSP` 仍是定义而非定理，paper-deltas #8 不能撤。**
实现性要一个从 laminar 族到 `SimpleGraph` 的显式构造（`Loop/TreeRepGeneral.lean` 已有 laminar 编码可复用），
唯一性要劈分系统等价定理——各自独立的一大块。
**没有发现论文哪一条按字面为假**：外部穷举里 (1)(2)(3) 在 `n ≤ 7` 上全部成立。

## Cowork 对「待 Jun 定夺」D1–D8 的处理（2026-09-21 11:55）

路由类问题 Jun 已授权 Cowork 直接定（「其他类似问题都同意」）；只有**论文措辞**转给 Jun。
* **D1 (a)** 带撇版，不就地改（冻结签名纪律）——已在 **T179**。**(b) 论文 (2.72) 是否写成带增益形 → 已转 Jun。**
* **D2** 已在 **T177**（两层接口都加预算；两条反例入库，含 `L^n → L^∞` 的连续性一步）。
* **D3** 走矩路线：**T180**（`MomentDuhamel.Hyp` 的高斯生产者，含 T132b 余项：`u ↦ Kval` 的时间可微性、固定 Hermitian `M` 时 `u ↦ gloop` 的可微性）→ **T181**（时间一致的 `Lemma514′`，`0 ≤ s`）。**不回 SumZeroDyn 路线。**
* **D4 / D5** = 论文改动预算第 11 / 10 条（`J* ≤ A_u` 补半句；(5.77) 补因子或补一句）——**措辞已转 Jun**。Lean 侧不需裁定。
* **D6** **不需要裁定**：Cowork 已核原文，论文 Theorem 2.2 的 (2.10) **本来就带** `1(λ_k ∈ [−2+κ, 2−κ])`，只断言体内特征向量。Lean 的 Theorem 2.2 照此措辞。路线：**(i) 走新文件**（0 个现有签名改动，不与并行车道抢 `Cond272` 的 14 个文件）。
* **D7 / D8** 都在 **T184**（地板内核下沉 + `LKDecayQuant` 八条重复改指 + `norm_couplingLen_le` 的 `hD` 收紧带撇版）。

## ⭐ T183：`DiagBoundFlow'` 落地——**(4.2)/(4.3) 已从 `Step1.Hyp` 的假设表里彻底消失**（2026-09-21）

`lake build RBM1D` exit=0，审计 **9372** 条。纯新增 207 行于 `Gauss/EntryBoundTime.lean`（501 → 709），
`Green/*`、`Gauss/LDENetClose.lean`、`Gauss/Lemma41FlowGauss.lean`、`Gauss/Step1Hyp.lean` **一字未动**。

`diagBoundFlow_floor : DiagBoundFlow' d E s t (fun N => N^{−B})`——`DiagBoundFlow` 的控制加 `+ fl N`，其余一字未改；
三条 LDE 输入（T148 的 row/col + T166 的 quad）**零改写塞进槽位、`exact` 直接过**。

**`step1Hyp_gauss_of_scale''` 与 `step1Hyp_gauss_of_scale` 的假设表逐字相同，只是同时删掉了 `hEntry` 和 `hDiag`，没有任何东西顶替。**

### 三个余项的实情
1. **`hLdiag` 带时间版确实白送，但不是自动的**——`StochDom.of_subset` 要求同一指标类型，得用 `of_subset_union h h` 换类型。
   数学只有一行：`‖H_{u,ii}‖² = u(ω c)² ≤ (ω c)² = ‖H_{1,ii}‖²`，控制与 `u` 无关，故任意时刻的坏事件含在 `u = 1` 的坏事件里（~25 行）。
   **没有遇到 T107 在 row/col 侧撞上的那种缺口**——那边缺的是 `entry_bound_stochDom_floor_idx` 本身，这边 T166 已经交了对角版。
2. **地板吸收直接复用 T107 的 `stochDom_indicator_add_const`，没写第二条**；`B := 1` 够用。
3. `hδ` 不是新负担。

**一处形状差异（不是新假设）**：(4.3) 的确定性内核带 `Kstab κ`，故 `diagBoundFlow_floor` 收的是 `0 < κ ≤ 1` + `|E| ≤ 2−κ`
而非 `entryBoundFlow_floor` 的 `|E| < 2`。**在 `Step1.Hyp` 层面代价为零**（`step1Hyp_gauss_of_scale` 本来就带这两条，内部用 `min κ 1` 封顶）。**不构成 paper-delta。**

**四条 `rfl` 探针全过**（`have : h_unprimed = h_primed := rfl`，编译验证不是目测），
覆盖 `stochDom_indicator_diag_flow`、`llMax_sq_flow`、`lemma41Flow`、`step1Hyp_gauss_of_scale`(′/″)。

## ⭐ T180：`MomentDuhamel.Hyp` 的生产者——六个字段里四个已产（`Gauss/MomentDuhamelHyp.lean`，633 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9409** 条。产出 `hypOfMoments`（一般 `Band`）与 `gaussHypOfMoments`（高斯，连 `integrable` 都不用给）。

| 字段 | 状态 |
|---|---|
| `F` | **已产**，钉死为 `DriftDef.driftF`（`hypOfMoments_F` 以 `rfl` 闭合） |
| `drift` | **已产**——**工单说它是唯一障碍，这条现在不成立了**：T163 + T58 之后 `drift` 是免费的（`drift_split_gen` + 窗口 `[0,1)` 卸掉 `hz`/`hm`） |
| `cMD`/`cMD_nonneg` | 已产（唯一自由度，类型 `ℕ → ℝ` **禁止依赖 `N`**，且同一个 `cMD p` 也出现在消费者的 `hrhs` 里——**闭合的一对**） |
| `integrable` | **已产**（高斯，经 T132b 的 `integrable_lkT_pow`） |
| `momentDuhamel` / `momentDuhamelQ` | **未产**，已归约成一句关于 `ψ'` 的话，见下 |

**收口那一半做完了**：`momNorm_le_of_integral_le`（T132a 的 `sqrt_le_of_integral_le` 代入 `ψ = (E|Y|^{2p})^{1/p}`）、
两个字段的本体、以及 `momentIneq_of_diffIneq`（**整条 `MomentIneq` 由逐点的 `hdu` 推出**）。
**常数定死了**：生成元给 `ψ' ≤ 2√ψ·‖U∘F‖_{2p} + (2p−1)·‖(U⊗U)∘(E⊗E)‖_p`，故 **`cMD p = 2p−1`**，
与字段里 `momNorm B.P p`（不是 `2p`）的指数正好对上（Hölder 共轭指数是 `p`）。

### ⚠ 查到一处过度量化（按要求报告而不是绕开）→ 见「待 Jun 定夺」D9
`hdu` 要用 T132b 的 `hasDerivAt_integral_Psi_pairs`，它要求 `TestFunT`；而 `Ψ(u,M) = |(U_{u,v}∘(L−K)(u,M))_a|^{2p}` **不在那个类里**：
① `bdd₀/₁/₂` 对**所有**矩阵量化，而 `(M − z_u)⁻¹` 在非 Hermitian `M` 上无界；
② `TestFunT.slice` 要**全局** `ContDiff ℝ 2`，而在奇异的非 Hermitian `M` 处 `Ψ` 连连续都不是（Lean 的 `Ring.inverse` 在那儿是 `0`）。
**在 Hermitian 集上两条都成立**，而整个论证本来就待在那里（流是 Hermitian，流值之间的线段也是）。

### 可满足性检查（逐字段，都是编译过的）
* **`drift` 在 `[s_N,t_N] ⊆ [0,1)` 上成立，含 `u = 0`**——**这里没有 T152 的 `0 < u` 接缝**：
  导数是对**冻结矩阵** `M` 的 `v ↦ gloop(M,z_v)` 与 `v ↦ K_v`，**`√u` 根本不出现**。`u = 1` 处不可满足，这正是论文的 `t_N < 1`。
* `MomentIneq`/`MomentIneqQ` 在**退化点 `v = s_N`** 取等号成立（两个时间积分为 0、`U_{s,s} = 1`）——字段在窗口塌缩处不是恒假。
* **`F` 根本不是接口的自由度**：`F_eq_driftF_of_window` 证了**任何** `Hyp`（不止这里造的）在 `[0,1)` 上都有 `F = driftF`。

**另记两处会被重新踩的接缝**：`hasDerivAt_integral_Psi` 带 `0 < u`，故 `hdu` 只能由**开区间**导数 + 连续性得到（同 T161/T173）；
T72 的 `genMomentPt_le` 同样要全局 `ContDiff ℝ 2`。

## ⭐ T177：基数预算 `#ι ≤ n` —— 两层接口都修了，(4.12) 到 `Eq45Flow` 打通（2026-09-21）

`lake build RBM1D` exit=0、`errors: 0`，审计 **9410** 条（9309 → 9410），全部落在
`propext / Classical.choice / Quot.sound`。动了三个文件：`Gauss/FlucIter.lean`（+~200 行）、
`Gauss/FlucIterHigh.lean`（+~70 行）、`Gauss/MinorDiffCond.lean`（726 → 1421 行）。
**`Gauss/CondStableFlow.lean` 与 `Gauss/Eq45FlowInputs.lean` 一个字没动**（只读），`Gauss/MinorDiffGain.lean` 也没动。

### 先把「不可满足」这件事入库（此前只在探针里）
两条反例现在是仓库里的编译定理，并排放着，差别一眼可见：

| 接口 | 定理 | 结论 |
|---|---|---|
| `FlucGainUpTo`（无预算，**活路径上**） | `integral_pow_norm_flucDiag_le_of_flucGainUpTo` | `∫‖Z_k‖^j ≤ B^j` 对**每个** `j`（T176 探针 P5 入库） |
| `MinorDiffGainUpTo`（无预算） | `integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo` | 同上（T171 已有） |
| `FlucGainUpTo'`（带预算） | `integral_pow_norm_flucDiag_le_of_flucGainUpTo'` | 只对 `j ≤ n` |
| `MinorDiffGainUpTo'`（带预算） | `integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo'` | 只对 `j ≤ n` |

⚠ **`‖Z_k‖_∞ ≥ 64/65` 与 `L^n → L^∞` 那一步仍未入库**（T176 的「声明的盲区」照旧）：
本单把**推出 `B ≥ ‖Z_k‖_{L^j}`（∀j）**这一半编译了，**没有**补 T172 的两点反例与连续性。
所以「旧接口不可满足」严格说是「旧接口 + T172（未入库）不可满足」。

### 预算的形状与「`#ι ≤ 2p` 本来就成立」的核查（load-bearing，已查）
`FlucGainUpTo' … (M n : ℕ)`：`M` 管字长，`n` 管 `#ι`。核查结论：
**整条链里接口只被用了一次**，在 `norm_integral_prod_epsHom_flucDiag_le_budget`
（`FlucIter.lean:2470`）处，`ι = Fin p ⊕ Fin p`、`Fintype.card = 2p`。
再往下的 `norm_integral_prod_qRow_le_graded` / `norm_integral_prod_applyOps_le_graded`
收的是**已经把 `ι` 固定好的** `hgain`，不再碰接口，所以它们**一个字都不用改**。
于是 `M = n = 2p`，与 `OpsOkOut.length_le` 同源，**确认不损失任何东西**。

### 余项吸收（T171 写下的算术，现在是定理）
`minorDiffGainUpTo'_of_le_on`：`B₀ := 2·minorDiffC M·Ψ + condCost`，
`#ι ≤ n`、`∑q ≤ #ι·M ≤ nM`、`B₀ ≤ 1`、`2Ψ ≤ 1`、`1 ≤ condEnv`（新证 `one_le_condEnv`）时
`condEnv^{#ι}P(Bad) ≤ condEnv^n P(Bad) ≤ B₀^n(2Ψ)^{nM} ≤ B₀^{#ι}(2Ψ)^{∑q}`，
加回主项付一个 `2 ≤ 2^{#ι}`，得 `B = 2B₀`、**增益 `ρ = 2Ψ` 一点没退化**。
⚠ **`#ι = 0` 必须单独走**：那一档余项形式给的是 `1 + P(Bad) ≤ 1`，**为假**；
实际结论是空积的 `∫1 = 1 ≤ 1`（用 `P d` 是概率测度）。这一步不是形式主义，是真的会塌。

### 可满足性检查（两个，都跑了）
1. **退化检查重跑（负向）**：在 scratchpad 里把 T171 的 `ι = Fin j`、空词脚本原样喂给
   `FlucGainUpTo'`，剩下的目标就是 `Fintype.card (Fin j) ≤ n`，即 `j ≤ n`，**无法证**。
   这正是此前推出 `B ≥ ‖Z_k‖_∞` 的那一步，现在被预算挡住了。
2. **数值束的正向见证**（仿 T167）：`minorDiffGain_budget_hyps_consistent`（已编译）——
   对任意 `E,t`（`|E|<2`、`t<1`）与任意预算 `M,n`，给出显式的
   `Ψ = (8(minorDiffC M + 1))⁻¹ > 0`、`ε = condEps E t M Ψ > 0`、`pBad > 0`（且 `≤ 1`），
   使 `2Ψ ≤ 1`、`B₀ ≤ 1`、`hsmall` **同时成立**，并且 `B = 2(2 minorDiffC M + 1)·Ψ`，即 `B ≍ Ψ`。
   `pBad` **严格正**，所以不是「例外集测度为 0」那种平凡见证。

### 上层也修了，而且没动只读文件
`eq45Flow_of_localLaw_gain'`（`CondStableFlow.lean:1246`）吃的 `FlucGainUpTo` 没法就地换，
于是在 `MinorDiffCond.lean` 里把 `Eq45FlowInputs` 的那条链**按预算版重建**了一遍
（`unifDomIcc_flucAvg_iter_budget` → `…_blockAvg_/_Sblk_` → `…_condExpDiag_psi_budget` →
`eq45Flow_of_localLaw_gain_budget`，全部**结论逐字等同**旧版，假设表只差 `FlucGainUpTo → FlucGainUpTo'`），
收口仍然调用只读文件里的 `eq45Flow_of_unifDom_ibp`。代价是 `MinorDiffCond.lean` 多 import 了
`Gauss/CondStableFlow.lean`（无环，已验证）。

**端到端**：`eq45Flow_of_goodSetFlow_budget` 从 `goodSetFlow`（= (4.1)）走到 `StepGlue.Eq45Flow`，
`hg` 是**现场产出**的（`flucGainUpTo'_goodSetFlow`），**假设表里没有任何对所有 `ω` 量化的好事件假设**。
尺寸是论文的：`Ψ_N = 2δ_N`、`ρ = 2Ψ_N`、`B_p = 2(2 minorDiffC(2p)+1)Ψ_N = Kp p·Ψ_N`，控制 `ρB ≍ Ψ²`。

### 还欠的一步（如实，**不要当成已完成**）
`hsmall`（`condEnv^n·P(badTower) ≤ B₀^n(2Ψ)^{nM}`）**目前是端到端定理的一条假设**，
没有从 `HighProb (goodSetFlow)` 推出来。要补的是纯记账但不平凡：
`meas_badTower_le` 是 `ℝ≥0∞` 里的 `ε^{M+1}P(Bad_{M+1}) ≤ (ε+#Idx)^{M+1}P(Bad_0)`，
要 (a) 转成实数、(b) 把 `condEnv ≤ N^{C}`、`condEps ≥ N^{-C'}`、`δ_N ≥ N^{-c}` 这些区制界接上、
(c) 用 `HighProb` 的「对每个 `D`」吃掉多项式因子。**数学上没有悬念**（`P(Ω(t,c)ᶜ)` 超多项式小），
但需要 100–200 行 rpow/ENNReal 的活，本单没做。

### 旧声明的处置
`FlucGainUpTo`/`MinorDiffGainUpTo` 及其全部消费者**一字未动**，`FlucGainUpTo.budget` /
`MinorDiffGainUpTo.budget` 把旧的（更强的）推到新的，所以已有的供给（`FlucGain.upTo` 一路）不丢。
文件头已注明旧接口在 `B ≍ Ψ` 前提下不可满足，**不要再拿它当假设**。
paper-deltas 记 `T177a`（临时号）→ **Cowork 已分配 #126**。

## Jun 裁定（2026-09-21 12:10）：D1(b) 选 (a)；论文改动预算第 9–12 条措辞 OK

* **D1(b) → (a)**：**论文 (2.72) 陈述不改**；在 Step 2 的 (5.41) 处补一句「先用 (2.73) 把 `(1+J*A^{−1})` 因子去掉（降到 `J*` 一次）」，于是所有项 `β* < 30` 严格成立、裸 (2.72) 就够（论文改动预算第 14 条）。
* **Lean 侧后果**：Lean 的 `Thm221` 最好也收**裸** `Cond272`，与论文逐字一致——由 `Cond272`（`R^{30} ≤ A_t`）+ 区制自带的 `N^c ≤ A_t` 推出带增益、**指数略小于 30** 的 `hregS_β`（`β < 30`），前提是全链 `β* ≤ β`（T132c 走 shape 2 后最大约 17.5–28.5）。T179 的网格增益路线照做（它给出 `Thm221′`、零新数学、先打通总装）；**字面版另开 T186**，在 T132c 落地后做。
* **第 9–12 条**（(5.51) 下标、(5.77) 补因子、(5.35) 补 `J* ≤ A_u`、(5.36) 证明里「by symmetry」的指代）：措辞 Jun 已 OK。

## Cowork 对 D9 的处理（2026-09-21 12:30）

**选 (i)**：`TestFun`/`TestFunT` 加带撇版，把 `∀ M` 放松到 `∀ M, M.IsHermitian →`（与 T145 对 `Hyp.drift` 的修补同型），控制收敛在流上重证；**不走截断 (ii)**——`Hyp.momentDuhamel` 是结构性不等式，不需要截断给的尺寸估计。开 **T187**。路由类决定，Jun 已授权，不转 Jun。
**T179 验收**：`Thm221′` 已通（`c = min(τ,1)/32` 取自 (2.2)，增益上界约 `τ/16`，故 `c` 量化在 `step` 内）；D1 的 Lean 侧已无需裁定，论文侧 Jun 已选 (a)（(5.41) 补一句），字面版由 T186 收回。

## T184：过时消费者已按编译器级护栏退役 + 地板内核归位（2026-09-21）

`lake build RBM1D` exit=0，审计 **9401** 条（9410 − 删除的 8 条；移动不改数）。

### ⭐ 新增项（最重要的一条）：`eq45Flow_of_localLaw_gain(')` 退役
**grep 结论：Lean 代码里没有任何声明依赖它**（八处全是 docstring 文本）。但 `content.tex:2295` 的 `\lean{}` 列了这两个名字，
而蓝图对该 agent 只读，**删声明会让节点指向不存在的名字**，所以保留 + 钉死。

**做法值得推广：加 `@[deprecated "RETIRED (T184): …" (since := "2026-09-21")]`**——
**这是编译器级护栏，不只是文字**：将来谁再把它当入口，`lake build` 会直接打出带替代者名字的警告。
**docstring 挡不住下一个 agent，`MinorGood` 那次就是证据。**
docstring 同时写清：`hg` 槽要的正是 `B ≍ Ψ`；已编译的证据链（T176 探针 P5 + T171 的低层孪生）；
**并诚实标出唯一未入库的一步是 `L^j → L^∞` 的极限**；以及替代者 `eq45Flow_of_localLaw_gain_budget`/`eq45Flow_of_goodSetFlow_budget`。
不带撇的那条**一并退役**（它吃 `FlucGain`，经 `FlucGain.upTo` 落进同一堵墙，a fortiori）。

⚠ **还有两个消费者没动**：`Eq45FlowInputs.lean` 的 `unifDomIcc_flucRow/flucBlk_condExpDiag_psi` 是 `gain'` 的直接喂料，
**同样站在 `FlucGainUpTo` + `Bp ≤ Kp·Ψ` 上，而该文件没有任何不可满足性警告**——在只读清单里，**留作后续工单**。

### 地板内核归位
`entry_bound_stochDom_floor_idx` 下沉到 `Green/EntryBoundFloor.lean`，紧挨 `diag_bound_stochDom_floor_idx`（两者是 (4.2)/(4.3) 的两半），
**证明一字未改**；旧名以 `export` 保留，`rfl` 探针验过是**同一个常量**。

### `LKDecayQuant` 的八条重复：删除改指
加 `import RBM1D.Green.EntryBoundFloor`（`Hierarchy → Green`，无环），**删掉整个 `section EntryFloor` 与 `BlkFloor` 里的一条**，共 8 条；
删前逐条比对过**语句与证明逐字相同**，八个公开名全部 `export` 保留，**8 条 `rfl` 探针**确认是同一常量。
下游的 `norm_sq_green_le_of_far_floor`/`loopDecay_gloop_of_event_floor`/`lemma59_floor`/整个 `Flow'` 节**一字未动**。

**工单第 (3) 项未做**：`Decay.norm_couplingLen_le` 的 `hD` 带撇版要改 `Hierarchy/Decay.lean`，不在该 agent 的可写清单里（= STATUS 的 D8）。

## ⭐ T182：Step 6 的 `hH`/`hFD`/`h5133` 全部卸掉——**但 T152 的单张量归约被推翻**（`Gauss/Step6DriftSplit.lean`，963 行，2026-09-21）

> **⚠ 后续更正（T189，2026-09-21）**：本节把短掉的 `A^{−1}` 全部归因于「期望里的抵消」——**归因要修正**：两半**各**多出一个 `A^{−1}`，理由不同。`K` 半靠 (5.126) `E⟨(G−m)E_a⟩ ≺ A^{−2}`（逐路径只有 `A^{−1}`），**这半才是期望里的抵消**；`L−K` 半是**纯逐路径**的，它的 `A^{−1}` 来自「3-loop 取 `L−K` 而不是 `L`」（(2.78) 给 `(L−K)_3 ≺ A^{−3}`，而 (2.77) 的 `L_3` 只有 `A^{−2}`）——**(5.77) 第 3 行短一个 `A`，正因为它把 3-loop 取成了 `L`**。

`lake build RBM1D` exit=0，审计 **9422** 条。`Step6HierarchyGauss.lean` 与四个只读文件**一字未动**。

### ⚠⚠ 核心发现：**T152 的「拆成 `DLK`/`DG` 在 Lean 里毫无代价可省」对恒等式成立，对 size estimate 不成立**
`driftBound_of_5133` 与 `driftBound_of_5134` 给出同一个界不假，**但证法不同**；单张量把两半绑死之后，
**`eG` 那半在逐路径意义下比 (5.133) 恰好弱一个因子 `A = Wℓ_uη_u`**，而那个因子**只能从期望里的抵消**（论文 (5.134)）拿回来。
逐路径拿不回来的理由是完整的：`Ξ^{(L)}_{u,3} ≲ 1`（(2.59)+(5.76)）与 `Ξ^{(L−K)}_{u,1} ≲ 1`（(2.68)，即 #119）**都已经用掉了**。

**所以本单把漂移按论文拆回两个张量，两者都是 `def`**：`driftELK = E[primBil(L−K,L−K)]`、`driftEG = E[E^{(G)}]`，
`driftE = driftELK + driftEG` 是**定理**（`driftE_eq_driftELK_add_driftEG`）。消费者改用**双张量的 `Step6.sharpExpect_step6`**
（它本来就收 (5.134) 作 `hG`），不再走 `sharpExpect_step6_single`。
**⚠ STATUS 的 T152 节与 T173 节据此加注，否则后来人会照着单张量再撞一次那个 `A^{−1}`。**

### 另一处对 T165 的更正
比 (5.77) 通用形状 `A^{−(n+2)}` 多出来的那个 `A^{−1}` **就长在 `Φ` 自己身上**（`Φ = Ξ_2·Ξ_2·A⁻¹`），不是变出来的。
**`DriftBound.norm_driftF_le` 把三行并进一个 `cDrift` 时把它丢了**，所以那条界对 (5.133) 恰好弱一个 `A`。

### 落地
`norm_primBil_lkPath_le`（**(5.77) 第 2 行在 `n = 0` 处直接写成 (5.133) 的形状**）、
`norm_integral_le_add_measure_compl`（好集外一阶矩记账，**不要求好集可测**，用 `toMeasurable` 的补绕过）、
**`unifDetDom_driftELK`（(5.133) 落地）**、`fastDecay_integral_of_highProb`（**好集版**——T173 的版本要求对**每个** `ω` 成立，Lemma 5.9 给不出）、
**`fastDecayHyp_driftSplit`（`hFD`）**、**`hierarchy_driftSplit`（`hH`，仍只用 `_Ioo`）**、
**`sharpExpect_step6_driftSplit`（(2.80)，`hH`/`hFD`/`h5133` 全部卸掉）**。
`hlow` **从假设变成了定理**（`eventually_rpow_neg_three_le_drift_target`，`Blow = 3`）——**T165 的同名假设至此也有了产出者**。
工单建议的 `eGpm_le_reduced`/`norm_eLL_le` 两条路线**没用上**：`Decay` 的逐项界在 `n = 0` 处直接给出 (5.133) 的形状，更短。

### 剩下什么、归谁（全部不提漂移）
1. **`hG` = (5.134)**——**唯一还约束 `E E^{(G)}` 的假设**，本就是 `Step6.sharpExpect_step6` 的字段、不是本单新增的债。
   ⚠ **但它与 T152 的 `hG_zero_right` 性质不同**：那里 `DG = 0` 可自由取所以空洞，**这里 `driftEG` 已钉死，`hG` 是真约束**。目前无人认领。
2. `hin59`/`hinQ`——Lemma 5.9 的衰减 + (5.76) 的计数，与 T165 的 `DriftInputs` **同源**。
3. `henvQ`/`henvG`/`hEnvpoly`/`hmeasQ`/`hmeasG`——与 `DriftBound.hFmom_of_driftInputs` 的 `henv`/`hEnvpoly`/`hmeas` **完全同形**，归包络那条线。
4. `hEL` 已可产（T176 探针 P6）；`hcont`/`hintU` 是 T176 自列的盲区。

**fiat 审计**：两个张量都是 `def`、无结构字段、无自由张量变量；**没有为了让 (5.133) 出来去调整任何定义**，短的那个因子如实报告。
全程未实例化 `SumZeroDyn.Hierarchy`、未用 `Lemma510` 任何字段、只用 `_Ioo` 版。

## T178：`h572` 卸掉；**`h566` 的机器全部落地但假设不可卸——一条精确的否定发现**（2026-09-21）

两文件 `lake env lean` 均 exit=0。

**`h572` 落地**（`Lemma57.lean` 新 `section Loop6` + `EEDef` 的 `eeL6k_two_{zero,one}_le_glue`）。
**一处对论文的修正**：(5.72) 论文写 `max_{y∈I_b}|G_{x₁y}||G_{x₁'y}|`，**诚实的指标序是 `|G_{yx₁}||G_{yx₁'}|`**
——复 Hermitian `H` 的 `G(z)` **不对称**。记 paper-deltas #113 ⑦。

**`h566` 的机器全部落地**：`gloop_six_eq_trace`（(5.65) 的开环）、`norm_chain_four_apply_le`、
`trace_Eblk_glue_eq_gloop_four`（`G(σ)E_bG(−σ)` 的块平方质量 **= 4-loop**，正是 (5.66) 里那个 `max`）、
`sum_blkW_mul_le_sqrt`（**块权是概率权，论文 `W^{−2}·W·(W²L)^{1/2}` 的 `W` 计数自动消掉**）、收口 `norm_gloop_six_le_schwarz`。
`glueIdx_two_{zero,one}` 把 (5.23) 在 `n = 0` 算成显式 6-loop（一次 `simp` 就过，证实了手算），
**两个 `k` 的右端肉眼可见地不同**：碰到黏合标号 `b'` 的那两条 `G` 边，`k=1` 接 `a₂`、`k=0` 接 `a₁`。

### ⚠ 否定发现：`h566` 与 `hsym` 不是两条独立假设
`eeL6` 按定义是 `∑_{k ∈ range m}`，而 `h566` 的右端是 **`k=1` 的形状**。在 `case2a_pointwise` 真正用它的区制里
（`‖a₁−b‖ ≤ ℓ*_u` 且 `‖a₁−a₂‖ ≥ 4ℓ*_u`），`Gsq b a₂` 被 `h42sq` 压小，而 **`k=0` 项带的 `Gsq b a₁` 完全没有衰减**
（`b` 就在 `a₁` 的 `ℓ*_u` 邻域里，只有 `≺ (ℓ_u/ℓ_s)A_u^{−1}`）。过完 `Wℓ*_u ∑_b` 后 `k=0` 项给出 `η_u^{−1}(J*)²T²`，
**比 (5.36) 的 `η_u^{−1}A_u^{−1/2}(J*)³T²` 差整整 `A^{1/2}`**。
**所以 `k=0` 项正是 `hsym` 管的那一半，换个方向看。** 这**没有推翻 #113 ②**，而是把它的 `k` 依赖在 Lean 里变成了可见的两条并列定理。
**要卸 `h566`，需要的正是 `hsym` 需要的那个 `k`-拆分。**
对照之下 **`h572` 的形状是对称的**（那里黏合因子自己也带尾函数），所以可卸——前提是调用方的 `Gsq` 取 (4.2) 的等号。

### 造轮子检查（照规矩先搜了一遍，三处命中）
* `RBM.sum_norm_SB_row` 已在 `Loop/KBound.lean:2321` 且可见——**删掉了新写的那条，改用已有的**。
* `RBM.mul_Eblk_mul_apply` 已在 `Loop/ChainExpand.lean:1262`，但 `Lemma57` **不能 import 它**（会拖进 `Green/Minor`，方向不对），故新条改名 `mul_Eblk_mul_apply_ite` 并注明。
* `Gauss.sq_sum_weighted_le` 从 `Lemma57` **不可见**（已编译验证），只好重写 4 行，docstring 注明是同一个轮子。
* 顺带发现既有重复（未动）：`Lemma57.blkW` 与 `ChainExpand.eblkW` 是同一个块权。

## ⭐ T188：`hsmall` 已由高概率推出；顺带修掉 T177 端到端定理的**空真**（`Gauss/Eq45Small.lean`，新文件，2026-09-21）

`lake build RBM1D` **exit=0**，`RBM1D.lean:159` 审计 **9475** 条全在
`[propext, Classical.choice, Quot.sound]` 内。**只读文件（`CondDom` / `FlucIter*` /
`CondStableFlow` / `Eq45FlowInputs`）一个字没动**；改动只在 `Gauss/MinorDiffCond.lean`
（量词放宽）、新文件 `Gauss/Eq45Small.lean`、以及 `RBM1D.lean` 加一行 import。

### 1. `hsmall` 现在是定理

`RBM.Gauss.hsmall_of_highProb`（及一般预算版 `..._aux`）把 T177 留下的
`condEnv^n · P(badTower) ≤ B₀^n (2Ψ)^{nM}` 从假设变成结论，**唯一的概率输入是 (4.1) 本身**
（`HighProb (P d) (goodSetFlow …)`）。端到端定理
`RBM.Gauss.eq45Flow_of_goodSetFlow_highProb` 的假设表里**没有 `hsmall`**。

**实际用到的区制界只有两条，而且两条原本就是该定理的假设**——没有新增任何前提：

| 需要的界 | 由哪条现成假设给出 | 桥 |
|---|---|---|
| `δ_N ≥ N^{-(2K+6)}`（`Ψ = 2δ` 不是超多项式小） | `hδnet` | `polyLo_of_one_div_rpow_le` |
| `η_{t_N}⁻¹ + 1 ≤ N^{Kenv}` | `hEnv`（`(η⁻¹+1)^2 ≤ N^{Kenv}`，配 `η⁻¹+1 ≥ 1`） | `polyHi_of_sq_le` |
| `#rows ≤ N` | `Dims.dim` | 既有的 `card_Idx_le` |
| `u` 一致性（`u ∈ [s_N,t_N]`） | `η` 关于时间反单调 | 既有的 `etaT_le_of_le` |

记账工具是两条一行谓词 `PolyLo f`（`∃C>0 ∃D, ∀ᶠN, C·N^{-D} ≤ f N`）与 `PolyHi f`，
加上乘/幂/和/逆/商/单调的闭包引理，和**唯一用到 `HighProb` 的那一条**
`measureReal_compl_le_of_polyLo`：高概率事件的补集最终被**任何** `PolyLo` 函数压住
（`∀ D` 量词就花在这里，`ℝ≥0∞ → ℝ` 的转换因为 `P d` 是概率测度而免费）。
**这两条谓词是通用轮子**，若出现第二个消费者应下沉到 `RBM1D/Defs/`。

`#ι = 0` 不需要特判：`M = n = 2p`，`p = 0` 时包络幂为 `1`、目标为 `1`，一般论证照走
（T177 提醒的那个「`1 + P(Bad) ≤ 1`」是 `minorDiffGainUpTo'_of_le_on` 内部的事，早已分情况）。

### 2. ⚠⚠ 顺带查出：T177 的端到端定理原本是**空真**的

按工单要求查可满足性时发现，`eq45Flow_of_goodSetFlow_budget` 的两条 `p`-指标假设

```
hMδ : ∀ p N, 8 * (2p) * δ N ≤ 1
hδC : ∀ p N, 2 * minorDiffC (2p) * (2 δ N) + 2 δ N ≤ 1
```

与 `hδpos : ∀ N, 0 < δ N` **不可满足**：固定 `N`，左边关于 `p` 无界
（`minorDiffC (2p) = 4^{2p} atomC(2p)^3` 更快）。论文的量词次序是另一个：**`p` 固定、`N → ∞`、
`δ_N → 0`**。已把 `hg` / `hsmall` / `hMδ` / `hδC` 四条统一改成 `∀ p, ∀ᶠ N in atTop, …`
（**假设变弱 ⇒ 定理变强**，结论一字未改），并在 `MinorDiffCond.lean` 里顺着 `hg` 的消费链
把 `unifDomIcc_flucAvg_iter_budget` 的 `filter_upwards` 多收一项，其余四处只改签名。

正反两向都入库：
* **反向** `not_forall_mul_le_one`：`0 < δ N → ¬ ∀ p, 8(2p) δ_N ≤ 1`。
* **正向** `eq45Flow_delta_hyps_consistent`：显式 `s = t = 0`、`δ_N = (N+4)^{-28}`、`K = 12`
  （净化指数 `(K+2+1)/(1/2) = 30`），使 `hδpos`/`hδ4`/`hδnet`/`hfine`/`hMδ`/`hδC` 同时成立。
  **这里真正要验的是 `hδnet`（下界）与 `hfine`（上界，逼 `δ_N ≤ η⁶/(16N⁶)`）打不打架**：
  它们相容**只因为 `K` 自由**——`K = 0` 时净化条件要 `η⁶ ≥ 16`，而 `η ≤ 1`，无解。

### 3. P1 的 (4.5) 槽已经换掉

探针（scratchpad，未入库）`steps45_glue_no_eq45Flow`：`Step2PP.flow_steps45_glue_flowAs`
在 `X = sample d` 上，`h45 : StepGlue.Eq45Flow` **从假设表里消失**，现场由
`eq45Flow_of_goodSetFlow_highProb` 产出；`#print axioms` 干净。
（六步链里 `Eq45Flow` 只出现在 `flow_steps45_glue{,'}` / `flow_steps45_glue_flowAs{,'}` 这一处，
`sharpExpect_step6_driftE` 不收它，所以这就是 STATUS「T176 假设 #6」的全部。）

### 还欠的一件（工单的可选项 (4)，没做）

`‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步仍未入库——它需要 `ω ↦ Z_k(ω)` 的连续性，
T171/T172/T177 都没写出这一步。它只影响「旧接口不可满足」这一结论的**完整性**，
不在任何活路径上（活路径已全部改吃带预算的接口）。

**蓝图**：这一簇（T171/T177/T188 的 `MinorDiffCond` + `Eq45Small`）在
`blueprint/src/content.tex` 里**没有对应节点**（T171/T177 当时也没加），
新声明因此无处挂 `\lean{}`。补节点需要给它一个与论文编号对应的名字，属于范围决定，留给 Cowork。

## ⚠⚠ T188 的附带发现：T177 的端到端定理**原本是空真的**（2026-09-21）

按「先查可满足性」的规矩查时发现，`eq45Flow_of_goodSetFlow_budget` 的
`hMδ : ∀ p N, 8(2p)·δ_N ≤ 1` 与 `hδC : ∀ p N, 2·minorDiffC(2p)·(2δ_N) + 2δ_N ≤ 1`
配 `hδpos : ∀ N, 0 < δ N` **不可满足**——固定 `N`、令 `p → ∞` 即破（`minorDiffC(2p) = 4^{2p}·atomC(2p)³` 破得更快）。
**论文的量词次序是「`p` 固定、`N → ∞`、`δ_N → 0`」，而 Lean 写成了对 `p` 与 `N` 同时全称。**

**已修**：`hg`/`hsmall`/`hMδ`/`hδC` 四条统一改成 `∀ p, ∀ᶠ N in atTop, …`——**假设变弱 ⇒ 定理变强，结论一字未改**；
`MinorDiffCond.lean` 只改 5 处签名 + 一行 `filter_upwards`。
**正反两向都入库**：反向 `not_forall_mul_le_one`；正向 `eq45Flow_delta_hyps_consistent`（显式 `δ_N = (N+4)^{−28}`、`K = 12`）。
**真正要验的是 `hδnet`（下界）与 `hfine`（上界，逼 `δ_N ≤ η⁶/(16N⁶)`）打不打架：它们相容只因为 `K` 自由**
——`K = 0` 时净化条件要 `η⁶ ≥ 16` 而 `η ≤ 1`，无解。

**这是今天第六次同类事故**（T145、T132b、T154、T164/T172、T180，现在 T177）。
前五次是「对所有矩阵/所有样本点过度量化」，**这次是量词次序**——形式不同，症状相同：
**假设不可满足 ⇒ 定理空真 ⇒ 编译器永远不报。**

## T188：`hsmall` 已由 (4.1) 推出，(4.5) 槽在六步探针里消失（`Gauss/Eq45Small.lean`，706 行）

`lake build RBM1D` exit=0。`hsmall_of_highProb` 把 T177 留下的假设变成结论，**唯一的概率输入是 (4.1) 本身**；
`eq45Flow_of_goodSetFlow_highProb` 端到端 (4.1) → `StepGlue.Eq45Flow`，**假设表里没有 `hsmall`**。

**没有新增任何假设**——四条区制界全部来自**原本就在的** `hδnet`/`hEnv`/`Dims.dim`/`etaT_le_of_le`。
记账工具是两条一行谓词 `PolyLo`/`PolyHi` 加闭包引理；**`HighProb` 只在一处用到**
（`measureReal_compl_le_of_polyLo`：高概率事件的补集最终被**任何** `PolyLo` 函数压住，`∀ D` 量词花在这里）。
**若出现第二个消费者，这两条通用轮子应下沉 `Defs/`。**

**接进六步探针**：`flow_steps45_glue_flowAs` 的 `h45` 从假设表里消失、现场产出。
**六步链里 `Eq45Flow` 只出现在 `flow_steps45_glue{,'}`/`..._flowAs{,'}` 这一处**（`sharpExpect_step6_driftE` 不收它），
所以这就是 T176 清单第 6 条的全部。

**未做**：`‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步仍未入库（需 `ω ↦ Z_k(ω)` 连续性），
它只影响「旧接口不可满足」这一结论的完整性，**不在活路径上**。
⚠ **蓝图缺节点**：T171/T177/T188 这一簇在 `content.tex` 里**没有对应节点**，新声明无处挂 `\lean{}`；
补节点要给它一个与论文编号对应的名字，属范围决定，留给 Cowork。

## ⭐ T187：`TestFun'`/`TestFunT'`（只对 Hermitian 量化）落地 —— D9 的 (i) 已实现；两条 `Hyp` 字段**没有**闭合（`Gauss/TestFunHerm.lean`，756 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9561** 条。新增文件 `RBM1D/Gauss/TestFunHerm.lean`（50 条声明），
`Gauss/MomentDuhamelHyp.lean` 只改 import + 文件头（把 D9 的「两条路」段落换成结论与余项清单）。
**`TestFun`/`TestFunT` 一字未改**，`Generator.lean`、`MomentDuhamelGauss.lean` 一字未动。

### 产出
* `TestFun'`/`TestFunT'`：`∀ M` → `∀ M, M.IsHermitian →`，`ContDiff` → 该点 `ContDiffAt`；
  `TestFun.toTestFun'`/`TestFunT.toTestFunT'` 把旧类装进新类（**已有供给全部继续可用**）。
* **桥**：`TestFun'.herm`/`TestFunT'.herm` —— 带撇类的 `hermFun`（`Φ ∘ hermCLM`）正则化是**货真价实的旧类**，常数相同。
  于是四条生成元恒等式（`hasDerivAt_integral_Phi′/_pairs′`、`…_Psi′/_pairs′`）是旧恒等式的**推论**，
  **控制收敛一个字都没有重证**（工单预期的「大头」不存在）。结论逐字不变，讲的是 `Φ`/`Ψ` 本身。
* 支撑件：`fderiv_comp_clm_apply`/`fderiv2_comp_clm_apply`（任意 CLM 复合的一、二阶导）+ 算子范数版
  `norm_fderiv{,2}_comp_clm_le`；`coordD1/coordD2/wirtSecond/genD/quadVar/genMomentPt` 在 Hermitian 点
  对 `hermFun` 不变。**这正是 `Generator.lean` 里「The Hermitian projection」那段只写了散文、没有证的断言。**
* **T180 记的第二条接缝已闭合**：`genMomentPt_le'`（T72 的逐点界，假设降成「每个 Hermitian 点 `ContDiffAt`」，
  结论在 Hermitian 点）。第一条（`hasDerivAt_integral_Psi` 带 `0 < u`）照旧。

### ⚠ 比 D9 想的更细的一条（本单最重要的发现）
**带撇类对"原始"（未正则化）的 `Ψ` 仍然给不出来。** `TestFun'.bdd₁/₂` 要的是**全方向**算子范数
`‖fderiv Φ M‖`（M Hermitian，方向任意），而正则化只给 `‖fderiv (Φ∘hermCLM) M‖ = ‖fderiv Φ M ∘ P‖`，
**反方向不成立**（反 Hermitian 方向被投影杀掉）。原始 `Ψ` 的这些界**数学上是真的**（都是 `‖G‖ ≤ |Im z|⁻¹` 的幂），
但库里没有：`LoopC2.lean` 的 `BddC2C` 链整条是**全局有界**版，要逐点版得重做一遍（且该文件不在本单可写清单里）。

**所以真正能用的形状是 `_of_herm` 版**（同样已编译，且严格弱于带撇类）：
`hasDerivAt_integral_{Phi,Psi}_pairs_of_herm`，只收两条——
(a) `Ψ u` 在每个 Hermitian 点 `ContDiffAt ℝ 2`；(b) **正则化**满足旧的 `TestFunT`。
**这两条对原始对象都是现成的**：(a) = `EGDef.contDiffAt_gloop_matrix`（T58），(b) = `testFun_momentFun_ukerObs`（T133），
因为 `hermFun (原始) = ukerObs` **按定义相等**（`loopObs` 本来就是 `gloop ∘ hermCLM`）。

### 可满足性检查（都编译过）
1. **正向、原始对象**：`hasDerivAt_integral_momentFun_ukerRaw` —— 对 `Ψ(M) = |(U∘(L−K))_a|^{2p}`（用**原始 `gloop`**，
   即 `MomentDuhamel.lkFun` 的传播子共轭）在任意 `Im z ≠ 0` 处成立的生成元恒等式（`∑_{ij} S_ij ∂_ij∂_ji` 形）。
   配套：`ukerRaw`、`hermFun_ukerRaw`/`hermFun_momentFun_ukerRaw`（`funext + simp only`，**不能写 `rfl`**：
   defeq 检查在 `LoopArg` 上 whnf 超时，踩过）、`contDiffAt_{,momentFun_}ukerRaw`。
2. `testFun'_momentFun_ukerObs`：带撇类非空。**今天仓库里每一个 `TestFun'` 供给都经由旧类**，见上一节。
3. **负向**（未入库、但已在上面说清）：`TestFun'.of_herm` 写出来是**假的**，第一次编译就被 Lean 拦下——
   正则化的一阶/二阶界推不回原始的。这一条是本单唯一被证伪的猜测。

### 两条 `Hyp` 字段**没有**闭合，还差什么（如实，别当成做完了）
`momentIneq_of_diffIneq`（T180）把 `MomentIneq`/`MomentIneqQ` 归约成逐点 `hdu`，`cMD p = 2p−1` 已定死。
本单给了 `hdu` 所需的**生成元恒等式**，但 `hdu` 还差两大块：
1. **含时可容许性**：`TestFunT d N T (hermFunT Ψ)`，即 (a) `(u,M)` **联合** `C²`——圈沿 `u ↦ z_u`
   （`contDiffAt_resH_zt` 只做了单个预解式；圈要把 `EGDef.contDiffAt_gloopProd_matrix` 的归纳改成 pair 版），
   **外加** `edgeKer` 与 `Kval` 对 `u` 的 `C²`（只知道一阶，见 `hasDerivAt_edgeKer`/T58）；
   (b) 字段 `bddT`：`∂_u Ψ` 在窗口上一致有界，需要圈对 **`z`** 的导数界——
   T141 的球版给的是「`M`-导数界对 `z` 一致」，**不是 `z`-导数界**。这是真缺口。
2. **drift + Hölder 链**：`∂_1 Ψ` 用 `Hyp.drift` + `hasDerivAt_Uker_path` 换掉、二阶项用 `genMomentPt_le'`、
   其二次变差认成 `(U⊗U)∘(E⊗E)`（`quadVarPairs_Uker` + T127）、Hölder、再除以 `p ψ^{p−1}` 把
   `∂_u E|Y|^{2p}` 变成 `ψ′`（`ψ = 0` 处要小心，这正是 T132a 取积分形式的原因）。

### 重复劳动（按 CLAUDE.md「造轮子之前先查」记一条）
`Hierarchy/EGDef.lean` 早有 `fderiv2_comp_clm`（`T M = M` 的对角特例）与
`coordD2_gloop_eq`/`wirtSecond_gloop_eq`（圈的特例）。本单的是一般版（`P M` 任意、两个方向、带算子范数界——
类的转移必须要算子范数，对角特例给不了），文件头已互相指认；`Hierarchy/` 一个字没动。
**教训**：按名字 grep（`coordD2_herm`、`hermFun`）查不到，按**概念**（`hermCLM` + `coordD2`）才查得到。

### 蓝图待挂（本单不可写 `content.tex`，节点已找好，整合时一次贴上）
* `content.tex:1447`（T71 生成元恒等式节点）：`RBM.Gauss.TestFun'`、`hermFun`、`TestFun'.herm`、
  `hasDerivAt_integral_Phi'`、`hasDerivAt_integral_Phi_pairs'`、`hasDerivAt_integral_Phi_pairs_of_herm`
* `content.tex:1488`（T72 节点）：`RBM.Gauss.genMomentPt_le'`
* `content.tex:2263`（T132b 含时恒等式节点）：`RBM.Gauss.TestFunT'`、`TestFunT'.herm`、
  `hasDerivAt_integral_Psi'`、`hasDerivAt_integral_Psi_pairs'`、`hasDerivAt_integral_Psi_pairs_of_herm`


## T175：具体的 `C²` 截断 `χ`（`Gauss/CutoffChi.lean`，416 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9605** 条。

**先查后建的结论：Mathlib 的光滑过渡在这里用不了。** `Real.smoothTransition` 与 `ContDiffBump` 都只证了
`nonneg`/`le_one`/`monotone`/`ContDiff`——**没有导数公式、没有导数界、没有 Lipschitz 常数**。
而 `abs_threshold_drift_le` 要的是一个**真正的数** `C_χ`；`smoothTransition` 的 `‖χ′‖∞` 没有闭式，二阶更甚。
**没有硬编常数，而是换了构造。**

用**五次 Hermite 截断**（恰好 `C²`，正是 T158 与生成元 `𝓛` 所需），写在截断幂基里：
`cutChi x = 1 − (6u⁵−15u⁴+10u³) + (6v⁵+15v⁴+10v³)`，`u = (x−1)₊`、`v = (x−2)₊`。
`[2,∞)` 上恒为 0 靠恒等式 `P(s+1) = 1 + Q(s)`；**`C²` 是由通用引理 `hasDerivAt_maxPow` 推出来的、不靠手工拼接条件**
（`(·)₊^{n+2}` 含断点可导，用 `HasDerivWithinAt.union` + `Set.Iic_union_Ici`）。

| 常数 | 值 |
|---|---|
| `abs_cutChiD_le` | `‖χ′‖∞ ≤ 15/8`，**紧的**（`cutChiD_three_halves` 证 `χ′(3/2) = −15/8` 取等） |
| `abs_cutChiDD_le` | `‖χ″‖∞ ≤ 15`（真值 `10/√3 ≈ 5.77`，按「常数不求最优」未收紧） |

`χ′` 的支集含于 `[1,2]`——**恰好就是 T158 的 gap `J_u/Θ_u ∈ [1,2]`**。

**T158 里关于 `χ` 的假设已全部关闭**：grep 确认 `CutoffBounds.lean` 只有两条声明量化了 `χ`，两条都已卸
（`hasDerivAt_cutComp_cutChi`、`abs_threshold_drift_cutChi_le`，后者取 `C_χ = 15/8` 得**数值**界 `≤ 15m/η`）。
`abs_cutChiDD_le` 目前**没有消费者**，是为 T132c 的生成元项提前备好的。

**可满足性（已编译）**：`cutChi_spec` 把 T158 对 `χ` 的**整包**要求合成一条定理并证明有居留，**排除了「同时不可满足」**；
另有数值自检（`χ(3/2) = 1/2`、`χ′(3/2) = −15/8`、`χ″(5/4) = −45/8` 说明 χ″ 界不是关于零函数的陈述）——**抄错系数会当场编译失败**。


## ⭐ T189：Step 6 最后一条有内容的假设 `hG` 卸掉——(5.134)/(5.135) 已是定理（`Gauss/Step6DriftEG.lean`，895 行，2026-09-21）

`lake env lean RBM1D/Gauss/Step6DriftEG.lean` exit=0；`#print axioms` 对本文件 16 条声明全部只含
`propext / Classical.choice / Quot.sound`（跑完即删）。**新文件，五个只读文件一字未动。**
（`RBM1D.lean` 的 import 由协调者加。）

### 抵消到底给了多少：**完整的一个 `A^{-1}`，而且是两半各拿一半**

T182 的诊断是对的（逐路径差一个 `A = Wℓ_uη_u`），但「缺口只能从期望里拿」这句要精确化。
按论文 (5.134) 在 `E^{(G̃)}` 的 3-loop 里写 `L = K + (L−K)`，两半**各自**多出一个 `A^{-1}`，
而且**理由不同**：

| 半边 | 1-loop | 3-loop | 结果 |
|---|---|---|---|
| `K` 半（`E^{(G)}(E(L−K), K)`） | **(5.126)**：`E⟨(G−m)E_a⟩ ≺ A^{-2}`（逐路径只有 `A^{-1}`） | (2.59)：`‖K_3‖ ≲ A^{-2}` | `η_u^{-1}A^{-3}` |
| `L−K` 半（`E[E^{(G)}(L−K, L−K)]`） | (2.78)：`(L−K)_1 ≺ A^{-1}` | **(2.78)**：`(L−K)_3 ≺ A^{-3}`（(2.77) 的 `L_3` 只有 `A^{-2}`） | `η_u^{-1}A^{-3}` |

**期望里的抵消只出现在 `K` 半**；`L−K` 半是逐路径的，它的 `A^{-1}` 来自「3-loop 取 `L−K` 而不是 `L`」。
T182 的 (5.77) 第 3 行之所以短一个 `A`，正是因为它把 3-loop 取成了 `L`（`Ξ^{(L)}_{u,3}`）。

### ⚠ 否定发现：`Step6.sharpExpect_step6` 的 `hG` 按字面**不可证**（不是可满足性问题，是推不出来）

`hG` 只给一个**一致界** `Λ`（对所有 `E[⟨(G−m)E_{a₁}⟩L_{u,σ',a'}]`），却要结论 `≤ C·W·ℓ_u·Λ`。
但 `E^{(G)} = W∑_{a,b}S^{(B)}_{ab}X_aY_b` 且 `∑_{a,b}S^{(B)}_{ab} = L`，**一致界只能给 `W·L·Λ`**。
论文的 `W·ℓ_u` 来自 3-loop 的**衰减**（`Decay.norm_sum_SB_le_right`：`a` 求和被压在 `O(ℓ_u)` 窗口里），
而 `hG` 不提供衰减。记 paper-deltas #127。

**所以本单不证 `hG`，而是直接证它的结论 (5.135)**，消费者换成 `Step6.sharpExpect_of_hierarchy`
（收两个已证的 `DriftBound`），`sharpExpect_step6_driftEG` 的假设表里**没有 `hG`**。
连带**少掉两条**：`hq13`（`E[(L−K)_1(L−K)_3] ≺ A^{-4}`）与 `hint2`——(5.134) 的 `L−K` 半是逐路径的，
用不到混合二阶矩。

### 落地

`eG_add_right`（`E^{(G)}` 对 loop 变元可加）、`integral_eG_const_right`（**对确定性 `Y`，`E` 穿到 1-loop 上**）、
`integrable_eG_const_right`、`gloop_one_conj`/`lkPath_one_conj`/`norm_integral_lkPath_one`
（**Lemma 5.15 覆盖两个电荷**：`G(σ)ᴴ = G(−σ)`、`m(−) = conj m(+)`；没有这条，(5.134) 只覆盖 `σ ∈ {+,−}²` 四种里的一种）、
`norm_eG_two_le`（**(5.77) 第 3 行在 `n = 0` 处、写成 (5.133) 的形状**，`Ξ·Φ ≤ C·A^{-1}` 是唯一的额外前提）、
`eG_gloop_eq_add`/`driftEG_eq_add`（**(5.134)**）、
**`unifDetDom_driftEG` / `driftBound_driftEG`（(5.135)）**、
**`sharpExpect_step6_driftEG`（(2.80)，`hG` 已卸）**。

### 可满足性检查（都编译了，不是散文）

* `exists_loopDecay_Kval`——`hKd`（`K` 在长度 3 的衰减，本文件唯一新增的确定性要求）由
  `Decay.loopDecay_Kgen` 在**任意** `ℓ > 0` 处产出，非空洞。
* `mem_egInputs_of`——新好集 `EGInputs` 的衰减合取项**被 T182 已在用的 `FDInputs`（带 `L` 的长度-3 衰减）加上 `hKd` 蕴含**（预算翻倍）。
  故 `hinG` 没要 Lemma 5.9 给不出的东西；真正新增的只有 (5.76) 在长度 `1`、`3` 的功率计数，与 T182 的 `xiLK … 2 ≤ Ψ` 同类。
* `h526`——就是 `Step6.lemma515` 的结论，总装里由 `h527`/`hq11` 产出，不作假设。
* `scale_shape_check` / `pathwise_shape_is_one_power_weaker`——数值自检：`Wℓ A^{-4} = η^{-1}A^{-3}`，
  且逐路径形状 `η^{-1}A^{-2}` 恰好是它的 `A` 倍（**增益是一个 `A` 不是两个**，抄错指数会当场编译失败）。

### fiat 审计

`driftEG` **一字未改**（T182 的定义逐字使用，`driftEG_eq_add` 是关于它的定理）。
没有为了让 (5.135) 出来去调整任何定义。未实例化 `SumZeroDyn.Hierarchy`、未用 `Lemma510` 任何字段。
剩下的假设全是样本侧或包络/可测/可积侧：`hKd`、`EGInputs` 的计数、`Env`/`hmeasLK`/`henvLK`、
一圈的可积性 `hintL1`（**两个电荷都要**，比 T182 的 `hint1` 宽一点）。

## ⭐⭐ T181：`Lemma514` 的矩路线打通——**六步链上最后一条 fiat 冲突消失**（`Gauss/Lemma514Moment.lean`，787 行，2026-09-21）

> **⚠ 后续更正（T192，2026-09-21）**：本节说 `hHol` 缺三块——**第一块其实早就存在**（T116 的 `Gauss.norm_gloop_sub_le`/`norm_Lval_sub_le_sqrt` 就是 `m` 个预解式乘积的伸缩模），真正无主的是后两块。另：**`lemma514_forall_of_momentDuhamel` 把 `(K, γ)` 排在 `∀ m` 前面，要一个常数通吃所有环长——这个要不到**（`m` 个预解式的模必带 `η^{−(m+1)}`，常数按 `m` 几何增长）。好在该定理的证明只用 `hHol (n+2)`，**正确接口是单 `m` 的 `lemma514_of_momentDuhamel`**；T192 另给了 `lemma514_forall_of_hHol_flow`，逐 `m` 取自己的 `K` 组装出同样的结论。

`lake build RBM1D` exit=0，审计 **9660** 条。
**文件里没有任何 `SumZeroDyn.Hierarchy`、没有任何 `Lemma510` 字段**（grep 只在注释里出现），**全程只用 `0 ≤ s N`**。

**端到端验收探针 `flow_sharpLmK_of_momentDuhamel` 通过**：产出喂进 `Step45.flow_sharpLmK` 的 `h514` 槽，**bare application**。

### 链条上两处方法性的东西
* **量词交换** `unifDomIcc_of_forall_stochDom`：「对每条终点时间序列都有 `≺`」⟹ `UnifDomIcc`。
  **合法的唯一理由是 `τ,D` 排在 `∀ᶠ N` 之前、前面没有 `∃ C`**；并且证了**逆向** `forall_stochDom_of_unifDomIcc`
  ——**两者等价，所以交换没有偷偷加强假设**。
* `stochDom_xiLK_of_nonneg` 把 `0 < s N` 减弱成 `0 ≤ s N`（改用 `scale_pos'`）——**这就是矩路线不重新撕开 T161 那条缝的地方**。
* T124 的网格引擎在常数控制下特化，`hζlow`/`hslow` **全免**，只剩 `hHol`。

### ⚠ 负面发现：**量词交换对 `hrhs` 不适用**
`hrhs_of_moment_inputs` 的结论是 `∃ C, ∀ᶠ N, …`，**`C` 排在 `∀ᶠ N` 前面，选择论证在那里不成立**。
本文件因此把交换用在 `stochDom_of_momentDuhamel` 的**输出**上（此时 `C` 已被 Markov 吃掉）。
而 `rhs514At_forall_of_moment_inputs` 又表明 **`hrhs` 侧根本不需要交换**——它本来就把 `v` 当参数收，`MomentDuhamelRhs.lean` 一字不用改。

### 还短什么（精确到条，带归属）
* **A. `H : ∀ n, MomentDuhamel.Hyp`** ——T180 产了 4/6，`momentDuhamel`/`momentDuhamelQ` 未闭合，短的正是 T187 写明的两块。
  **归属 T187/T180 的余项。** 本单所有定理都是「从一个 `Hyp` 出发」，实例一出现就接上。
* **B. `hHol`（本单新引入、唯一真正无主的一条）**：`u ↦ (Wℓ_uη_u)^m‖(L−K)_{u,σ,a}‖` 在高概率事件上的确定性 Hölder-γ 模。
  现成材料是 T106 的**单个**预解式模；缺三块：(i) 传播到 `m` 个预解式的乘积；(ii) `Kval` 对 `u` 的模；(iii) `(Wℓ_uη_u)^m` 对 `u` 的模
  （`ellHat` 显式，初等但没人证）。**该落在 `Gauss/FlowHolder.lean`。**
* **C. `hrhs` 的输入**：`hinit`/`hFmom`/`hEEmom` **T157 已卸**（`hFmom` 由 T165 的 `hdom_of_driftInputs` 喂），只需把窗口读宽（机械）；
  `hkerlt`/`hkerC`/`hker2lt`/`hker2C` 是 `edgeKer` 行和、纯记账、**无主**；**`hnum`（(5.92) 的数值收口）无主**。

### 可满足性检查（都编译过，六条）
`card_loopData_le`（`hcard` 不再是假设，显式 `Cv = m+1`）；量词交换的逆向；
`rhs514At_self`（终点 `v = s` 时两个时间积分为 0，**逐字退化成 (2.68)**——六步本来就有的输入）；
`hHol_of_window_degenerate`（**docstring 明确写了这只是相容性、不是真实估计的证据**）；逐条核过的量词序；
以及 **`Lemma514Premises` 必须留着**——若删掉改为对所有 `(Λ,Φ)` 量化，则在 `Λ = Φ = 0` 处控制塌成 `scale_v^{−(n+2)}`，
**假设不可满足、定理变空**。这正是今天反复撞到的那类陷阱。

## ⭐⭐ T185：Lemma 3.2 完整证出——**蓝图里「未形式化」的节点归零**（`Loop/CanonicalRealize.lean`，1667 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **9868** 条；蓝图 **170 节点、167 已形式化、0 statement-only、0 not-yet**。
`Loop/Crossing.lean`、`CanonicalPartition.lean`、`TreeRepGeneral.lean` **一字未动**。

| | 定理 |
|---|---|
| **(2) 实现** | `FGamma_canonGraph`、`isCanonicalTree_canonGraph` |
| **(5) 像** | `mem_TSP_iff_exists_isCanonicalTree`：`F ∈ TSP n ↔ ∃ Γ a, IsCanonicalTree ∧ F(Γ) = F` |
| **(3) 唯一性** | `canonIso`、`exists_iso_of_FGamma_eq`（保叶标的同构） |

**⇒ `RBM.TSP` 从「把论文的分类定理当定义」升级成定理，paper-deltas #8 撤销**，只剩 #128 的 `3 ≤ n`。

**两条路线都按 T168 的提示走，没另起炉灶**：
* 实现复用 `TreeRepGeneral.lean` 已有的 laminar 编码；**无环性不用 `decide`**——每条边给一个 `Bool` 割证书喂进已有的 `sep_of_cut`，
  配 `isAcyclic_iff_forall_adj_isBridge`，秒过（对比 T168 实测 9 点树 `decide` 要 85 秒）。
* 唯一性把 `Γ` 生根在叶 `a_{n−1}`，**枢纽仍是 T168 那条 `leafSide_eq_inArc`**（边下方的叶恰是 pair 的弧）——
  在抽象树里也是全部关键；两条核心引理的极小性论证都归结为单调性引理 `inArc_mono_up`。

**防抄错的锚点**：文件末尾两条编译过的 `example` 把两半都实例化到 Figure 4 的 `F = {(0,3),(3,5)} ∈ TSP 6`（用 T168 的 `figure_four`）。
**没有发现论文任何一条按字面为假**，与 T168 的外部穷举完全一致。

**命名检查是手动做的**：97 个顶层名字逐个全仓 grep，零冲突——**单文件编译查不出跨文件重名**。

## ⭐⭐ T192：`Lemma514` 矩路线的三块余项全部落地（`Gauss/Lemma514Holder.lean`，新建 1071 行，2026-09-21）

`lake env lean RBM1D/Gauss/Lemma514Holder.lean` **exit=0**，0 sorry、0 axiom，
八条主定理 `#print axioms` 只出现 `propext / Classical.choice / Quot.sound`（审完已删 print）。
**`Gauss/Lemma514Moment.lean` 一字未动**；新文件名不是 T181 建议的 `FlowHolder.lean`——那个名字
**已被 T106 占用**（预解式单条模），所以另起 `Lemma514Holder.lean`。
（本单**没有**改 `RBM1D.lean` 的 import，按协调者要求由他加。）

### (1) `hHol` —— T181 标「唯一真正无主的一块」，已证出

T181 列的三个缺口里，**第一个其实早就有了**：
`RBM.Gauss.norm_gloop_sub_le` / `norm_Lval_sub_le_sqrt`（T116，在 `Gauss/Step1Hyp.lean`）
就是 `m` 个预解式乘积的伸缩模。真正缺的是后两个，本单补上：

* **`Kval` 对 `u` 的模**（核心）：`RBM.norm_primRhs_le`——(2.48) 右端是 `≤ n²` 对 `(k,l)` 的和，
  每项 `∑_{a,b} K(G^L) S^{(B)}_{ab} K(G^R)`，两条剪接环长度都在 `[2, n]`，`S^{(B)}` 行和为 1，
  故 `‖primRhs‖ ≤ W n² L B²`；配 `hasDerivAt_Kgen_all` + 中值不等式得
  `RBM.norm_Kgen_sub_le` / `norm_Kgen_sub_le'`（后者去掉 `2 ≤ n` 限制：长度 0/1 时 `K` 与 `u` 无关）。
  **`K` 这一半是 Lipschitz 的，不是 1/2-Hölder。**
* **`(Wℓ_uη_u)^m` 对 `u` 的模**：`RBM.abs_ellHat_sub_le`——`ℓ̂ = min((1−u)^{-1/2}, L)`
  在 `u → 1` 附近**只有 1/2-Hölder**，常数 `(1−T)⁻¹`；这和流的 `√u` 给出同一个 `γ = 1/2`。

成品：`RBM.Gauss.abs_scaleLK_sub_le`（**全显式**常数）→ `scaleLK_const_le`（塌成 `(m²+5m)R^{3m+4}`）
→ **`RBM.Gauss.hHol_flow`**：`γ = 1/2`，`K = c(3m+4)+1`。三个输入是
`hreg`（`η_{t_N} ≥ N^{-c}`，论文自己的 `t ≤ 1−N^{-1+τ}`）、`hXΞ`（`‖X‖ ≺ 1`，T100）、
`hKb`（`K` 的多项式包络）。**全程只用 `0 ≤ s N`。**

**验收探针 `lemma514_of_hHol_flow`**：裸应用喂进 `lemma514_of_momentDuhamel` 的 `hHol` 槽，编译通过。

### ⚠ 负面发现：`lemma514_forall_of_momentDuhamel` 的 `hHol` 量词序要不到

那条定理把 `(K, γ)` 排在 `∀ m` **前面**——要求一个常数对所有环长通用。
**这个做不到**：`m` 个预解式乘积的模带 `η^{-(m+1)}`，而 `η⁻¹` 在区制里是 `N` 的正幂，
常数按 `m` 几何增长。但**它的证明只用 `hHol (n+2)`**，所以正确的接口是
`lemma514_of_momentDuhamel`（单个 `m`）；本单给出 `lemma514_forall_of_hHol_flow`，
逐个 `m` 取自己的 `K` 组装出 `∀ m, 2 ≤ m → Step3.Lemma514`，结论一样（`Lemma514` 本身不带常数）。

### (2) `edgeKer` 行和：`hkerlt`/`hker2lt` 无条件，`hkerC`/`hker2C` **需要短窗口**

`‖xiOf (mSigma E) σ i‖` 在体内**恰好等于 1**（`norm_xiOf_mSigma`），于是

* `hkerlt_flow`、`hker2lt_flow`：化归为 `w < 1`，**无条件成立**（只要 `0 ≤ s N`、`t N < 1`）；
* `hkerC_flow`、`hker2C_flow`：左端恰是 `1 + (w−u)/(1−w)`，**常数 `Ck` 存在当且仅当
  `t_N − s_N ≤ κ(1−t_N)`**，此时 `Ck = 1 + κ`。
  **这一条不是记账，是真假设**：固定窗长而 `t_N ↑ 1` 时 `(1−t_N)⁻¹ → ∞`，该槽不可满足。
  配套 `norm_xi2_mSigma`（双环的 `‖ξ‖ = 1`）。

### (3) `hnum`：两端点归约

`hnum_of_endpoints`——(5.92) 的 `w` 依赖在两侧单调方向相反：左端只通过 `w − s_N` 且系数非负，
右端 `(Wℓ_wη_w)^{-(n+2)}` 因 `flowScale_antitoneOn`（p. 24）单调不减。
所以全窗口的 (5.92) 只要在**左端 `w = t_N`、右端 `w = s_N`** 各验一次。
再配 `hnum_endpoint_of_three` 把三项（初值 (2.68)、漂移 T165、`E⊗E` (5.24)）各按 `c_N/3` 分账。

### 可满足性检查（都编译过）

* `exists_highProb_normX`：`‖X‖ ≺ 1`（T100）真的造出满足 `hXΞ` 的高概率事件 `Ξ`——
  否则 `Ξ = ∅` 会让 `hXΞ` 空真，`hHol_flow` 里除它以外没有任何东西约束 `Ξ`。
* `norm_Kval_two_le_rpow`：长度 2 处 `hKb` **是定理**（`norm_Kgen_two_le` 给 `W⁻¹(1−T)⁻¹`，
  被 `hreg` 吃掉），所以包络假设在基础长度上非空真。长度 ≥ 3 对应 (2.59) `norm_Kgen_le`，本单没装。

### 还短什么

* `hKb` 在长度 `≥ 3` 上没有装配（(2.59) `norm_Kgen_le` 比需要的强，但它要 `0 < t` 且只覆盖 `3 ≤ len`，
  接缝没缝）。
* `hkerC`/`hker2C` 的短窗口条件 `t_N − s_N ≤ κ(1−t_N)` 目前是假设，没有从六步的窗口构造里导出。
* `hnum` 的三项各自的界仍归 T146/T157/T165。
* `MomentDuhamel.Hyp` 的 `momentDuhamel`/`momentDuhamelQ` 仍是 T187/T180 的余项（本单不碰）。

### 命名检查（手动，单文件编译查不出跨文件重名）

30 个新顶层名逐个全仓 grep：**撞了一个** —— `RBM.ellHat_nonneg` 已存在于
`Propagator/Rate.lean`（我的 import 链够不到它，单文件编译发现不了，全量 `lake build` 才会炸）。
已删掉重复声明、改成内联。其余 29 个零冲突。

## ⭐ T191：`Hyp` 两字段的**分析链全部打通**，剩下的是含时可容许性（`Gauss/MomentDuhamelTime.lean`，1421 行，2026-09-21）

`lake env lean RBM1D/Gauss/MomentDuhamelTime.lean` exit=0、零 warning；本文件 34 条声明逐条
`#print axioms` 全是 `propext / Classical.choice / Quot.sound`（跑完即删）。
**新文件，`Gauss/MomentDuhamel.lean`、`MomentDuhamelRhs.lean`、`TestFunHerm.lean`、
`Lemma514Moment.lean`、`Hierarchy/*` 一个字没动**（`RBM1D.lean` 的 import 由协调者加）。

### ⭐ 第 0 步的答案：`TestFunT` 对**时间**的 `C²` 确实是过度要求（今天第七次）

逐行读 `hasDerivAt_integral_Psi` 的证明，联合 `contDiffAt`（`ContDiffAt ℝ 2` on `(u,M)`）**只被用了两处**：

| 用处 | 真正需要的 |
|---|---|
| `hasDerivAt_Psi_Hflow` | `DifferentiableAt ℝ (uncurry Ψ) (x, H_x ω)` —— 联合**一阶** |
| `continuous_timeD1` | `M ↦ timeD1 Ψ u M` 连续（只为 `∂₁Ψ(u,H_u·)` 的可测 + 可积） |

其余全部是**矩阵**切片 `Ψ u` 的事（`slice`、`continuous_coordD1/D2`、`hasDerivAt_coordD1_update`、
`sum_used_eq_sum_pairs_coordD2`），那里 `C²` 是真需要的。

于是落地 `RBM.Gauss.TestFunT₁`：把联合 `C²` 换成 `contDiffM`（切片 `C²`）+ `diffJoint`（联合可微）
+ `contT`（`∂₁Ψ` 对 `M` 连续），四条界原样。配套
`hasDerivAt_integral_Psi₁` / `…_pairs₁` / `…_pairs_of_herm₁`，**结论逐字不变**——
把原证明重放一遍就是这条结论的验证：若联合 `C²` 在别处被用到，这次重放根本编译不过。

* `TestFunT.toTestFunT₁`：旧类装进新类，**已有供给一条不丢**（非空）。
* `TestFunT₁.of_contDiffAt_one`：联合 `C¹` + 切片 `C²` 就够，这是将来检查 `Ψ` 可容许性的形状。
* **放宽是严格的（本单最重要的负向检查）**：`kinkT u M = (u−½)|u−½|`（对 `M` 常值）
  `testFunT₁_kinkT` 属于新类，`not_testFunT_kinkT` **证明它不属于旧类**
  （`deriv` 是 `2|·−½|`，在 `½` 不可微，经 `ContDiffAt.derivWithin` + `not_differentiableAt_abs_zero`）。
  所以这不是"换个写法"，新类真的接纳旧类拒绝的函数。

**对 T191 的后果**：`edgeKer` / `Band.Kval` 对 `u` 的**二阶**依赖**不用做了**。
仓库现有的一阶事实 `hasDerivAt_edgeKer`、`hasDerivAt_Kgen_all`（长度 ≥ 2 全覆盖）就是对的阶。
短的是**联合**正则性，不是第二个时间导数。

### 漂移 + Hölder 链：三块全部落地

1. **Hölder（两条，含时无关）**：`integral_pow_sub_one_mul_le`
   （`E[|Y|^{2p−1}|Z|] ≤ (E|Y|^{2p})^{(2p−1)/(2p)}·‖Z‖_{2p}`）与 `integral_pow_sub_two_mul_le`
   （`E[|Y|^{2p−2}Q] ≤ (E|Y|^{2p})^{(p−1)/p}·‖Q‖_p`，`Q ≥ 0`）。
   经 Mathlib 的 `integral_mul_le_Lp_mul_Lq_of_nonneg`；桥 `memLp_ofReal_of_integrable_rpow`
   把接口自带的 `Integrable (|·|^q)` 变成 `MemLp`（就是 `momNorm_le_momNorm_of_exponent_le` 里
   那段 `hfin` 计算的通用版）。⚠ **`p = 1` 必须单独走**：第二条的共轭指数 `p/(p−1)` 在 `p=1` 没定义，
   那一档是 `E[Q] ≤ E[Q]`，直接证。
2. **除以 `p ψ^{p−1}`（`ψ = 0` 处安全）**：`rpow_inv_le_of_deriv_le` / `…_Icc` /
   `diffIneq_of_deriv_le`。`φ^{1/p}` 在 `φ = 0` 处不可导，所以在 `φ + ε` 上做 FTC 再让 `ε ↓ 0`；
   **`ε` 极限是初等的**（`Real.rpow_add_le_add_rpow` 的次可加性把误差写成
   `ε^{1/p} + 2ε^{1/(2p)}∫f`），**不需要控制收敛**。
   **导数只在开区间 `Set.Ioo (s N) v` 上假设**——正是 `hasDerivAt_integral_Psi` 的 `0 < u` 逼出来的接缝。
   `diffIneq_of_deriv_le` 的结论**逐字是** `momentIneq_of_diffIneq` 要的 `hdu`（含 `momNorm`）。
3. **总装**：`momentIneq_of_derivBound` 与 `momentIneqQ_of_derivBound` ——
   **`MomentIneq` / `MomentIneqQ` 现在只差一条逐点的导数不等式**，
   外加可积性/上界这些边条件。顺带补了 T180 文档里"同样三行"却**从未写出来**的
   `momentIneqQ_of_diffIneq`（`Q_t` 路线的接线）。

### ⚠ 常数的一个真陷阱：`cMD p = 2p − 1` 在 `p = 0` 是负的

`Hyp.cMD_nonneg : ∀ p, 0 ≤ cMD p` 对**所有** `p : ℕ` 量化，而两条不等式只在 `1 ≤ p` 处发声。
字面 `2p − 1` 在 `p = 0` 取 `−1`，**装不进字段**。落地 `cMDval p = max 0 (2p−1)`，
`cMDval_of_one_le` 证明它在 `1 ≤ p` 处就是 `2p−1`。STATUS 里 T180 写的"常数定死 `cMD p = 2p−1`"
要按这个读。

### 可满足性 / 锐度检查（全部编译过）

* `holder_first_sharp` / `holder_second_sharp`：`Z = Y`（resp. `Q = |Y|²`）时两条 Hölder **取等**，
  配 `holder_first_lhs_self` / `holder_second_lhs_self`（左端就是同一个积分）。
  指数抄错则这两条恒等式当场失败。
* `deriv_le_hyp_sharp_one` / `rpow_inv_le_of_deriv_le_sharp_one` / `deriv_le_conclusion_sharp_one`：
  `p = 1`、`φ u = u`、`f ≡ 0`、`g ≡ 1` 时假设**取等**、结论读作 `v ≤ v` 也取等，
  所以 `2p − 1` 不能再小，假设集非空。
* `testFunT₁_kinkT` + `not_testFunT_kinkT`：见上，Step 0 的放宽严格。
* `TestFunT.toTestFunT₁`：新类非空（旧类的每一个供给都还在）。

### 还短什么（如实，别当成做完了）

**两条 `Hyp` 字段仍未闭合**，剩下的**全部**是含时可容许性 + 生成元的逐点展开，具体三条：

1. **`TestFunT₁ d N T (hermFunT d N Ψ)`**（`Ψ(u,M) = |(U_{u,v}∘(L−K)(u,M))_a|^{2p}`）：
   (a) `contDiffM` = T133 的 `testFun_momentFun_ukerObs`，**现成**；
   (b) `diffJoint`（联合可微）——圈沿 `u ↦ z_u` 要把 `EGDef.contDiffAt_gloopProd_matrix` 的归纳
   改成 pair 版（预解式的联合 `C²` 已有：`contDiffAt_resH_zt`），再配 `hasDerivAt_edgeKer`
   与 `hasDerivAt_Kgen_all`；**只要一阶**；
   (c) `contT`（`∂₁Ψ` 对 `M` 连续）与 `bddT`（`∂_u Ψ` 在窗口上一致有界）——
   后者仍要**圈对 `z` 的导数界**；T141 给的是「`M`-导数界对 `z` 一致」，**不是 `z`-导数界**（T187 的判断成立）。
2. **`φ' u` 的存在与识别**：由 `hasDerivAt_integral_Psi_pairs_of_herm₁`（本单提供）得到
   `φ' = ∫∂₁Ψ + ½∑S∫wirtSecond`，再用 `Hyp.drift` + `hasDerivAt_Uker_path` 把
   `∂₁Ψ` 与 `genS` 项对消（`hasDerivAt_Uker_thetaOp` 已有），二阶项用 `genMomentPt_le'`（T187），
   其二次变差认成 `(U⊗U)∘(E⊗E)`（`quadVarPairs_Uker` + T127）。
3. **边条件**：`φ'`、`f`、`g`、`ψ·f` 的区间可积性与 `ψ` 在窗口上的一致上界。
   高斯模型上都应由确定性包络 `‖G‖ ≤ η⁻¹` 给出（同 `integrable_lkT_pow` 的路子），本单没做。

### 命名检查（手动，单文件编译查不出跨文件重名）

新增的 34 个顶层名逐个全仓 grep，**零冲突**（`TestFunT₁`、`kinkT`、`cMDval`、
`rpow_inv_le_of_deriv_le*`、`diffIneq_of_deriv_le`、`integral_pow_sub_{one,two}_mul_le`、
`holder_*`、`memLp_ofReal_of_integrable_rpow`、`momentIneq{,Q}_of_derivBound`、
`momentIneqQ_of_diffIneq`、`momNorm_eq_rpow` 等）。

## ⭐⭐ T190：`h566` 与 `hsym` **同时卸掉**——T178 的障碍是割点选错（2026-09-21）

`lake build RBM1D` exit=0，审计 10016 条（含 T191）。`ee_le_EEpath_sym` / `ee_le_paper_EEpath_sym` 的假设表里**既无 `h566` 也无 `hsym`**。

**关键不是拆 `k`，是换割点。** (5.23) 的 6-loop 有**两个**黏合标号 `b`、`b'`，T178 只在 `b` 处开环。
**在 `k=1` 的圈里 `b` 只碰 `a₁` 块、`b'` 只碰 `a₂` 块，`k=0` 反过来——这才是 Figure 14 那个对称的实质。** 于是
`b` 靠近 `a₁` 时 `k=1` 割 `b`、`k=0` **割 `b'`**；`b` 靠近 `a₂` 时镜像；两者都远时任一割法都行。
`b`-求和因此是**两个逐点估计（`a₁↔a₂` 互换）+ 一个远场估计**，拼接用 (5.35) 用过的同一个三分 split。
**T178 说的「`k=0` 项差整整 `A^{1/2}`」是割点选错造成的，换割点后消失**，结果在两个标号上对称、没有任何东西短。

**代价是记账而非缺口**：`hrow` 把论文 "treat `b = b′`" 显式化（paper-deltas #129），损失 `W^{o(1)}` 吸进 `J*`；
结论里的两个常数 `2` 就是 (5.22) 的两项——**以前其中一项是被假设掉的**。
`hfarb` 用 (5.67) **之后**的约化形状，因为 `k=0` 的尾函数出场次序与 `k=1` 相反、只有过完 (5.67) 才合流。

**可满足性已编译**：`ee_sym_hyp_consistent` 给出显式见证**同时**满足两条定理的全部假设，
**并补上了旧 `ee_hyp_consistent` 没覆盖的 `hA`/`hr` 两条**；另有解包后直接喂进两条主定理的非空真探针。

## ⭐ T191：矩 Duhamel 的分析链全部打通，两字段**仍未闭合**（`Gauss/MomentDuhamelTime.lean`，1421 行）

**第 0 步的答案：`TestFunT` 对时间的 `C²` 是过度要求——今天第七次，而且放宽是严格的。**
逐行读 `hasDerivAt_integral_Psi` 后发现联合 `contDiffAt` **只被用了两处**（`hasDerivAt_Psi_Hflow` 要**联合可微**一阶、
`continuous_timeD1` 要 `∂₁Ψ` 对 `M` 连续），其余全是矩阵切片的事。
落地 `TestFunT₁` 与三条恒等式，**结论逐字不变**。
**后果：`edgeKer`/`Kval` 对 `u` 的二阶依赖不用做了**——现有的一阶已是对的阶，短的是**联合**正则性。
**严格性是证出来的**：`(u−½)|u−½|` 属于新类且 **`not_testFunT_kinkT` 证明它不属于旧类**。

**漂移 + Hölder 链三块全部落地**：Hölder（⚠ **`p = 1` 必须单独走**，共轭指数 `p/(p−1)` 在那里没定义）；
除以 `pψ^{p−1}` 的 `ψ = 0` 安全版（在 `φ+ε` 上做 FTC 再令 `ε ↓ 0`，**极限是初等的、不需要控制收敛**；
**导数只在开区间假设**，对上 `0 < u` 的接缝）；总装 `momentIneq_of_derivBound`，
并补了 T180 文档里「同样三行」却**从未写出来**的 `momentIneqQ_of_diffIneq`。

**⚠ 一个真陷阱：`cMD p = 2p − 1` 在 `p = 0` 是负的**，而 `Hyp.cMD_nonneg` 对**所有** `p : ℕ` 量化，**字面装不进字段**。
落地 `cMDval p = max 0 (2p−1)`。**T180 记的「常数定死 `2p−1`」要按这个读。**

**锐度检查（编译过）**：Hölder 在 `Z = Y`、`Q = |Y|²` 处**取等**；`p=1` 时假设取等、结论读作 `v ≤ v`，**`2p−1` 不能再小**。

**唯一的真缺口**：`bddT` 仍要**圈对 `z` 的导数界**——**T187 的判断成立，T141 给的是「`M`-导数界对 `z` 一致」，不是 `z`-导数界**。
另两块有主：`diffJoint` 只要把 `EGDef.contDiffAt_gloopProd_matrix` 的归纳改成 pair 版（**只要一阶**）；边条件应由 `‖G‖ ≤ η⁻¹` 给出。

## ⭐⭐ T132c：`BootPP.step` 与 (5.48) 落地；**`MomentHyp.step` 按冻结形状不可证——两条阻塞都编译成了定理**（`Hierarchy/Step2MomentStep.lean`，1001 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **10077** 条。只碰了这一个新文件。

### 指数账（实际编译出来的）
走 shape 2、跳过 (5.36)→(5.42) 的吸收步后：(5.40) 两行 `β* = 10`（沿用 `phi_arith` 原样，**是瓶颈**），
**近场 `q = r³` 的 `β* = 4`（零余量，正好吃满预算的 `R⁴`）**，远场主项 **5.5**、次项 **4.5**，全部 `< 30`。**(2.72) 的指数没有被碰。**
`beta_star_margin` 编译验证 `hregS` 蕴含所需边条件只要 `4δ ≤ 2c`（现有 `δ ≤ c/24` **富余一个数量级**）。
`phi_lt_threshold` 把回路闭上。常数只比 `Step2.cStep` 多一个 `m⁻¹`。

**近场积分（T174 的第 2 条建议）已兑现**：`integral_nearInt_le` 证出 `∫ ≤ (Im m)⁻¹(η_s/η_v)^4`，**正好是 (5.43) 的预算、`R` 上零损失**；
关键是**先把四个因子乘拢**（塌成 `η_v^{−4}η_s^{5/2}η_u^{1/2}`，关于 `η_u` 单增）再取 sup。
**`coarse_sq_ge` 编译验证了逐因子取 sup 的粗算至少超预算 `R^{5/2}`——T174 说的 `R^{2.5}` 属实。**

### ⚠ `MomentHyp.step` 不是对的靶子，两条阻塞都是定理
1. **`bnd_poly` 不允许 `bnd` 带任何 `N` 的幂**（`bnd_poly_excludes_pow`）。而 `J*` 是对 `L²` 个 loop 取 max，
   矩层唯一的初等界是并集界，**每一阶都要付 `L² ≍ N²`**。去掉它需要 `‖max‖_q ≤ L^{2/Q}max‖Y_a‖_Q` 且 `Q ≫ q`，
   而 `step` 的前缀假设只给**同一阶** `q`。
2. **矩层去截断的余项不小于门槛本身**（`detrunc_remainder_ge_thr`）。要压下去必须把阶数乘 `(K+δ)/δ`
   （`detrunc_order_needed`）；流上 `K ≍ D ≥ 60`、`δ ≤ c/24`，是天文数字。
**这正是规格说的「不在矩层面用指示函数截断」。** 替代路径已落地：`le_of_gap_crossing` + `le_of_gap_net`
（缺口条件只需在**网点上**、且只需**条件于前缀**），配 `netSet`/`hclose_of_modulus`。

### `(+,+)` 的捷径被证否
先试了「用 (2.73) 的无条件先验一次性打穿、免掉自举」，**两条编译的否定结论**：
`xiLK_two_apriori` 表明无条件先验只有 `Ξ^{(L−K)}_{u,2} ≺ A_u(R+C)`
（⚠ **注意 (5.76) 的两个归一化差一个 `A`**：`Ξ^{(L)}_m` 带 `A^{m−1}`、`Ξ^{(L−K)}_m` 带 `A^m`）；
`no_finite_pass` 表明 (5.83) 的自二次项让 `θ ↦ c + θ²A_t^{−1}` 在 `θ ≥ A_t` 处**不收缩**，
先验正好落在收缩半径之外，**任何固定有限次 `≺`-迭代都到不了 `Θ = A_s^{1/2}`**。

### 交付
* **`BootPP.step`**：`bootPP_step_of_net` 把对**连续统**的量化化归成**网点上的有限多个定时刻**，`bootPP_of_net`/`bootPP_of_modulus` 直接造出整个 `BootPP`。未卸的只有网点上的条件改进 `hev`。
* **(5.48)**：`flowEq548_of_near_far` 直接产出 `Step45.FlowEq548`。近场输入就是锐化的 (5.47)；未卸的只有远场 `hfar`。

### 余项与归属
* **`hev`** 要**带截断**的矩 Duhamel（`χ(Ξ₂/Θ)` 在支撑上线性化，前缀事件上截断与未截断的 loop 重合）——现有 `MomentDuhamel.Hyp` 没有截断版。
* **`hfar` 是 (5.48) 唯一缺的东西**：要把 (5.39)/(5.41)/(5.44) 的三个指示函数**带过** one-step bound，
  而 `Step2.step_bound` 把它们全丢了——**要么改它，要么在矩路线上重做一份带指示的 step bound。**
* `MomentHyp.step` 建议按规格新增 `MomentHypCut`，§5/§6 的化归件已就位。

### 可满足性（六条，全部是定理不是注释）
退化点下 `phi_arith'` 的假设全可满足且结论非空（常数几乎取等）；**`hbeta`/`hgamma` 的边条件在 `r=R=x=A=1` 处取等，
所以 5.5/4.5 在这个论证下不能再降**；`le_of_gap_net` 与 `hclose` 各有非空见证（**证明那两条是真化归不是空化归**）；
两条负面结论也在退化点取等、非空。量词序逐条核过（`bnd_poly_excludes_pow` 是「`p`、`α` 先固定再 `N → ∞`」，不是 `∀p ∀N`）。

## Cowork 对 D10、D11 的处理（2026-09-21 15:10，路由类，Jun 已授权）

* **D10 → (a)**：新建 `Gauss/MomentDuhamelCut.lean` 作截断版矩 Duhamel 接口，**现有 `MomentDuhamel*.lean` 一字不动**（冻结签名纪律）。`MomentHyp.step` 按冻结形状不可证（T132c 已编译两条阻塞）——**冻结不动**，新增 `MomentHypCut` 走前缀条件下的网上穿越。开 **T197**。
* **D11 →** 在**矩路线上**重做一份带三个指示函数的 one-step bound（(5.39)/(5.41)/(5.44)），**不改** `Step2.step_bound`（旧路线，挂在 fiat 的 `Step2.Hyp` 上）。开 **T198**。

---

# ⭐ 滞留工单审计（交 Cowork 再分析，2026-09-21）

**一句话**：Jun 点名的 11 张里 **9 张的余项已被后来的工作解决或作废**；真正可开工的只有 **T159**；
而审计的主要产出是**四块无主、且卡在六步活路径上的东西**。

## A. 点名的 11 张：9 死、1 可开工、1 部分
**已死（余项被取代，逐条查过生产者在树里）**：T100（→T109）、T113（→分级+预算链 T137/T142/T171/T177/T188）、
T115（→T122）、T116（→T125，`step1Hyp_gauss_of_scale''` 已完整填出 `lift`）、T117（→T182+T189，**六条假设一条不剩**）、
T118（(i)(iii) 已落，(ii) 被 T176 判为死项）、T128（→T136+T137）、T132a（→T146→T181→T192）、T152（**被 T182 推翻并取代**）。
**T159（六步端到端核对）真实、且现在最该做**：两个前置 T161/T163 均已完成，而 T176 的清单今天已被
T177/T181/T182/T183/T188/T189/T190/T192 大幅改写。
**T132b** 的 ①③ 已解，② 两条矩不等式仍未闭合 → 阻塞于 T196。

## B. ⚠ 四块无主且在活路径上（本次审计的主要产出）

### B.1 Step 6 的样本侧收口——**全无主**
`sharpExpect_step6_driftEG` 的漂移侧已被 T182/T189 全部卸掉，**剩下的假设全在样本/记账侧，没有任何工单认领**：
`FDInputs`/`QuadInputs`/`EGInputs`/`DriftInputs` 四个好集**只有定义和消费点、零生产者**（原料已在：T126 的 `LKDecay`/`LDecay`、`Decay.lemma59`、Step 3 的计数）；
一批 `henv*`/`hEnvpoly`/`hmeas*`（T182 标「归包络那条线」，**那条线没有单**）；
一批 `hcont`/`hintU*`/`hintL*`/`hintQ`/`hintG`（T176 列为盲区，至今无人碰）；
`hEL` **已可产**（`LoopC2.differentiableAt_integral_gloop_flow` 在树里）**但没人接上去**。
**开单时必须点名每一个字段名与定义位置**，否则会重演「归包络那条线」这种没有收件人的转述。
⚠ **先裁一条**：`docs/STATUS.md` 记着论文 p.25 的注记——**Step 6 可以从 Thm 2.21 里摘掉**。若属实，整块可能不必做。

### B.2 ⚠⚠ `Gauss.Dims` 没有居民——**全高斯层的空真风险，无主**
`Gauss/Model.lean:110-113` 自己写着这一条，全仓 grep 确认**至今没有任何 `Dims` 的实例**。
而 `Gauss.band d`、`Gauss.sample d` 全部量化在 `d` 上，**六步链的高斯实例化整体挂在这上面**。
数学上平凡（`L = 3`、`W = ⌊N/3⌋`、`c = 1/4`），但**它正是可满足性审计的第 0 条**——
今天七次空真事故的教训在这里是最贵的：若 `Dims` 无居民，整条矩路线都是空真的。**建议与 T159 一起做。**

### B.3 `hKb`（(2.59) 在所有环长上的装配）——无主
T192 明写「接缝没缝」。**但 `Flow/Iteration.lean:598 norm_Kval_le` 是对一般 `n` 的界**——看上去只差一层接线，
**T192 可能没看到它**。T195 的规格只覆盖 `edgeKer` 行和、不含 `hKb`。

### B.4 T196 的规格漏项（已就地修正，见下）
T191 的余项是**四项**（`diffJoint`、`contT`、`bddT`、φ′ 的识别与边条件），而 T196 的标题与规格**只写了 `bddT`**。
**已直接告知该 agent 补全**，并按 CLAUDE.md 的教训记一笔：转派前要重读工单全文。

## C. 两条不阻塞但该处理的
* **`condExpDiag_stochDom_of_pieces` 的 `hminor` 在对角为假**（T112 编译发现，`Gauss/IBP.lean:1214`），现为死代码但**是个假假设地雷**——
  照 T184 给 `eq45Flow_of_localLaw_gain(')` 的做法加 `@[deprecated]` 护栏即可。
* `‖Z_k‖_∞ ≥ 64/65` 的 `L^n → L^∞` 一步至今未入库（T171/T177/T188 三次都记了没做），只影响那条记载的完整性。

## D. 审计的盲区（如实转述）
只编译了一个探针、**未跑全量**；凡说「在树里/无生产者」的依据是 grep 与已编译签名文本。
**完全没有读论文 PDF**，凡涉及「论文是否真这么写」的判断均转述 STATUS、未独立核对。
逐张核过约 40 张，**只看状态栏未进 STATUS 的约 80 张**——这批里若有「表面完成、实际留了无主余项」的会被漏掉。

## T194：能量一致的 `Thm221`（`Flow/EnergyUniform.lean`，685 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **10168** 条。**0 个现有签名改动**，`Flow/` 下既有文件一字未动。

落地 `E : ℕ → ℝ` 版的 `BoundsCoreN`/`BoundsN`/`Cond272N(')`/`Thm221N(')` + 六条常数能量特化 +
四条迭代引理（**证明脚本逐字照抄，只把 `E` 写成 `E N`，一次都没改过**）+ `BoundsN_of_Thm221N(')`
—— 即 Lemmas 2.18–2.20 在 `N` 依赖能量上；以及 Theorem 2.3 整条到
**`localSemicircleLaw_of_Thm221N_of_z`——陈述里已完全不出现能量参数**。

**⇒ paper-deltas #38 的局部律那一半撤销**：`SpecSeqN.of_z` 证明能量切片条件恒可满足。

**镜像了哪个变体、为什么**：两个都镜像，**承重的是带撇的 `Thm221N'`**。
判断是「`N` 依赖能量与 (2.72) 的 `N^c` 加成是正交的两件事，耦在一起以后合并只会更痛」，
所以照 `Flow/Iteration.lean` 的分层原样复制。**T186 若改了未加成路线，只有不带撇那一支需要跟进，带撇主干不受影响。**

**路线 (ii) 的网现在够得着了**：`localSemicircleLaw_of_Thm221N_of_z` 的假设只剩 `Transfer`/`TransferLoop1` 与 `z` 的定义域条件，
网点能量 `E_j(N)` 直接作为 `z` 的实部塞进去即可，**不再需要「能量切片」这个前提**。

**T153 留的 `∀E ∃C` 盲区已处理**：全树扫出 **40 条**（不是 34 条），**没有一条落在本单路径上**——
**这不是抽查结论而是编译事实**：本文件全程没引入额外假设、没有常数出现在结论里，
唯一进入下游的常数 `cScale κ` **只依赖 `κ`**。那 40 条全部位于**生产** `Thm221N` 的六步内部，
将来真去证 `Thm221N` 时才会撞上；根仍是 `Loop/SumZero.norm_Alayer_le` 的 `ι = (mE E).im`。

**非空性已编译**（两条 `example`）：`Thm221N.step` 的前提**联合可满足**（`s = t ≡ 0` 处），
所以 `step` 不是空蕴含、前面的 `∀ E : ℕ → ℝ` 不是空量词；`SpecSeqN` 在真正 `N` 依赖的能量上有居留元。

**未做**：Theorem 2.4 的 `N` 版（Theorem 2.2 用不到，纯机械复制）；
`Loop/SumZero.norm_Alayer_le` 的非一致修复（协议只允许动新文件，**建议单开一张小单，改动机械、不需搬文件**）；
`lem:2.18–2.20`/`thm:2.3` 节点的 `\lean{}` 需要补 `N` 版名字（蓝图由 T193 持有）。

## ⚠⚠ T195：短窗口条件**在总装窗口上是假的**；矩路线在 (5.92) 处用错了引理（只读审计 + 7 条编译定理，2026-09-21）

> **⚠ 记账更正（T193 查出）**：T195 是**只读审计**，那 7 条定理在 scratchpad 里编译过但**没有入库**（全仓 grep 零命中）。所以本节的结论是**可信的**（编译过），但**仓库里没有对应的 Lean 名字**；谁要接手 (7.16) 的矩形式，得把 `gridS_window_len`/`no_const_Ck`/`one_add_norm_mul_eq`/`prefactor_not_absorbable_in_Scales` 重做一遍入库。蓝图据此**没有**给它们挂 `\lean{}`。

### 1. 短窗口条件不可导出——它在论文自己的网格上**反向成立**
论文 p.24 的网格是 `1 − s_k = W^{−kτ'}`（Lean 的 `gridS`）。已编译：
`gridS_window_len` 给出 `(t−s)/(1−t) = W^{τ'} − 1` **恰好相等**；`no_const_Ck` 由此证明——
若 `hkerC` 在该窗口上以 `N`-无关常数 `Ck` 成立，则 `W_N^{τ'} ≤ Ck`，而 `W_N → ∞`，**矛盾**。
**所以不是「没证出来」，是 `κ` 必须 `≥ W^{τ'} − 1`。** T192 说「这是真假设」，T195 把它锐化成**「在总装窗口上不可满足」**。

### 2. ⭐ 根因：`hkerC` 的左端**逐字就是 Lemma 7.1**，而 (5.92) 的「无前因子」正是「不许用 7.1」
已编译 `one_add_norm_mul_eq`：`‖ξ‖ = 1` 时左端**恒等于** `η_u/η_w`，故 `Ck^{n+2} = (η_s/η_t)^{n+2}` —— **正是 (7.1)**。
通读 §5.5（pp.67–69）：Lemma 5.14 的**每一项**都经 `Q_u` 投影后用 **(7.16)**，**没有一处用 (7.1)**。
精确账 `ρ = r·R`；仓库里三档齐备（(7.1) 付 `ρ^n`、(7.14) 付 `R·r^n`、**(7.16) 付 `r^n`**），
**`r^n` 恰好抵消 `A^{−n}` 归一化——这就是「无前因子」的来源**。矩路线用的是**最弱那一档**，多付 `R^{n+2}`。
**论文自洽，缺口完全在 Lean 这一侧**（paper-deltas #131）。

### 3. 「常数取 `C·R^k`」这条退路不闭合
已编译 `prefactor_not_absorbable_in_Scales`：给出 `(As,R,A) = (256,2,256)` 逐条满足 `Step3.Scales` 的全部七个字段，
而 `R^n·As^{1/2} > A` 对一切 `n ≥ 5` 成立——**`n ≥ 5` 时额外的 `R^n` 已超出 `Scales` 的预算**。
**更致命**：这个 `R` 的幂**乘在 `Λ^{1/2}` 上**，而 `Ψ(n,k)` 的 `A_s^{1/2}` 地板**与 `k` 无关**，
**所以加大 `k` 救不了**——Step 3 的双重归纳靠 `k` 吸收 `R` 幂的通道，对这个损失是关闭的。
退到 (7.14) 把损失降到 `R^1`（在 `Scales` 里够），但**同样乘在 `Λ^{1/2}` 上，仍破坏 `S(n,k)` 的地板**。
**只有 (7.16) 的 `r^n` 是零损失的。**

### 4. ⚠ 立即的风险与下一步（给 Cowork）
* **不要把短窗口条件当假设接进总装**：`hkerC_flow`/`hker2C_flow`（`Gauss/Lemma514Holder.lean:962–986`）**本身是真定理**，
  但它们的 `hwin` 槽在 Theorem 2.21 的窗口上**不可满足**，**用它填 `hrhs` 会让 Step 3 空真**。
  建议照 T184 的先例给它们加编译器级护栏，并把 docstring 从「genuine hypothesis」升级为「on the six-step grid it is false」。
* 真正要补的两块：**(i) (7.16) 的矩形式**（`momNorm_Uker_apply_le` 的对应物，建在 `norm_Uker_fastDecay_le_sumZero`/`norm_Uker_sumZero_scale_le` 上）；
  **(ii) `Hyp.momentDuhamelQ` 的消费者**——该字段**至今没有消费者**，`MomentDuhamel.lean` 自己就写着这句。
* 两个已知接缝：`SumZero` 在 `Qop` 之后是代数恒等式（逐 ω 免费），但 **`FastDecay` 只在高概率事件上成立**，
  所以矩形式必须走好事件 + `momNormDom_of_stochDom`（与 `hHol` 的 `Ξ` 同一模式）；
  另外 `momentDuhamelQ` 的左端是 `Q_v∘(L−K)_v`，要回到 `(L−K)_v` 还得补 (5.95)–(5.101) 的 `P∘(L−K)` 那一半。
* `hkerlt`/`hker2lt` 无条件，保持不变。

## Cowork 对滞留审计（B.1–B.4、C）与 T195 的处理（2026-09-21 16:00）

* **T195 → T201**：Lemma 5.14 矩路线改走 `Q_u` + (7.16)（论文本身自洽，缺口在我们：paper-deltas #131）；`hkerC_flow`/`hker2C_flow` 加 `@[deprecated]` 并入 T201。
* **B.2 → T202**（最高优先）：`Dims` 居民 + `OpNormBound` 核对 + `hminor` 护栏（C 的第一条）。
* **B.3 → T203**：`hKb` 经 `norm_Kval_le`。
* **B.4**：T196 规格已更正为四项（`diffJoint`、`contT`、`bddT`、`φ′`）——Cowork 转派时漏读，已记。
* **B.1 Step 6 样本侧：暂不开单，转 Jun 裁（D12）**。Cowork 已核原文：p.25（仓库 PDF）Step 6 之后原话「(2.71) will not be needed for Steps 1–5, i.e., Theorem 2.21 holds if (2.71) were removed from both the assumption and statement」；(2.71)/(2.80) 在 Theorems 2.2–2.5 的证明里都没再出现，**但 §7.2 的 (7.29) 明写「can be proved by following the proof of (2.80)」**，即 Theorem 2.6 阶段要用 Step 6 的方法。

## D12 ⭐ Lean 的六步目标是否按论文 p.25 的注记去掉 (2.71)/(2.80)？（Cowork 2026-09-21 16:00，等 Jun）
* **(a) 去掉**：Lean 的 `Thm221` 取论文注记里的变体（假设与结论都不含 (2.71)），Step 6 的漂移侧（T182/T189 已完成）保留，**样本侧（四个好集生产者、包络/可测/可积一批、`hEL` 接线，约 2–4 张单）推迟到 Theorem 2.6 阶段**（那时 (7.29) 要用同一套方法）。六步主线更短。
* **(b) 保留**：按论文正文的完整 Theorem 2.21 做，现在就开样本侧的单。
Cowork 倾向 (a)：论文自己说了不需要，主定理 2.2–2.5 都不用 (2.71)，且工作不会白费（Theorem 2.6 阶段接着用）。

## ⭐ T186：`Thm221` 收裸 `Cond272` —— **裁定反转：裸 (2.72) 不够，缺的不是指数而是 `A_t` 的多项式下界**（2026-09-21）

`lake build RBM1D` exit=0，审计 **10199** 条。新文件 `RBM1D/Flow/Thm221Bare.lean`（468 行，纯新增；
`Flow/Hypotheses.lean` / `Iteration.lean` / `Scales.lean` / `Thm221Gain.lean` **一字未动**，只在 `RBM1D.lean` 加一行 import）。

### 结论（与 D1 括注相反，**请更新裁定**）

T174 / T132c 的「走 shape 2 后所有行 `β* < 30` 严格成立」是对的，但**「所以裸 (2.72) 就够」不成立**。
`hregS` 里的 `N^c` 有**两个**用处，之前只核了第一个：

1. 压住 `R = η_s/η_t` 的幂 —— 这个确实由 `β* < 30` 白送；
2. **给 `A_t = Wℓ_tη_t` 一个多项式下界**，好把 `≺` 的 `N^δ` 吃掉（`phi_arith` 的 `x^{17}R^{10} ≤ A` 里那个 `x^{17} = N^{17δ/8}`）。

裸 (2.72) 对第 2 点**一点都不给**：取 `s = t`，(2.72) 逐字就是 `1 ≤ A_t`，而 `A_t = 1` **确实取得到**——
`flowScale = W·Im m·min(√(1−t), L(1−t))`，`L ≤ W·Im m` 时取 `1−t = (WLIm m)^{-1}`，否则取 `1−t = (W Im m)^{-2}`，
两支都给 `A_t = 1`（`RBM.exists_flowScale_eq_one`，已编译）。于是
`RBM.exists_cond272_not_rpow_le_scale`：**存在逐字满足 (2.72) 的时间列，其上 `N^c ≤ A_t` 对任何 `c > 0` 都失败**。
（这不是「Lean 陈述太宽」：论文 Theorem 2.21 的假设表里也只有 (2.72)，多项式下界是**应用时**由 p.24 的
`t ≤ 1−N^{-1+τ}` 网格给的，定理本身没写。）

### 能做到的最强形式：`Cond272Reg` / `Thm221Reg`

`Cond272Reg B E s t c := Cond272 B E s t ∧ ∀ᶠ N, N^c ≤ B.scale E N (t N)`
—— **(2.72) 逐字 + Step 1 本来就带的具名假设 `hreg`**（`eventually_scale_facts`、`weakLaw_highProb` 的那一条）。
这个下界在网格上是白送的：网格步 `η_s/η_t = W^{τ'}` 本身是 `W` 的正幂，(2.72) 于是逼出 `A_t ≥ W^{30τ'}`。

强弱链（全部已编译）：`Thm221 → Thm221Reg → Thm221'`，`Cond272' → Cond272Reg → Cond272`，
`Bounds_of_Thm221Reg`（与 `Bounds_of_Thm221` 结论 `rfl` 相等，T107 手法探针已编译）。

### 指数记账（按**已编译的**陈述核的，不是抄旧审计）

判据从 `β* ≤ 30` 换成了 `e/c + b/30 ≤ a`（`RBM.rpow_mul_rpow_le_of_pow_thirty`：`R^b ≤ A^{b/30}`、`N^e ≤ A^{e/c}`、`A^{e/c+b/30} ≤ A^a`）。

| 消费者（已编译） | 要的形 | 裸路线的条件 |
|---|---|---|
| `Step2.phi_arith` / `Step2MomentStep.phi_arith'` 的 `hA` | `x^{17}R^{10} ≤ A`（**(5.40)，`β* = 10`，瓶颈**） | `17δ/(8c) + 1/3 ≤ 1` ⟺ `δ ≤ 16c/51` |
| `Step2MomentStep.beta_star_margin` | `x^{32}R^{11} ≤ A²`（(5.41) 远场主项，`β* = 5.5`） | `4δ/c + 11/30 ≤ 2` ⟺ `δ ≤ 49c/120` |
| `Step2MomentStep.hgamma_of_reg` | `x^{24}R^{9} ≤ A²`（远场次项，`β* = 4.5`） | 弱于上一行 |
| `phi_arith'` 的 `hq`、`hJΛ` | `r³ ≤ R²`、`J ≤ x⁸R⁴`（近场，`α = 0`） | 与 `A` 无关，免费 |

**`δ ≤ c/4` 同时满足前两行**；带增益路线（`beta_star_margin`）只要 `δ ≤ c/2`，所以**裸路线的代价就是 `δ` 预算少一半**，没有别的。
`Cond272Reg.hA_phi` / `Cond272Reg.hA_betaStar` 直接产出这两条，且**对 `u ∈ [s,t]` 一致**（`A_u ≥ A_t`、`R_u ≤ R_t`）。

**探针（scratchpad，已编译）**：`Step2MomentStep.side_conditions_of_reg` 的**整个**三条结论
（`hq_of_ratio` + `hbeta_of_reg` + `hgamma_of_reg`）从 `Cond272Reg` 重建出来，全程不碰 `Cond272'`。
——所以 Step 2 那一侧确实只差把 `side_conditions_of_reg` 的假设从 `N^c R^{30} ≤ A_u` 换成 `x^{32}R^{11} ≤ A_u^2`（带撇版），
该文件当前被别的 agent 占着，没动。

### 论文字面 shape 1 仍然不行（顺带核实）

`phi_arith`（shape 1）的 `hα : α·x^{24}R^{10} ≤ 1`，`α = A^{-1/3}`，即 `x^{72}R^{30} ≤ A`。
在判据里是 `b = 30, a = 1`，于是 `e/c + 1 ≤ 1` 逼出 `e ≤ 0`：**`N^δ` 一点余量都没有**。
这正是 Jun 12:10 裁定 (a) 的必要性——(5.41) **必须**走 (2.73) 降幂，否则连 `Cond272Reg` 都不够、只能回到 `Cond272'`。

### 还欠的（如实）

* `Thm221Reg` 只是接口 + 转换 + 算术桥，**没有**从六步把它证出来（六步链本身还没在仓库里合拢，见 T176 探针 P1）。
* `Hierarchy/` 那一侧的带撇版（`side_conditions_of_reg'`、`harith_flowAs'` 等）没做：要改 `Step2MomentStep.lean` / `Step2PP.lean` / `StepGlue.lean`，与并行车道冲突。
* `blueprint/src/content.tex` 被别的 agent 占着，`\lean{}`/`\leanok` 未补。

## ⭐⭐ T197：截断版矩 Duhamel——**Step 2 现在整体绕开了已证不可证的 `MomentHyp.step`**（`Gauss/MomentDuhamelCut.lean`，1021 行，2026-09-21）

`lake build RBM1D` exit=0，审计 **10312** 条。只碰了这一个新文件。

**验收**：`aprioriDecay_cut` / `step2_cut` 的**结论与 `Step2Moment.aprioriDecay`/`step2` 逐字相同**，
假设里 `MomentHyp` 换成 `MomentHypCut`。**整个 Step 2 现在只剩一条具名假设 `CutHyp.moment`。**

**两条设计上的要点**：
* `cutTrunc Θ x = χ(x/Θ)·x` 自带**确定性包络 `2Θ`**，于是 `integrable_cutTrunc_pow` 免假设，
  **`MomentHyp` 的 `env`/`env_le` 两个字段直接消失**；`continuousOn_of_modulus` 让 `cont` 也消失。
* `cut_contraction`：`4Θ ≤ A` 时 `χ(J/Θ)J²/A ≤ ½·χ(J/Θ)J`——**正是 T132c `no_finite_pass`（`θ ↦ c+θ²/A` 在 `θ ≥ A` 不收缩）的对照面**。
  截断把映射拉回收缩半径内，这就是它能替代停时的机制。
* **去截断在概率层、余项为零**：前缀假设取 `u = ws` 即给出 `J_{ws} ≤ N^{2δ}Θ`，正是截断水平，故 `cutTrunc = J`；
  代价只有网点上的并集界 `N^{Ccard}`，取 `p ≥ 2(D+Ccard+1)/δ` 吸收。

**可满足性检查的质量值得记**（全部编译）：`satCutHyp` 给出**完整的 `CutHyp` 实例**，
且取在**临界标度 `J ≡ Θ`**（不是退化的 `J ≡ 0`）、窗口非退化、用的是**流自己的参数**；
关键是 `mesh_fine`（要网细）与 `card_le`（要网粗）这对**方向相反、最容易联合不可满足**的条件，
**由同一个见证同时满足**，且 `sat_mesh_card` 证明 `mesh_fine` 在该见证处**取等**、网不能再粗。
另有 `sat_moment_at_zero`（T191 那个 `p = 0` 陷阱的同形检查）与 `sat_cut_sq_nonvacuous`（线性化不是退化的 `0 ≤ 0`）。
**踩到过一个真的退化点**：见证里 `mesh N = N²` 在 `N = 0` 给 0、`mesh_pos` 当场失败，改成 `(N+1)²`。

### 尚缺与归属
1. **`CutHyp.moment`（截断 Duhamel 的高斯层计算）**——T132b/T198 一线；**Step 2 只剩这一条**。
2. `hfar` —— T198，且正好建在本文件的接口上。
3. ⚠ **一条无主项**：`flowEq548_of_near_far` 的 `hnear` 要**锐化到 `(η_s/η_u)²`**，
   而仓库的 (5.47)（含 `jS_stochDom_cut`）只给 `(η_s/η_u)^4`。**T198 的规格只点名 `hfar`，`hnear` 的锐化目前没人负责。**

## D12 裁定与 Cowork 更正（2026-09-21 16:10）

* **Jun 选 (a)**：Lean 的六步目标按论文 p.25 注记，先做**不含 (2.71)** 的 Theorem 2.21 变体。
* **⚠ Cowork 更正（给 Jun 的信息有误）**：Cowork 说「Theorems 2.2–2.5 都不用 (2.71)」**是错的**。已核原文：
  (2.71) 经 (2.62)（`|E L − K| ≺ (Wℓη)^{−3}`）给出 **Theorem 2.4 的期望界 (2.8)(2.9)**（「Together with (2.66) and (2.57), it yields the expectation bounds (2.8) and (2.9) in Theorem 2.4」；「(2.8) and (2.9) follow from (2.62)」），而 **Theorem 2.5 (QUE) 的证明直接用 (2.8)(2.9)**；Lean 里 `Flow/Consequences.lean` 的 `expect_loop2_of_bounds`/`expect_quantumDiffusion_*` 也正是吃 `hB.expect`。
  **所以 Step 6 不能推迟到 Theorem 2.6 阶段**，否则丢掉 Theorem 2.4 的 (2.8)(2.9) 与 Theorem 2.5。
* **Cowork 的执行方案（两遍归纳，不丢任何定理）**：第一遍 = 不含 (2.71) 的 `Thm221` 变体（T204），给出 Theorems 2.2、2.3 与 2.4 的 (2.6)(2.7)；第二遍 = 在第一遍结论之上单独对 (2.71) 做一次归纳（Step 6 的样本侧，T205），给出 (2.8)(2.9) 与 Theorem 2.5。论文注记保证第一遍不需要 (2.71)，第二遍每步只用第一遍的结论 + 上一步的 (2.71)。**Jun 16:15 确认：可以。**

## ⭐⭐ T196：`TestFunT₁` 对矩路线的 `Ψ` **七个字段全部闭合**（`Gauss/MomentDuhamelBddT.lean`，新文件，2026-09-21）

`lake env lean RBM1D/Gauss/MomentDuhamelBddT.lean` exit=0、零 warning；本文件 56 条声明逐条
`#print axioms` 全是 `propext / Classical.choice / Quot.sound`（跑完即删）。
**新文件**；`Gauss/MomentDuhamel*.lean`、`Gauss/TestFunHerm.lean`、`Hierarchy/*` 一个字没动
（`RBM1D.lean` 的 import 由协调者加）。56 个新顶层名逐个全仓 grep，**零冲突**。

### 交付：`testFunT₁_momentObsT`

`Ψ(u,M) = |(U_{u,v}∘(L−K)_u)_a|^{2p}` 落地为 `momentObsT`（内层 `ukerObsT u M = ukerObs d N (zt Ev u) σ ξ (u:ℂ) t (K u) a M`）。
`testFunT₁_momentObsT` 给出 **`TestFunT₁ d N (Icc u₀ u₁) (momentObsT …)` 的完整实例**，
假设只有：`0 < η`、`hzim : ∀ u ∈ 窗口, η ≤ |Im z_u|`（窗口上由 `le_abs_im_zt_of_le` 从 `|E| < 2`、`u₁ < 1` 直接给出）、
以及 `K` 的可导性与 `K`、`∂_u K` 的界（三条里没有任何矩阵、没有任何预解式）。

**T191 点名的四条**：`contDiffM`、`diffJoint`、`contT`、`bddT` 全部落地；
另外三条一致界 `bdd₀`/`bdd₁`/`bdd₂` 也落地（见下，它们**原本也短**，T191 没点名）。

收口件 `hasDerivAt_integral_momentObsT`：把 `hasDerivAt_integral_Psi_pairs₁` 喂上去，
**对 `Ψ` 再无任何假设**的 (T132b) 生成元恒等式。

### `bddT`：T187/T191 的判断成立，但"缺口"不是 `∂_z G = G²`

`z`-导数**仓库里已经有**：`hasDerivAt_gloop_zt`（T134）+ 确定性包络 `norm_zMotion_le`。
真正要做的是**组装**：`u` 同时出现在三处（`z_u`、传播子的运行时间、`K_u`），
`hasDerivAt_Uker_arg`（`Uker` 的 Leibniz，**带动的自变量**，`hasDerivAt_Uker_apply` 只动核）
+ `hasDerivAt_momentFun_path`（`(f·conj f)^p` 沿实路径求导，`conj` 只是 `ℝ`-线性，用 `Complex.conjCLE`）
给出闭式 `ukerObsTDeriv`，再取界。
**窗口一致性的来源分两块**：矩阵那一半由 `η⁻¹` 包络（对 `∀ M` 一致，因为 `loopObs` 自带 `hermCLM`），
`u` 那一半由 `ukerCoefBd`（**只含 `u`、不含矩阵**）在紧窗口上的连续性 + `IsCompact.exists_bound_of_continuousOn`。
**按「常数不求最优」没有写显式常数**。

### `diffJoint`：`contDiffAt_gloopProd_zt_pair` 就是 T191 说的 pair 版归纳

`contDiffAt_Gsig_zt_pair`（把 `Gsig (hermCLM M) (zt Ev u) σ` 认成 `resH ((E)+(1−u)m(σ)) M`，
再用现成的 `contDiffAt_resH_path`）+ 对 (2.41) 的 `n` 个因子归纳。结论是**联合 `C²`**，
但下游只用一阶（T191 已证二阶时间正则性是过度要求）。
**没有 Hermitian 边条件**——`loopObs` 复合 `hermCLM`，所以在**每个**矩阵处成立。

### ⚠ `bdd₀`/`bdd₁`/`bdd₂` 的一致版原本也是缺口（T191 未点名）

T133 的 `testFun_momentFun_ukerObs` 给的是**固定 `u`** 的三条界，而 `TestFunT₁` 要**窗口一致**，
`∃ C` 不能穿过 `∀ u`。`bddC2_momentFun` 恰恰是存在量化的，用不上。
落地 `exists_bddC2C_momentFun`：**常数不依赖于函数**的 `momentFun` 版，
由 `BddC2C` 对乘积（`bddC2C_mul_cx`，经 `ContinuousLinearMap.mul ℝ ℂ` + 现成的 `bddC2C_clm_apply`）
与幂（`exists_bddC2C_pow`，对 `p` 归纳）的封闭性得到。
这样 `u` 的依赖只剩 `ukerRow`（传播子行的 `ℓ¹` 大小，只含 `u`），紧窗口取 sup 即得。

### 可满足性检查（三条，都编译过）

1. `testFunT₁_momentObsT_zero`：取 `K = 0`，**所有假设由 `|E| < 2` 与 `u₁ < 1` 直接卸掉，无自由数据**。
2. `exists_not_isHermitian_green_eq_zero`：显式造出 `M = z·1 + (单个非对角 1)`——**非 Hermitian 且 `M − z` 奇异**，
   故**原始**预解式 `green M z = 0`（Mathlib 的 `nonsing_inv` 在奇异处给 0），整块信息坍塌。
3. `bddT_momentObsT_at_singular`：`bddT` 的一致界**确实在这个点上被取值**。
   —— 这正是 T180 那次空洞事故的同形检查：`∀ M` 不是伪装的 `∀ M, M.IsHermitian →`。
   它能成立的**唯一**理由由 `ukerObsT_hermCLM` 写明：`Ψ` 经 `hermCLM` 分解，
   所以界讲的**不是**原始预解式（T187 关于 `bdd₁/₂` 要全方向算子范数的结论没有被绕过）。

### 还短什么（如实）

**`MomentDuhamel.Hyp` 的两条字段仍未闭合。** T191 之后剩下的、本单**没有**做的：

1. **`φ'` 的识别**：`hasDerivAt_integral_momentObsT` 只给了 `φ'` 的**存在**与右端的形状；
   把 `∫∂₁Ψ` 与 `genS` 项对消（`Hyp.drift` + `hasDerivAt_Uker_path` + `hasDerivAt_Uker_thetaOp`）、
   二阶项过 `genMomentPt_le'`、二次变差认成 `quadVarPairs_Uker` + T127 —— 一条都没做。
2. **边条件**：`φ'`、`f`、`g`、`ψ·f` 的区间可积性与 `ψ` 的窗口一致上界（应由 `‖G‖ ≤ η⁻¹` 给，同 `integrable_lkT_pow`）。
3. **桥**：`momentObsT u (Hflow d N u ω)` 与 `Uker … (SumZeroDyn.lkT X E N u ω σ) a` 的逐字对齐
   （`⟨σ, List.ofFn b⟩` 与 `LoopData.idx (σ, b)` 的记账，外加 `K u b = B.Kval E N u …`）。**本单把 `K` 保持抽象**，
   只要 `HasDerivAt` + 两条界；在高斯模型上这两条由 `hasDerivAt_Kgen_all` 与 `norm_primRhs_le`（见 `norm_Kgen_sub_le`）给出，**本单没有接线**。

因此 `momentDuhamelHyp_gauss`（工单验收里点名的那个实例）**仍然不存在**，本单没有制造它。

## ⭐ T198：`hfar` 关上了——但 (5.48) 是化归不是定理（`Hierarchy/Step2MomentStep.lean` 新增 §11，2026-09-21）

`lake build RBM1D` exit=0，审计 **10411** 条。只动了这一个文件。

`flowEq548_of_near_farInputs` 产出 `Step45.FlowEq548`，**假设表里没有 `hfar`**（验收达成）。
取而代之的 `FarInputs` 是逐 `(N,ω)` 的一步输入（(5.21) 的 Duhamel 恒等式、(2.69) 初值、**带指示函数的** (5.35)、(5.45) 鞅界），
**而这四条正是近场那一半本来就要的**——所以远场特有的缺口没有了，但**(5.48) 仍是一条化归，不是定理**（已写进文件头）。

### 两条真正的新数学（仓库里原先没有）
* **支撑估计** `norm_Uker_supp_far_le`：住在对角带上的张量**做不出远场**——`‖a₁−a₂‖ ≥ 6ℓ*_v` 处
  `≤ 128e³‖A‖_∞(η_u/η_v)²e^{−(5/4)(log W)^{3/2}}`。机制是 `Θ` 的真指数衰减，质量必须搬 `≥ (5/2)ℓ*_v`。
  **这就是论文那句「From the decay of `U_{u,t}`, `(U∘f₂)_a` is exponentially small」的定量版。**
* **(7.2) 的锐化远场** `norm_Uker_far_le_of_tail`：`Step2.norm_Uker_le_of_tail` 在**所有**距离上都把膨胀因子 `(η_u/η_v)²` 折进主项，
  而 `ℓ*_v` 以外 (7.2) **根本没有那个因子**，膨胀只活在 `W^{−D}` 余项上。**这才是 (5.48) 远场为 `O(1)` 的真正原因。**

### ⭐ 指示函数的代价：在 `R` 上是零，不碰 `β* = 4` 的预算
审查时发现**指示函数只被一个地方需要**：(7.2) 本身已经把 `R²` 从初值项、`E^{((L−K)×(L−K))}` 项、
以及 (5.35) 的非指示部分上**全部剥掉了**；唯一剥不掉的是 (5.35) 近场项的 `q = (ℓ_u/ℓ_s)³`，
配 `∫η_u^{−1}du ≤ R` 就是 `R·q ≈ R²`——**只有支撑估计能杀掉它**。
远场常数 `cFarStep` 不含 `R`；`R²` 只出现在 `FarResidue` 里、由**尾部层级**支付（两个自由大参数），
**完全不进 `phi_arith'` 的预算，所以 T132c 的 `β* = 4` 零余量原封不动**。

### 可满足性（编译过）
`farInputs_of_remainder`：取 `F = Fn = 0`、整个 Duhamel 余项当鞅项，**对任意样本可实现** → 假设束非空；
**同一个见证也说明真正的内容不是可实现性而是 `cFarStep ≺ 1`，而它给不出来**——文档里明写了这一点。
残差条件由机制性而非退化性成立。**量词序逐条核过**（`∀ D > 0, ∃ D' ≥ D, ∀ᶠ N`，**不是 `∀ p ∀ N` 那种错序**）。
一处诚实的边界说明：`6ℓ*_u > L/2` 时远场区域为空、(5.48) 退化成近场那一半——**这是论文自身的区制，不是形式化缺陷**。

**未做**：按 D11 的裁定**没动 `Hierarchy/Step2.lean`**，旧 `step_bound` 一字未改。
残差条件要 `log W ≥ (4(D+P)/5)²`，该 agent 判断**不构成 paper-delta**（陈述本身是 `∀ D > 0, ∀ᶠ N` 且流上 `W → ∞`），**我同意**。

## D13 裁定（Jun 2026-09-21 16:25）：选 (i)
论文 **Theorem 2.21 补上 `t ≤ 1 − N^{−1+τ}`**（论文改动预算第 16 条）。Lean 的最终 `Thm221` 取 **`Cond272Reg`**（(2.72) 逐字 + 该区间条件，δ 预算 `c/4`），与补正后的论文逐字一致；T204（不含 (2.71) 的变体）与 T186 的 `Thm221Bare` 一律按 `Cond272Reg` 收口，`Thm221′`（带增益）降为推论。

---

## ⭐ 给 Cowork：`docs/agent-playbook.md`（并行 agent 协调手册，2026-09-21）
Jun 要求把 Claude Code 侧这一天的经验写下来，**由 Cowork 做成 skill**。已落盘 `docs/agent-playbook.md`，十一节：
① **本项目最主要的缺陷是空真不是错证明**（一天八次，附全表与处方，含六个可直接抄的可满足性样板）；
② **工单文本与 STATUS 会很快过时，必须核不能读**（五次实例）；③ **只读审计的探针不入库**（T195 被 T193 当场查出）；
④ **按文件分工挡不住重复造轮子**（要按概念 grep）；⑤ 编译与构建的三个陷阱；
⑥ **改共享文档的脚本**（我把 TASKS.md 截成 4 行那次的教训：不要把文件写成它自己的前缀切片，写前断言行数）；
⑦ **检查器本身要有总数守恒的断言**（蓝图静默丢节点三次）；⑧ `decide` 不可伸缩时把自检搬出 Lean 并说明范围；
⑨ **派单 prompt 的八段骨架**；⑩ 协调者自己的纪律（**无主的活要点名到字段级**——T182 那句「归包络那条线」没有收件人，结果那条线根本没有单）；
⑪ **最值得保留的产出形态是带证明的否定结论**（六条，全部编译成了定理，其中一条反转了裁定）。

## ⭐⭐ T202：`Gauss.Dims` **有居民了**——全高斯层的空真风险解除（`Gauss/DimsExample.lean`，新文件，2026-09-21）

滞留审计 B.2 的第 0 条：`Gauss.band d` / `Gauss.sample d` 全部量化在 `d : Dims` 上，`Dims` 若无居民，**整条矩路线都是空真的**，而 `lake build` 永远绿。现在两个完整见证都编译了：

* `Dims.example`（工单建议值 `L ≡ 3`、`W = max 1 ⌊N/3⌋`、`c = 1/4`）——**原样可行**。工单 ⚠ 里担心的 `dim` 与 `bandwidth` 联立不可满足**不成立**：`N^{3/4} ≤ ⌊N/3⌋` 等价于 `N³ ≤ ⌊N/3⌋⁴`，从 `N ≥ 100` 起成立（`dim` 从 `N ≥ 4` 起），`∀ᶠ N` 够用。
* `Dims.exampleGrow`（`L ≈ N^{1/4}`、`W ≈ N^{3/4}`、`c = 1/8`）——**非退化见证**：`L N → ∞` 且 `W N → ∞`（`tendsto_growL` / `tendsto_growW`），(2.2) 还留着 `N^{3/4}` 对 `N^{5/8}` 的余量。加这一个是因为 `L ≡ 3` 是 `three_le_L` 允许的最小值、也是论文真正关心的区制之外的平均场端点。

**`Dims` 的四个字段一个没削弱**，`dim` / `bandwidth` 都保持 `∀ᶠ N in atTop`。

**往下挪一层也查了**（空真风险最容易从一层挪到下一层）：
* `Dims.nonempty_Idx`——指标型 `ZMod (L N) × Fin (W N)` 对**任意** `d : Dims` 非空（空指标型会让所有逐元陈述空真）；
* `Dims.exists_Sblk_pos`——方差廓线 `S` **不恒为零**（由 `sum_Sblk_row = 1` 反证）。这条挡的正是 `ω = 0` 型事故：`S ≡ 0` 的模型满足一大堆估计的字面而无内容；
* `band d` / `sample d` 是**定义**不是结构假设，故 `Dims` 一有居民它们就有（`band_example` / `sample_example`、`nonempty_Omega`）；
* 顺带确认 `GaussIBP d`（`Gauss/IBPPoly.lean:243`）与 `TraceMomentBound d`（`Gauss/TraceMoment.lean:935`）都是**对每个 `d : Dims` 的定理**，所以它们现在是真有居民的结构。

**顺手项 (a)：`OpNormBound` 已卸。** `RBM.Gauss.opNormBound_gauss (d : Dims) : OpNormBound d`（`Gauss/TraceMoment.lean:964`）**无条件**、公理干净。`Gauss/Model.lean` 文件头那段「What is **not** done here」已按事实改写（**只改注释，定义与签名一字未动**）；`paper-deltas` #49 关闭。

**顺手项 (b)：`hminor` 护栏已加。** `Gauss/IBP.lean` 的 `condExpDiag_stochDom_of_pieces` 加了 `@[deprecated "RETIRED (T112/T202): …"]`——`hminor` 在对角 `k = i` 处断言的量是涨落 `−(1−E_i)(G_ii−m)`，尺度 `Ψ` 而非 `Ψ²`，故假设不可满足、定理空真。活的入口是 `condExpDiag_stochDom_of_localLaw`（`Gauss/CondDom.lean`，只要对角外的 `hminor`）。全仓无 Lean 调用点，加护栏不产生新 warning；声明保留只因 `blueprint/src/content.tex` 引了它。

**未闭合（T202 顺手查到，不在本单范围）**：`RBM.Bounds` 的居民只有 `Flow/Iteration.lean:165 Bounds_zero`（`s ≡ 0` 处），**`s > 0` 的居民仍无**——归 T204 / T205。

## ⭐ T203：`hKb` 在所有环长上装配完毕，(2.59) 的接缝缝上了（`Gauss/Lemma514Holder.lean` 续，1071 → 1321 行，2026-09-21）

`hKb` 从**假设**变成了**定理**（`hKb_flow`），所以「`hKb` 空真」这个风险从结构上消失。端到端探针 `lemma514_forall_of_hHol_flow` 与新的 `flow_sharpLmK_of_hHol_flow` 的假设表里都**没有 `hKb`**（后者连 `hHol` 也没有）。

**工单的猜测成立**：`Flow/Iteration.lean:598 norm_Kval_le` 确实只差接线，**没有数学缺口**，`η` 的幂对长度 ≥ 3 是够的。但形状有一处**真差别、必须显式付**：

* `norm_Kval_le` 给 `C_n·(Wℓ_wη_w)^{−(n−1)}`，`hKb` 要 `≤ N^c`。压过去要 (a) `(Wℓ_wη_w)^{−1} → η_w^{−1}`（靠 `W ≥ 1`、`ℓ̂_w ≥ 1`），(b) `η_w^{−1} → η_{t_N}^{−1}`（`η_u = (1−u)·Im m` 反单调），再用 `hreg`。
* **代价是指数从 `c` 变成 `c·m + 1`**（每条边一个 `N^c`，`+1` 吞常数 `C_n`）。这不是记账错误、是真实的归一化差额；无害是因为 `hreg`/`hXΞ` 对 `c` **单调变弱**，两条探针内部把调用者给的 `c` 抬到 `c(n+2)+1` 再喂 `hHol_flow`，**对外签名不变**。
* 每条长度各有自己的 `C_n`，所以先要 `exists_norm_Kval_le_upto` 取 max——`hKb` 量化在一个长度**集合**上，不是单个长度。

**冻结签名的改动（两条，是去掉一条假设、不是弱化结论）**：`lemma514_of_hHol_flow` 与 `lemma514_forall_of_hHol_flow` 的 `hKb` 参数**已删**，内部由 `hKb_flow` 产出。两条全仓无外部消费者，故没留带撇版。`hHol_flow` 本身不变。

**与 T201 的边界干净**：全程**没有用到**短窗口条件 `t_N − s_N ≤ κ(1−t_N)`（T195 判为在总装窗口上不可满足），`s` 在整条链上根本不出现，`0 < s N` 也没用到。

**可满足性见证 `exists_hHol_flow_inputs`**：一次性造出**同一个 `c = 2`** 下的全部输入（`hreg`、`hXΞ`、导出的 `hKb`），取**临界标度**而非退化点——`t_N = 1 − (N ∨ 1)^{−1}`，即 `η_{t_N} = N^{−1}·Im m`（论文 `t ≤ 1 − N^{−1+τ}` 允许的最小尺度，只差 `N^τ`），`ℓ̂_{t_N} = min(N^{1/2}, L)` 真的在长，窗口不塌缩。**包络若差一个 `W` 或 `L` 的幂，这个见证就造不出来。**

**仍在假设表里的**：`hrhs`（含 `hnum` + `edgeKer` 行和）→ **T201**；`MomentDuhamel.Hyp` 的 `H` → T191/T196/T206；Step 3 的 `h0/h12/h1/h2`、`Cond272` → 不在本单范围。

**`Lemma514Moment.lean` 的接线清单是空的**：`hKb` 从来没出现在那个文件里。T192 的旧记载仍成立——`lemma514_forall_of_momentDuhamel` 的 `(K,γ)` 排在 `∀ m` 前面、要不到；`lemma514_forall_of_hHol_flow` 逐 `m` 组装已绕过。

**待 T201 接线**：`hkerC_flow` / `hker2C_flow`（`Lemma514Holder.lean` 约 1240–1270 行）的 `@[deprecated]` 护栏——T203 收工时 T201 的文案还没到，按工单指示没动。

## ⭐⭐ T204：不含 (2.71) 的 Theorem 2.21（`Flow/Thm221NoEL.lean`，747 行，2026-09-21）

**没有造 `BoundsCore″`**：`Flow/Hypotheses.lean` 里的 `RBM.BoundsCore` **就是**「(2.71) 删掉」的那个包，`BoundsCore_of_Steps` 也已经是「不用 Step 6」的那一半。缺的只是定理和迭代——按「造轮子之前先查」直接复用。

落地的：`Thm221NoEL`（收 D13 的 `Cond272Reg`）、`Thm221NoEL'`（收 `Cond272'`）、Lemmas 2.18–2.20 **去掉 (2.62)** 的重跑、(2.61)、Theorem 2.3 全条、**Theorem 2.4 的 (2.6)(2.7)**。结论**一字未改**——8 条 `rfl` 探针逐条验了 `localLaw_of_bounds hB = localLaw_of_boundsCore hB.toBoundsCore` 等，以及 `localSemicircleLaw_of_Thm221' = localSemicircleLaw_of_Thm221NoEL'`、`quantumDiffusion_of_Thm221'` 的第 1、2 个合取 = `quantumDiffusion_pm_pp_of_Thm221NoEL'` 的两项。(2.8)(2.9) 与 Theorem 2.5 仍吃 `Bounds.expect`，**没有挂到空假设上**（归 T205）。

**可满足性（本单风险最高的一条）**
* 正向见证 `boundsCore_gauss_witness` 用 T202 刚落地的 `Gauss.Dims.exampleGrow`（`L ≍ N^{1/4}`、`W ≍ N^{3/4}`），证 `BoundsCore (Gauss.sample exampleGrow) 0 0` **并且** `∀ᶠ N, N^{1/2} ≤ scale`——右端真的是 `≺ N^{−n/2}` 而不是 `≺ 1`，**不是退化的 0**。
* 联立检查 `Band.cond272Reg_grid`：`τ′, c > 0, n₀` 先于 `E, t` 选定，网格 `u_k = min(1−W^{−kτ′}, t)` 的**每一步**都满足 `Cond272Reg`，且都在 D13 的窗口 `t ≤ 1−N^{−1+τ}` 里。**T195 挂掉的正是这类联立。**
* `BoundsCore` 三个字段全是 `StochDom`/概率型，**没有 `∀ ω` 字段**——T164 的 `ω = 0` 缺陷在这里结构上不可能发生。
* 诚实边界：`Thm221NoEL(')` 自身的见证 = 证明 Theorem 2.21，够不着；树里已有的 `Thm221`/`Thm221'`/`Thm221Reg` 同理，**不是本单新增的洞**。

**⚠ 更正 T204 工单文本**：工单写「`Cond272Reg`（(2.72) 逐字 + `t ≤ 1 − N^{−1+τ}`）」。树里 `Flow/Thm221Bare.lean` 的实际定义是 `Cond272Reg B E s t c := Cond272 B E s t ∧ ∀ᶠ N, N^c ≤ B.scale E N (t N)`——第二项是**尺度下界**（Step 1 自带的 `hreg`），时间窗是**应用侧**产生它的来源。已按树里实际定义收口，并把「窗口 ⇒ 下界」编译成 `Band.eventually_rpow_le_scale`。

**⚠ 更正 T176**：「`Bounds → Steps` 差 10 条具名假设」在 Steps 1–5 这半边现在是 **6 条**（`Step1.Hyp`、`MomentHypCut`、`hΘ`、`Lemma514`、`Eq45Flow`、`FlowEq548`）；`EntryBoundFlow`/`DiagBoundFlow` 已被 `Step1.Hyp.lemma41` 吸收（T107/T183），`MomentHyp` 已由 T197 的 `MomentHypCut` 取代。

**⚠ Theorem 2.2 全仓没有组装**：`Delocalization.lean` 只有确定性内核，概率一半的输入是 `EnergyUniform.lean` 的 `localSemicircleLaw_of_Thm221N_of_z`。所以 T204 对下游「改吃 `Bounds″`」这一条**无事可做**——真正的组装归 T199。

## ⭐⭐ T209：Steps 2–5 改吃 `Cond272Reg`，`Thm221NoEL`（不带撇）落地（2026-09-21）

**`RBM.Thm221NoEL` 有生产者了**：`RBM.thm221NoEL_of_inputs`（`Flow/Thm221NoEL.lean` §5b）。
`lake build RBM1D` exit=0，审计 `10780 declarations in RBM, all within [propext, Classical.choice, Quot.sound]`。

### 桥确实不存在，但根本不需要桥

T204/T186 记的缺口是「`Cond272Reg → Cond272'` 的桥在 `(a,b) = (1,30)` 处零增益」。**桥确实造不出来，这一点没变**
（`rpow_mul_rpow_le_of_pow_thirty` 要 `e/c + b/30 ≤ a`，`a = 1, b = 30` ⇒ `e ≤ 0`）。
本单的做法是**不造桥**，而是把三个消费者里 `hregS` 的**实际用途**逐个拆开——结果是**一处都不需要增益**：

| 消费者 | `hregS` 实际用在哪 | 替代 |
|---|---|---|
| Step 1 `Step1.step1` | 本来就是 `Cond272` + `N^c ≤ A_t` | 无需改动，`Cond272Reg` 逐字 |
| Step 2 (2.76) `aprioriDecay_cut` | 只经 `Step2.cond272_of_strict` 取 `Cond272` | `StepGlue.aprioriDecay_of_jS_of_cond272` |
| Step 2 弱律 (2.74) | 本来就是 `Cond272` + `N^c ≤ A_t` | 无需改动 |
| Step 2 局部律 (2.75) `Step2.localLaw` | 只经 `Step2.eventually_R4_le_scale` 取两条标度事实 `(η_s/η_u)^4 ≤ A_u`、`N^c ≤ A_u`——**指数是 4，不是 30** | `StepGlue.eventually_R4_le_scale_of_cond272` + `StepGlue.localLaw_of_scale_facts` |
| Steps 3–5 胶水 `flow_sharpLoop_glue_of'` / `flow_steps45_glue_of'` | 只经 `cond272_of_strict` 取 `Cond272` | `Step2PP.flow_sharpLoop_glue_of_cond272'` / `flow_steps45_glue_of_cond272'` |
| Steps 3–5 算术侧条件 `harith_flowAs` | `Q^{30} ≤ A_t`（裸 (2.72) 取逆）**加** `4 ≤ A_t^{1/12}`（区制界）——两条都是 `Cond272Reg` 的分量 | `Step2PP.harith_flowAs_of_reg` |

⚠ **更正 T209 工单**：工单写「把三个消费者改成吃 `Cond272Reg.hA_phi` / `hA_betaStar`」。
**那两条在这条链上一次也没被用到**——它们是**矩路线**的侧条件（`phi_arith'` / `beta_star_margin`，
即假设 `MomentDuhamelCut.MomentHypCut` **内部**的事），而 Steps 1–5 的装配把 `MomentHypCut` 当黑箱吃。
所以 **T209 不消耗 `δ` 预算**（T186 的 `δ ≤ c/4` 仍只是矩路线生产者的事，归 T212/T214）。
T207 的 `phi_arith_second_pass` 同理不在本链上。

### 新增声明（15 条，全部 `[propext, Classical.choice, Quot.sound]`）

* `Hierarchy/StepGlue.lean`：`StepGlue.eventually_R4_le_scale_of_cond272`、
  `StepGlue.aprioriDecay_of_jS_of_cond272`、`StepGlue.localLaw_of_scale_facts`
* `Hierarchy/Step2PP.lean`：`Step2PP.harith_flowAs_of_reg`、`flow_sharpLoop_glue_of_cond272'`、
  `flow_steps45_glue_of_cond272'`、`flow_sharpLoop_glue_flowAs_of_cond272'`、
  `flow_steps45_glue_flowAs_of_reg'`
* `Gauss/MomentDuhamelCut.lean`（**只追加**，T210 只读，一个字没删）：
  `MomentDuhamelCut.aprioriDecay_cut_of_cond272`、`MomentDuhamelCut.step2_cut_of_reg`
* `Flow/Thm221NoEL.lean` §5b：`boundsCore_step_of_flow_reg`、`boundsCore_step_of_inputs_reg`、
  **`thm221NoEL_of_inputs`**、`Thm221NoEL.step_boundsCore_reg`、`cond272Reg_grid_step_domain`，
  外加一条 `rfl` 探针（`Eq` 逼两条路线的结论是同一条陈述，T107 技法）

**旧签名一字未动**：`Cond272'` 形的 `step2_cut`、`flow_sharpLoop_glue_flowAs'`、
`flow_steps45_glue_flowAs'`、`thm221NoEL'_of_inputs` 全部原样保留（`Thm221NoEL'` 仍由它们产出，
`BoundsCore_of_Thm221NoEL'` 的归纳仍跑在带撇版上——网格直接给 `Cond272'`）。

### 验收探针

* **假设表无 `Cond272'`**：`#check @RBM.boundsCore_step_of_inputs_reg` 与
  `#check @RBM.thm221NoEL_of_inputs` 打印出的类型里 `Cond272` 只出现 `Cond272Reg` 一种形式（7 处），
  `Cond272'` **0 处**。从 `BoundsCore X E s` 到 `BoundsCore X E t`，六条具名假设与 T204 完全相同
  （`Step1.Hyp`、`MomentHypCut`、`hΘ`、`Lemma514`、`Eq45Flow`、`FlowEq548`）。
* **可满足性见证**：`RBM.cond272Reg_grid_step_domain`（新增）。走**论文自己的网格**
  `u_k = min(1 − W^{−kτ′}, t)`（`Band.cond272Reg_grid`，即 `1 − s_k = W^{−kτ′}`），
  把一个 step 的**四条**域条件 `0 ≤ u_k`、`u_k ≤ u_{k+1}`、`u_{k+1} < 1`、`Cond272Reg … c`
  **同时**证出来，`τ′, c, n₀` 在 `E, t` **之前**选定，且带 `gridT … n₀ = t` 那一条
  （窗口不塌缩，网格真的走到 `t`）。
* **反向对照保留**：`Cond272'` 形的 `Thm221NoEL'` 与链 `Cond272' → Cond272Reg → Cond272` 仍在树里；
  `exists_cond272_not_rpow_le_scale`（T186）证 `Cond272Reg` 严格强于 `Cond272`，
  `Cond272'.toCond272Reg` 证它严格弱于 `Cond272'`——三档没有一档塌成同一个。
* **量词次序**：`c` 量化在 `Thm221NoEL.step` **内部**（paper-deltas #125：网格给的 `c` 上界约 `τ/16`），
  每条假设内部的渐近条件都是 `∀ᶠ N in atTop`。
* **退化检查**：`s = t` 时 `Cond272Reg` 仍要 `N^c ≤ A_t`，不塌成平凡（`cond272Reg_zero` 是 `s = t = 0`
  处的非退化见证，`A_0 = W·Im m ≥ N^{1/2}`）。`BoundsCore` 三个字段全是 `StochDom` 型，无 `∀ ω` 字段。

### 本单没做的

* **`Hierarchy/Step2.lean` / `Hierarchy/Step2Moment.lean` 的原版没改成一行推论**：不在 T209 的可写文件集里。
  `StepGlue.localLaw_of_scale_facts` 与 `StepGlue.aprioriDecay_of_jS_of_cond272` 是
  `Step2.localLaw` / `Step2Moment.aprioriDecay_of_jS` 的**严格更一般**重述，证明脚本逐字照抄。
  下次动那两个文件的单应把原版改成一行推论（纯机械，**无主**）。
* **`Thm221NoEL` 的六条具名假设仍无生产者**——与 T204 相同，归 T210/T212/T213/T214/T215/T216。
* `Flow/EnergyUniform.lean` 的 `Cond272N` 侧没有对应的 `Reg` 形（归 T199 续单，**无主**）。
* blueprint 节点未补 `\lean{}`（本单新增的全是 Lean 内部重述，无对应论文编号节点）。

### paper-delta

`T209a`（临时号）：**更正 #125** 的「§2.7 六步全链要 `N^c` 增益」那半句——六步只要 (2.72) 逐字
加区制界（= `Cond272Reg`，#132/D13）。#125 的「`c` 必须量化在 `step` 内部」仍成立。

## ⚠ 无主的活（T204 交出，点名到字段级）

1. ~~**`Thm221NoEL`（`Cond272Reg` 形）产不出来**~~ **已由 T209 收口（2026-09-21）**：见下面「T209」一节。`RBM.thm221NoEL_of_inputs` 产出不带撇的 `Thm221NoEL`，假设表里无 `Cond272'`（`#check` 探针验过）。**更正原记载**：收口**不是**改成吃 `Cond272Reg.hA_phi`/`hA_betaStar`——那两条是**矩路线**（假设 `MomentHypCut`）的侧条件，本链一次也没用到；真正要做的是把三个消费者里 `hregS` 的**实际用途**拆开（见下节）。
2. **`Flow/Consequences.lean` 的改吃 `BoundsCore`**（机械：`hB : Bounds …` → `hB : BoundsCore …`，**证明脚本一字不动**；T204 文件里已有逐字副本 + `rfl` 探针作模板）。应改的：`localLaw_of_bounds`、`loop1_of_bounds`、`partialTrace_of_bounds`、`trace_of_bounds`、`loop2_of_bounds`、`quantumDiffusion_pm/pp_of_bounds`、四条 `*_prob_of_bounds`、`localSemicircleLaw_of_Thm221` 整条，以及把 `quantumDiffusion_of_Thm221` 的**前两个合取**拆成独立定理。**不许动**：`expect_loop2_of_bounds`、`expect_quantumDiffusion_*`、`QDExpect.of_Thm221*`、`theorem2_5_of_Thm221*`（都要 (2.71)，归 T205）。**没有单负责。**
3. **`Flow/EnergyUniform.lean` 的 `BoundsCoreN` 版**（`localSemicircleLaw_of_Thm221N*` 与 `*_of_z`）——Theorem 2.2 路线 (ii) 将来要吃的。归 T199 或其续单。
4. **`RBM.Bounds` 在 `s > 0` 处仍无居民**（T202 查出；只有 `Flow/Iteration.lean:165 Bounds_zero`）。`BoundsCore` 这一侧已由 `boundsCore_gauss_witness` 解决，**带 `expect` 的那一侧没有**。归 T205。

## T200：`docs/REPORT.md` 已起草（537 行，活文档，2026-09-21）

九节：主定理清单（Lean 名 + 完整假设表 + ①无条件/②化归/③空着）、六步链现状、外部输入声明、公理审计、**没有生产者的具名假设（点名到字段级）**、方法学附录（空真与 fiat 两张风险清单）、paper-deltas 索引、探针清单、待定夺。

**数据纪律**：每一条「Lean 名 + 假设表 + 有没有生产者」都是 **scratchpad 里编译探针打印出来的**，不是从 STATUS/TASKS 的叙述里抄的。基准快照 `HEAD = 2bde09d`；协调者已在文件头补记 T202/T203/T204 落地后的变化。

**T200 的一条方法学发现（值得进 playbook）**：按「结论头常量」找生产者的元程序对 **`def` 形状**的假设有**假阴性**——五条 `*Flow` 被误报为无生产者，实际是定义展开。所以 `def` 一律要用**裸 `:=` 探针**逐条核（`T200Defeq.lean` 把 Step 1/2/3/4-5 的结论喂进四个槽，四条全过）。

**T200 如实写明它没做的**：① 没读论文 PDF，凡「论文是否真这么写」均转述 STATUS/paper-deltas；② 没跑 `lake build RBM1D`（九个 agent 并发）；③ 没对**全部** `def` 形状假设做裸 `:=` 逐条核（只核了六步链上的五条 + 八条）。

## 待 Jun 定夺：R1–R5（T200 交出，2026-09-21）

* **R1（报告口径）**：Theorems 2.3/2.4/2.5 目前全是「吃 `Thm221` 的化归」。最终报告是把它们**并列为主定理**（附「以 Theorem 2.21 为前提」），还是**只把 Theorem 2.21 与 Lemmas 2.18–2.20 列为成果**、2.3–2.5 作为推论一并陈述？两种写法给读者的印象差别很大。
* **R2（Theorem 2.6 的范围）⭐**：`DBMUniversality` 与 `GreenComparison` 按 Jun 的永久规则**都要改形状**（前者重写成逐字的 [51] Theorem 2.2 复 Hermitian 形式、量化在所有满足其前提的模型上；后者改为自证）。是否在本轮范围内？在它们完成之前，报告 §3「外部输入声明」只能写「待定」。**（Cowork 2026-09-21 07:50 报过同一问题，至今未见裁定。）**
* **R3（`OUFlow` 的保真）**：现有 `OUFlow` **未钉死分布**，常值流使 Theorem 2.6 的三条假设**全部平凡**（fiat）。是现在就钉死 `H_t := e^{−t/2}H + (1−e^{−t})^{1/2}G`，还是等六步完成？**在钉死之前，报告不能把 `theorem2_6_of_steps` 算作 Theorem 2.6 的形式化。**
* **R4（Step 6 与 D12/D13 的联动）**：**已被 D12/D13 回答**（选 (a)，T204 今日落地第一遍）。剩下的是 Step 6 样本侧四个好集（`FDInputs`/`QuadInputs`/`EGInputs`/`DriftInputs`）的开单时机——按 D12 归 T205。**此条可视为已裁定，留档备查。**
* **R5（否定结论怎么呈现）**：`LDENetClose` 按字面不可证、`MinorGood` 恒假、`MomentHyp.step` 在冻结形状下不可证、裸 `Cond272` 不够——四条都**编译成了定理**，是本项目的真实产出。最终报告单列一节（「形式化查出的论文/草图缺陷」）还是只作脚注？T200 建议单列；涉及论文措辞，请 Jun 定。

## ⭐⭐ T207：(5.47) 锐化到 `(η_s/η_u)²` —— **两次幂不是丢了，是从来没取出来过**（`Hierarchy/Step2Near47.lean`，939 行、38 条，2026-09-21）

**第 0 步的答案：工单列的三个候选一个都不是机制。**

* **(a) `⁴` 是 bootstrap 的归一化，不是估计的损失。** `Hierarchy/Step2Moment.lean:150` 的 `jSnorm := Step2.jS / ratR^4` 把 (5.29)/(5.43) 的**先验门槛** `(η_s/η_u)^4` 写死进整条链（`MomentHypCut.cut` → `stochDom_jSnorm_cut` → `jS_stochDom_cut`）。证出 `J* ≺ (η_s/η_u)^4` 就是论文那句「hence `P(T ≤ t)` is negligible」。**论文的 (5.47) 是同一条一步界的第二次读法**（p.58），**仓库从来没做这第二次读**。
* **(b) 记账层唯一真是 `R⁴` 的那一项是 `phi_arith'` 的 `t4`**（`Step2MomentStep.lean:158–161`）：它把 (5.41) drift 近场的两个 `u`-依赖因子 `(η_u/η_t)²` 与 `(ℓ_u/ℓ_s)³` **分开各取上确界**。其余六项（(5.39) 初值、(5.40) 两项、(5.41) 两个远场、(5.45) 鞅）已经是 `R²` 或 `O(1)`。
* **(c) ⚠ 更正工单候选 ①**：`integral_nearInt_le` **做了，但积的是另一条积分，而且全仓无消费者**——它积的是 **(5.44) 二次变差**的被积函数（预算本来就是 `R⁴`，开方给 (5.45) 的 `R²`，已经对）；**(5.41) 的 drift 被积函数从来没被积过**。顺带查到 **`phi_arith'` 本身也没有消费者**，整个记账层与 `CutHyp.moment` 字段是断开的（T132c 留下的形态，本单没有改变它）。
* **(d) 候选 ②③ 都不是**：T174 说的「(5.36) 的 `(ℓ_u/ℓ_s)^{3/2}` 在 (5.44) 的积分里免费」属实；`η_s/η_t` 与 `η_s/η_u` 没有混用，后者是子窗口读法、**更强**，方向有利。

**补齐的办法**：把 (5.41) drift 近场**联合积分**。机制与 (5.44) 那条**相反**——`nearInt` 关于 `η_u` 单增（sup 在左端，sup×长度够用），而 drift 的被积函数 `= η_u^{−1/2}η_s^{3/2}η_v^{−2}` 关于 `η_u` 单**减**，sup×长度只给到 `m⁻¹R^{5/2}`（`sup_mul_len_driftNearInt_eq`），**还差半个幂**；必须真做原函数 `∫(1−u)^{−1/2}du = 2(√(1−s)−√(1−v))`，做完是 `2m⁻¹R²`（`integral_driftNearInt_le`）。

**核心结论（`phi_arith_second_pass`）**：**只改 `t4` 一项、`J*` 仍停在已建立的 `x⁸R⁴` 先验水平，输出就已经是 `R²`——不需要第二次 bootstrap。** 唯一代价是两个远场边条件从 `β* = 5.5/4.5` 变成 `9.5/6.5`，而 `second_pass_side_conditions_of_reg` 证明它们由 (2.72)+增益在**同一个 `4δ ≤ 2c`** 下给出。**锐化在指数预算上是零成本**；近场那一行反而从 `β* = 4`（零余量）降到 `β* = 2`。

**可满足性**：`phi_arith_sharp_flow` 把 `qI` 取成**真实积分** `∫_s^v driftNearInt`，近场假设由 `integral_driftNearInt_le` 兑现——**不是假设 `R²` 而是算出 `R²`**（主要的反 fiat 见证）。非退化：`driftNearInt_pos`（被积函数严格正，预算不是靠零被积函数满足）、`sharp_lt_blunt`（`R > 1` 时 `R² < R⁴`，是真增益）、`jSnorm2_left`（`u = s_N` 处两种归一化重合，**初值条件一字未加强**，(2.69) 原样）。**否定结论也编译了**：`crude_exceeds_budget`——`R > 4` 时分开取 sup 严格超预算，**那两次幂是真花掉的**，不是记账产物。

**`flowEq548_of_near_far` / `_farInputs` 一字不用改**：`hnear` 槽由 `hnear_sharp` 填，`flowEq548_of_sharp_farInputs` 是现成的一行封装。

**未闭合**：`MomentHypCutSharp.cut` 仍是具名假设，与 T197 的 `MomentHypCut.cut` **同级**（本单证了它**不比钝版要求更多**，`jSnorm_le_jSnorm2`）——归 `CutHyp.moment` 的生产者那条线。

## ⚠ 无主的活（T207 交出）

**`MomentDuhamelCut.CutHyp` 的 `Θ : ℕ → ℝ` 要推广成 `Θ : ℕ → ℝ → ℝ`。** 真正的「第二遍」接口现在**表达不出来**：`phi_arith_second_pass` 说第二遍只要钝版前缀，那么正确接口应是「截断水平取自钝版结论、结论关于 `jSnorm2`」的 `CutHyp`，而钝版水平换算到 `jSnorm2` 单位是 `N^{2δ}(η_s/η_u)²`，**带 `u`**；现有 `Θ` 没有 `u`-依赖。推广后能把 T207 §3 的那条假设**彻底去掉**（数学上已经证完）。**没有单负责。**

## T207 给 `Step2MomentStep.lean` 的文档接线（等 T208 交出后由协调者做）

`Step2MomentStep.lean` 当时在 T208 手里，以下只是文档指针，**不删任何东西**：
1. `phi_arith'`（:104）、`phi_lt_threshold`（:933）——无消费者，加 `See also Step2Near47.phi_arith_second_pass` / `phi_lt_threshold_sharp`。**不建议删**：它们仍是钝版路线诚实的记账。
2. `integral_nearInt_le`/`nearInt_le`/`coarse_sq_ge`（:307/:343/:378）——全仓无消费者，**不要删**（是 (5.44) 二次变差的预算与其锐性）；但文件头第 32 行那一格应改成「这是 **(5.44) 二次变差**的近场积分；(5.41) **drift** 的孪生积分在 `Step2Near47.integral_driftNearInt_le`，机制相反，**那一条才是两次幂的所在**」。
3. `hq_of_ratio`（:194）保留加说明；`side_conditions_of_reg`（:442）的 `.2.1`/`.2.2` 被 `sharp_side_conditions_of_reg` **原样复用**（这就是「指数表没动」的编译证据）。
4. `jS_stochDom_cut`/`Step2Moment.jS_stochDom` **不要 deprecate**——`jS_stochDom_of_sharp` 证明锐版逐字蕴含它们，`aprioriDecay_of_sharp` 证明同一假设束也供得起 (2.76)。

---

## ⭐ T208：(5.48) 的漂移钉死了；`cFarStep ≺ 1` **按 T198 的形状为假**，修正形 `cFarStep' ≺ 1` 已证（新建 `Hierarchy/Step2FarInputs.lean`，917 行，2026-09-21）

`lake env lean RBM1D/Hierarchy/Step2FarInputs.lean` exit=0；`lake build RBM1D` exit=0，审计 **10635**（本文件尚未进 `RBM1D.lean`，import 待协调者加；20 条声明逐条 `#print axioms` 干净）。**`Hierarchy/Step2MomentStep.lean` 一字未动**（T207 在只读引用它；本单不需要改它，见下）。

### 1. fiat 审计：T198 的 `FarInputs` 里漂移**确实是自由字段**
`FarInputs` 的形状是 `∀ v, ∃ F Fn : ℝ → LoopArg L 2 → ℂ, ∃ Mrt, …`——`F`（漂移）、`Fn`（近场部分）、`Mrt`（鞅）**三个都是自由张量**，所以 `farInputs_of_remainder` 能取 `F = Fn = 0` 把一切塞进 `Mrt`。逐字段：

| `FarInputs` 字段 | T198 | `FarInputs'`（本单） |
|---|---|---|
| Duhamel 恒等式 (5.21) | 对自由 `F`、`Mrt` 断言 | **定义**：`farMart` 就定义成 Duhamel 亏量，恒等式是 `ring` |
| 漂移 `F` | 自由 | **钉死** `farDrift = DriftDef.driftF`（`n = 0`, `σ = (+,−)`），`= eGpm + primBil(L−K,L−K)`（`farDrift_eq_eGpm_add_quadGlue`），且 `= MomentDuhamel.Hyp.Fpath`（`Fpath_eq_farDrift`） |
| 近场部分 `Fn` | 自由 | **定义**：`farDriftNear` = `farDrift` 在 `‖b₁−b₂‖ ≤ ℓ*_u` 上的限制，所以两条漂移条件是对 `farDrift` 本身在两个区域上的陈述 |
| 鞅 `Mrt` | 自由 | **定义**：`farMart` = 亏量（假设只剩「亏量小」，即 (5.20)+(5.45) 合成一条，严格弱于分别假设两条） |
| (2.69) 初值 | 关于 `Step2.lk` | 同 |

**反 fiat 证书（编译过）**：`farDrift_eq_zero_of_farInputs'_zero`——`M_n = M_f = 0` **迫使模型自身的漂移在 `[s,t)` 上恒为 0**。T198 的包没有这个性质（`farInputs_of_remainder` 对任意样本都能取 `M_n = M_f = 0`）。

### 2. ⚠ 核心否定结论：**`cFarStep ≺ 1` 按 T198 的形状不成立**
`cFarStep = Ξ(M_i + M_f) + M_m + 1`，其中 `M_f` 是 (5.35) 远场前因子在 `u ∈ [s,v)` 上的 **sup**。(5.35) shape 2（`EGDef.eGpm_le_reduced`）的前因子是

`η_u^{-1}( c_far (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} J* + 169 (ℓ_u/ℓ_s) A_u^{-1} (J*)^{3/2} )`，

`η_u^{-1}` 在 `u = s` 处是 `η_s^{-1}`，最大到 `N^{1−τ}`，**不是 `N^{o(1)}`**。真正 `≺ 1` 的是**时间积分**：`step_bound_far` 把 `∫_s^v du` 放成 `sup_u × |v−s|` 之后**又把 `|v−s| ≤ 1` 扔掉**，而 `|v−s| ≤ 1−s = η_s/Im m` 恰好抵消 `η_s^{-1}`（`etaT_inv_mul_one_sub`：`η_u^{-1}(1−u) = (Im m_E)^{-1}`，常数）。

两条编译过的对照：
* `cFarStep'_detDom_critical`：在**临界标度** `M_f N = N+1`、`1−s N = 1/(N+1)`、`M_i = M_m = 1` 上，`cFarStep' ≺ 1` **成立**；
* `cFarStep_not_detDom`：同一组数据上 `cFarStep ≺ 1` **为假**（用 `1 ≤ Ξ`，即 `one_le_xiK`）。

`s = 0` 时两者逐字相等（`cFarStep'_eq_cFarStep`），所以 **T198 的 §11 不是错的，只是只在 `s` 远离 1 时可用**——而 Lemmas 2.18–2.20 的网格 `1−s_k = W^{-kτ'}` 正是 `s → 1`。记 paper-delta **T208a**。

### 3. 交付（`RBM1D/Hierarchy/Step2FarInputs.lean`，6 节）
1. `farDrift` / `farDriftNear` / `farMart`（定义）、`farDrift_duhamel`、`farDrift_eq_eGpm_add_quadGlue`、`Fpath_eq_farDrift`；
2. `step_bound_far'` / `lkErr_far_le'`——`step_bound_far` 保留区间长度 `len`，且**鞅界只在用到的那个远场 `a` 上要求**（T198 要求在所有 `a` 上，配 `M_m ≺ 1` 按字面不可满足，记 **T208b**）；
3. `FarInputs'`（**无任何存在量词**）、`cFarStep'`、`FarResidue'`、`far_le_of_farInputs'`、`stochDom_far_of_farInputs'`、**`flowEq548_of_farInputs'`**（产出 `Step45.FlowEq548`）、`farInputs_of_farInputs'`（把钉死的三个对象喂进 T198 的包）;
4. **`eventually_xiK_le`：`Ξ ≺ 1` 是定理不是假设**（只用 `W L ≤ N`、(2.2)、`N ≤ W²`，与流无关）；`detDom_cFarStep'`：`cFarStep' ≺ 1`；4b. `flowEq548_of_farInputs'_detDom`——端到端，`hpoly` 不再是假设；
5. `farInputs'_of_eG_of_quad`：两条漂移输入由 **(5.35)（`eGpm`）+ (5.34)（`primBil` 二次粘合项）** 逐项产出——漂移只有这两项，所以这就是全部输入；
6. `farDrift_eq_zero_of_farInputs'_zero`、`etaT_inv_mul_one_sub`、`cFarStep'_detDom_critical`、`cFarStep_not_detDom`。

### 4. 没做的部分（**要点名接手人**）
* **`M_m ≺ 1`（(5.45) 的远场鞅界）仍是假设**——要 BDG，属随机层（CLAUDE.md 规则 6）。`FarInputs'` 的第四条就是它，左端是钉死的 `farMart`。**无主**。
* **`M_i ≺ 1`（(2.69)）**由 Step 1 给，`FarInputs'` 直接收。
* **`M_f(1−s) ≺ 1` 还没从 `eGpm_le_reduced` 机械地推出来**：`farInputs'_of_eG_of_quad` 把它化归到「`‖eGpm‖ ≤ M_gf·T` 且 `‖primBil‖ ≤ M_qf·T`（远场）」，但把 `eGpm_le_reduced` 的右端（含指示函数项与 `(r/(ℓ_uη_u))·L·ρ` 余项）整理成这个形状、并核出 `M_gf(1−s) ≺ 1` 的显式指数账，**本单没做**。建议开新单，输入是 (2.72)/(2.73) 与 `J* ≺ (η_s/η_u)²`（T207）。
* **把一步界改成带 `L¹` 权的积分形**（`∫_s^v η_u^{-1}du = (Im m)^{-1}log R`）可以彻底去掉 `1−s`，与论文字面一致；需要漂移的可积性假设，**本单没做**（T208a 已记）。
* **没动 `Step2MomentStep.lean`**：里面没有按字面为假的陈述（`cFarStep` 是定义，`flowEq548_of_near_farInputs` 在 `s = 0` 可用），加 `@[deprecated]` 会在该文件内部产生约 8 条弃用警告、干扰正在只读它的 T207。守卫以**定理**形式放在 `Step2FarInputs.lean`（`cFarStep_not_detDom`），`grep -rn "cFarStep"` 一定命中。

## ⭐ T206：φ′ 识别成钉死的 `driftF`、桥是等式定理——但 **`momentDuhamelHyp_gauss` 仍不存在**（`Gauss/MomentDuhamelHypGauss.lean`，741 行、19 条，2026-09-21）

**第 (1) 步（φ′ 的识别）与第 (3) 步（桥）全部落地。**

* `hasDerivAt_ukerObsT_drift`：`(∂_u + 𝓛)(U_{u,t}∘(L−K)_u)_a = (U_{u,t}∘F_u)_a`，**`F` 逐字是 `DriftDef.driftF`（T58 的定义），不是自由张量、不是 `Hyp` 的字段**；`K` 被 `hKdef` 钉在 `B.Kval`，`∂_uK` 被钉在 `Kprim = primRhs`。两侧都没有可选数据。
* `timeD1_add_genMomentPt_le_driftF`：(5.20) 的**逐点被积式**，常数正是定 `cMDval` 的那两个。
* `ukerObsT_eq_Uker_lkFun` / `momentObsT_flow`：`momentObsT ↔ Uker∘lkT` 是**等式定理**，不是假设。

**一处数学要点（防 fiat 的地方）**：`genMomentPt_le` 在最后一步就把 `Re(F̄𝓛F)` 放成 `‖F‖‖𝓛F‖`，**对矩路线早了一步**——时间导数另出一项 `Re(F̄∂_uF)`，两项必须**先相加再取模**，那正是 `∂_uΨ₁ = U∘(L−K)′ − U∘Θ_u(L−K)` 里的 `Θ` 与漂移恒等式里的 `genS` 相消的位置（`genS` 与 `ThetaOp` 定义相等）。分开放缩会留下 `U∘Θ(L−K)`，**它不小**。故新证 `genMomentPt_le_re`。

**可满足性**：`hasDerivAt_ukerObsT_drift_flow` / `timeD1_add_genMomentPt_le_driftF_flow` 取**全开区间** `0 ≤ u < 1`、`0 ≤ v < 1`（允许 `v ↑ 1`，不是退化点）；退化检查 `hasDerivAt_ukerObsT_drift_at_zero` 证 `ω = 0`（流矩阵 `0`、`G = −z⁻¹`）处恒等式**照样成立且有内容**——T164 事故要求的同形检查。

## ⚠⚠ 更正 T206 工单：它少点名了两项，所以 `Hyp` 还差三块不是一块

工单说「余三步」做完就能交 `momentDuhamelHyp_gauss`。**不对。** 除第 (2) 步外还有两项工单没点名，实例**仍不存在**：

1. **第 (2) 步（边界可积性）——仍属本条线，一条都没做。** `momentIneq_of_derivBound` 每个 `(p,N,σ,v,a)` 要八件东西，T206 只给了最后一件（逐点不等式）与桥。缺的五件：`ψ` 的窗口界、`u ↦ E|Ψ₁|^{2p}` 的 `ContinuousOn`、`φ′` 的区间可积、`u ↦ ‖U∘F_u‖_{2p}` 与 `u ↦ ‖(U⊗U)∘(E⊗E)‖_p` 的区间可积、乘积 `ψ·f` 的可积。机制上都该由确定性包络 `‖G‖ ≤ (Im z_u)^{−1}` + 控制收敛给出（仿 `integrable_lkT_pow` 的定时版）。
2. **⚠ 无主：二次变差还不是接口要的 `E⊗E`。** `MomentIneq` 右端要 `‖(U⊗U)∘(E⊗E)_{a,a}‖_p`（`Uker` 在 `SumZeroDyn.xi2` 上作用于 `eeFun`）。仓库有的是 `quadVarPairs_Uker`（`quadVar(Ψ₁) = ∑_{ij}‖(U∘E^{(M)}(i,j))_a‖²`）与**单条 loop** 的 `eeRaw_self_eq_quadVarPairs` + (5.22) `eeEdge_eq_sum_SB`。**缺的是该胶合的双线性、`U` 共轭版**：`∑_{ij}(U∘E^{(M)}(i,j))_a·conj((U∘E^{(M)}(i,j))_{a′}) = (U⊗U∘eeArg)_{a,a′}`。已核：`Hierarchy/EEBridge.lean` 里**一个 `RBM.Uker` 都没有**。归 `EEBridge`/`DischargeBDG` 那条线，**没有单负责**。
3. **⚠ 无主：`Q_t` 路线（`MomentIneqQ`）完全没碰。** 它的漂移恒等式要 `∂_u Q_u`，由此才生出 (5.91) 的 `SumZeroDyn.commS` 与 `varthetaDot` 两项；**仓库里没有对 `Qop` 求时间导数的任何东西**。**没有单负责。**（注意这与 T201 的 `Q_u` + (7.16) 是同一个 `Q`，两条线应当合看。）

## ⭐ T199：**Theorem 2.2 落地**——能量网 + `‖∂_E Im G‖ ≤ η^{-2}`（`Flow/EnergyUniform.lean` 续 + `Delocalization.lean`，2026-09-21）

`lake build RBM1D` exit=0，`build.log` `errors: 0`、审计 **10661** 条（全在 `propext/Classical.choice/Quot.sound`）。0 sorry、0 axiom。

### 落地的声明
`Delocalization.lean`（确定性，**不动既有签名**，只新增 4 条）：
`sum_sq_norm_eigenvectorBasis`（`∑_l |ψ_l(x)|² = 1`）、`abs_poisson_sub_le`（单个 Poisson 核的 `wη^{-2}`-Lipschitz）、
**`im_green_lipschitz_energy`**（`|Im G_xx(E+iη) − Im G_xx(E′+iη)| ≤ |E−E′|η^{-2}`）、
**`sq_norm_eigenvector_le_of_norm_green_le_near`**（(2.10) 在**邻近确定性能量**处：`|λ_k−E| ≤ d` 且 `‖G_xx(E+iη)‖ ≤ C` ⟹ `|ψ_k(x)|² ≤ ηC + d/η`）。
⭐ 全部只用谱分解，**不需要算子范数、不需要预解式恒等式**——所以能住在 `Delocalization.lean` 现有的两个 Mathlib import 之内。

`Flow/EnergyUniform.lean`（新增 13 条）：
`eventually_forall_measure_index_le` + **`StochDom.of_forall_seq`**（网引擎）、
`netDen`/`netDen_pos`/`netDen_cast_pos`/`bulkNet`/`abs_bulkNet_le`/`exists_bulkNet_close`/`card_bulkNet_le`/`netDen_inv_div_rpow_le`（能量网）、
**`Band.rpow_le_zScale`**（`η = N^{-1+θ}`、`θ ≤ c` ⟹ `Wℓ(z)η ≥ N^θ/2`，即论文的「𝓁 ∼ L」，**(2.2) 只在这里用**）、
**`delocalization_of_Thm221N'`**（承重）与 **`delocalization_of_Thm221N`**（沿 `Thm221N.toThm221N'` 的一行推论）。

### ⚠ 更正 T199 工单：**Theorem 2.2 不能放在 `Delocalization.lean`**
工单写「`Delocalization.lean`（Theorem 2.2 的最终陈述所在）」。**方向反了**：`Loop/GLoop.lean:7` import 了 `RBM1D.Delocalization`，而 `Flow/Hypotheses ← Loop/GLoop`，所以 `Delocalization.lean` 在 `Flow/` **上游**，import `Flow/EnergyUniform` 会成环。
处理：概率版 Theorem 2.2 放 `Flow/EnergyUniform.lean`，`Delocalization.lean` 只收确定性的 Lipschitz 四条（并在文件头写清两边的分工）。

### 陈述（逐字对照 p.8）
```
∀ᶠ N in atTop, B.P {ω | ∃ p : Idx N × Idx N, (N:ℝ)^(-1+τ) <
    ‖(T.hermitian N ω).eigenvectorBasis p.1 p.2‖^2 *
      Set.indicator (Set.Icc (-2+κ) (2-κ)) (fun _ => 1) ((T.hermitian N ω).eigenvalues p.1)}
  ≤ ENNReal.ofReal ((N:ℝ)^(-D))
```
指示函数**在体内**（论文如此）；`max_k ‖ψ_k‖²_∞` 写成 `∃ (k,x)`（失败事件），`P(成立) > 1−N^{-D}` 写成 `P(失败) ≤ N^{-D}`——都是 `Flow/` 全文件的既有约定。
**量词次序 = 论文**：`∀ κ τ D, ∀ᶠ N in atTop`（不是 `∀ κ τ D N`）。

### Theorem 2.2 的完整假设表（是否「无条件」）
| 假设 | 来源 | 论文里有吗 |
|---|---|---|
| `B : Band Ω` | 模型；含 (2.2) `W ≥ N^{1/2+c}` | 有 |
| `X : Sample B` | (2.34)/(2.36) 的流 | 有（§2.4） |
| `T : Transfer X` | (2.39)/(2.66) 写成 `≺` 转移 | 论文里是「同分布」这件事实 |
| `hκ : 0 < κ`、`hτ : 0 < τ`、`hD : 0 < D` | 论文 | 有 |
| `hT : Thm221N' X κ`（或 `Thm221N X κ`） | Theorem 2.21（`N` 依赖能量） | 有 |
**没有别的**：不需要 `TransferLoop1`（只用逐元素的 (2.3)）、不需要 `κ ≤ 2`（`κ > 2` 时体内指示函数恒 0，单独一支证空事件）、不需要任何网的参数假设（网是**造**出来的，三条性质都是定理）。
所以：**相对 `Thm221N′` + 模型是无条件的**，但绝对意义上仍挂在 `Thm221N′`（六步）与 `Transfer` 上——与 Theorem 2.3/2.4 完全同级，本单没有新增任何悬空假设。

### 可满足性见证（两条 `example`，已编译）
1. **网的粗细联立**：`∀ᶠ N`，同一个 `bulkNet κ N` 同时满足 (i) `∀|E| ≤ 2−κ, ∃j, |E−E_j| ≤ 1/(N+1)^4`、(ii) `#net ≤ N^5`（并集界付得起）、(iii) `mesh/η ≤ η`（`η = N^{-1+θ}`）。三条是**同一组参数**、全是定理不是假设——T199 工单担心的 (a) 结构上不存在。
2. **指示函数会亮、且界会失败**：`1×1` 零矩阵的特征值 `0 ∈ [−2+κ, 2−κ]`（`Matrix.IsHermitian.eigenvalues_eq_zero_iff`），而 `|ψ_0(0)|² = 1 > N^{-1+τ}`（`N ≥ 2`、`τ < 1`）。所以结论事件**既不恒真**（否则定理空洞）**也不恒假**——这正是工单 (d) 要的「有特征值落在区间内的见证」，而且顺带证明了本定理是真正的概率陈述。
3. 逐点不等式全部在好事件 `ω ∈ Good N` 里推（工单 (c)）：结论只是一个概率界，`ω = 0` 处（`H = 0`）事件确实可以失败——见上一条。

### 造轮子的说明
`StochDom.of_forall_seq` 与 `Gauss.stochDom_reindex_of_forall_seq`（`Gauss/Step1Hyp.lean:269`）是**同一个论证**（by_contra + 逐 `N` 选一个坏指标 = 一条序列 + `of_forall_le` 的并集界），差别只在指标集：那边写死成 `TimeIcc s t N` 并带 `θ` 重标，这里是任意 `[Fintype][Nonempty]` 的 `J N`、`θ = id`。
**不能复用**：`Gauss/` 在 `Flow/` **下游**（`Gauss/Step1Hyp ← Hierarchy ← Flow`）。按 CLAUDE.md 该下沉到 `RBM1D/Defs/`（它本来就 generic），本单协议只允许动两个文件，**没做**。
**待定夺（Jun / Cowork）**：开一张小单，把 `StochDom.of_forall_seq` 下沉到 `RBM1D/Defs/StochDom.lean`，再让 `Gauss.stochDom_reindex_of_forall_seq` 变成它的一行推论（`J N := TimeIcc s t N` 经 `θ`）。纯机械，无新数学。

### 未做 / 归谁
* **蓝图**：`thm:2.2` 节点的 `\lean{RBM.delocalization_of_Thm221N}` + `\leanok` 没补——`blueprint/` 归 T193，本单协议只允许动两个 Lean 文件。
* **Theorem 2.4 的 `N` 版**（T194 已记）仍未做；Theorem 2.2 用不到。
* **`Loop/SumZero.norm_Alayer_le` 的 `ι = (mE E).im` 非一致**（T153/T194 已记）仍未修，不在本单路径上。
* **T204 落地后要改吃 `Bounds″` 的是哪几条**：见下一节。

### 若 T204 落地（已核实际命名：`Thm221NoEL`/`Thm221NoEL'` + 既有的 `BoundsCore`，**不是** `Bounds″`）
收工时 `Flow/Thm221NoEL.lean` 已有 `Thm221NoEL`/`Thm221NoEL'`、`BoundsCore_of_Thm221NoEL(')`、`SpecSeq.boundsCore`、`localLaw_of_boundsCore`、`localSemicircleLaw_of_Thm221NoEL'`——**它复用既有的 `BoundsCore`，没有新建 `Bounds″` 结构**（工单文字过时，更正之），而且全部是**固定能量**（`SpecSeq`）版。

Theorem 2.2 **只用局部律 (2.3)**，而 (2.3) 只吃 `BoundsCore.localLaw`（(2.70)/(2.64)），**完全不碰 `expect`/(2.71)**。所以要改吃的恰好是三处，全在 `Flow/EnergyUniform.lean`：
1. `localLaw_of_boundsN` 的参数 `hB : BoundsN X E _` → `BoundsCoreN X E _`（证明里只用 `hB.localLaw`，**证明一个字都不用改**；调用点补 `.toBoundsCoreN`）；
2. `SpecSeqN.boundsN'` → 需要 `SpecSeqN.boundsCoreN`，其输入是 `BoundsCoreN_of_Thm221NoELN'`；
3. `BoundsN_of_Thm221N'` → `BoundsCoreN_of_Thm221NoELN'`，即把 `Flow/Thm221NoEL.lean` 的 `BoundsCore_zero`/`BoundsCore.congr`/`BoundsCore_of_Thm221NoEL'` 照 T194 的办法镜像到 `E : ℕ → ℝ`（**纯机械照抄**，`BoundsN_zero`/`BoundsN.congr` 的 `expect` 分量直接删掉即可）。

`delocalization_of_Thm221N'` 本身只要把 `(hspec j).boundsN' X hκ hT hθ0` 换成 `(hspec j).boundsCoreN X hκ hT hθ0`，其余逐字不动。`StochDom.of_forall_seq`、能量网四条、`Band.rpow_le_zScale`、`Delocalization.lean` 的四条 Lipschitz **与 (2.71) 无关，完全不受影响**。

## ⭐⭐⭐ T201：(7.16) 的矩形式落地，(7.1) 档的否定结论**入库**；但工单那一步**在原地做不到**（`Gauss/Lemma514Q716.lean`，917 行、31 条，2026-09-21）

**⚠⚠ 更正 T201 工单本身（本单最重要的发现）**：工单说「把矩路线里用 `edgeKer` 裸行和的地方**逐处换成** `Q_u` 投影后的 (7.16) 档」——**这一步在原地做不到，也不该这么描述**。`hrhs_of_moment_inputs` 里 `U` 下面的三个张量是 `SumZeroDyn.lkT`、`H.F`、`eeFun`，**它们本身不是 sum-zero 的**，(7.16) 对它们不适用。`Q_u` 投影过的版本是**另一条陈述**，就是 `MomentDuhamel.Hyp.momentDuhamelQ`（五项，每个张量都已投影）。

**所以：带撇的 `hrhs_of_moment_inputs`（结论一字不改）做不出来。** 正确的路线是**矩路线改以 `momentDuhamelQ` 为接口** —— 这是范围问题，见下面的 D14。

**落地的**
* **(7.1) 档的否定结论入库**（T193 查出 T195 的 7 条探针从未入库，现已补）：`one_add_norm_edge_eq`（`‖ξ‖=1` 时 `hkerC` 左端**恒等于** `η_u/η_w`，逐字 Lemma 7.1）、`gridS_window_len`（网格上 `(t−s)/(1−t) = W^{τ′}−1`，**等式**）、**`no_const_hkerC_on_gridS`/`no_const_hker2C_on_gridS`**（假设是 `hrhs_of_moment_inputs` 的槽**逐字原形**，结论 `False`）。
* **Minkowski**：`momNorm_le_affine`。T146 的 `momNorm_le_of_le_weighted_sum` **是 Jensen**，只在各项共用同一个 `M` 时才等于 Minkowski；(7.16) 的主项随机、误差项确定，必须要真的 Minkowski。
* **(7.16) 的矩形式**（T195 点名的缺口 (i)）：`momNorm_Uker_sumZero_scale_le` 及任意 `ξ` 的带撇版（`E⊗E` 的电荷 `xi2` 是 `Fin.append`，不是 `xiOf`）。
* **`momentDuhamelQ` 五项的 (7.16) 界**：`momNorm_Uker_Qop_le`（第 1、2 项）、`momNorm_Uker_commS_le`（(5.99)）、`momNorm_Uker_PsumVarthetaDot_le`（(5.100)）、`momNorm_Uker_QQ_le`（(5.103)）。**每一条里 (7.16) 的 sum-zero 前提都是定理而非假设。**
* **好事件拆分** `momNorm_le_affine_on_event`：(7.13) 只在高概率事件上成立，损失是 `Env·P(Ξᶜ)^{1/q}`。

**可满足性见证 `gridS_Q716_witness`**：网格是**论文自己的 p.24 网格** `1 − s_j = W^{−jτ′}`，取一格窗口；假设只有 `1 ≤ W`、`0 ≤ τ′`、`3 ≤ L`、`0 < κA`，**不带任何短窗口假设**。三合一结论：`witTensor ≠ 0`（**`Q_u` 之后的对象非零**）、`Qop` 确实不杀它、矩界常数 `cKerSumZero(m+2)·3^{2(m+2)}` **与 `N` 无关**。同一窗口上 `momNorm_Uker_apply_le` 的常数是 `(W^{τ′})^{m+2}`——**正向见证与 T195 的反证一并入库，互为对照**。

**事实核对（与工单描述有出入）**：`SumZeroDyn.norm_Uker_sumZero_scale_le` **已经**是归一化后「无前因子」的形式（`integral_term_le` 的 docstring 甚至已写着 "there is no `(η_s/η_v)` prefactor"）。「三档齐备」是对的；路径层面缺的只有矩形式（本单补上）+ Q 半边接线。

**已按 T201 的文案接线（协调者做的）**：`Gauss/Lemma514Holder.lean` 的 `one_add_norm_mul_le` / `hkerC_flow` / `hker2C_flow` 三条加了 `@[deprecated "RETIRED (T201): …"]`（全仓无外部消费者，零新 warning）；文件头那段与 :1150 那段**事实错误的 docstring**（「That last point is a genuine hypothesis and not bookkeeping」）已按 T195/T201 的结论改写。`hkerlt_flow`/`hker2lt_flow` **没有**加——它们无条件，(7.16) 档仍要用。

## ⭐ 待 Jun 定夺 D14（T201 逼出来的唯一范围问题）

**矩路线的接口是否从 `Hyp.momentDuhamel` 改为 `Hyp.momentDuhamelQ`？**

* **改**：要新开两张单——① **`P∘(L−K)` 半边**（从 `‖Q_v∘(L−K)_v‖` 回到 `‖(L−K)_v‖`，即 `A = Q_t A + (P·A)ϑ_t` 里 `Psum` 那一项的界；`SumZeroDyn.norm_le_norm_Qop_add` 与 `norm_Psum_lkT_le` 都是现成的，但没接到矩路线）；② **`stochDom_of_momentDuhamelQ`**（`stochDom_of_momentDuhamel` 的 Q 类比；本单已交付它需要的五个核估计，总装定理没写）。
* **不改**：**Lemma 5.14 的矩路线在总装窗口上永远是空真的**——`hkerC` 在那里不可满足（已编译证明），而 (7.16) 对未投影的张量不适用。

T201 没有权限做这个决定。

**另附：第三块（`FastDecay` 的生产者）**——五个张量沿流的 `FastDecay` 是 (7.13) 的前提，也是**唯一一个关于模型而不是关于核的前提**；`SumZeroDyn.lean:3093/3549` 有 `fastDecay_Qop_le` 的用法但都在好事件上、没接到矩路线。归随机层（T163/T167 的后继），**目前无主**。

## T201 给协调者的其余接线（尚未做，记档）

* `Gauss/Lemma514Holder.lean:919 one_add_norm_mul_le` 可改成 `one_add_norm_edge_eq` 的一行推论（已 deprecated，改不改无碍）。
* `Gauss/MomentDuhamelRhs.lean:265 momNorm_Uker_apply_le` **不删**（(7.1) 档在别处仍合法），但 docstring 的「with the same constant `C^n` as Lemma 7.1」下面该加一句指向 `no_const_hkerC_on_gridS`：**在总装窗口上这个 `C` 不存在**。
* `Hierarchy/SumZeroDyn.lean:1252 norm_Uker_sumZero_scale_le` 现在是 `Gauss.norm_Uker_sumZero_scale_le'` 的特例，但方向是新文件依赖旧文件，要改须把带撇版下沉——**建议先不动**。

## Cowork 裁定（2026-09-21 17:25）：R1–R5 与 D14

**R1–R5（Jun 17:15 同意 Cowork 的建议；全文见 `docs/REPORT.md` §9，commit 9f2a2f0）**
* **R1**：Theorems 2.2–2.5 **并列为主定理**，各附完整假设表；六步合拢前状态写「以 Theorem 2.21 为前提」。Theorem 2.21 与 Lemmas 2.18–2.20 作为关键中间结果单列；Theorem 2.6 单列，标明是全文唯一用外部输入的地方。
* **R2**：已由 Jun 的范围规则回答——Theorem 2.6 在范围内，等其余各块无高风险项后再开；外部输入 = [51] Theorem 2.2 的**复 Hermitian 形式**；`GreenComparison` 自证。
* **R3**：钉死 `OUFlow` 的分布随 Theorem 2.6 一起做；此前 `theorem2_6_of_steps` **不**算 Theorem 2.6 的形式化。
* **R4**：已由 D12/D13 回答（T204 第一遍已完成，(2.71) 与 Step 6 样本侧归 T205，不推迟到 2.6）。
* **R5**：否定结论单列一节，分 (a) 论文层面的修正、(b) 形式化中被证伪的**自设接口**（不是论文错误）两小节。
* 报告按此改写 → **T217**。

**D14 → 改（Cowork 按路由类裁定，不涉及论文陈述）**：矩路线的接口从 `Hyp.momentDuhamel` 改为 **`Hyp.momentDuhamelQ`**。理由：(i) 这正是论文 Lemma 5.14 的证明路线——(5.92) 的「无 `(η_s/η_t)` 前因子」来自 `Q_u` 投影后用 (7.16)，Cowork 在 T195 之后已按此定过方向（T201 工单）；(ii) 不改则 Lemma 5.14 的矩路线在总装窗口上**永远空真**（`no_const_hkerC_on_gridS` 已编译）；(iii) 论文陈述一字不动。`Hyp.momentDuhamel`（未投影）字段**保留**，T206/T212/T213 那条线照做——它仍被 Step 2 等处消费。
* 新单：**T218**（`P∘(L−K)` 半边接到矩路线）、**T219**（`stochDom_of_momentDuhamelQ` 总装 + Lemma 5.14 矩路线改吃 `Q` 接口）、**T220**（(7.13) 的前提 `FastDecay` 沿流的生产者，T201 另附的第三块）。
* **T214**（`∂_u Q_u`，`MomentIneqQ` 的漂移恒等式）因此进入关键路径：`momentDuhamelQ` 的生产者要它。
* T201 列的「给协调者的其余接线」三条（docstring 指针等）不开单，由协调者顺手做。

## T211：`Flow/Consequences.lean` 改吃 `BoundsCore`（13 条新名 + 15 条 `rfl` 探针，2026-09-21）

**⚠ 更正 T211 工单（用编译探针核过）**：工单让「与 T204 重复的部分改成一行推论指向它」——**不可行**。`Flow/Thm221NoEL.lean` 是 `Flow/Consequences.lean` 的**下游**（`Thm221NoEL → Thm221Bare → ⋯ → Consequences`），不是上游；Consequences 既不能引用它，也不能复用它已占掉的七个裸名。所以七条核心定理放进 **`namespace Core`**（`RBM.Core.*_of_boundsCore`）与 T204 的裸名并存。**这是本单唯一的重复劳动，在「只写一个文件」的前提下消除不掉。**

落地：`Core` 内七条（证明脚本与旧版**一字不动**）+ `RBM` 内六条全新（四条 `*_prob_of_boundsCore`、`localSemicircleLaw_of_boundsCore` = **Theorem 2.3 整条**、`quantumDiffusion_pm_pp_of_boundsCore` = `quantumDiffusion_of_Thm221` 的**前两个合取**拆出来）。**13 条旧名签名一字未改**，全部降为一行推论。`Thm221Gain`/`EnergyUniform`/`Universality`/`DistEq`/`Thm25Gauss` 全部无改动即通过。

**越界检查（本单真正的风险不是空真而是越界）**：全仓 `grep "\.expect"` 在本文件只命中一处（`:611`，`expect_loop2_of_bounds` 的 `hB.expect.precomp_param`），沿依赖链因此**保持在 `Bounds` 上**的是六条：`expect_loop2_of_bounds`、`expect_quantumDiffusion_pm/pp_of_bounds`、两条 `_W_` 版、以及 `quantumDiffusion_of_Thm221` 的**第 3、4 合取**（(2.8)(2.9)）。**没有把任何一条挂到空假设上**——另加两条**反向** `rfl` 探针把 (2.8)(2.9) 钉死在 `expect_*_W_of_bounds` 上，证明它们仍然吃 (2.71)。

**paper-delta 不需新号**：结论一字未改；假设弱化那条偏差已由 **#134（原 T204b）** 覆盖，本单只是把同一拆分搬到了上游文件。

## ⚠ 无主的活（T211 交出）

1. **合并 T204 与 T211 的重复七条**：T209 交还 `Flow/Thm221NoEL.lean` 后，删掉它 §6 里与 `RBM.Core.*_of_boundsCore` 逐字相同的七条，把 Consequences 的 `Core.` 前缀去掉；`localSemicircleLaw_of_Thm221NoEL'` / `quantumDiffusion_pm_pp_of_Thm221NoEL'` 改成一行推论指向 `RBM.localSemicircleLaw_of_boundsCore` / `RBM.quantumDiffusion_pm_pp_of_boundsCore`。**归 `Thm221NoEL.lean` 的持有者（T209 之后）。**
2. **`Flow/EnergyUniform.lean` 的 `SpecSeqN` 一套（:506/:521/:542/:552/:568）是第三份同样的证明脚本**——归 T199 的后继。

## ⭐⭐ T210：`CutHyp.moment` **不能直接从 Duhamel 产出**——障碍精确定位并编译成化归（`Gauss/CutHypTheta.lean`，1062 行、39 条，2026-09-21）

**第 0 步最重要的发现**：**`CutHyp.moment` 是无条件的，而 Duhamel 计算只在「前缀事件」上成立。** 截断 `χ(J_{ws}/θ)` 只约束**端点** `ws` 处的值，对中间时刻 `u ∈ [s,ws]` 的 loop hierarchy 毫无约束；而 (5.39)–(5.44) 的每一项都要用中间时刻的先验界。

化归已编译（`moment_of_conditional`）：

> 无条件 `moment` ⟸（**条件**矩界，限制在前缀事件 `A N ws` 上）＋（`A` 以 `HighProb` 成立）＋（截断水平多项式有界 `2·lev ≤ N^{Clev}Θ`）。前缀外由截断自身的包络 `2θ` 付账，`D` 在 `∀ p` **之内**选（`D := (2δ+Clev)(2p)+1`）压掉它。

后果分两边：**第二遍（sharp）这条前缀是免费的**——它就是第一遍的结论（`prefix_of_stochDom`）；**第一遍（blunt）这条前缀正是自举要证的东西**，在 `moment`「一次性对所有网点、无条件」的形状下拿不到。⚠ 这是**结构性障碍的精确定位，不是不可证性证明**——T210 只编译了化归，**请勿当作否定定理引用**。

**⚠⚠ 更正 T210 工单**：工单说推广 `Θ` 后「能把 T207 §3 的那条假设**彻底去掉**」——**做不到，方向还相反**。`cutTrunc` 对水平**单增**（`cutTrunc_mono_level`，严格性见 `sat_level_strict`），把截断水平从 `1` 抬到 `(η_s/η_u)²` 是**加强**假设，不是删除。真实结果：
* `MomentHypCutSharp`（T207 §3）**不再是独立假设**，由 `momentHypCutSharp_of_cut2` 从 `MomentHypCut2` + `MomentHypCut` 导出（`init` 走 `jSnorm2_left`，与 (2.69) 逐字同一条）；
* 但 Step 2 的具名假设仍是**两条**：`MomentHypCut.cut`（钝版）与 `MomentHypCut2.cut`（锐版），二者之差恰是 `R^{−4p}` 的增益，**即 (5.47) 的全部数学内容，不可能从钝版推出**；
* 推广真正买到的是：(i) 假设现在写在**数学真正支持的截断水平**上；(ii) 第二遍**不需要第二次 bootstrap，也不需要第二个初值条件**（`stochDom_of_cutHyp'_of_prefix` 的假设表里没有 `hinit`、没有 `Θ ≥ 1`）。

**可满足性**：主见证 `satCutHyp'` 取**临界标度** `J ≡ Θ ≡ 1`（不是退化的 0），水平 `satLev N u = (1−u)⁻¹` **真带 `u`**，窗口右端 → 1；`mesh_fine`/`card_le` 这对反向条件由同一见证满足。`sat_lev_unbounded` 证 `u ↑ 1` 处水平无界（非退化）。⚠ **`lev_ge` 必须限制在窗口**：`u > 1` 时 `η_s/η_u < 0` 且其平方很小，`∀ N u, Θ N ≤ lev N u` **按字面为假**——结构体字段因此写成 `∀ N, ∀ u ∈ Set.Icc (s N) (t N), …`。

**协调者已接线**：`Hierarchy/Step2Near47.lean` 文件头那段「Generalizing `Θ` … would remove the last piece of assumption here」与 `Gauss/MomentDuhamelCut.lean` 文件头「the Gaussian discharge of `CutHyp.moment`」两段**已按本单结论改写**（前者原措辞为错，后者补上障碍的精确定位与化归指针）。

## ⚠ 无主的活（T210 交出）

1. **`CutHyp.moment` 的条件版生产者**：交付 `moment_of_conditional` 的 `hcond`（**前缀事件上的截断 Duhamel 矩界**）+ 前缀事件可测性。输入是 T212/T213/T214 的 `momentDuhamelHyp_gauss` 三块；`phi_arith'` / `integral_nearInt_le` / `phi_arith_second_pass` 的**记账层接线并入该单**（T207 查出那三条全仓无消费者，要接的正是这条条件矩界）。**T210 没有硬接**——差的是 (5.34)/(5.35)/(5.36) 三项的界，硬接会变成 fiat。
2. **前缀事件的可测性**：`moment_of_conditional` 把 `hA` 当假设收；路径连续 + `AEStronglyMeasurable` 只能给到 `NullMeasurableSet`，要去掉这条假设得改用 `integral_add_compl₀` 并补一条「连续路径的一致上界事件是零可测集」的引理。并入上一条。
3. **T209 的余项**：`Step2.localLaw` / `Step2Moment.aprioriDecay_of_jS` 的原版该改成一行推论（`StepGlue` 里已有严格更一般的重述，证明脚本逐字照抄）。纯机械。

## ⭐⭐⭐ T213：查出 `SumZeroDyn.xi2` **按字面不是论文那个量**——第二半漏了共轭（`Gauss/EEUker.lean`，744 行、44 条，2026-09-21）

**第 0 步的答案：对不上，差的就是第二半的一次复共轭。**

* `emart`/`emartEdge` 与 p.55 逐字对应，**对得上**；`EEBridge.eeArg`/`MomentDuhamel.eeFun` 是 Def 5.4 在 #102 约定下的形式，(5.22) 的 `W∑S^{(B)}` 已由 `eeEdge_eq_sum_SB` 消掉，**对得上**。
* **`SumZeroDyn.xi2` 错了。** 论文 Lemma 5.5（p.55）把算子写死成 `[(U_{u,t,σ} ⊗ U_{u,t,σ̄}) ∘ A]`，紧接一句 "where σ̄ is the conjugate sign vector of σ"；(5.23) 的 `σ(k)` 后半段也全带杠。仓库的 `xi2 E σ = Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) σ)` **重复了未共轭的 ξ**。独立推导同结论：`d⟨M_a, M̄_{a'}⟩ = ∑_{b,b'} K_{ab}·conj(K_{a'b'})·eeRaw(b,b')`，第二槽必须是 `K̄ = Uker(conj ξ)`。
* **差在哪个因子**：只差第二半那 `n+2` 个边参数上的一次 `starRingEnd ℂ`（等价于把 `σ` 换成 `!∘σ`）。
* **为什么此前没人发现**：`|E| ≤ 2` 时 `‖ξ_i‖ = 1`，所以**仓库里所有经 `xi2` 的估计看不见这个差别**（`norm_xi2_le`、`xi2_ne_zero`、`norm_xi2_mSigma`、整个 §7.1），但**等式**对 `xi2` 为假。`norm_xi2bar` 证两者逐项模相同（⇒ 下游估计一字不用动），`xi2bar_ne_xi2` 给出 `E = 1`、`σ ≡ +` 的反例（⇒ 修正非空）。

**交付**：`sum_Uker_mul_conj_Uker`（核心代数等式，任意 `Fintype ι` 与任意族）、`quadVarPairs_Uker_eq_norm_eeRawArg`（**等式**，无 Schwarz 无链式法则）、`quadVarPairs_Uker_le_norm_eeArg`（**(5.25)**）、`quadVarPairs_Uker_le_norm_eeFun`（Band 版，右端逐字是 `MomentDuhamel.eeFun`）。

**数值自洽检查**（本单最重要的验收物）：`L = 3`、一条边、`ξ = i`、`s = 1`、`t = 0`、`E = (1, i, i)`。`(a,a') = ((0),(1))` 与 `((0),(0))` 两处，两侧**各自独立**算出 `8/9 − (4/3)i` 与 `26/9`，**都非零**；两侧求值**不用本文件任何定理**。**判别性**：`sanity_rhs_xi2_wrong` 证明第二半改用 `ξ`（即现有 `xi2` 的做法）在同一点给出**不同的数**——这个共轭不是装饰。

## ⭐⭐ T214：`stochDom_of_momentDuhamelQ` **总装起来了**——D14「改」那一侧的消费者端不再是缺口（`Gauss/MomentDuhamelQ.lean`，884 行、27 条，2026-09-21）

**⚠⚠ 更正 T214 工单（也更正 `MomentDuhamelHypGauss.lean` 文件头第 3 条）**：工单说「仓库里没有对 `Qop` 求时间导数的任何东西，`hasDerivAt_Qop_hierarchy` 是对层级求导不是对 `u`」——**两句都是错的**。`Hierarchy/SumZeroDyn.lean` 早就有 `hasDerivAt_Qop`（:1157，**逐字就是 `∂_u Q_u`**）与 `hasDerivAt_Qop_hierarchy`（:1174，**即 (5.88)**，结论里 `commS` 与 `varthetaDot` 已显式出现）。真正缺的是**传播子共轭 + 矩阵生成元**那一版，即 T206 的 `hasDerivAt_ukerObsT_drift` 的 `Q` 孪生——本单补的就是这个：

> `(∂_u + 𝓛)(U_{u,v} ∘ Q_u (L−K)_u)_a = (U ∘ Q_uF_u)_a + (U ∘ [Q_u,Θ_{u,σ}](L−K)_u)_a − (U ∘ (P(L−K)_u)_{b₀}ϑ̇_{u,b})_a`

三项与 `MomentIneqQ` 的三个漂移被积式**逐字同形**。代数关键：`Q_u(dv + 𝓛(L−K)) = Q_u(Θ_u(L−K) + F)`，`commS` 恰好是 `Q_uΘ_u − Θ_uQ_u` 的亏量，传播子的 `Θ` 与之相消。漂移全是钉死的（`driftF`、`commS`、`varthetaDot` 都是定义，`K` 由 `hKdef` 钉成 `Band.Kval`），**两侧无自由张量**。

**对 D14 的输入**：`stochDom_of_momentDuhamelQ` 编译通过、公理干净，所以 **D14 的「改」那一侧，消费者端不再是缺口**。代价只有一条 `QIntegrable`（paper-delta T214a），在高斯模型上是定理。但 **`MomentIneqQ` 本身仍未产出**，还差三件（见下）；**T201 的五条核估计至今仍无消费者**，把它们接进 `hrhs` 现在做不到——它们的 `hGd`（(7.13) 快衰减沿流）T201 自己写明没产出。**这是矩路线走 `Q` 的真实剩余风险，D14 裁定时请一并计入。**

## ⚠ 无主的活（T213 / T214 交出，点名到字段级）

1. **⭐ 修正 `SumZeroDyn.xi2` 的定义**（T213 查出）：`Hierarchy/SumZeroDyn.lean:1445` 改成 `Fin.append (xiOf (mSigma E) σ) (xiOf (mSigma E) (fun i => !(σ i)))`（或保留 `xi2` 并把消费者改吃 `EEUker.xi2bar`）。改完 `xi2_ne_zero`(:3650)、`norm_xi2_le`(:3657) 只需在第二半多一步 `xiOf_not` + `Complex.norm_conj`。**消费者共 11 个文件**：`SumZeroDyn.lean`(18 处，含 `Hierarchy.bdg`/`bdgQ` 字段与 Lemma 5.10 侧估计)、`Gauss/MomentDuhamel.lean`(3 处：`Hyp.momentDuhamel`、`momentDuhamelQ`、`stochDom_of_momentDuhamel` 的 `hrhs`)、`Lemma514Holder`(4 处)、`Lemma514Moment`/`Lemma514Q716`/`MomentDuhamelHyp`/`MomentDuhamelHypGauss`/`MomentDuhamelQ`/`MomentDuhamelRhs`/`MomentDuhamelTime`。**全部只用 `‖xi2‖ = 1` / `≠ 0`，机械替换。**
2. **`hsplit`（链式法则 `E^{(M)}(α) = ∑_k E^{(M)}(α,k)`）与 `hdiff` 仍是假设**（T213 查出）：与 `Gauss.quadVarPairs_le_of_split`、`quadVarPairs_Uker` 同一条缺口（`DischargeBDG.lean` 文件头已承认：需要 `List.foldr` 预解式乘积的 Leibniz 法则）。**全仓无人负责。**
3. **`Q` 版的 `TestFunT₁` / 生成元恒等式**（T214 交出，**`MomentIneqQ` 唯一的大缺口**，约等于 T196 的体量）：`momentIneqQ_of_derivBound` 的 `hbound` 要 `∂_u E[·]` 的**期望**形式，T214 给的是**逐点**被积式；桥是 `testFunT₁_qMomentObsT` + `hasDerivAt_integral_qMomentObsT`，而 `testFunT₁_momentObsT`/`exists_bddC2C_momentObsT`/`bddT_momentObsT`/`differentiableAt_momentObsT_pair`/`continuous_timeD1_momentObsT` 全是对 `momentObsT` **特化写死**的。**最省的做法**：`qUkerObsT` 与 `ukerObsT` 同属「确定性系数的 loopObs 有限线性组合」这一类，把那五条按「系数族对 `u` 是 `C¹` 且有界」**泛化一次，两条路线一起吃**。
4. **`Q` 版的五件区间可积性**（T212 那条线的孪生）与 **`Q` 版的二次变差桥**（T213 那条线的孪生：`∑_{ij}(U∘Q_u∘E^{(M)}(i,j))_a·conj(…)_{a′} = ((U⊗U)∘QQ(eeArg))_{a,a′}`）。
5. **去重下沉到 `RBM1D/Defs/`**：`EEUker.mSigma_not` ≡ `Gauss/Step6DriftEG.lean:192` 的 `RBM.mSigma_not`；`EEBridge.leftArg`/`rightArg` ≡ `SumZeroDyn.spl1`/`spl2`（定义相等）。

## ⚠ T214 的一条局限（如实转述）

本机**没有 poppler/pdftotext**，T214 **没有**直接逐字核对论文 (5.91)/(5.99)/(5.100)/(5.103) 的印刷文本；对齐靠仓库里已对齐的 `Hyp.momentDuhamelQ` 五项与 `hasDerivAt_Qop_hierarchy` 的 (5.88)。**论文层面的逐字复核请 Cowork 用会话里的 PDF 做一次。**

## Cowork 裁定（2026-09-21 17:55）：T209/T210/T213/T214 之后

* **T209 审计通过**：`thm221NoEL_of_inputs` 的类型里 `Cond272'` 0 次、`Cond272Reg` 7 次；见证 `cond272Reg_grid_step_domain` 在论文网格上、参数先于 `E, t` 选定、窗口不塌缩；三档强弱各有严格性定理。**D13 收口**。更正 #125 那半句的 T209a 待赋号。
* **`xi2` 漏共轭（T213）→ 原地改定义（T223）**。理由：(i) 旧定义不是论文 Lemma 5.5 的对象（`U_σ ⊗ U_σ̄`），`Hierarchy.bdg`/`bdgQ`、`Hyp.momentDuhamel(Q)` 里对它断言的等式**按字面为假**，这些接口在旧定义上**产不出来**——继续保留会是空真/不可产出的根源；(ii) 所有既有估计只用 `‖xi2‖ = 1`/`≠ 0`，T213 已证修正后逐项模不变，所以**声明类型一字不变、证明只多一步**；(iii) 这是 Lean 侧定义的修正，论文不改。冻结签名规则保护的是**声明类型**，这里类型不变、改的是一个与论文不符的定义体，属于修错而不是改接口。不走「保留 `xi2`、消费者改吃 `xi2bar`」的路：那会留下一个错误对象和 11 个文件的双份陈述。
* **T210 的结构性障碍 → T222**：钝版（第一遍）改成**沿网格逐步**自举，第 `k` 步的前缀由归纳假设供给；`hcond` 与前缀可测性、三条无消费者的记账层一并归 T222。T210 自己记的「这是化归不是否定定理」照录。
* **T214 → T225（`Q` 版生成元恒等式，泛化一次两路共用）、T226（`Q` 版两条孪生缺口）**；T213 的 `hsplit`/`hdiff` → **T224**；去重两条并入 **T221**。
* **T214 请 Cowork 用论文 PDF 逐字核 (5.88)/(5.91)/(5.99)/(5.100)/(5.103)**：Cowork 本次心跳做，结果另记于下。

## ⭐⭐⭐ T205：**空真第九例**——Step 6 的包络假设按字面不可满足，而且是量词写错（`Gauss/Step6Sample.lean`，465 行、23 条，2026-09-21）

**主结论：Step 6 的样本侧现在做不了，不是因为数学缺口，是因为 `sharpExpect_step6_driftEG` 的 `henvQ`/`henvG`/`henvLK`、`hmeasQ/G/LK`、`hintL1` 把时间 `v` 量化在整个 `ℝ` 上，而不是窗口 `[s_N, t_N]`。**

**`Gauss.not_exists_env_eG`（已编译，公理干净）**：在 `E = 0`、样本点 `ω = 0`（此处 `H_v = √v·X(0) = 0`，对**每个** `v`）、`v = 1 − w` 处，(5.131) 的被积量有**闭式**
`E^{(G)}(L−K, L)_{v,(+,+),(a₀,a₀)} = 2(w⁻¹ − 1)·w⁻³ / W`（`Gauss.eG_value`），`w ↓ 0` 时无界。**没有抵消**：`a,b` 双和经 `sum_SB_col`（列和 = 1）整体坍缩，`k = 1,2` 两项相等。于是**不存在任何 `Env : ℕ → ℝ`**（不论是否多项式）满足 `henvG`。因为 Theorems 2.4/2.5 量化在所有 `|E| ≤ 2 − κ` 上，**在 `E = 0` 处不可满足即整条 (2.71) 归纳被封死**。

**这是量词写错，不是数学缺口，三条证据**：
1. 两个文件内部**只在窗口时刻**用它——`unifDetDom_driftELK` 先 `rintro ⟨v, q⟩`（`v : TimeIcc s t N`）才用 `henv`；`fastDecayHyp_driftSplit` 在 `vv : TimeIcc s t N` 下用；
2. T150 早就把同一件事写成了窗口版：`Gauss.int1_gauss : ∀ N (v : TimeIcc s t N), Integrable …`，与 `hintL1 : ∀ N (v : ℝ), …` **形状对不上**；
3. `sharpExpect_step6_driftEG` / `_driftSplit` 全仓**零消费者**，所以没人撞上过。

**T205 没有把 (2.71) 的步进定理写出来**——唯一的 (2.80) 生产者带不可满足假设，写出来就是空真（这正是工单禁止的）。交的是总装桥 `bounds_of_boundsCore_of_sharpExpect`（配 `rfl` 对照 `Bounds_of_Steps`，证明没改形状）与两个能交的槽 `hEL_gauss`（**零新假设**）、`hintL2_gauss`。见证 `bounds_witness_zero` 是**退化见证**（`s = t = 0`），文件里明写了退化——**非退化见证正是被上面那条封死的**。

**第 0 步的字段清单（已核，非旧记载）**：有生产者的只有 `h5132`（= 归纳假设本身）、`h527`、`hq11`、`hEL`、`hintL2`；`hcont`/`hintQ`/`hintG`/`hintU1`/`hintU2` 量词正确但未做（纯分析）；`hlk` 要 Lemma 5.9 的**期望**版（依赖 `Env`）；`hKd` 只有半个（`exists_loopDecay_Kval` 给「存在某个 δ」，量化形 `(ℓ_v N^τ, N^{−D})` 没有）；**四个好集 `FDInputs`/`QuadInputs`/`EGInputs`/`DriftInputs` 全仓零生产者**，但 `mem_egInputs_of` 已把 `EGInputs` 逐点归约为 `FDInputs` + `hKd` + `xiLK ≤ Ψ`。好集的分解是明确的：`xiLK ≤ Ψ` 那几项由 Step 3/4 的 `StochDom` 经机械的 `StochDom → HighProb` 即得，**真正缺的是 `LoopDecay` 那几项**（Lemma 5.9 逐点版 + Lemma 4.1 事件的高概率）。

**T202 的第 4 条仍未闭合**：`Bounds` 在 `s > 0` 处无居民。T205 **没有**把 (2.8)(2.9) 挂到空假设上，`Flow/Consequences.lean` 的 `expect_*` 一条未动。

## ⚠⚠ 无主的活（T205 交出，第 1 条是零数学的一行修复）

1. **⭐ 包络量词修复（零数学）**：`Gauss/Step6DriftSplit.lean` 与 `Gauss/Step6DriftEG.lean` 里把 `henvQ`/`henvG`/`henvLK`/`hmeasQ`/`hmeasG`/`hmeasLK`/`hintL1` 的 `∀ (v : ℝ)` 改成 `∀ (v : RBM.TimeIcc s t N)`，调用处 `N v σ a` 改成 `N ⟨v, _⟩ σ a`。修完后 **`hintL1` 立刻由 `int1_gauss` 补上**，`hmeas*` 由 `continuous_gloop_Hflow` 补上，`henv*` 由 `norm_gloop_le_rpow` + `norm_Kval_le` + `hη : N^{−c} ≤ η_v`（与 `quad11_unifDetDom_gauss` 同款侧条件）补上。**没有单负责。**
2. **四个好集的 `HighProb` 生产者**（`FDInputs`/`QuadInputs`/`EGInputs`/`DriftInputs`）：数学缺口在 `LoopDecay` 那几项；`xiLK ≤ Ψ` 那几项机械。**可拆两张单。**
3. **`hKd` 的量化形**：把 `Decay.cKdecay 3 (1−v)·exp(−cor35Rate(1−v)·ℓ)` 压到 `N^{−D}`，即「`ℓ̂_v` 确实是衰减长度」那步算术。
4. **`hcont`/`hintQ`/`hintG`/`hintU1`/`hintU2`**（量词正确，纯分析）与 **`hlk`**（Lemma 5.9 的期望版，依赖第 1 条）。

## Cowork 17:58：论文逐字核对 (5.88)–(5.105)（应 T214 之请）与 T205 审计

**核对（用仓库 PDF p.66–69 的页面图像，不是 pdftotext）**
* (5.88)–(5.91)：T214 的逐点恒等式 `(∂_u + 𝓛)(U∘Q_u(L−K)_u) = U∘Q_uF_u + U∘[Q_u,Θ_u](L−K)_u − U∘(P(L−K)_u)ϑ̇_u` 与 (5.91) **逐项同形**：`Q_uF_u` 恰为 `Σ_{l_K>2}`、`E^{((L−K)×(L−K))}`、`E^{(G̃)}` 三项之和（`driftF` 的三块），换位子项取 `+`、`P·ϑ̇` 项取 `−`；换位子方向 `[Q,Θ] = QΘ − ΘQ` 与 (5.89) 一致。
* **(5.99) 第一行印刷有误**：整体差一个负号（由 Def 5.12 直接展开得 `Q_uΘA − ΘQ_uA = −(P∘ΘA)ϑ_u + Θ[(P∘A)ϑ_u]`），且第二项 `ϑ_t` 应为 `ϑ_u`。**Lean 的 `commOp_eq` 一直是对的**，第二行的界取绝对值、(5.100) 以后不受影响。记 **paper-deltas #146**，论文改动预算**第 17 条**（笔误级，按「小错误可自行修改」列入）。
* (5.103)/(5.105) 的算子是 `U_{u,t,σ} ⊗ U_{u,t,σ̄}`——**与 T213 对 `xi2` 的更正一致**，T223 的方向对。(5.104) 与 `Q_u ⊗ Q_u = (I−ϑP)⊗(I−ϑP)` 一致。
* paper-deltas 临时号赋号：T209a → 142、T210a → 143、T213a → 144、T214a → 145。

**T205 审计：空真第九例成立，修复开 T227。** `not_exists_env_eG` 是真的否定定理（`E = 0`、`ω = 0` 处闭式无界、无抵消）；判为量词写错而非数学缺口的三条证据充分（内部只在 `TimeIcc` 上用、仓库已有窗口版 `int1_gauss`、零消费者）。`bounds_witness_zero` 是**退化见证**，T205 自己标明了——不作为可满足性证据。T227 用带撇版改量词（旧版加 `@[deprecated]`），补三类槽，然后写 (2.71) 的步进定理；验收要求**非退化**见证。

## ⭐⭐⭐ T216：**`M_m ≺ 1` 不是输入——它与 (5.48) 远场半边互为等价**（`Hierarchy/Step2FarMart.lean`，940 行、37 条，2026-09-21）

**第 0 步的结论推翻了工单的前提。** `farMart_far_equiv` 已编译：在 (2.69)+(5.35) 的其余三条之下，两个方向用**同一个**加性常数 `Ξ(M_i+M_f·len)+1`——
* `‖lk_v a‖ ≤ J_f·T` ⟹ `‖farMart‖ ≤ (J_f+c)·T`（`norm_farMart_le_tT`）；
* `‖farMart‖ ≤ M_m·T` ⟹ `‖lk_v a‖ ≤ (M_m+c)·T`（`far_bound_of_farMart_tT`）。

**所以矩路线的二次变差项给不出它**：三角不等式只能把 (5.47) 的 `J* ≺ (η_s/η_v)²` 搬过来，得到 `M_m ≺ (η_s/η_v)²`，**在 Lemmas 2.18–2.20 的网格上不是 `≺ 1`**（`cFarStep'_apriori_not_detDom` 已编译）。

**真正卡住的不是估计，是接口**（精确到因子）：矩路线替代 BDG 要对 `Φ_u = Ψ_u − Ψ_s − ∫_s^u(U∘F)` 用生成元恒等式——一阶项由 `Gauss.hasDerivAt_ukerObsT_drift`（T206）**恰好相消**，只剩 `E⊗E`，正是 (5.42)→(5.44) 那一项，**远场积分确实 `≺ 1`**。卡的是：① `Ψ_s` 是 `H_s`-可测的随机常数，要在对 `H_s` 取条件的法下读恒等式，而 **`RBM.Sample` 没有滤子、没有 Markov 性**，`MomentDuhamel.Hyp` 是对 `(u,H_u)` 的**确定性**试验函数的接口；② `Φ_u` 带可加泛函 `∫_s^u(U∘F)`，要把状态扩成 `(H_u, A_u)`、生成元加 `(U∘F)_u ∂_A`。**两条都是接口决策，不是引理。**

**因此 T216 交的是绕开 `M_m` 的那条路**：`flowEq548_of_jSfar` 直接产出 `Step45.FlowEq548`，**假设表只有 `hnear` + `jSfar ≺ 1`，无 `M_m`、无鞅、无漂移包**。

**本单另一条已编译的否定结论（新发现）**：把 `jSfar` 塞进 `MomentDuhamelCut.CutHyp` 自举**不可行**。`ℓ*_u` 随 `u` **单增**（`ellStar_mono_time`），远场族只会**变小**（`far_mono_time`），所以 `6ℓ*_u` 越过某个实现距离时 `jSfar` **向下跳整整一个 `‖lk‖/T`**（`lkFar_crossing`）——而 `CutHyp.modulus` 是**双侧**模、`stochDom_of_net` 要 `ContinuousOn`，两者都不成立。**所以 T216 没有定义 `FarHypCut` 这个结构**——写出来就是一个不可满足的包，正是本项目的头号缺陷。

**可满足性**：`cFarStep'_detDom_far_critical`（正向，网格 `s_N = 1−1/(N+1)`、**`M_f = (N+1) = (1−s)^{−1}` 即 (5.35) 真给的大小，不是退化的 0**）与 `cFarStep'_apriori_not_detDom`（反向，同一组数据只换 `M_m` 槽），打包为 **`Mm_slot_decides`**。退化检查：`farMart_self`（`v = s` 时亏量 = 0，该条**空**而非假）；`one_le_jSfar`（`jSfar ≥ 1` 恒成立，`≺ 1` 是**临界**请求，不能由 `jSfar ≡ 0` 平凡满足）；`ω = 0` 无风险——全文件没有对全体 `ω` 的量化。

## ⭐ 待 Jun 定夺 D15（T216 逼出来的；前两条碰 CLAUDE.md 规则 6 的边界）

**`M_m ≺ 1`（(5.45) 的远场鞅界）三选一：**

1. **给 `RBM.Sample` 加滤子 + 流的 Markov 性接口**（矩路线做 BDG 的前提 ①）。碰随机层边界，需要 Jun 拍板。
2. **把 `MomentDuhamel.Hyp` 的生成元扩展成带可加泛函 `A_u`**（前提 ②）。接口变更，不是引理。
3. **两条都不做时的替代路（T216 认为最具体可行、且不碰随机层）**：把 (5.48) 远场半边的阈值从 `6ℓ*_u` **放宽到 `12ℓ*_u`**，并把指示函数在 `[6ℓ*_u, 12ℓ*_u]` 上**光滑化**。这样远场泛函在 `u` 上**连续**（`ℓ*_u` 连续），`CutHyp` 自举重新可用，**`M_m` 整条线可以删掉**。代价是要改 `Step45.lean:339`（硬编码的 `6`）与 `Step2MomentStep.flowEq548_of_near_far`；下游 `decay_of_split` 用的是 Step 4 的一致界，**初看能吞下 `6 → 12`**。

⚠ 注意：若选 3，则 T216 已交的 `flowEq548_of_jSfar` 就是现成的落点；若选 1 或 2，则要新开单做接口。

## ⚠ 无主的活（T216 交出）

1. **`FarInputs'` 的第四条建议删除**，下游改用 `Step2FarMart.flowEq548_of_jSfar`——`farMart_far_equiv` 证明它与结论等价，留着只是把 (5.48) 远场半边换了个名字。若保留，它现在**由定理供给**（`farInputs'_of_far_apriori`）。
2. **`step_bound_far'` 拆成两半**：初值项+漂移积分那段 = `Step2FarMart.norm_init_add_drift_le`；拆完 `step_bound_far'` 与 `lkErr_far_le'` 都可改写成 `far_bound_of_farMart(_tT)` 的一行推论。
3. **`farInputs_of_farInputs'` 的 `hmartAll`（对**所有** `a` 要鞅界）按 T208b 不可满足**——建议加 `@[deprecated]`。`FarInputs'` 自身只在远场要求，是对的。（`Step2FarInputs.lean` 当时在 T215 手里，故未加。）
4. **`FarInputs'`/`HighProb` 的形状 vs `StochDom`**：`flowEq548_of_farInputs'_detDom` 要一条**确定性**的 `M_m ≺ 1` 加高概率事件，而矩路线的自然输出是 `StochDom`，两者之间要一次对角抽取（`τ_N → 0`）。**本单没做**，也是建议直接走 `flowEq548_of_jSfar` 的理由之一。
