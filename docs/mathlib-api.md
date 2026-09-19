# Mathlib API notes（Lean 4.34.0 / Mathlib `5ed2965256`）

「这个东西在 Mathlib 里叫什么、签名长什么样」的核实记录。每条都在本仓库的工具链上编译确认过。
原 `RBM1D/Probe.lean`（Phase 1 的 API 侦察本）的结论已并入本文件，文件本身已删除。
**新的侦察请用 scratch 文件**（`lake env lean /tmp/xxx.lean`），确认后把结论补到这里。

## 矩阵、算子范数（`Propagator/Basic.lean`）

需要 `open scoped Matrix.Norms.Operator`（ℓ∞ 算子范数）。在这个 scope 下以下实例都能 `infer_instance`：

| 事实 | 说明 |
|---|---|
| `NormedRing (Matrix n n ℂ)`、`NormedAlgebra ℂ (Matrix n n ℂ)` | 算子范数 |
| `NormOneClass (Matrix n n ℂ)`、`HasSummableGeomSeries (Matrix n n ℂ)` | Neumann 级数可用 |
| `norm_smul c A : ‖c • A‖ = ‖c‖ * ‖A‖` | |
| `((Units.oneSub t h)⁻¹ : Matrix …) = ∑' i, t ^ i` | **定义性相等（`rfl`）** |
| `Matrix.linfty_opNNNorm_def` | 行和的 sup |
| `Ring.inverse_unit`、`Ring.inverse_mul_cancel`、`Ring.mul_inverse_cancel` | `Theta` 用 `Ring.inverse` 定义 |
| `Units.val_oneSub` | |
| `Matrix.submatrix_mul_equiv`、`Matrix.submatrix_one_equiv` | 平移不变性（沿 `Equiv.addRight` 共轭） |
| `Matrix.circulant_apply`、`circulant_mul`、`circulant_mul_comm`、`circulant_inj`、`circulant_sub`、`circulant_smul`、`circulant_single_one` | 循环矩阵 |
| `Matrix.mulVec_mulVec`、`mulVec_smul`、`smul_mulVec`、`Matrix.sum_apply` | |
| `Matrix.kroneckerMap_transpose`、`kronecker_apply`（记号 `⊗ₖ`，`open scoped Kronecker`） | `Defs/Model.lean` |
| `Matrix.diagonal_mul_diagonal`、`diagonal_conjTranspose`、`smul_one_eq_diagonal`、`diagonal_smul` | |

## 级数与极限

| 名字 | 说明 |
|---|---|
| `Summable.tsum_le_tsum`、`norm_tsum_le_tsum_norm`、`norm_pow_le` | |
| `tsum_geometric_of_lt_one`、`summable_geometric_of_lt_one`、`geom_sum_mul`、`smul_pow` | |
| `eventually_nhdsWithin_of_eventually_nhds` | (2.51) 的邻域论证 |
| `tendsto_rpow_atTop`、`tendsto_natCast_atTop_atTop` | `Defs/Domination.lean`：`N^τ → ∞` |
| `Real.rpow_add'`、`Real.rpow_nonneg`、`Real.one_le_rpow` | |

## 导数（`Propagator/Deriv.lean`、`Loop/Primitive.lean`）

| 名字 | 说明 |
|---|---|
| `HasDerivAt.comp_ofReal` | ℂ 上的导数拉回到 ℝ 变量（`Mathlib.Analysis.Complex.RealDeriv`） |
| `HasDerivAt.mul_const`、`HasDerivAt.const_mul`、`HasDerivAt.mul`、`HasDerivAt.fun_sum` | 需 `import Mathlib.Analysis.Calculus.Deriv.Mul` |
| `HasDerivAt.congr_deriv` | 换导数值；函数须定义性相等。比 `convert` 可靠（`convert` 会把函数相等拆成单独目标） |
| `HasDerivAt.unique` | 导数唯一，用来证「不是解」 |
| `HasDerivAt.mul` 给出的函数是 Pi 乘法 `f * g`；用 `congr_deriv` 接到 `fun s => f s * g s` 上即可 | |

## ZMod、特征标、Fourier（`Propagator/Symbol.lean`）

| 名字 | 说明 |
|---|---|
| `ZMod.val_add`、`ZMod.val_lt`、`ZMod.val_cast_of_lt`、`ZMod.val_natCast_of_lt`、`ZMod.neg_val`、`ZMod.natCast_zmod_val`、`ZMod.val_injective`、`ZMod.card` | |
| `ZMod.stdAddChar : AddChar (ZMod N) ℂ`，`j ↦ exp(2πi j/N)` | `ZMod.stdAddChar_apply`、`ZMod.toCircle_apply`（`.val` 形式） |
| `ZMod.isPrimitive_stdAddChar N` | |
| `AddChar.sum_mulShift b hψ : ∑ x, ψ (x * b) = if b = 0 then card else 0` | 特征标正交性（结果带 `ℕ → ℂ` 的 cast） |
| `AddChar.map_add_eq_mul`、`AddChar.map_neg_eq_inv`、`AddChar.norm_apply` | `‖ψ x‖ = 1`（有限群） |
| `Complex.two_cos : 2 * cos x = exp (x * I) + exp (-x * I)` | |

## Hermitian 谱定理（`Delocalization.lean`）

文件在 **`Mathlib/Analysis/Matrix/Spectrum.lean`**（不在 `LinearAlgebra/Matrix/`）。

| 名字 | 说明 |
|---|---|
| `hA.eigenvalues : n → ℝ`、`hA.eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)` | |
| `hA.eigenvectorUnitary : unitaryGroup n 𝕜`；`IsHermitian.eigenvectorUnitary_apply : U i j = eigenvectorBasis j i` | |
| `hA.spectral_theorem : A = conjStarAlgAut 𝕜 _ U (diagonal (ofReal ∘ eigenvalues))` | 展开后是 `U * D * star U`（`rfl`） |
| `Unitary.coe_star_mul_self`、`Unitary.coe_mul_star_self` | |
| `Matrix.inv_eq_right_inv` | |

## 杂项

| 名字 | 说明 |
|---|---|
| `IsAlgClosed.exists_pow_nat_eq` | 取平方根（`Root.lean`、`Semicircle.lean`；需 `Mathlib.Analysis.Complex.Polynomial.Basic`） |
| `Complex.sq_norm : ‖z‖ ^ 2 = normSq z`、`Complex.normSq_apply`、`Complex.inv_im`、`Complex.div_ofReal_re/im` | |
| `Finset.sum_ite_irrel` | 把与求和变量无关的 `if` 提出和号——折叠 Kronecker δ 的关键 |
| `Finset.sum_ite_eq`、`Finset.sum_ite_eq'`、`Finset.sum_comm`、`Finset.sum_pair` | |
| `Fin.prod_univ_two`、`Fin.prod_univ_four` | |
| `Lean.collectAxioms` | `#print axioms` 的底层；`Test/Axioms.lean` 用它做硬性审计 |
| `Real.exp_lt_one_iff`（**不是** `Real.exp_lt_one`，后者不存在）、`Real.exp_le_one_iff` | `exp x < 1 ↔ x < 0` |
| `Complex.norm_le_abs_re_add_abs_im` | `‖z‖ ≤ \|re z\| + \|im z\|` |
| `List.getD_replicate` | 首个参数 `a` 显式：`List.getD_replicate _ (h : i < n)` |
| `inv_le_iff_one_le_mul₀`、`inv_le_iff_one_le_mul₀'`、`inv_anti₀` | 倒数不等式 |
| `Finset.single_le_sum`（`f` 常需 `(f := …)` 显式给出） | 非负和 ≥ 单项 |

## 本工具链里已弃用的名字

| 旧 | 新 |
|---|---|
| `if_pos` / `if_neg` | `ite_eq_left` / `ite_eq_right` |
| `dif_pos` / `dif_neg` | `dite_eq_left` / `dite_eq_right` |
| `ite_cond_eq_false`、`dite_cond_eq_true` | `ite_eq_right_of_eq_false`、`dite_eq_left_of_eq_true` |
| `if_true` | `ite_true` |
| `push_neg` | `push Not` |
| `List.getLast?_eq_getLast` | `List.getLast?_eq_some_getLast` |
| `Mathlib.Data.Real.Sqrt` | `Mathlib.Analysis.Real.Sqrt` |
