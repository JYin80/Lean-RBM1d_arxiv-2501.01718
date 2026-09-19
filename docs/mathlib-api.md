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
| `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`（`...Measure.MeasureSpace` 已弃用） | `Measure`、`measure_mono`、`measure_union_le`、`measure_iUnion_fintype_le`、`measure_empty` |
| `ENNReal.ofReal_add`、`ENNReal.ofReal_mul`、`ENNReal.ofReal_natCast`、`ENNReal.ofReal_le_ofReal` | |
| `Real.le_sqrt`、`Real.one_le_sqrt`、`eq_inv_mul_iff_mul_eq₀`、`div_le_of_le_mul₀` | |
| `sq_sum_le_card_mul_sum_sq`（需 `Mathlib.Algebra.Order.Chebyshev`） | Cauchy–Schwarz 的求和形式 |
| `Matrix.exists_mulVec_eq_zero_iff`、`Matrix.IsHermitian.im_star_dotProduct_mulVec_self` | |
| `List.range'_concat` | |
| `add_le_add_left` 参数形式已变 → 用 `add_le_add le_rfl _` | |
| `dotProduct_star_self_eq_zero` 要 `StarOrderedRing`，`ℂ` 只在 `ComplexOrder` 下有 | |
| `Lean.collectAxioms` | `#print axioms` 的底层；`Test/Axioms.lean` 用它做硬性审计 |
| `Real.exp_lt_one_iff`（**不是** `Real.exp_lt_one`，后者不存在）、`Real.exp_le_one_iff` | `exp x < 1 ↔ x < 0` |
| `Complex.norm_le_abs_re_add_abs_im` | `‖z‖ ≤ \|re z\| + \|im z\|` |
| `List.getD_replicate` | 首个参数 `a` 显式：`List.getD_replicate _ (h : i < n)` |
| `inv_le_iff_one_le_mul₀`、`inv_le_iff_one_le_mul₀'`、`inv_anti₀` | 倒数不等式 |
| `Finset.single_le_sum`（`f` 常需 `(f := …)` 显式给出） | 非负和 ≥ 单项 |

## 有限和、树求和（`Loop/Cor35.lean`、`Loop/Layer.lean`、`Loop/SumZero.lean`）

| 名字 | 说明 |
|---|---|
| `Finset.prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i)` | 非负乘积的单调性（**不是** `Finset.prod_le_prod`，后者在本工具链里是有序幺半群版、只收一个参数） |
| `div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d` | |
| `Finset.prod_univ_sum` + `Fintype.piFinset_univ` | `∏ i, ∑ j, f i j = ∑ x : ∀ i, _, ∏ i, f i (x i)`（标号和的 Fubini） |
| `Equiv.piSplitAt i β : (∀ j, β j) ≃ β i × (∀ j : {j // j ≠ i}, β j)` | 把一个坐标单独拿出来求和（`sum_out`） |
| `Fin.consEquiv α : α 0 × (∀ i, α i.succ) ≃ ∀ i, α i`、`List.ofFn_succ` | 列表和 `allSum` ↔ `Fin n → _` 上的和 |
| `Equiv.sum_comp e f`（对 `Equiv.Perm` 要写全名 `Equiv.sum_comp e`，点记号会解析成要 `hs` 的 `Equiv.Perm.sum_comp`） | 换元 |
| `Finset.sum_fiberwise_of_maps_to (h : ∀ i ∈ s, g i ∈ t) f` | 按纤维分组求和（分层 `sum_TSPlong`） |
| `geom_sum_Ico_le_of_lt_one`（需 `Mathlib.Algebra.Order.Field.GeomSum`） | `∑_{Ico m n} x^i ≤ x^m/(1-x)` |
| `Fin.prod_univ_castSucc`、`Fin.last_add_one`、`Fin.val_add_one_of_lt`、`Fin.castSucc_lt_last`、`Fin.prod_univ_eq_prod_range` | 循环乘积写成 `range` 上的积（`prod_cyc`） |
| `Finset.prod_range_mul_prod_Ico`、`Finset.prod_Ico_consecutive`、`Finset.prod_Ico_eq_prod_range`、`Finset.prod_eq_prod_Ico_succ_bot` | 区间乘积的拼接与平移 |
| `Complex.mul_conj' : z * conj z = ‖z‖ ^ 2` | `m(+) m(−) = \|m\|² = 1` |
| `ZMod.neg_val : (-a).val = if a = 0 then 0 else n - a.val` | |
| `Function.update_of_ne (h : a ≠ a') v f : update f a' v a = f a`、`Function.update_self` | |
| `Finset.filter_image : (s.image f).filter p = (s.filter (p ∘ f)).image f` | |

## 本工具链里已弃用的名字

| 旧 | 新 |
|---|---|
| `if_pos` / `if_neg` | `ite_eq_left` / `ite_eq_right` |
| `dif_pos` / `dif_neg` | `dite_eq_left` / `dite_eq_right` |
| `ite_cond_eq_false`、`dite_cond_eq_true` | `ite_eq_right_of_eq_false`、`dite_eq_left_of_eq_true` |
| `if_true` | `ite_true` |
| `push_neg` | `push Not` |
| `mul_le_one₀` | 无替代，用 `mul_le_mul … ` 等拆开 |
| `Fin.coe_castSucc` | `Fin.val_castSucc` |
| `List.getLast?_eq_getLast` | `List.getLast?_eq_some_getLast` |
| `Mathlib.Data.Real.Sqrt` | `Mathlib.Analysis.Real.Sqrt` |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `zero_le _`（带参数） | `zero_le`（参数已隐式） |
| `if_pos h` | `ite_eq_left h`（仍可用 `if_pos`，但报弃用） |
