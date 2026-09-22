# Historical Phase 1 plan

Archived from `CLAUDE.md` on 2026-09-22 because its "next goal" was no longer the live project priority. Consult current `docs/STATUS.md` and `docs/TASKS.md` for scheduling.

Phase 1 传播子 Θ_ξ 已完成到 `Propagator/Support.lean`，全绿 0 sorry。

**下一个目标：(2.52) 的锐化指数衰减。** 现有的 `norm_Theta_apply_le_pow` 衰减长度由 `1-|ξ|` 控制，
论文要的是由 `|1-ξ|` 控制，即 `ℓ̂(ξ) = min(|1-ξ|^{-1/2}, L)`。两者在 `ξ = t·m²` 区制差别巨大。

路线（**不要走附录 B 的围道平移 + Poisson 求和**，d=1 最近邻有闭式解，代价低得多）：

1. 构造 `ρ(ξ)`：`ρ² − (3/ξ − 1)ρ + 1 = 0` 中模 < 1 的那个根。
   重根只在 `ξ = 1` 或 `ξ = -3` 出现，都不在 `|ξ| < 1` 内，可排除；`ξ = 0` 单独处理（`Θ = I`）。
2. 证闭式 `(Θ_ξ)_{xy} = c(ξ)·(ρ^d + ρ^{L−d})`，`d = (x−y).val`。
   做法是把闭式代回验证 `(1 − ξ S) Θ = 1`，再用已有的 `RBM.eq_Theta_of_mul` 收口 —— 有限的 `ZMod` 分情况代数。
3. **写证明之前**先在 `RBM1D/Test/Sanity.lean` 加 `L = 5, 7`、`ξ = 1/2` 的 `norm_num` 数值自洽检查，
   防止闭式抄错却「证明通过」。
4. (2.52)(2.53)(2.54) 和 (3.35)(3.36) 的锐化版全部建立在闭式之上。

`Propagator/Symbol.lean`（附录 B 的 Fourier 表示 (B.1)）仍然要做，但作为独立的结构性结果
（下游 (3.48) 会用 Fourier 形式），**不作为衰减估计的依赖**。
