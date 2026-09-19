# 形式化路线图

## 项目形状（为什么是这个形状）

1. **Mathlib 没有随机分析**：没有 Itô 公式、矩阵布朗运动、SDE、Dyson Brownian motion。
   论文 §2.4 之后的随机流（(2.34)–(2.47)、Lemma 2.18–2.20、Thm 2.21 的六步）**目前在 Lean 里无法证明**，
   只能作为 `axiom` 接口挂起来。
2. **可完全形式化的是确定性内核**：§2.5（传播子 Θ_ξ）+ 附录 B + §3（K 的树表示、Ward 恒等式、sum-zero）。
   纯线性代数 / 组合 / ODE，且正是论文的原创核心。
3. 所以：**自下而上建确定性骨架，随机层留接口。**

## 阶段表

| 阶段 | 内容 | 依赖 | 状态 |
|---|---|---|---|
| 1 | 传播子 Θ_ξ：Def 2.13、Lemma 2.14、(2.51)–(2.54)、(3.35)(3.36)、附录 B (B.1) | — | 进行中，见 STATUS.md |
| 2 | Def 2.9/2.10 的 loop 与 cut-and-glue 算子 `G^(a)_k`、`G^(a),L_{k,l}`、`G^(b),R_{k,l}`：纯粹是 (σ, **a**) 指标数据上的组合操作 | — | 未开始。先把索引类型设计对，这是整个 §3 的地基 |
| 3 | Def 2.12 原始方程 + Lemma 3.2（多边形典范划分 ↔ 无交叉配对）+ Def 3.3 + Lemma 3.4 树表示 | 1, 2 | 未开始 |
| 4 | Lemma 3.6 K 的 Ward 恒等式 + Cor 3.7 | 3 | 未开始 |
| 5 | Cor 3.5、Lemma 3.10 sum-zero、Lemma 3.11 K 的界 | 4 | 未开始 |
| 6 | Thm 2.2（由 local law 推 delocalization，(2.10)）、Lemma 2.8（z_t 流的代数） | 1 | 未开始。独立小块，可随时穿插，用 Mathlib 的 Hermitian 谱定理 |
| — | 随机层（Itô、loop hierarchy (2.45)、Thm 2.21、Lemma 2.18–2.20、universality） | — | **不形式化**，写成 `axiom`，让主定理的逻辑骨架能编译 |

### 阶段 3 的关键技巧

不要先证 ODE 的存在性。**把树公式当定义**，再证它满足 (2.48)；唯一性用 Gronwall
（Mathlib `ODE_solution_unique`）。

### 阶段 4 的形式化友好点

论文的证明是「差 D 满足齐次线性 ODE + 零初值」，这个结构直接搬得动。

## Phase 1 剩余清单

- `Propagator/Decay.lean` —— (2.52)(2.53)(2.54) 锐化版，走闭式 ρ 路线（详见 CLAUDE.md）
- `Propagator/Symbol.lean` —— 附录 B (B.1) 的 Fourier 表示：
  `Shat p = (1 + 2cos(2πp/L))/3`、`SB_mulVec_char`、`one_sub_xi_Shat_ne_zero`、`theta_apply_fourier`
- `Defs/Domination.lean` —— Def 2.1 (ii) 的确定性 ≺：
  `def DetDom (ξ ζ : ℕ → ℝ) : Prop := ∀ τ > 0, ∀ᶠ N in atTop, ξ N ≤ N ^ τ * ζ N`
  （概率版本 (i)(iii)(iv) 等随机层启动时再加）
- 删掉 `RBM1D/Probe.lean`
- `leanblueprint checkdecls` 通过

## Phase 1 完成标准

1. `./check.sh` → 零 error、零 sorry
2. `#print axioms` 对每条主定理只出现 `propext / Classical.choice / Quot.sound`
3. `Test/Sanity.lean`：L=5,7、ξ=1/2 在 ℚ 上数值验证 `(1 − ξS)Θ = I` 与闭式公式
4. `leanblueprint checkdecls && leanblueprint web` 通过
5. 人工复核 PDF p.19–21（Def 2.13、Lemma 2.14）与 p.89–91（附录 B），
   特别确认 `ℓ̂(ξ) = min(|1−ξ|^{-1/2}, L)` 的定义、以及 (2.52) 分母上的 `|1−ξ|·ℓ̂(ξ)`

## 风险与对策

| 风险 | 对策 |
|---|---|
| Mathlib 版本 API 漂移 | 锁死 `v4.34.0`；不确定的名字先 grep `.lake/packages/mathlib/` 或 `Probe.lean` `#check` |
| 闭式解的边界情形（ξ=0、L 偶、ρ 重根） | ξ=0 单独处理（Θ=I）；重根只在 ξ=1 / ξ=−3，不在 \|ξ\|<1 内 |
| 显式常数 C、c 的追踪很痛 | 统一 `∃ C > 0, ∃ c > 0, ∀ ...`，不求最优；≺ 用 `DetDom` 封装 |
| 范围蔓延 | 蓝图依赖图是唯一进度真相；Phase 1 不碰随机层任何东西 |

## 蓝图

`blueprint/src/content.tex` 写**整篇论文**的骨架（章节 + 每条定理的壳子和 `\uses{}`），
但只给已形式化的节点填 `\lean{}` 和 `\leanok`。依赖图配色：
绿 = 已形式化，蓝 = 已陈述未证，灰 = 仅在蓝图里（随机层）。
渲染需要 `pip install leanblueprint`，`leanblueprint web` 产出可推 GitHub Pages。
