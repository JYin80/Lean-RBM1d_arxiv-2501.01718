# 最终 Lean 报告（骨架，活文档）

> **本文件是 T200 起草的活文档。** 它的唯一价值在于**诚实**：
> 凡是「化归」就写化归，凡是「空着」就写空着，不许写成「已证明」。
>
> **数据来源纪律**：本文件里每一条「Lean 名 + 假设表 + 有没有生产者」都是
> **在 scratchpad 里编译探针打印出来的**，不是从 `docs/STATUS.md` / `docs/TASKS.md` 的叙述里抄的
> （那些叙述会过时——`docs/agent-playbook.md` 第二节记了五次实例）。
> 探针清单见 §8。**探针不入库**，相关结论一律标注为「编译过但未入库」。
>
> **基准快照**：`git HEAD = 2bde09d`，构建树时间 2026-09-21 09:52（`build.log`：`errors: 0`、
> `lake build exit=0`、3865 jobs）。当天有九个 agent 并发写码，工作树里有若干**尚未 import 进
> `RBM1D.lean`** 的新文件（`Gauss/DimsExample.lean`、`Flow/Thm221NoEL.lean`、
> `Gauss/Lemma514Q716.lean`、`Gauss/MomentDuhamelHypGauss.lean`、`Hierarchy/Step2Near47.lean`、
> `Hierarchy/Step2FarInputs.lean`）——**本文件的所有计数与「无生产者」判定不包含它们**，
> 涉及处已逐条注明日期。

> **快照之后已落地（协调者 2026-09-21 补记，`lake build RBM1D` exit=0、审计 10542 条）**：
> - **T202** `Gauss/DimsExample.lean` 已 import。§5 记的「`Gauss.Dims` 只有 `Band.toDims`，而 `Band`
>   只有 `Gauss.band : Dims → Band`，在 HEAD 上循环」**已解除**：`Dims.example` 与非退化的
>   `Dims.exampleGrow` 都是无条件定理。同时 `OpNormBound` 确认已卸（`opNormBound_gauss` 无条件）。
> - **T203** `hKb` 从假设变成定理（`hKb_flow`），`lemma514_forall_of_hHol_flow` 的假设表里没有它了。
> - **T204** `Flow/Thm221NoEL.lean` 已 import。§1 记的「Thm 2.3/2.4 吃 `Thm221`（❌无生产者）」
>   现在多了一条**不含 (2.71)** 的平行路线：`Thm221NoEL'` → Lemmas 2.18–2.20 → Thm 2.3 与
>   Thm 2.4 的 (2.6)(2.7)，结论一字未改。**R4 因此已被 D12/D13 裁定回答**（选 (a)：先做不含
>   (2.71) 的第一遍，(2.71) 的归纳与 Step 6 样本侧归 T205）。
> - `RBM.Bounds` 在 `s > 0` 处仍无居民这条**仍然成立**，但只对带 `expect` 的那一侧；
>   `BoundsCore` 一侧已由 `boundsCore_gauss_witness` 给出非退化见证。

---

## 目录

1. 主定理清单（Lean 名 + 完整假设表 + 状态）
2. Theorem 2.21 的六步链：当前到哪一步
3. 外部输入声明
4. 公理审计
5. 没有生产者的具名假设（点名到字段级）
6. 方法学附录：空真风险与 fiat 风险
7. 建模选择与对论文的偏差（索引）
8. 本报告用到的编译探针
9. 待定夺

---

## 1. 主定理清单

**状态记号**

- **①无条件**：Lean 里是一条不吃任何具名假设的定理（只吃论文里就有的显式条件，如 `0 < η`、`|E| ≤ 2 − κ`）。
- **②化归**：是定理，但结论建立在一条或多条**具名假设**之上；列出假设名，并标明该假设**有没有生产者**。
- **③空着**：Lean 里目前没有对应的陈述，或只有零件没有总装。

「有没有生产者」的判定标准：全环境里**存在一条结论的头常量就是该假设**的声明
（构造子 / 投影 / recursor 排除在外）。探针 P-B（§8）是编译过的。

---

### Theorem 2.2（离域化）

| Lean 名 | 位置 | 状态 |
|---|---|---|
| `RBM.sq_norm_eigenvector_le_im_green` | `RBM1D/Delocalization.lean` | **①无条件** |
| `RBM.sq_norm_eigenvector_le_of_norm_green_le` | 同上 | **①无条件** |
| Theorem 2.2 本身（高概率的离域化界） | — | **③空着** |

**假设表**（`#check @` 打印，探针 P-A）

```
sq_norm_eigenvector_le_im_green :
  ∀ {n} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {η : ℝ},
    0 < η → ∀ (k x : n),
      ‖(hH.eigenvectorBasis k).ofLp x‖ ^ 2 ≤ η * (green H (hH.eigenvalues k + η * I) x x).im

sq_norm_eigenvector_le_of_norm_green_le :
  ∀ {n} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {η C : ℝ},
    0 < η → ∀ (k x : n),
      ‖green H (hH.eigenvalues k + η * I) x x‖ ≤ C → ‖(hH.eigenvectorBasis k).ofLp x‖ ^ 2 ≤ C * η
```

两条都**不吃任何具名假设**：这是论文 (2.10) 的确定性内核，逐字对应。

**缺的是概率那一半**，而且不只是记账（T147 §1）：谱参数 `λ_k(ω)` 是**随机的**，
而 `RBM.localSemicircleLaw_of_Thm221N_of_z` 是对**确定性**的列 `z : ℕ → ℂ` 陈述的，
需要一个能量方向的覆盖论证。零件已在 `Delocalization.lean`（2026-09-21 T199 当日新增，
**在工作树里，尚未提交**）：`sum_sq_norm_eigenvectorBasis`、`abs_poisson_sub_le`、
`im_green_lipschitz_energy`（`Im G_xx` 对能量 `η^{-2}`-Lipschitz）、
`sq_norm_eigenvector_le_of_norm_green_le_near`（在**邻近的确定性能量**处的确定性内核）。
**总装尚未完成。** 相关 paper-delta：#5。

---

### Theorem 2.3（局部半圆律）

| Lean 名 | 状态 |
|---|---|
| `RBM.localSemicircleLaw_of_Thm221` | **②化归** |
| `RBM.localSemicircleLaw_of_Thm221'` | **②化归**（吃带增益的 `Thm221'`） |
| `RBM.localSemicircleLaw_of_Thm221N` / `..N'` | **②化归**（能量随 `N` 变，T194） |
| `RBM.localSemicircleLaw_of_Thm221N_of_z` / `..N'_of_z` | **②化归**（⭐陈述里已完全不出现能量参数） |

**假设表**（`localSemicircleLaw_of_Thm221`，探针 P-A 原样）

| 假设 | 类型 | 生产者？ |
|---|---|---|
| `T : Transfer X` | 结构 | ✅ `RBM.Gauss.transfer_gauss` |
| `TransferLoop1 T` | 结构 | ✅ `RBM.Gauss.transferLoop1_gauss` |
| `0 < κ` | — | — |
| **`Thm221 X κ`** | 结构 | ❌ **无生产者**（唯一来源 `Thm221N.toThm221`，而 `Thm221N` 也无生产者） |
| `0 < τ`、`SpecSeq κ τ E z` | 结构 | ⚠ 0 生产者，但 `SpecSeq` 只是「所选谱参数列满足 `0 < Im z ≤ 1`、`\|Re z\| ≤ 2−κ`、`N^{-1+τ} ≤ Im z`」的条件记录，使用者选定 `z` 后逐条验证即可；不是数学缺口 |
| `0 < τ'`、`0 < D` | — | — |

结论是 (2.3)、(2.4)、迹形式三条的合取，逐条是 `B.P {…} ≤ ENNReal.ofReal (N^{-D})` 的 `∀ᶠ N` 形式。

---

### Theorem 2.4（量子扩散）

| Lean 名 | 状态 |
|---|---|
| `RBM.quantumDiffusion_of_Thm221` | **②化归** |
| `RBM.quantumDiffusion_of_Thm221'` | **②化归** |

假设表：`T : Transfer X`（✅）、`0 < κ`、**`Thm221 X κ`（❌ 无生产者）**、`0 < τ`、
`SpecSeq κ τ E z`、`0 < τ'`、`0 < D`。
结论四条：`(+,−)`、`(+,+)` 的高概率形式各一条，以及它们的**期望**形式各一条
（右端 `W^{τ'}(W ℓ η)^{-3}`）。

---

### Theorem 2.5（广义 QUE）

| Lean 名 | 状态 |
|---|---|
| `RBM.theorem2_5_of_QDExpect` | **②化归**（吃 `QDExpect`，✅ 有生产者 `QDExpect.of_Thm221(')`） |
| `RBM.theorem2_5_of_Thm221` / `..'` | **②化归**（吃 `Thm221` ❌ + 两条可积性） |
| `RBM.Gauss.theorem2_5_gauss` | **②化归**（高斯模型；两条可积性**已卸**，只剩 `Thm221 (Gauss.sample d) κ` ❌） |

`theorem2_5_of_Thm221` 的假设表：`T : Transfer X`、`0 < κ`、**`Thm221 X κ`**、`0 < τ'`、
`0 < τ`、`τ < B.c/2`、`E : ℕ → ℝ`、`SpecSeq κ τ' E' (B.queZ τ E)`、
`∀ N x y, Integrable (trGG …)`、`∀ N x y, Integrable (trGGs …)`。
`Gauss.theorem2_5_gauss` 把最后两条卸掉了，所以**它的唯一实质假设就是 `Thm221`**。

结论：(2.12)、(2.13) 的事件概率界，`≤ (size N)^{-τ/6}`。

---

### Theorem 2.6（体区普适性）

| Lean 名 | 状态 |
|---|---|
| `RBM.theorem2_6_of_steps` | **②化归**，三条假设**全部无生产者** |

```
theorem2_6_of_steps :
  ∀ {Ω} [MeasurableSpace Ω] {B : Band Ω} {H} (F : OUFlow B H) (hH : ∀ N ω, (H N ω).IsHermitian)
    {κ : ℝ}, DBMUniversality F κ → GreenComparison F κ → StepTwoClaim F κ →
      BulkUniversality B H hH κ
```

| 假设 | 应该是什么 | 现状 |
|---|---|---|
| `RBM.DBMUniversality F κ` | Theorem 2.6 Step 1 的外部输入 [51] | ❌ 无生产者，且**当前形状不符合 Jun 的永久规则**：它被特化到「我们的流」、跳过了 [51] 的前提。规则要求逐字按 [51] Theorem 2.2 陈述、量化在**所有满足其前提的模型**上 |
| `RBM.GreenComparison F κ` | [37] Thm 15.3 + [70] Prop 4.17 | ❌ 无生产者。按规则**不得**作为外部 input，必须自证 |
| `RBM.StepTwoClaim F κ`（即 (2.23)） | **本文自己的数学**，要 (2.25)–(2.33) | ❌ 无生产者，是真正开放的一块 |

另有 `RBM.OUFlow`（❌ 0 生产者，且只记录了路径的 Hermitian 性与 `H_0 = H`，**未钉死分布**）。

**保真警告**（Cowork 2026-09-21）：取常值流 `H_t ≡ H` 时 `Claim223`/`StepTwoClaim` 平凡成立、
`GreenComparison` 结论平凡，而 `DBMUniversality F` **恰好就是 (2.18)**——
`theorem2_6_of_steps` 在那个流上等于假设了结论。
**任何人不得用常值流或其他 fiat 流去「卸」这三条假设。**

§7.2 那一半（QUE 相）：`RBM.que_flow_of_eq747`、`RBM.measure_bad_flow_of_eq747` 已形式化，
压在 `RBM.Eq747` 上；`Eq747` 有一个**条件**生产者 `RBM.GUEPhase.eq747_of_inputs`，
其输入 `RBM.GUEPhase.Eq747Inputs`（字段 `law726`、`eq729`、`integrable_pp`、`integrable_pm`）
与 `RBM.GUEPhase.GUEFlow`（字段 `Ht`、`hermitian`）**均无生产者**。

---

### Theorem 2.21

**没有任何一个版本有生产者。** 探针 P-B 原样输出：

| Lean 名 | 字段 | 生产者 |
|---|---|---|
| `RBM.Thm221` | `step` | 仅 `RBM.Thm221N.toThm221`（而 `Thm221N` 无生产者） |
| `RBM.Thm221'`（带 `N^c` 增益的 (2.72)） | `step` | 仅 `Thm221.toThm221'`、`Thm221Reg.toThm221'`、`Thm221N'.toThm221'` |
| `RBM.Thm221Reg`（(2.72) 逐字 + 区间条件，**D13 裁定的最终形式**） | `step` | 仅 `Thm221.toThm221Reg` |
| `RBM.Thm221N` / `Thm221N'`（能量随 `N`） | `step` | `Thm221N`：**0**；`Thm221N'`：仅 `Thm221N.toThm221N'` |

也就是说：**全部是互相转换，没有一条是从六步走上来的。**

`Thm221.step` 的形状（`Flow/Hypotheses.lean:317`）：

```
step : ∀ E, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
  (∀ N, t N < 1) → Cond272 B E s t → Bounds X E s → Bounds X E t
```

`Bounds` = `BoundsCore`（(2.68) `LmK`、(2.69) `decay`、(2.70) `localLaw`）+ (2.71) `expect`。

> **D13（Jun 2026-09-21 16:25）**：论文 Theorem 2.21 补上 `t ≤ 1 − N^{−1+τ}`；
> Lean 的最终 `Thm221` 取 `Cond272Reg`，`Thm221'`（带增益）降为推论。
> `RBM1D/Flow/Thm221NoEL.lean`（T204，2026-09-21，**工作树中，未提交、未 import**）
> 在做不含 (2.71) 的变体。

---

### Lemmas 2.18–2.20

**这一块是真正证出来的东西**：从 `Thm221` 出发沿 p.24 的时间网格 `n₀` 次迭代。

| Lean 名 | 状态 |
|---|---|
| `RBM.Bounds_of_Thm221` | **②化归**（吃 `Thm221`） |
| `RBM.Bounds_of_Thm221'` | **②化归**（吃 `Thm221'`；T179 证明这个更弱的版本就够） |
| `RBM.Bounds_of_Thm221Reg` | **②化归**（吃 `Thm221Reg`，D13 的最终形式） |
| `RBM.BoundsN_of_Thm221N` / `..'` | **②化归**（能量随 `N`，T194） |
| `RBM.stochDom_norm_Lval_of_Thm221` / `..'` | **②化归**——Lemma 2.18 的 **(2.61)** |

```
Bounds_of_Thm221 : ∀ {Ω} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E κ : ℝ},
  0 < κ → Thm221 X κ → |E| ≤ 2 - κ →
    ∀ {τ : ℝ}, 0 < τ → ∀ {t : ℕ → ℝ},
      (∀ N, 0 ≤ t N) → (∀ᶠ N in atTop, (N:ℝ) ^ (-1 + τ) ≤ 1 - t N) → Bounds X E t
```

除 `Thm221` 外**不吃任何具名假设**——时间网格、`N^ε` 损失的吸收、(2.67) 的初值都是定理。

---

## 2. Theorem 2.21 的六步链：当前到哪一步

`RBM.Steps`（`Flow/Hypotheses.lean:387`，八个字段 `apriori` `weakLaw` `localLaw`
`aprioriDecay` `sharpLoop` `sharpLmK` `sharpDecay` `sharpExpect`）**无生产者**——
这是**设计如此**（T149）：把整包当假设去产它自己的后面字段是循环的（T147 §0a 用探针证过）。
真正的接线走五条拆开的陈述 `AprioriFlow` / `LocalLawFlow` / `AprioriDecayFlow` /
`SharpLoopFlow` / `SharpLmKFlow`。

> ⚠ **一条必须写明的方法学更正**：探针 P-B（按结论头常量找生产者）对这五条报「无生产者」，
> 这是**假阴性**——它们是 `def`，步骤定理的结论是它们的**定义展开**。
> 探针 P-C 用**裸 `:=`**（无 `convert`、无 `simp`）把步骤定理的结论直接喂进这五个槽，**四条全过**：
> `apriori_of_step1`、`localLaw_of_step2_cut`、`sharpLoop_of_glue`、`sharpLmK_of_glue`。
> 所以**凡是 `def` 形状的假设，本报告一律不用 P-B 的结论**，只用逐条的 P-C 式探针。

| 步 | 主定理 | 携带的具名假设 | 生产者 |
|---|---|---|---|
| Step 1 (2.73)(2.74) | `RBM.Step1.step1` | `Step1.Hyp`（字段 `scaling` `lift` `lemma41` `cont`）、`BoundsCore X E s`、`Cond272`、`∀ᶠ N, N^c ≤ Wℓ_tη_t` | ✅ `Step1.Hyp` 有 5 个高斯生产者（`Gauss.step1Hyp_gauss_of_scale''` 等） |
| Step 2 (2.75)(2.76) | `RBM.MomentDuhamelCut.step2_cut`（截断矩路线，T197 起是活路径） | **`MomentHypCut X E s t D`（字段 `cut : CutHyp …`、`init`）** + `Step1.Hyp` + `BoundsCore` + `hregS` | ❌ **`MomentHypCut` 无生产者**。`CutHyp` 只有两个：可满足性见证 `MomentDuhamelCut.satCutHyp`（取 `J ≡ Θ ≡ 1` 的临界标度，**不是真 `J*` 的生产者**）与投影 `MomentHypCut.cut` |
| Step 2（旧的两条路线） | `RBM.Step2.step2`（路线 A）、`RBM.Step2Moment.step2`（路线 B） | `Step2.Hyp`（`H` `eG` `δ₀` `δ₀_pos` `mart` `cont`）、`Step2Moment.MomentHyp`（15 字段，硬字段 `step`） | ❌ 两者**均无生产者**；路线 B 的 `MomentHyp.step` 已被 T132c **编译成「按冻结形状不可证」的定理** |
| Step 3 (2.77) | `RBM.Step2PP.flow_sharpLoop_glue_flowAs'` | `AprioriFlow`、`LocalLawFlow`、`hΘ`（← `Step2PP.BootPP`）、`h514`（`Step3.Lemma514`） | ✅ `BootPP` 3 个生产者；`Step3.Lemma514` 9 个生产者 |
| Steps 4/5 (2.78)(2.79) | `RBM.Step2PP.flow_steps45_glue_flowAs'` | 上面几条 + `StepGlue.Eq45Flow`、`Step45.FlowEq548` | ✅ `Eq45Flow` 9 个；`FlowEq548` 2 个（`Step2MomentStep.flowEq548_of_near_far(Inputs)`） |
| Step 6 (2.80) | `RBM.Step6.sharpExpect_step6` | `Step6.Hierarchy`、`Step6.FastDecayHyp`、`Step6.Eq527` + 一批**样本侧**假设 | ✅ 漂移侧三条都有生产者（T182/T189/T123）；❌ **样本侧四个好集 `FDInputs` / `QuadInputs` / `EGInputs` / `DriftInputs` 零生产者**（都是 `Set Ω`，需要高概率定理），见 §5.2 |

**所以，今天卡住 `Thm221` 的是**（按杠杆排序）：

1. **Step 2 的 `MomentHypCut`**（尤其 `cut.moment`：网点上的截断一步矩界，以及 `init`）——
   Step 2 的三条路线里，A（`Step2.Hyp`，要实例化 `SumZeroDyn.Hierarchy`，已被纪律禁止）
   与 B（`MomentHyp.step`，已被编译证明在冻结形状下不可证）都走不通，
   只剩 T197 的截断路线，而它的接口还没有针对真正的 `J* = jSnorm` 的生产者。
2. **Step 6 的样本侧**——若 D12 选 (a)（去掉 (2.71)/(2.80)），这一整块推迟到 Theorem 2.6 阶段。
3. **把五条产出封成 `Bounds` 再封成 `Thm221.step`** 的总装本身——这一步在树里**还没有人写**。
   （`RBM.Bounds_of_Steps` 只把 `Steps` 包转成 `Bounds`，`Steps` 包本身没人造。）

---

## 3. 外部输入声明

> **（逐字照抄 `CLAUDE.md`「外部输入的边界」与「β = 2 的处理」，Jun 的永久规则）**

**全项目唯一允许的外部输入是 Theorem 2.6 Step 1 所用的 [51]（Landon–Sosoe–Yau）Theorem 2.2 的
复 Hermitian 形式**，必须逐字按其陈述写成假设、量化在所有满足其前提的模型上，
**不得编造类似结论作为 input**；其余一切（包括 Theorem 2.6 的 Step 2/3 与 §7.2）都要自证。
**最终报告必须写明 Universality 部分用了外部 input，其余全部是独立完整的 Lean。**

**β = 2 的处理（Jun 2026-09-21 定为方案 (A)）**：[51]（`paper/1609.09011v3.pdf`）的 Theorem 2.2
字面只陈述 β = 1（`W` 是 GOE，比较对象 `p_GOE`），摘要声称「classical values of β … GOE/GUE」，
正文无 β = 2 的编号定理。我们的矩阵是复 Hermitian，所以**唯一的外部假设 =
[51] Theorem 2.2 逐字、只把 (2.1) 的 GOE 与 (2.9) 的 `p_GOE` 换成 GUE**
（前提 `(g,G)`-正则、时间窗、能量窗、结论形状一字不改）。

**最终报告必须写明这一点**：「[51] 正文陈述 β = 1；此处使用其摘要所声称的 β = 2 版本」。

> **待更新**：Jun 正请 [51] 的作者在 arXiv 版里补上「complex 同理」（2026-09-21）；
> 补上后外部假设改为逐字引用新版，本节措辞随之简化。
>
> 已核过的替代方案 (B)（[35] = Erdős–Péché–Ramírez–Schlein–Yau, CPAM 2010,
> `paper/0905.4176v2.pdf`, Prop. 3.3）**不可用**，三条理由见 `docs/STATUS.md`
> 「Theorem 2.6 外部输入：方案 (A)」。

### 当前实现状态（2026-09-21）：**尚未落实，写「待定」**

Lean 里现有的 `RBM.DBMUniversality` **不是**上面这条规则要求的形状：
它被特化到我们的流、跳过了 [51] 的前提。`RBM.GreenComparison` 也仍是外部假设，
而按规则它**必须自证**。两者都要在 Theorem 2.6 开单时替换 / 卸掉。
**因此本节在 Theorem 2.6 完成之前，结论一栏写「待定」。**

**除 Universality 以外，本项目目前没有任何 `axiom`**（§4）。

---

## 4. 公理审计

**全库审计**（`RBM1D.lean` 末尾的 `#assert_rbm_axioms`，`RBM1D/Test/Axioms.lean`；探针 P-D 复核）：

```
RBM declarations visible from root RBM1D: 10441
axiom audit: 10441 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
```

即：`RBM` 命名空间下 **10441** 条声明，公理依赖**只有** `propext` / `Classical.choice` / `Quot.sound`
三条标准公理；**无 `sorryAx`、无项目自定义 `axiom`**。这条检查是**硬性的**：违规即编译失败。

**逐条 `#print axioms`**（探针 P-E，全部输出 `[propext, Classical.choice, Quot.sound]`）：

`RBM.sq_norm_eigenvector_le_of_norm_green_le`、`RBM.localSemicircleLaw_of_Thm221`、
`RBM.localSemicircleLaw_of_Thm221N_of_z`、`RBM.quantumDiffusion_of_Thm221`、
`RBM.theorem2_5_of_Thm221`、`RBM.Gauss.theorem2_5_gauss`、`RBM.theorem2_6_of_steps`、
`RBM.Bounds_of_Thm221`、`RBM.BoundsN_of_Thm221N`、`RBM.stochDom_norm_Lval_of_Thm221`、
`RBM.Bounds_of_Steps`、`RBM.Step1.step1`、`RBM.MomentDuhamelCut.step2_cut`、
`RBM.Step6.sharpExpect_step6`、`RBM.Gauss.transfer_gauss`。

> ⚠ **「公理干净」不等于「有内容」。** 一条假设若按字面不可满足，下游定理全是空真的，
> 编译器与 `#print axioms` 都发现不了。见 §6。

---

## 5. 没有生产者的具名假设（点名到字段级）

**判定方法**：探针 P-B3 扫全环境里的 `RBM` **结构**（共 57 个），统计有多少声明的结论头常量是它。
零命中 = 仓库里没人能造出它。**对 `def` 形状的假设此法有假阴性**（见 §2 的警告），
`def` 一律另行逐条核。

### 5.1 结构，零生产者（编译过，2026-09-21 09:52 的树；57 个里有 10 个）

| 结构 | 字段 | 诊断 |
|---|---|---|
| **`RBM.Thm221N`** | `step` | ⛔ **主定理链的根**：`Thm221` 唯一的来源就是它 |
| **`RBM.Steps`** | `apriori` `weakLaw` `localLaw` `aprioriDecay` `sharpLoop` `sharpLmK` `sharpDecay` `sharpExpect` | **设计如此**（T149 反循环）：接线走五条拆开的 `def`，不走这个包 |
| **`RBM.MomentDuhamelCut.MomentHypCut`** | `cut : CutHyp …`、`init` | ⛔ **Step 2 活路径的唯一缺口**。`CutHyp` 的 17 个字段里，实质缺的是 `moment`（网点上的截断一步 `2p` 矩界）；其余（`modulus` / `mesh_fine` / `card_le` / `Kmod` / `γ` …）已有 T192/T197 的机器 |
| **`RBM.Step2.Hyp`** | `H : SumZeroDyn.Hierarchy … 0`、`eG`、`δ₀`、`δ₀_pos`、`mart`、`cont` | Step 2 路线 A。**禁止实例化 `SumZeroDyn.Hierarchy`**（CLAUDE.md 矩路线纪律），故此路线已放弃 |
| **`RBM.Step2Moment.MomentHyp`** | `cont` `Kmod` `gam` `Kmod_nonneg` `gam_pos` `holder` `env` `env_le` `meas` `bnd` `thr` `bnd_lt_thr` `init` **`step`** `bnd_poly` | Step 2 路线 B。硬字段 `step` 已被 T132c **证明在冻结形状下不可证**（两条阻塞各编译成一条定理） |
| **`RBM.SumZeroDyn.Lemma510`** | `F_le` `F_decay` `EE_le` `EE_decay` | T58 的遗留；`F` 已由 T163 / T58 在一般回路长度上钉死（`Hierarchy/DriftDef.lean`），但这个包本身仍无人组装 |
| **`RBM.GUEPhase.Eq747Inputs`** | `law726` `eq729` `integrable_pp` `integrable_pm` | §7.2 的 (7.47) 输入；Theorem 2.6 阶段的活 |
| **`RBM.GUEPhase.GUEFlow`** | `Ht` `hermitian` | 同上 |
| **`RBM.OUFlow`** | `Ht` `hermitian` `start` | ⚠ **只记路径、未钉死分布** —— Theorem 2.6 的保真缺口，见 §1 与 §6.3 |
| `RBM.SpecSeq` | `im_pos` `im_le_one` `abs_re_le` `im_ge` `lemE_eq` | ⚠ **不是缺口**：给定一列 `z` 后逐条验证即可（`SpecSeqN.of_z` 就是这么用的） |

### 5.2 `def` 形状，逐条核过、零生产者

| 名字 | 位置 | 诊断 |
|---|---|---|
| **`RBM.DBMUniversality`** | `Flow/Universality.lean` | 外部 [51]。**当前形状违反 Jun 的永久规则**（特化到我们的流、跳过前提），要重写 |
| **`RBM.GreenComparison`** | 同上 | 按规则**不得**作外部 input，必须自证 |
| **`RBM.StepTwoClaim`**（(2.23)） | 同上 | 本文自己的开放数学，要 (2.25)–(2.33) |
| **`RBM.DriftBound.DriftInputs`** | `Hierarchy/DriftBound.lean:587` | Step 6 样本侧好集（`Set Ω`）。**只有定义与消费点，零高概率定理**；文件 docstring 自己写着「是假设不是定理」 |
| **`RBM.QuadInputs`** | `Gauss/Step6DriftSplit.lean:312` | 同上 |
| **`RBM.FDInputs`** | `Gauss/Step6DriftSplit.lean:571` | 同上 |
| **`RBM.EGInputs`** | `Gauss/Step6DriftEG.lean:447` | 同上 |
| `RBM.Step2MomentStep.FarInputs` | `Hierarchy/Step2MomentStep.lean:1632` | T208 正在做（2026-09-21，`Hierarchy/Step2FarInputs.lean`，**未提交、未 import**）。见 §6.4 的 fiat 清单 |

### 5.3 有生产者，但生产者本身是条件的（**不要当成已卸**）

* `RBM.Thm221` ← `Thm221N.toThm221`（`Thm221N` 零生产者）；
  `RBM.Thm221'` ← `Thm221.toThm221'` / `Thm221Reg.toThm221'` / `Thm221N'.toThm221'`（全是转换）。
* `RBM.Gauss.Dims` ← 仅 `RBM.Band.toDims`，而 `RBM.Band` 的唯一生产者是 `RBM.Gauss.band : Dims → Band`
  ——**在 HEAD 上是循环的，整条矩路线原本悬在「`Dims` 有没有居民」上**（滞留审计 B.2）。
  **2026-09-21 T202 已造出居民**：`RBM.Gauss.Dims.example`（`L ≡ 3`、`W = max 1 ⌊N/3⌋`、`c = 1/4`）
  与非退化的 `RBM.Gauss.Dims.exampleGrow`（`L ≈ N^{1/4} → ∞`、`W ≈ N^{3/4} → ∞`、`c = 1/8`）。
  ⚠ 该文件 `RBM1D/Gauss/DimsExample.lean` 在**工作树里，尚未提交、尚未 import 进 `RBM1D.lean`**，
  所以 §4 的 10441 与 §5.1 的计数**不含它**。**整合后请把本条从「风险」改成「已关闭」。**
* `RBM.Gauss.LDENetClose` ← 仅 `Gauss.ldeNetClose_of_lower_bound`；T148 已**编译证明**
  `LDENetClose` 按字面等价于一个**为假**的下界，即它按字面不可证。
* `RBM.MomentDuhamelCut.CutHyp` ← `satCutHyp`（**可满足性见证**，取临界标度 `J ≡ Θ`，
  不是真 `J*` 的生产者）与投影 `MomentHypCut.cut`。

---

## 6. 方法学附录：空真风险与 fiat 风险

### 6.1 这个项目最主要的缺陷不是错证明，是**空真**

**症状**：假设没人能满足 ⟹ 定理空真 ⟹ `lake build` 永远绿、`#print axioms` 也干净。
2026-09-21 一天之内出了**八次**（`docs/agent-playbook.md` §1 的原表）：

| # | 对象 | 病因 | 谁发现 |
|---|---|---|---|
| 1 | `MomentDuhamel.Hyp.EE` / `drift` | 字段无约束；`drift` 对所有矩阵量化 | T145 |
| 2 | `genLK` 多一个 `W⁻¹` | 钉死的 `F` 不是 (5.15) 的 `F` | T132b |
| 3 | `Hyp.integrable` 对 `u ∈ ℝ` 量化 | `u = 1` 处无包络 | T154 |
| 4 | `MinorGood` / `MinorGood'` | `∀ ω` 无事件限制，**对任何 `Ψ` 都假** | T164 → T172 |
| 5 | `FlucBound` 的 `B ≥ 64/65`、`MinorDiffGainUpTo` 同 | `ι` 无基数预算，`B ≍ Ψ` 不可达 | T171 / T176 |
| 6 | `TestFun` / `TestFunT` 对所有矩阵量化 | 非 Hermitian 处预解式无界 | T180 |
| 7 | `hMδ` / `hδC` 写成 `∀ p ∀ N` | 论文是「`p` 固定、`N → ∞`」，**整条端到端定理空真** | T188 |
| 8 | `hkerC` 的短窗口条件 | **在论文自己的网格上为假** | T192 → T195 |

### 6.2 项目采取的机制

1. **编译过的可满足性见证**（不接受散文论证）。每条新假设要做：
   (a) 退化样本点（`ω = 0`、单个对角坐标拉大）；(b) 退化参数（固定 `N` 令 `p → ∞`、窗口塌缩、`Λ = Φ = 0`）；
   (c) **量词次序对照论文**（渐近条件一律写成 `∀ p, ∀ᶠ N in atTop, …`，不写 `∀ p ∀ N`）；
   (d) 正反两向：给出满足新形式的**正向见证**，以及旧形式的**反证**。
   样板：`RBM.EEDef.ee_hyp_consistent`、`T169.MinorGoodLe.goodEvent`（把「结论非空洞」反向证成定理）、
   `MomentDuhamelCut.satCutHyp`（取在**临界标度 `J ≡ Θ`**，让 `mesh_fine`（要网细）与
   `card_le`（要网粗）这对最易联合不可满足的条件由同一见证满足）、
   T196（显式造非 Hermitian 且奇异的 `M`）、`T175.cutChi_spec`、T177、T181。
2. **`@[deprecated "RETIRED (Txxx): …"]` 编译器级护栏**：查出假陈述后必须用它，
   **不能只写 docstring**——`MinorGood` 那支就是靠 docstring 活了几周（T184）。
   `#assert_rbm_axioms` 也已实际拦下过一次漏网的 `sorry`。
3. **fiat 审计与空真审计并行**：审计完成的单时，除 fiat（可被平凡满足）外，
   **还要查空真（不可满足）**——两者方向相反，都让定理失去内容。
4. **类 / 结构的正则性要求只证明实际用到的阶数**（T145 / T180 / T187：`∀ M` 该是 `∀ M Hermitian`；
   时间 `C²` 可能只需 `C¹`）——要求多了，具体对象就放不进去。
5. **模型 / 建模步是编译器唯一查不出的错**，必须另有独立自检；自检可以在 Lean 外跑，
   但要写明范围与理由（T168 的 Python 穷举 + Lean 里的小锚点 `figure_four`）。

### 6.3 当前**仍未提供可满足性见证**的接口（2026-09-21）

* **`RBM.OUFlow`**（Theorem 2.6）：只记路径、未钉死分布。⚠ 它的问题不是「难满足」而是「**太好满足**」
  ——常值流 `H_t ≡ H` 就满足，且在那个流上 `theorem2_6_of_steps` 等于假设了结论。
  修法（Cowork 2026-09-21）：钉死 `H_t := e^{−t/2}H + (1−e^{−t})^{1/2}G`（`G` 为独立 GUE）。
* **`RBM.GUEPhase.Eq747Inputs` / `GUEFlow`**：零生产者、零见证。
* **`RBM.SumZeroDyn.Lemma510`** 的四个字段：零生产者、零见证。
* **Step 6 的四个样本侧好集** `FDInputs` / `QuadInputs` / `EGInputs` / `DriftInputs`：
  只有定义与消费点，没有「这个事件是高概率的」的定理，也没有见证。
* **`RBM.MomentDuhamelCut.MomentHypCut`**：有 `CutHyp` 的临界标度见证 `satCutHyp`，
  但**没有**针对真正的 `J* = jSnorm` 的见证或生产者。

### 6.4 fiat 风险清单

**fiat = 自由张量 / 自由漂移让结论无内容**：签名里留了一个可以随便取的对象（常取 0），
于是定理成立但什么也没说。

| 对象 | 状态（2026-09-21） |
|---|---|
| `MomentDuhamel.Hyp` 的 `drift` / `EE` | ✅ **已堵**：T145 加约束，T163 把 `E^{(G̃)}` 变成定义、`F` 由恒等式钉死（`Hierarchy/EGDef.lean`） |
| `SumZeroDyn.Lemma510` 的 `F`（`DischargeBDG.lean:70ff` 的约束） | ✅ **已钉死**：T58 / T118(iii) 在一般回路长度上给出具体 `F`（`Hierarchy/DriftDef.lean`），长度 2 的恒等式推广且只多一项 |
| Step 6 的 `DLK` / `DG` 漂移张量 | ✅ **已钉死**：T173（单张量）、T182（拆分；T182 同时推翻了 T152「单张量归约」对 size estimate 的适用性）、T189 |
| **`Step2MomentStep.FarInputs`** | ⚠ **未清**：T198 的可满足性见证取 **drift = 0**（整个 Duhamel 余项当鞅项），对任意样本可实现 ⟹ **假设束非空但可能无内容**。该见证同时说明真正的内容是 `cFarStep ≺ 1`，而**那一条给不出来**。T208（2026-09-21）正在做「从钉死的漂移产出一步输入并证 `cFarStep ≺ 1`」 |
| `RBM.DBMUniversality` / `GreenComparison` / `StepTwoClaim` / `OUFlow` | ⛔ **最大的一处**：常值流让三条全部平凡（见 §6.3）。**明令禁止**用常值流或其他 fiat 流去卸 |
| `MomentDuhamelCut.CutHyp` | ⚠ 见证 `satCutHyp` 取 `J ≡ Θ ≡ 1`，是**临界标度**（不是退化的 0），这一点做得对；但它不是真 `J*` 的生产者 |

### 6.5 「带证明的否定结论」是本项目最值得保留的产出形态

改变计划的几乎全是否定结论，而且都**编译成了定理**：
`LDENetClose` 按字面不可证（T148）；`MinorGood` 对**任何** `Ψ` 都假（T172）；
`MomentHyp.step` 在冻结形状下不可证（T132c，两条阻塞各一条定理）；
`hG` 按字面推不出来（T189）；`(+,+)` 的「免自举」捷径不收缩（T132c）；
裸 `Cond272` 不够（T186，**反转了一次裁定**，直接导致 D13）。

---

## 7. 建模选择与对论文的偏差（索引）

**完整底账在 `docs/paper-deltas.md`（132 行，本节只给索引，不复制全文）。**
每条记录了：① 论文第几页 ② 改哪一段 / 哪个编号 ③ 大约几行 ④ 是否需要重新编号。

### 7.1 几条**方法层面**的建模选择（不是小改动，必须在最终报告正文里写清楚）

| # | 选择 | 理由 |
|---|---|---|
| #88 | **随机层的模型：论文保留布朗运动，Lean 用 `H_u = √u·X`**（Jun 2026-09-20 选 (a)） | Mathlib 没有随机分析；一时刻律与布朗模型对齐 |
| #49、#53、#54、#55 | **矩路线替代 Itô / BDG / 停时**：生成元恒等式 + 对矩的 Grönwall + `N^{-C}` 时间网 + 反向桥 `≺ ⟹ 矩` | 同上；`≺` 用 `DetDom` / `StochDom` 封装 |
| #8（已撤销） / #124 / #128 | **Lemma 3.2 的组合模型**：T185 完整证出，#8 撤销；代价只剩 Lean 版要 `3 ≤ n`（#128）。`decide` 不可伸缩（9 点树 85 秒），模型自检搬到 Lean 外（Python 穷举 `n ≤ 7`：1/3/11/45/197），Lean 里留可编译锚点 `figure_four` | T168、T185 |
| #3 | 指标类型用块 / 偏移 `ZMod L × Fin W`，论文原式在 `ZMod (W*L)` 上照写并经双射证逐元素相等 | — |
| #1 | `3 ≤ L` 作为显式假设（`L = 1, 2` 时行和随机性失效） | — |
| #2 | `≺` 的一致版 `UnifDetDom`（论文 (ii) 只说「非负确定量」，而 (2.53)(2.54) 是对格点一致的） | — |

### 7.2 分类摘要（按主题）

* **传播子 Θ_ξ / 附录 B**：#12、#13、#71（衰减率 `1 − ‖ρ(ξ)‖`）；
* **loop 层 / §3**：#4、#6、#8′、#9、#10、#11、#14–#22、#124、#128；
* **§5 六步**：#26、#27、#33、#36、#37、#42–#44、#47、#72、#73、#80、#82、#103–#113、#116、#117、
  #119、#121–#123、#125–#127、#129–#132；
* **§4 局部律 / LDE / 涨落**：#32、#39、#57–#65、#66–#70、#75–#79、#81、#83–#87、#90–#102；
* **Theorems 2.2–2.6 与 §7.2**：#5（Thm 2.2 的概率一半）、#24、#25、#29、#31、#38、#45、#46、
  #114（[51] 的 β = 2 引用）；
* **已撤销 / 已关闭**：#8（T185 撤销）、#49（T109 关闭）、#52（T134 解除）、#74（T125 解决）、#78。

### 7.3 需要重新编号或新增编号命题的（标「需 Jun 确认」）

见 `docs/paper-deltas.md` 中带「**需 Jun 确认**」标记的行，以及项目文档
`claude/paper-edit-budget.md` 的论文改动最小集合（第 6–15 条）。
**已裁定的两条**：#106/#107（(5.16) 漏 `S^(B)`，Jun 已裁定并落地 `RBM.ThetaOp` 重定义）；
#132（Theorem 2.21 假设表补 `Wℓ_tη_t ≥ N^c`，D13 裁定走 `Cond272Reg`，论文改动预算第 16 条）。

> **取号纪律**：agent 新增的 paper-delta 一律不写数字号，`#` 栏写 `T<工单号><字母>`；
> 数字号由 Cowork 在心跳时统一分配。本节引用的数字号均为已分配的。

---

## 8. 本报告用到的编译探针

**全部放在 scratchpad，全部 `lake env lean` exit=0，全部 _未入库_。**
目录：`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM1D/4652a42d-f1fc-42cf-a1ef-6c3ecf43f92a/scratchpad/`

| 探针 | 文件 | 做什么 |
|---|---|---|
| P-A | `T200Probe.lean` | `#check @` 打印 Theorems 2.2–2.6、2.21、Lemmas 2.18–2.20 的**完整**签名（§1 的假设表逐字来自它） |
| P-A2 | `T200Probe2.lean` | `#check @` 打印 `Step1.step1`、`Step2.step2`、`Step2Moment.step2`、`Step6.sharpExpect_step6` |
| P-B | `T200Producers.lean` | 元程序：给定常量 `C`，扫全环境找**结论头常量是 `C`** 的声明（滤掉构造子 / 投影 / recursor）。⚠ 对 `def` 形状的假设有假阴性 |
| P-B2 | `T200Prod2.lean` | 同上，用于 `BootPP` / `FlowEq548` / `Lemma514` / `MomentHypCut` / `CutHyp` / `MomentDuhamel.Hyp` |
| P-B3 | `T200Sweep.lean` | 同一元程序扫**全部 57 个 `RBM` 结构**，输出零生产者的 10 个（§5.1 的表） |
| P-C | `T200Defeq.lean` | **裸 `:=`**（无 `convert`、无 `simp`）把 Step 1 / 2 / 3 / 4-5 的结论喂进 `AprioriFlow` / `LocalLawFlow`+`AprioriDecayFlow` / `SharpLoopFlow` / `SharpLmKFlow` 四个槽——**四条全过**，证明 P-B 对这五条的「无生产者」是假阴性 |
| P-D | `T200Count.lean` | 声明计数 + `#assert_rbm_axioms`（§4 的 10441） |
| P-E | `T200Axioms.lean` | 15 条主定理逐条 `#print axioms`（§4） |
| P-F | `T200Fields.lean` | 打印 §5.1 各结构的字段名 |

> **本报告没有做的**（如实）：① 没有读论文 PDF，凡涉及「论文是否真这么写」的判断均转述
> `docs/STATUS.md` / `docs/paper-deltas.md`；② 没有跑 `lake build RBM1D`（九个 agent 并发写码），
> §4 的全量数字取自 `build.log` 09:52 那一轮与探针 P-D；
> ③ 没有对**全部** `def` 形状的假设做 P-C 式逐条核（只核了六步链上的五条 + §5.2 的八条）。

---

## 9. 裁定（2026-09-21 17:15，Jun 同意 Cowork 的建议）

> R1–R5 原文见 `docs/STATUS.md`「待 Jun 定夺：R1–R5」。下面是结论；按 R1/R5 改写 §1 与 §6.5/§7 的结构由后续工单做（Cowork 开单）。

* **R1 → 并列为主定理。** 按论文结构，§1 把 Theorems 2.2–2.5 并列为主定理，每条附完整假设表。
  六步合拢之前，状态栏写「以 Theorem 2.21 为前提」；合拢后改为无条件（只依赖模型假设 (2.2)）。
  Theorem 2.21 与 Lemmas 2.18–2.20 作为关键中间结果单列。
  Theorem 2.6 单列，并写明它是全文**唯一**用外部输入的地方。

* **R2 → 已由 Jun 的范围规则回答。** Theorem 2.6 在本项目范围内，但要等其余各块都没有高风险项后再开。
  外部输入是 [51] Theorem 2.2 的**复 Hermitian 形式**：逐字写成假设，量化在所有满足其前提的模型上。
  `GreenComparison` 自证。开工之前，§3 写「外部输入：[51] Theorem 2.2（复形式）；Lean 实现在 Theorem 2.6 阶段」，不再写「待定」。

* **R3 → 随 Theorem 2.6 一起做。** 钉死 `OUFlow` 的分布归 Theorem 2.6 阶段。
  在此之前，`theorem2_6_of_steps` **不**算 Theorem 2.6 的形式化，§1 的 Theorem 2.6 条目标「③ 空着」。

* **R4 → 已由 D12/D13 回答。** 先做不含 (2.71) 的第一遍（T204，已完成）；(2.71) 的归纳与 Step 6 样本侧的四个好集归 T205（第二遍，**不**推迟到 Theorem 2.6）。
  原文里「若选 (a)，可整体推迟到 Theorem 2.6 阶段」一句作废。

* **R5 → 单列一节，分两小节。**
  * **(a) 论文层面的修正**：对应论文改动预算的条目，全部零重新编号。例如：
    * 裸 (2.72) 不够，所以 Theorem 2.21 补 `t ≤ 1 − N^{−1+τ}`（第 16 条）；
    * (5.36) 补一个因子（第 13 条）；
    * [51] 字面只陈述实对称情形，需要补一句说明（第 8 条）。
  * **(b) 形式化中被证伪的中间接口**：`MinorGood`、冻结形的 `MomentHyp.step`、`LDENetClose`、T198 形的 `cFarStep ≺ 1` 等。
    这些是形式化过程中**自设的接口**，不是论文的错误，作为方法学产出写。

  两小节分开写，免得读者把 (b) 当成论文缺陷。

---

*起草：T200（Claude Code 子 agent），2026-09-21。本文件随进度更新；
更新时请同步 §1 的状态记号、§5 的生产者清单与 §8 的探针表，并保留「探针不入库」的标注。*
