# 任务队列

两边共用的工单。**认领前先改 `认领` 一栏并提交**，避免重复劳动。

分工原则：**按文件切分，不按难度切分**。同一时间两边不碰同一个文件，合并就永远是平凡的。

| # | 任务 | 文件 | 认领 | 状态 |
|---|---|---|---|---|
| T1 | `1 − ‖ρ(ξ)‖ ≍ \|1−ξ\|^{1/2}` 的定量估计 | `Propagator/Decay.lean` | **Cowork** | 进行中（精确恒等式已证） |
| T2 | `‖A(ξ)‖` 的上界 | `Propagator/Decay.lean` | **Cowork** | 待 T1 |
| T3 | 组装成论文 (2.52) 的形式 | `Propagator/Decay.lean` | **Cowork** | 待 T1,T2 |
| T4 | (2.53)(2.54) 差分估计 | `Propagator/Decay.lean` | **Cowork** | 待 T3 |
| T5 | 附录 B (B.1) 的 Fourier 表示 | `Propagator/Symbol.lean` | Claude Code | **完成** |
| T6 | Def 2.1(ii) 的确定性 ≺ | `Defs/Domination.lean` | Claude Code | **完成** |
| T7 | 删掉 `RBM1D/Probe.lean` | — | 空闲 | 等 Phase 1 收尾 |
| T8 | (B.3) 符号的双边界 `\|1−ξŜ(p)\| ≍ \|1−ξ\| + \|p\|²` | `Propagator/SymbolBound.lean`（新建） | 空闲 | **排在第 3 节之后** |
| T9 | 无穷体积核 + 围道平移 (B.4)(B.5) | 同上 | 空闲 | 排在第 3 节之后 |
| T10 | Poisson 求和 / 周期化 → 环上的 (2.52) | 同上 | 空闲 | 排在第 3 节之后 |
| T11 | dyadic 分解 → (2.53)(2.54) 的一般证明 | 同上 | 空闲 | 排在第 3 节之后 |
| T12 | 数值回归测试 | `Test/Numeric.lean` | Claude Code | **完成** |
| T13 | Thm 2.2：由 local law 推 delocalization | `Delocalization.lean` | Claude Code | **完成**（确定性部分） |
| T15 | §2.1 模型层：S_W、S = S^(B)⊗S_W、E_a、N = WL | `Defs/Model.lean` | Claude Code | **完成** |
| T16 | Def 2.9/2.10：loop 的指标数据与 cut-and-glue 算子 | `Loop/Index.lean` | Claude Code | **完成** |

---

## 路线决定（2026-09-19）

合作者倾向用附录 B 的一般 Fourier 方法，理由正确：闭式解是 **d=1 最近邻的偶然**，
一般 variance profile 或 d ≥ 2 时三项递推和特征方程都不存在，那条路断掉。

但有个事实：**在有限环上、d=1 时，Fourier 方法与闭式解是同一个计算。**
令 z = e^{ip}，(B.1) 是对 L 次单位根求和 `(1/L) Σ_{z^L=1} z^u g(z)`，
`g(z) = 1/(1 − (ξ/3)(1+z+z^{-1}))` 是 z 的有理函数，极点恰是 ρ 与 ρ^{-1}；
做留数/部分分式出来的就是 `ρ^u + ρ^{L-u}`。附录 B 引入无穷体积核、围道平移、
Poisson 求和、dyadic 分解，是因为**一般情形下做不了这个留数计算**（符号不再是有理函数）。

**当前决定：先用闭式把 (2.52)(2.53)(2.54) 完成，一般 Fourier 机器排在第 3 节之后做。**

这是**排期**，不是放弃，也不是留给以后的论文——一般机器仍在本项目的队列里（见下面 T8–T11），
只是先让第 3 节（树表示、Ward 恒等式、sum-zero —— 论文真正原创的部分）开工。
等第 3 节落地后回头补一般机器，届时 d=1 的闭式结果作为它的交叉验证。

T5（(B.1) 的 Fourier 表示）照做不误：它是 (3.48) 要用的结构性结果，
也是将来搭一般机器的地基，只是不再是 (2.52) 的路径。

---

## T5 — 附录 B (B.1) 的 Fourier 表示

新建 `RBM1D/Propagator/Symbol.lean`。**与 T1–T4 完全独立**，不依赖闭式解。

目标（论文 p.89）：设 `ζ = exp(2πi/L)`，特征标 `e_p(x) = ζ^(p·x)`。

1. `Shat L p = (1 + ζ^p + ζ^(-p))/3`，即论文的 `Ŝ(p) = (1 + 2cos p)/3`
2. `SB_mulVec_char`：`S^(B) *ᵥ e_p = Shat p • e_p`
   推导：`(S *ᵥ e_p)(x) = Σ_y sbKernel(x−y) ζ^{p y} = ζ^{p x} Σ_u sbKernel(u) ζ^{−p u}`
   —— 用 `RBM.sum_over_sbSupport`（已在 `Defs/Block.lean` 里）把求和展开成三项
3. `one_sub_xi_Shat_ne_zero`：`‖ξ‖ < 1` 时 `1 − ξ·Shat p ≠ 0`。
   注意 `‖Shat p‖ ≤ 1`（三项各模 ≤ 1/3），故 `‖ξ·Shat p‖ < 1`
4. `theta_apply_fourier`：`(Θ_ξ)_{xy} = (1/L) Σ_p ζ^{p(x−y)} / (1 − ξ Shat p)`

**下游用途**：(3.48) 用的是 Fourier 形式。衰减估计**不走**这条路（走闭式，见 T1–T4）。

可能要用的 Mathlib：`Complex.exp`、`Complex.isPrimitiveRoot_exp`、
`Finset.sum_nbij` / `ZMod` 上的特征标正交性。名字先 grep `.lake/packages/mathlib/Mathlib/`。

---

## T6 — Def 2.1(ii) 的确定性 ≺

新建 `RBM1D/Defs/Domination.lean`。**与其他任务完全独立**，纯定义 + 基本性质。

```lean
def DetDom (ξ ζ : ℕ → ℝ) : Prop := ∀ τ > 0, ∀ᶠ N in Filter.atTop, ξ N ≤ (N : ℝ) ^ τ * ζ N
```

要的基本性质：自反、传递、对加法与乘法封闭、常数倍不变、
`DetDom ξ ζ → DetDom (c • ξ) ζ`（c > 0）。

概率版本 Def 2.1 (i)(iii)(iv) **现在不做**，等随机层启动。
论文 (2.53)(2.54)(3.35)(3.36) 都是用 ≺ 陈述的，这一层是把它们写成论文原样的前提。

---

## 给 Claude Code 的一句话

> 读 `docs/TASKS.md`，做 T5（或 T6）。先在表格里把认领改成 Claude Code 并提交，
> 然后按 `CLAUDE.md` 的硬性规则做：不留 sorry、不发明 Mathlib 引理名、
> 每条主定理跑 `#print axioms`、偏离论文记进 `docs/paper-deltas.md`。

## 共享同一个工作树

两边指向的是**同一个文件夹、同一个 git 仓库、同一个工作树**，不是两份副本。
所以：工单不需要 push 对方就能看到；也**不需要 `git pull --rebase`**（没有第二份要拉）。

真正的风险因此不是合并冲突，而是三种并发争用：

1. **同时写同一个文件** —— 靠上面的按文件切分避免。共享文档（`docs/*.md`、
   `blueprint/src/content.tex`、`CLAUDE.md`）改动要小、要立刻提交，不要长时间持有。
2. **git index.lock 争用** —— 两边同时 `git add`/`commit` 会撞。撞到就等几秒重试；
   若残留 `.git/index.lock` 且确认没有别的 git 在跑，删掉它即可。
3. **绝不用 `git add -A`** —— 它会把对方正在写的文件暂存进你的提交。
   **只按文件名 `git add` 自己的那几个。**
4. **`build.log` 是共用的** —— `watch.sh` 全量编译，两边的报错都会写进同一个文件。
   读日志时按文件名过滤自己那部分，别把对方进行中的报错当成自己的。

`watch.sh` 只要开着，任何一边改动都会触发重编，这对双方都有用。
单文件快速检查用 `lake env lean RBM1D/Propagator/Xxx.lean`，它不抢 lake 的构建锁。

### 核实过的事实（2026-09-19）

`git worktree list` 只列出一个工作树；`git rev-list --count origin/main..HEAD` 与反向都是 0。
所以确实是**一个共享工作树**，没有第二份克隆。

若 `git pull --rebase` 看起来"带回"了对方的 commit：那是 rebase 重放**本地**提交时
git 列出的它们，不是从远端取回的新东西。同一个树里拉不回自己已有的提交。
这条无害，照做也行。


---

## T12 — 数值回归测试

新建 `RBM1D/Test/Numeric.lean`。`CLAUDE.md` 里 Phase 1 完成标准的第 3 条。

`L = 5, 7`、`ξ = 1/2` 时在 `ℚ` 上验证 `(1 − ξ·S^(B))·Θ = I`。做法：
用 `Matrix (Fin L) (Fin L) ℚ` 显式写出 `1 − ξS`，用 `decide` / `norm_num` 验证它乘以
显式给出的逆等于单位阵。**不必**与 `RBM.Theta` 直接挂钩（那是 ℂ 上的、noncomputable），
这条的价值在于它独立于整条符号推导链，能抓住定义层面的抄写错误。

闭式解现在已是定理（`kern_defect` 若 A 抄错就证不出来），所以这条不再是防抄错的必需品，
但作为独立回归测试仍然值得有。

---

## T13 — Theorem 2.2：由 local law 推 delocalization

新建 `RBM1D/Delocalization.lean`。**与传播子那条线完全独立**，只用 Mathlib 的 Hermitian 谱定理。

论文 p.9 的论证（(2.10)）：设 `H` Hermitian，`λ_k`、`ψ_k` 是特征值与单位特征向量，
`G(z) = (H − z)^{-1}`，`η = Im z > 0`。则对任意 `x`

    |ψ_k(x)|² ≤ Σ_l η²|ψ_l(x)|² / ((λ_k − λ_l)² + η²) ≤ η · Im G_xx(λ_k + iη)

**第一个不等号**：右边的和里 `l = k` 那一项就是 `|ψ_k(x)|²`（分母 `η²`），其余项非负。
**第二个等号/不等号**：谱分解给出 `Im G_xx(E + iη) = Σ_l η|ψ_l(x)|²/((λ_l − E)² + η²)`，
取 `E = λ_k` 即得。

于是：若 local law 给出 `‖G − m‖_max ≺ 1` 且 `m = O(1)`，则 `Im G_xx = O(1)`，
代入得 `|ψ_k(x)|² ≤ Cη`。论文取 `η = N^{-1+τ}` 得 Thm 2.2。

Mathlib 里要用的：`Matrix.IsHermitian.spectral_theorem`、`Matrix.IsHermitian.eigenvalues`、
`Matrix.IsHermitian.eigenvectorUnitary`（名字先 grep 确认）。

**建议先做纯谱论的那一半**（上面两个不等式），把 local law 作为假设写进陈述，
不要去碰随机层。这样这条定理现在就能无 sorry 地成立。

---

## T15 — §2.1 的模型层

新建 `RBM1D/Defs/Model.lean`。论文 p.6–7。纯定义 + 平凡性质，但下游全要用。

* `W L : ℕ`，`N = W * L`
* 块 `I_a = {aW, aW+1, …, aW+W−1}`，`a : ZMod L`
* `S_W : Matrix (Fin W) (Fin W) ℂ`，`(S_W)_{αβ} = W⁻¹`（全 1 矩阵除以 W）
* `S = S^(B) ⊗ S_W`（Kronecker 积，Mathlib `Matrix.kroneckerMap` / `⊗ₖ`）
* `E_a`：(2.5) 的块投影，`(E_a)_{ij} = δ_{ij} · W⁻¹ · 1(i ∈ I_a)`
* 要的性质：`Σ_a E_a = W⁻¹ · I`（Lemma 3.6 Step 1 用）、`E_a` 自伴、
  `S` 的行和为 1（由 `S^(B)` 与 `S_W` 的行和各为 1）

**注意**：`RBM.SB` 已经在 `Defs/Block.lean` 里，直接复用，不要重新定义。

---

## T16 — Def 2.9/2.10：loop 的指标数据与 cut-and-glue 算子

新建 `RBM1D/Loop/Index.lean`。**这是第 3 节的地基**，也是整个项目里最值得先做对的一块。

难点不在数学，在**指标记账**。先不要碰 Green 函数，只把 `(σ, a)` 上的组合操作定义对。

数据：`σ : Fin n → Bool`（`true` = `+`），`a : Fin n → ZMod L`。建议用
`List Bool × List (ZMod L)` 并带长度相等的证明，或者 `n` 显式的 `Fin n →` 函数——
**哪种更好用由你判断，但要能方便地做"取前 k 段、接上后一段"这类操作**，
所以 `List` 大概率更合适。

论文 Definition 2.10 的三个算子（1-based 记号，`n` = 当前长度）：

**`G^{(a)}_k`**（1 ≤ k ≤ n）：把第 k 条 G 边劈开插入 `E_a`。长度 n → n+1。
    σ′ = σ 在第 k 位插入一个 σ_k 的副本
    a′ = a 在第 k 位插入 a
论文例子（n = 4, k = 2）：
    σ = (σ₁,σ₂,σ₃,σ₄) → σ′ = (σ₁,σ₂,σ₂,σ₃,σ₄)
    a = (a₁,a₂,a₃,a₄) → a′ = (a₁,a,a₂,a₃,a₄)

**`G^{(a),L}_{k,l}`**（1 ≤ k < l ≤ n）：剪开第 k、l 条 G 边得两条链，
把**含 `E_{aₙ}` 的那条**（左链）的两端粘起来并在粘点插入新的 `E_a`。长度 k+n−l+1。
    σ′ = (σ₁,…,σ_k) ++ (σ_l,…,σ_n)
    a′ = (a₁,…,a_{k−1}) ++ (a) ++ (a_l,…,a_n)
论文例子（n = 5, k = 3, l = 5）：
    σ′ = (σ₁,σ₂,σ₃,σ₅)，a′ = (a₁,a₂,a,a₅)

**`G^{(a),R}_{k,l}`**：粘**不含 `E_{aₙ}` 的那条**（右链）。长度 l−k+1。
    σ′ = (σ_k,…,σ_l)
    a′ = (a_k,…,a_{l−1}) ++ (a)
论文例子（n = 5, k = 3, l = 5）：
    σ′ = (σ₃,σ₄,σ₅)，a′ = (a₃,a₄,a)

**必须证的性质**（这些是后面 Lemma 3.4、3.6 反复用的）：
1. 三个算子的**输出长度**：分别是 `n+1`、`k+n−l+1`、`l−k+1`
2. **两条链长度之和**：`(k+n−l+1) + (l−k+1) = n+2`
   —— 论文 (2.48) 之所以是二次方程就因为这个
3. 左右链的长度**都 ≤ n**（当 `1 ≤ k < l ≤ n` 时），这是 §2.4 末尾说"K 可以按长度归纳求解"的依据。
   注意 `k=1, l=n` 时右链长度恰好 `= n`，**等号可以取到**，归纳要按别的量递减——
   论文的说法是「the lengths are no greater than the length of K」
4. 论文 Figure 1、2、3 的三个例子，写成 `example ... := by decide` 或 `rfl` 当回归测试

**建议**：先把长度性质做对，`example` 跑通论文的三个例子，再谈别的。
这一层做扎实，第 3 节会顺很多；做糙了后面全是坑。
