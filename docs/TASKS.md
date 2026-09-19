# 任务队列

两边共用的工单。**认领前先改 `认领` 一栏并提交**，避免重复劳动。

分工原则：**按文件切分，不按难度切分**。同一时间两边不碰同一个文件，合并就永远是平凡的。

| # | 任务 | 文件 | 认领 | 状态 |
|---|---|---|---|---|
| T1 | `1 − ‖ρ(ξ)‖ ≍ \|1−ξ\|^{1/2}` 的定量估计 | `Propagator/Decay.lean` | **Cowork** | 进行中 |
| T2 | `‖A(ξ)‖` 的上界 | `Propagator/Decay.lean` | **Cowork** | 待 T1 |
| T3 | 组装成论文 (2.52) 的形式 | `Propagator/Decay.lean` | **Cowork** | 待 T1,T2 |
| T4 | (2.53)(2.54) 差分估计 | `Propagator/Decay.lean` | **Cowork** | 待 T3 |
| T5 | 附录 B (B.1) 的 Fourier 表示 | `Propagator/Symbol.lean` | Claude Code | **完成** |
| T6 | Def 2.1(ii) 的确定性 ≺ | `Defs/Domination.lean` | Claude Code | **完成** |
| T7 | 删掉 `RBM1D/Probe.lean` | — | 空闲 | 等 Phase 1 收尾 |

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
3. **`build.log` 是共用的** —— `watch.sh` 全量编译，两边的报错都会写进同一个文件。
   读日志时按文件名过滤自己那部分，别把对方进行中的报错当成自己的。

`watch.sh` 只要开着，任何一边改动都会触发重编，这对双方都有用。
单文件快速检查用 `lake env lean RBM1D/Propagator/Xxx.lean`，它不抢 lake 的构建锁。
