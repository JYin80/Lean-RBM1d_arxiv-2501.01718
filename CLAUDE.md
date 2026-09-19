# CLAUDE.md — RBM1D

用 Lean 4 + Mathlib 形式化 Yau–Yin《Delocalization of 1D Random Band Matrices》(d=1)。

## 唯一真相来源

- **论文**：`paper/250520-YinJun-v2.pdf`（95 页）。**只依据这篇论文，不引用任何其他文献。**
- **路线图**：`docs/PLAN.md` — 阶段划分与每阶段的 Lean 声明清单
- **当前进度**：`docs/STATUS.md` — **每次会话开始先读它，结束前更新它**
- **与论文的偏差**：`docs/paper-deltas.md` — 凡 Lean 陈述 ≠ 论文字面陈述，必须在这里记一条

## 环境

Lean `4.34.0` / Mathlib `v4.34.0`（rev `5ed2965256`），cache 已拉好。
Mathlib 源码在 `.lake/packages/mathlib/Mathlib/` —— 找 API 就 grep 这里。

## 构建回路

```bash
lake env lean RBM1D/Propagator/Xxx.lean   # 单文件，秒级 —— 默认用这个
./check.sh                                 # 全量，结果写进 build.log
./watch.sh                                 # 另开终端，改动即自动重编
```

**绝不在没有实际跑过编译的情况下说"写好了"。** 每次回报前必须有一次 exit=0。

## 硬性规则

1. **不留 `sorry`。** 证不出来就停下说「卡在 X」，不要 sorry 占位然后继续往下写。
2. **不许发明 Mathlib 引理名。** 先 `grep -rn "circulant_mul" .lake/packages/mathlib/Mathlib/`，
   或在 `RBM1D/Probe.lean` 里加 `#check @foo` 编译看签名。`exact?` / `apply?` / `rw?` / `aesop` 鼓励用。
   （`Probe.lean` 是临时 API 侦察本，Phase 1 收尾时删掉。）
3. **公理审计。** 每条主定理证完跑 `#print axioms RBM.xxx`，只允许出现
   `propext` / `Classical.choice` / `Quot.sound`。出现 `sorryAx` 就是没做完。
4. **陈述逐字对应论文。** 不得不加假设（如 `3 ≤ L`）或换陈述形式，必须写进 `docs/paper-deltas.md`。
5. **小步提交。** 一次只动一条引理 / 一个文件；绿了就 `git commit`，不要攒一大坨再一起编译。
6. **不碰随机层**（Itô、Dyson Brownian motion、loop hierarchy、universality）。
   Mathlib 没有随机分析，那部分只写 `axiom` 接口，而且现在还不到时候。
7. **常数不求最优。** 统一写成 `∃ C > 0, ∃ c > 0, ∀ ...`；`≺` 用 `DetDom` 封装。

## 命名与风格

- namespace `RBM`；声明名走 Mathlib 风格（`Theta_apply_add_right`、`sum_SB_row`、`norm_Theta_le`）
- 变量约定：`L : ℕ`、`[Fact (3 ≤ L)]`、指标类型 `ZMod L`、谱参数 `ξ ζ : ℂ` 且 `‖ξ‖ < 1`
- 文件头 copyright 块照抄现有文件
- 每落地一个声明，去 `blueprint/src/content.tex` 对应节点补 `\lean{}` + `\leanok`；
  节点名与论文编号一一对应（`lem:2.14`、`eq:2.52`、`lem:3.6`）

## 分工：Claude Code 与 Cowork

两边都在用，边界按**迭代延迟**划，不按角色划。

| | Claude Code（本机） | Cowork / chat（云端） |
|---|---|---|
| 证明的试错循环 | **主场**。`lake env lean 单文件` 秒级返回 | 一轮约 2 分钟，不适合高频试错 |
| 读论文 PDF | 需要 `paper/` 下有 PDF（本地有，不入库） | PDF 在会话里，随时翻页 |
| 蓝图渲染 / 依赖图 | 需本机装 plasTeX + graphviz | 工具链现成，可直接发布成网页 |
| 路线规划、阶段划分 | — | **主场** |
| git / CI / GitHub Pages | 都行 | 都行 |

### 任务队列

`docs/TASKS.md` 是两边共用的工单表。**开工前先在表里认领并提交**。
分工按**文件**切分，不按难度切分：同一时间两边不碰同一个文件，合并就永远是平凡的。
推之前先 `git pull --rebase`。

### 交接契约

`docs/STATUS.md` 是两边**唯一**的共享状态。任何一边：

- 开工前先读它
- 收工前更新它（新增了哪些声明、卡在哪、下一步是什么）
- 卡住时在里面写清楚「卡在 X，试过 Y 和 Z，失败原因是 W」，另一边才接得上

`docs/paper-deltas.md` 同理：偏离论文字面陈述的地方，谁发现谁记，不要只在对话里说。

### 常设授权

路由决策（某项工作该在 Claude Code 还是 Cowork 做）不必每次征求同意，按上表直接定。
需要征求同意的只有：改变项目范围、公开/删除内容、以及任何不可逆操作。

### 论文 PDF

`paper/250520-YinJun-v2.pdf` 放在本地供 Claude Code 读，已在 `.gitignore` 里排除，
不会推到公开仓库。

## 当前位置与下一步

Phase 1 传播子 Θ_ξ 已完成到 `Propagator/Support.lean`，全绿 0 sorry。详见 `docs/STATUS.md`。

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

## 会话结束前的检查单

1. `./check.sh` → `build.log` 里 `errors: 0`、`exit=0`
2. `grep -rn "sorry" RBM1D/` → 只有 `Test/Sanity.lean` 里那句注释
3. 更新 `docs/STATUS.md`（新增的声明、下一步）
4. `git commit`

## 队列空了怎么办

**不要停下来等新工单。** `docs/TASKS.md` 末尾有「永不停工规则」和储备工单 B1–B6：
队列一空就按那个顺序自己挑活（先 T8–T11 的一般 Fourier 机器，再 B1–B6，再常规维护），
并在工单表里补一行说明你在做什么。空转是这个项目里唯一不可接受的状态。
