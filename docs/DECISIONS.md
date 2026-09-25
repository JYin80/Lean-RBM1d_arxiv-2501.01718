# DECISIONS — 仍然生效的决定（总调度独占；2026-09-25 起）

## 目标与口径
1. **目标**：`paper/250520-YinJun-v2.pdf` 的 Theorems 2.2–2.6 的源头忠实 Lean 证明，加上它们实际依赖的内部结果。完成标准见 `docs/PLAN.md` 的 Completion contract：条件定理、特例、有限例子都不能算作论文结论。
2. **论文忠实度**：以该 PDF 为唯一来源。允许微小改动（明显笔误、必要条件、等价表述），逐条记入 `docs/paper-deltas.md`；改动论文陈述、增删定理由 Jun 决定。
3. **唯一授权的外部输入**：[51, Theorem 2.2] 的复 Hermitian 版本，只用于 Theorem 2.6 Step 1（`docs/paper-deltas.md` #114）。其余一律内部证明，包括 [37]/[70] 的 Green 函数比较。
4. **随机模型**：论文保留布朗模型。`H_u = √u·X` 只与它有相同的单时刻分布，不能当作停止路径恒等式的证明。
5. **Lean 门槛**：无 `sorry`/`admit`/`axiom`；公开声明的公理只含 `propext`、`Classical.choice`、`Quot.sound`；不改冻结签名（加撇）；新模块须通过 `lake build RBM1D.<Module>`；新假设须有非退化的同时可满足见证。详见 `CLAUDE.md` §3。

## 团队与模型（Jun 2026-09-25 定）
6. ChatGPT/Codex 团队于 2026-09-25 停止，其规则与记录归档在 `docs/archive/2026-09-25-chatgpt-v6/`。Codex 暂不使用。
7. 分工：总调度 = Cowork 会话；独立数学监督 = Cowork 定时任务（事件触发，另有每天一次兜底）；执行中枢 = Mac 上常驻的 Claude Code 会话；写 Lean 的 agent 全在 Claude Code。章程见 `docs/claude-team/TEAM.md`。
8. 模型映射（2026-09-25 Jun：auditor、repairer 锁定 `claude-opus-5-5`，不用别名 `opus`）：低级 = Sonnet（`prover` 用 high，`prover-hard` 用 xhigh）；高级 = Opus（总调度、监督、`auditor`、`repairer`）；最高级 = Fable（总调度在 Cowork 调用的强力论证子代理，推理强度 max）。
9a. **省额度的三条（Jun 2026-09-25）**：
    - 执行中枢用 Sonnet，`/loop 10m`；没有新事时只更新在线信号，不输出文字。
    - 总调度的空闲心跳从简：先看信箱文件的修改时间，没有变化就只排下一次心跳。
    - 验收用 Opus 的 high（不用 xhigh），只看分支相对 main 的改动、目标声明和所用声明的签名，不通读依赖文件。
9b. **总调度必须跑在 Opus 5.5**（Jun 2026-09-25）：会话的模型会在上下文续接后退回 Sonnet。每次心跳第一步先查自己的模型；不是 `claude-opus-5-5` 就先提醒 Jun 运行 `/model claude-opus-5-5`，切回来之前只做空闲检查，不写工单规格，不做数学或路线判断，不改 mode。执行中枢（Sonnet）和各 agent（`.claude/agents/*.md` 里写死）的模型不受影响。
9. git：不用 `git add -A`/`git add .`；只提交指名文件；push 规则（Jun 2026-09-25 更新）：main 上每次按 Approved instruction 提交后，执行中枢紧接着 `git push origin main`，只推 main，禁止 force；被拒（非快进、鉴权失败等）就停下报告，不重试、不 rebase；其他分支不推；Cowork 一侧（总调度、监督、论证 agent）不执行任何 git 写操作，查 git 用 `git --no-optional-locks`。

## 路线（2026-09-25 Jun 批准）
10. **Step 2 路线：真路径试点**（Jun 2026-09-25 批准）。试点期间所有新证明单只投真路径（离散网格高斯游走，照论文 §5.3 用停时）；A′ 冻结（HOLD，不派新单，不删代码），是否正式放弃待试点结果再定。试点通过标准：P1–P5 在约 20 张证明单内编译并通过独立验收；失败信号：P4 或 P5 需要事先没有预见的新数学，出现时停下做数学评审。
10a. **开工顺序**（Jun 2026-09-25）：先由总调度完成 P4（停止过程矩不等式）和 P5（停时越过阈值一步的控制）的纸面论证，写入 `docs/claude-team/pilot-P4P5-paper.md`，确认不需要预料之外的新数学后，再发布 T1481–T1485 的改写规格并解除 HOLD。**2026-09-25 纸面论证完成**：经 Fable 独立复核，结论为不需要预料之外的新数学（P4 用 Mathlib 的 Azuma–Hoeffding 加 Doob，不需要 BDG；P5 越过阈值不需单独控制）。**2026-09-25 16:25 UTC Jun 批准**：改写规格 amend-1 发布，CONTROL 转为 RUN，A′ 仍冻结（不释放任何 A′ 工单）。首批工单 T1481–T1485 的原规格有缺陷，已在开工前撤回。
11. **T0 集成提交**：完成。H0 = 47dffbc；H1b = ab96505（1152 个文件；`lake build RBM1D` 通过，根公理审计通过）。

## 历史裁定索引
- D12–D22 与 Cowork 的工单节（§1–§19）：`docs/archive/2026-09-25-chatgpt-v6/CODEX-TICKETS.md` 及更早的 `docs/archive/` 快照。
- 论文与 Lean 的逐条差异：`docs/paper-deltas.md`。
