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
8. 模型映射：低级 = Sonnet（`prover` 用 high，`prover-hard` 用 xhigh）；高级 = Opus（总调度、监督、`auditor`、`repairer`）；最高级 = Fable（总调度在 Cowork 调用的强力论证子代理，推理强度 max）。
9a. **省额度的三条（Jun 2026-09-25）**：
    - 执行中枢用 Sonnet，`/loop 10m`；没有新事时只更新在线信号，不输出文字。
    - 总调度的空闲心跳从简：先看信箱文件的修改时间，没有变化就只排下一次心跳。
    - 验收用 Opus 的 high（不用 xhigh），只看分支相对 main 的改动、目标声明和所用声明的签名，不通读依赖文件。
9. git：不用 `git add -A`/`git add .`；只提交指名文件；不经 Jun 不 push；Cowork 一侧（总调度、监督、论证 agent）不执行任何 git 写操作，查 git 用 `git --no-optional-locks`。

## 待决（需 Jun）
10. **Step 2 的路线**：继续 A′ 光滑前缀权重（目前 HOLD），还是改走真路径（离散网格高斯游走，照论文 (5.43) 用停时）。Cowork 已给出工作量对比，建议先做 10–20 张单的真路径试点。批准前 `docs/queue/CONTROL.md` 保持 HOLD。
11. **T0 集成提交**：把前一团队已验收但未提交的成果提交入库（见 `docs/HANDOFF.md`）。须 Jun 看过文件清单后批准。

## 历史裁定索引
- D12–D22 与 Cowork 的工单节（§1–§19）：`docs/archive/2026-09-25-chatgpt-v6/CODEX-TICKETS.md` 及更早的 `docs/archive/` 快照。
- 论文与 Lean 的逐条差异：`docs/paper-deltas.md`。
