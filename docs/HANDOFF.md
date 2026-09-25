# HANDOFF — RBM1D 调度 V1（2026-09-25，由 Cowork 在交接时写）

## 1. 你的身份与规则
- 你是 RBM1D 的**总调度**（Cowork 会话）。章程：`docs/claude-team/TEAM.md`。生效的决定：`docs/DECISIONS.md`。执行侧规则：`CLAUDE.md`，写工单前必须清楚它。
- 你不写 Lean，不在仓库执行任何 git 写操作；查 git 一律用 `git --no-optional-locks`。你写 `docs/TASKS.md`、`STATUS.md`、`DECISIONS.md`、`HANDOFF.md`、`ROUTES.md`、`queue/CONTROL.md`、`tickets/*`。
- 与 Jun 用中文沟通；仓库里的规则、工单、报告用英文，面向 Jun 的账本和状态可以用中文。

## 2. 现状（详见 `docs/STATUS.md`、`docs/ROUTES.md`）
- 前一团队已停止；没有在跑的工单，也没有在跑的 Workflow。`CONTROL.md` 为 HOLD。
- 工作区构建全绿，但有约 1596 条定理未提交，要走 T0 分拣。
- 主定理都未无条件证明。最难的四块是：Step 2 的停时（路线待定）、全阶 Lemma 5.14、随机尺度 (4.5)、锐 (5.48)；Theorem 2.6 整条线尚早。

## 3. 第一批事项（按顺序）
1. **排心跳**：用定时提醒回到本会话，间隔不超过 20 分钟。先排下一次，再做本次的事。**空闲心跳从简**：先只看 `docs/queue/HUB.alive`、`docs/queue/*.state`、`docs/reports/`、`docs/supervisor/` 的修改时间，没有变化就只排下一次心跳然后结束本轮，不读别的文件、不写汇报。
2. **确认执行中枢在线**：看 `docs/queue/HUB.alive` 的时间是否在更新。若执行中枢以 Remote Control 启动，可用会话列表查它能否收消息；收不到就只靠文件轮询。
3. **建监督定时任务**：每天一次兜底，使用本机，只读，提示词见 `docs/claude-team/STARTUP.md` §4。建好后，事件发生时用「立即触发」并附上事件说明（触发条件见 TEAM §1）。
4. **向 Jun 提请两项批准**，一次提一件：
   a. **H0 + H1a**：提交交接文件；列出待提交的已验收成果清单，只列不提交。批准后把它们从 CONTROL 的 Pending 移到 Approved。H1a 的清单交 Jun 过目后，再批 H1b。
   b. **Step 2 路线**：A′ 继续 HOLD，还是做真路径（离散网格高斯游走）试点。完整的对比和试点范围见 `docs/claude-team/ROUTE-DECISION-step2.md`，向 Jun 说明时以它为准。要点：
      - 真路径约 130–300 张证明单，照论文走，基础设施可复用到 Theorem 2.6；
      - A′ 在一般 Dims 上还没有纸面证明，至少 300 张且可能做不成，还要付一个论文里没有的交叉项。
      - 建议先做 10–20 张单的试点。
5. **试点获批后**：
   - 先写试点的纸面论证和接口清单：网格游走、单时刻同分布转移、离散可选停止、停止过程的矩不等式、停时越过阈值一步的控制。需要时调用 Fable 子代理。
   - 逐条核对 Mathlib 现有的离散停时和可选停止 API 的签名，再写 `docs/tickets/T####.md`。
   - 在 `ROUTES.md` 为试点新开一行；在 `CONTROL.md` 的 Released 里放行。

## 4. 已知陷阱
- Cowork 设备 shell 的删除权限在重连后会重置；普通 `git status` 会在 `.git/` 留下锁文件并删不掉。一律加 `--no-optional-locks`。`.git/_to_delete/index.lock.cowork-0215` 是 09-25 留下的空文件，可以让执行中枢删掉。
- 执行中枢对 `CONTROL.md` 只能追加 `done:` 行，其余都由你写。它只执行 Released 列表里的单和 Approved 里的指令。
- 写工单规格前逐条核对（TEAM §3）：签名、量词、加性项走到最终归一化之后的大小、各假设能否同时满足。核对不了的写成「第 0 步只读核对」。
- 以签名的假设为准，不信 docstring 和蓝图。已知的过度声称和接口隐患列在 `docs/STATUS.md`。

## 5. 常用链接
- Step 2 路线决定备忘：`docs/claude-team/ROUTE-DECISION-step2.md`
- 论文逐条清单（Markdown，含每条命题的状态和说明）：`docs/claude-team/paper-ledger.md`
- 逐条证明清单：https://claude.ai/artifact/KCWCVS4YQH9WrEffStsMgp ；数据在 `Claude outputs/ledger/paper-ledger-2026-09-25.json`
- 蓝图：https://claude.ai/artifact/Nr3v69rGqWNrGvym6Jmzdr
- 数学 gate 与完成合同：`docs/PLAN.md`；论文差异：`docs/paper-deltas.md`；前一团队的记录：`docs/archive/2026-09-25-chatgpt-v6/`
