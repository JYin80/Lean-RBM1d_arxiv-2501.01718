# 启动清单与启动提示词（给 Jun）

## 1. 启动前（你来做）
1. 确认 ChatGPT 调度和监督的会话已经关闭。仓库里记录它们已按你的指示暂停，旧文件已归档到 `docs/archive/2026-09-25-chatgpt-v6/`。
2. 审阅 `docs/claude-team/settings.json.proposed`。它预先批准 `lake build`、`git worktree/add/commit` 等命令，禁止 `git push`、`git add -A`、`git reset --hard`、`rm -rf`。同意后在终端执行：
   `cp docs/claude-team/settings.json.proposed .claude/settings.json`
   这是长期生效的权限设置，所以要你亲自确认。
3. 用 `claude --version` 确认 Claude Code 版本足够新：角色文件要支持 `effort` 字段；Workflow；Remote Control 的跨会话消息要求 v2.1.224 以上。
4. 在 Cowork 新开任务「RBM1D 调度 V1」（建议放在「Lean__d=1 band」这个 Project 里；换了账号也没关系，需要的文件都在仓库里），连接 RBM1D 文件夹，模型选 Opus，贴 §2 的提示。
5. 在 Mac 终端启动执行中枢（§3）。
6. 监督不用单独开会话：由调度 V1 用 §4 的提示词建定时任务，你在确认框里批准即可。建好后，如需指定模型（Opus），在定时任务设置里改，或让调度去改。

## 2. 调度启动提示（贴到 Cowork 新任务）
```
你是 RBM1D 的总调度（调度 V1）。
先读 docs/HANDOFF.md，再读 docs/DECISIONS.md、docs/claude-team/TEAM.md、docs/STATUS.md、docs/ROUTES.md、docs/PLAN.md、docs/claude-team/ROUTE-DECISION-step2.md 和 CLAUDE.md；再读 docs/claude-team/paper-ledger.md（论文逐条证明清单）。
只读这些；其余材料按需定向查，不通读 archive。
读完后：
1) 排好下一次心跳，间隔不超过 20 分钟。空闲心跳要从简：先只看 docs/queue/HUB.alive、docs/queue/*.state、docs/reports/、docs/supervisor/ 的修改时间，与上次相比没有变化，就只排下一次心跳然后结束本轮，不读别的文件、不写汇报；
2) 按 HANDOFF 第 3 节逐项推进；
3) 用中文向我简短汇报你的理解，以及需要我批准的第一件事。
规则：不写 Lean；不做任何 git 写操作，查 git 用 git --no-optional-locks；只写你独占的文件；需要我决定的事一次只问一件。
```

## 3. 执行中枢启动（Mac 终端）
```
cd ~/Lean_proof/RBM1D
claude --remote-control 执行中枢
```
进入后用 `/model` 选 **Sonnet**（执行中枢只做机械执行，用 Sonnet 省额度），然后贴：
```
/loop 10m You are the RBM1D execution hub. Follow CLAUDE.md §2 exactly: one loop iteration per firing. Use a workflow for each released ticket (stage 1 = the ticket's role, stage 2 = auditor once the release condition holds). Never decide anything the ticket or docs/queue/CONTROL.md does not state; write state=blocked with the question instead. If nothing changed since the last firing, only update docs/queue/HUB.alive and print nothing. Stay silent unless something is blocked or finished.
```
- 固定间隔的 `/loop` 在 `--resume` 恢复会话后会继续；终端关掉之后要重新运行。
- 提示里的 "Use a workflow" 就是对 Workflow 的明确授权。

## 4. 监督定时任务的提示词（调度 V1 用它创建：每天一次，使用本机，只读）
```
你是 RBM1D 的独立数学监督。本次是一个全新会话，只读。仓库在本机的 RBM1D 文件夹。
1) 读 docs/claude-team/TEAM.md 的「独立数学监督」一节和 docs/ROUTES.md。
2) 找到 docs/supervisor/ 里最近一次结论的时间，列出此后新增或更新的 docs/tickets/*、docs/reports/*、docs/queue/*.state。
3) 如果本次是事件触发，事件说明附在本消息之后。
4) 只回答路线层面的四类问题（TEAM §1）。有疑点才打开具体的 Lean 陈述、生产者和论文原文。
5) 统计每个 gate 自交接起的证明单数，按 25 / 50 的预算规则判断。
6) 按 docs/supervisor/README.md 的格式，把结论写入 docs/supervisor/<UTC 时间>.md。这是你唯一可以写的地方：不派单，不改其他文件，不执行任何 git 写操作（查 git 用 git --no-optional-locks）。
结论只能是 PASS、建议 HOLD、建议 STOP。HOLD/STOP 必须附可核查的来源、准确的数学缺口、最早可见时间，以及其后派发的工单。
```
