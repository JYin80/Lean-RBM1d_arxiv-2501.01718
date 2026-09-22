# AGENTS.md

本仓库的规则写在 **`CLAUDE.md`**——名字带 Claude，但**对所有 agent 适用**（Codex、ChatGPT 等）。

* **Codex / ChatGPT 做 Lean 工单**：先读 **`docs/CODEX-TICKETS.md`**（背景、依赖、文件归属、Codex 专用 git 纪律），再读 `docs/TASKS.md` 里你那一行。
* **做 Lean 工单（工人）**：读 `CLAUDE.md`、`docs/TASKS.md` 里你认领的那一行、`docs/STATUS.md` 里相关的节。
* **接手调度（Cowork 离线时）**：读 **`docs/HANDOVER.md`**，按它的 §4 做心跳、§5 做审计、§6 分流决策。

**读文档**：`docs/STATUS.md`（摘要）可以读全；`docs/TASKS.md` 用 `grep -n '^| Txxx |'` 只取你那一行；`docs/archive/` 下的文件永远只 grep，不整份读（原 STATUS+TASKS 整份约 25 万 token）。完成报告写 `docs/reports/Txxx.md`。

硬规则摘要（完整版见 `CLAUDE.md`）：

1. 不留 `sorry`，不写 `axiom`；`#print axioms` 只允许 `propext` / `Classical.choice` / `Quot.sound`。
2. 不改冻结签名——要改就加带撇版 `Foo'`，旧版保留或加 `@[deprecated]`。
3. 不 `git add -A`；只 `git add` 具体文件。根文件 `RBM1D.lean` 只做点插入 import。
4. 新文件收工前必须 `lake build RBM1D.<模块>`（单文件 `lake env lean` 不施加 `autoImplicit` 等选项，不算数）。
5. 含新假设的定理必须附**非退化**的可满足性见证（本项目最常见的缺陷是空真）。
6. Lean 陈述与论文字面不同，写进 `docs/paper-deltas.md`，`#` 栏只写临时号 `T<单号><字母>`，数字号由调度分配。
7. 只依据 `paper/250520-YinJun-v2.pdf`；引用论文以公式编号为主。
