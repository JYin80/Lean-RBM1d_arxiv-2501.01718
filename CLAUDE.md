# RBM1D — rules for the Claude Code execution side (2026-09-25)

Who reads this file: the **execution hub** (one long-running Claude Code session on Jun's Mac) and the **subagents it starts** (`prover`, `prover-hard`, `auditor`, `repairer`, defined in `.claude/agents/`). The **dispatcher** (a Cowork session) and the **supervisor** (a Cowork scheduled task) follow `docs/claude-team/TEAM.md`. Effective decisions: `docs/DECISIONS.md`. Mathematical gates and completion contract: `docs/PLAN.md` (its process/forecasting parts are superseded by `docs/claude-team/TEAM.md`). History of the previous (ChatGPT) team: `docs/archive/2026-09-25-chatgpt-v6/` — targeted search only.

Write code, reports and commit messages in English. Work silently: no narration or progress chatter; one final result per task.

## 1. File ownership (one writer per file)

| Path | Writer |
|---|---|
| `docs/TASKS.md`, `docs/STATUS.md`, `docs/DECISIONS.md`, `docs/HANDOFF.md`, `docs/ROUTES.md`, `docs/queue/CONTROL.md`, `docs/tickets/*` | dispatcher only |
| `docs/queue/T####.state`, `docs/queue/HUB.alive`, `docs/queue/H*-files.txt`, merges into `main`, root imports in `RBM1D.lean` (only when an approved instruction says so) | execution hub only |
| the ticket's "sole writable files" in its worktree, `docs/reports/T####-prove.md` | the ticket's `prover` / `prover-hard` / `repairer` |
| `docs/reports/T####-audit.md` | the ticket's `auditor` |
| `docs/supervisor/*` | supervisor only |

Never edit: another ticket's files or reports, archived files, `Claude outputs/`, `.git/_to_delete/`, `blueprint/`, `docs/paper-deltas.md` numbering (append entries with a temporary tag `T####a`; the dispatcher assigns numbers).

## 2. Execution hub: one loop iteration

0. Overwrite `docs/queue/HUB.alive` with the current UTC time (liveness signal for the dispatcher).
1. Read `docs/queue/CONTROL.md`.
   - `mode: STOP` → start nothing; let running workflows finish their current stage and stop before the next stage.
   - `mode: HOLD` → start no new prover stage; audits of already-finished provers may continue.
   - `mode: AUDIT_FIRST` → start only audit stages.
   - `mode: RUN` → normal.
   - Execute every item in **Approved instructions** that has no `done:` mark, then append `done: <UTC time> <result>` under it (the hub may append only these `done:` lines to CONTROL.md; nothing else).
2. For every ticket ID in CONTROL's **Released tickets** list that has no `docs/queue/T####.state` yet (and mode allows):
   - write `docs/queue/T####.state` with `state: claimed`;
   - create branch `t/T####` and worktree `../RBM1D-wt/T####` from `main`; give it the build cache without sharing writable files: `mkdir ../RBM1D-wt/T####/.lake && ln -s "$PWD/.lake/packages" ../RBM1D-wt/T####/.lake/packages && cp -c -R .lake/build ../RBM1D-wt/T####/.lake/build` (APFS copy-on-write clone; never hard-link with `cp -al`, because Lake rewrites .olean files in place and a hard link would corrupt the main cache; never share one worktree between tickets);
   - tickets, reports, state files and CONTROL.md live only in the **main worktree** (`~/Lean_proof/RBM1D`); give every subagent the absolute path of the ticket file and of the main worktree's `docs/reports/`; their Lean edits stay in their own worktree;
   - start one workflow for the ticket (use a workflow): stage 1 = the role named in the ticket (`prover` or `prover-hard` or `repairer`), working only in that worktree; stage 2 = `auditor`, started only when the ticket's release condition holds (stage-1 report says math preflight PASS and the named modules build). Pass the ticket file path and the worktree path; add nothing, remove nothing.
3. Keep `T####.state` current: `claimed | proving | preflight-fail | built | auditing | audit-pass | audit-fail | blocked | merged`, with one line of reason and report paths. Anything the ticket does not specify → `blocked`, with the question; do not decide it yourself.
4. Never merge, commit to `main`, or touch the root `RBM1D.lean` except under an Approved instruction.

**Merge procedure (only when instructed):** in the main worktree, bring in exactly the ticket's files from `t/T####` (cherry-pick or checkout of those paths), add the point import to `RBM1D.lean` if the instruction says so, run `lake build RBM1D` and the root axiom audit, commit only those files with message `T####: <title>` and the attribution lines required by the session, record the commit hash in the state file. Never `git add -A` / `git add .`; never push.

## 3. Mathematical and Lean gates (all roles)

1. Sole source: `paper/250520-YinJun-v2.pdf`; cite formula numbers. Sole authorized external input: the complex-Hermitian version of [51, Theorem 2.2], only for Theorem 2.6 Step 1 (`docs/paper-deltas.md` #114). Everything else is proved internally.
2. No `sorry`, `admit`, or declared `axiom`. Public `#print axioms` may list only `propext`, `Classical.choice`, `Quot.sound`. Never change a frozen signature; add a primed successor.
3. Every new module must pass `lake build RBM1D.<Module>`; `lake env lean` alone is insufficient.
4. New hypotheses need a nondegenerate simultaneous satisfiability witness. Preserve the paper's parameter order (∀ fixed parameters before `∀ᶠ N`), sharp losses, all dimensions/energies/windows/charges; avoid vacuous `N = 0`, empty index sets, collapsed windows, and "witnesses" that are only satisfiable because a quantity is astronomically large.
5. The paper keeps its Brownian model. `H_u = √u·X` shares one-time laws only; it is not a proof of a stopped-path identity. A conditional adapter or a special-case (`Dims.exampleGrow`, fixed `D`, first cell, `E = 0`) result is never the general statement — say so in the report.
6. Docstrings are not evidence: judge a declaration by the hypotheses in its signature.
7. Any Lean/paper statement difference goes into `docs/paper-deltas.md` with a temporary tag.

## 4. Reports

`docs/reports/T####-prove.md`: (a) math preflight per target: PASS/FAIL/BLOCKED with reasons (written **before** any Lean); (b) declarations added, file, build commands and results, printed axioms; (c) key lemmas used; (d) open issues. `docs/reports/T####-audit.md`: per target PASS / RETURN (reason) / BLOCKED; statement vs paper, vacuity/hidden hypotheses/cycles, boundary cases, witness, module + root build, axioms. Final chat reply of any subagent: one line — ticket, verdict, report path.
