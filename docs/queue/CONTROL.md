# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: RUN
updated: 2026-09-25 16:25 UTC (Jun approved: amended pilot specs released, HOLD lifted)
reason: True-path pilot running. Only the tickets listed under Released may start. A′ stays frozen: no A′ ticket is released, and none may be started.

## Released tickets
The spec of each ticket below is `docs/tickets/T####-amend-1.md`; it supersedes `docs/tickets/T####.md`.
- T1481 (pilot P1, grid path + transfer lemma). Role: prover. Branch t/T1481. Sole writable: RBM1D/Gauss/GridPath.lean.
- T1483 (pilot P3, grid stopping times; generic). Role: prover. Branch t/T1483. Sole writable: RBM1D/Gauss/GridStop.lean.
- T1484 (pilot P4, Azuma + Doob, replaces BDG; generic). Role: prover-hard. Branch t/T1484. Sole writable: RBM1D/Gauss/GridAzuma.lean. Failure signal in the spec: stop, do not work around.
- T1485 (pilot P5, discrete Duhamel + Uker factorisation). Role: prover. Branch t/T1485. Sole writable: RBM1D/Gauss/GridDuhamel.lean.
(T1482, pilot P2, is NOT released yet: it needs T1481 merged. The dispatcher will list it here then.)

## Withdrawn original specs (never started)
- T1481–T1485: withdrawn 2026-09-25 15:55 UTC by the dispatcher. Defects: T1485 acceptance allowed `sorry` (violates CLAUDE.md §3); T1481 referenced a nonexistent `B.GaussSample` and stated the marginal law against a generic `Sample` (which carries no distribution) at a mismatched time; T1484/T1485 stated Gaussian increment bounds almost surely instead of with high probability, and T1484's moment inequality had the wrong form. Corrected specs will be issued as `docs/tickets/T148x-amend-1.md` and re-listed here.

## Approved instructions
- H0: commit the Claude-team cutover files: `.gitignore`, `AGENTS.md`, `CLAUDE.md`, `.claude/agents/*.md`, `.claude/settings.json`, `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/STATUS.md`, `docs/TASKS.md`, `docs/HANDOFF.md`, `docs/queue/CONTROL.md`, `docs/tickets/README.md`, `docs/supervisor/README.md`, `docs/claude-team/*` (incl. `paper-ledger.md`), and the moves into `docs/archive/2026-09-25-chatgpt-v6/`. Approved by Jun 2026-09-25.
  done: 2026-09-25 14:41 UTC — committed 47dffbc "H0: cutover to the Claude team" (32 files: 23 added, 3 deleted/moved into docs/archive/2026-09-25-chatgpt-v6/, 5 modified in place: .gitignore, AGENTS.md, CLAUDE.md, docs/STATUS.md, docs/TASKS.md).
- H1a: produce `docs/queue/H1-files.txt` = every untracked or modified `.lean` file transitively imported by `RBM1D.lean`, plus untracked `docs/reports/*` — do not stage anything. Approved by Jun 2026-09-25.
  done: 2026-09-25 14:44 UTC — wrote docs/queue/H1-files.txt (287 .lean files in RBM1D.lean's transitive import closure, 865 untracked docs/reports/* files; 1161 lines total). Nothing staged. Note: RBM1D.lean itself (M) and the 3 modified-but-tracked docs/reports/{T1044,T280e,T280g}.md are excluded per H1a's wording (only untracked reports were requested).
- H1b: commit every file listed in `docs/queue/H1-files.txt` (287 .lean files + untracked docs/reports/*); then run `lake build RBM1D`; then run the root axiom audit (`grep -r "sorry" RBM1D/ --include="*.lean" -l` or equivalent); record the commit hash and build result in `docs/queue/H1b-result.txt`. Approved by Jun 2026-09-25.
  done: 2026-09-25 ~15:40 UTC — committed ab96505 "H1b: commit T0 Lean files and audit reports" (1152 files). lake build RBM1D 9631/9631 PASS; root axiom audit PASS (20610 decls ⊆ propext, Classical.choice, Quot.sound). See docs/queue/H1b-result.txt.
  done: 2026-09-25 15:36 UTC — state=BLOCKED on the commit step: the harness's own auto-mode safety classifier denied `git add` of the 1152-file list as a bulk operation (no reason given), tried both `--pathspec-from-file` and plain-argument forms; did not chunk into smaller adds since the denial names that as a disallowed workaround for a blocked outcome. Ran `lake build RBM1D` anyway (build reads files off disk, independent of git state): 9631/9631 jobs, exit 0, 0 errors, 2192 lint-only warnings, root axiom audit passed (20610 `RBM` declarations, all within propext/Classical.choice/Quot.sound). No commit hash exists. Full detail in docs/queue/H1b-result.txt. Question for the dispatcher: who/how performs the commit (Jun directly, a smaller-batch retry, or other authorization) — not deciding this myself.
  done: 2026-09-25 15:40 UTC — RESOLVED: Jun explicitly instructed the commit in chat; re-ran `git add --pathspec-from-file` under that direction and it staged cleanly this time (1152 files, matches H1-files.txt). Committed ab96505 "H1b: commit T0 Lean files and audit reports" (1152 files changed, 146992 insertions(+), 0 deletions(-)). Build/audit results unchanged from the prior entry. Full detail in docs/queue/H1b-result.txt.

- H2: for T1481, T1483, T1484, T1485 only: overwrite the stale `docs/queue/T####.state` (state: blocked, from 15:47) with `state: claimed`, then start each ticket per CLAUDE.md §2 using its `docs/tickets/T####-amend-1.md` spec. Leave `T1482.state` as it is (blocked, not released). Approved by Jun 2026-09-25.

- H3: (1) commit exactly these files on `main` with message `H3: dispatcher records for the true-path pilot`: `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/queue/CONTROL.md`, `docs/claude-team/pilot-P4P5-paper.md`, `docs/supervisor/2026-09-25-1554.md`, `docs/tickets/T1481.md` … `docs/tickets/T1485.md`, `docs/tickets/T1481-amend-1.md` … `docs/tickets/T1485-amend-1.md`. (2) Then `git push origin main` (no `--force`, no other branch). If the push is rejected for any reason, stop and record the exact error here; do not pull, rebase or retry. Standing rule from now on (DECISIONS §9): after every commit to `main` made under an Approved instruction, push `main` the same way. Approved by Jun 2026-09-25.

- H4: the dispatcher changed, at Jun's direct request, `model: opus` → `model: claude-opus-5-5` in `.claude/agents/auditor.md` and `.claude/agents/repairer.md`, and in `.claude/settings.json` allowed `Workflow` and `Bash(git push origin main)` (force/delete pushes stay denied) so that the hub runs without prompts (files already edited on disk). Commit exactly these three files with message `H4: pin auditor/repairer to claude-opus-5-5; allow workflows and push of main`, then push `main` per H3's standing rule. Every auditor/repairer stage started from now on must use the pinned model. Approved by Jun 2026-09-25.

## Pending approval (information only — the hub must NOT act on these)
(none)
