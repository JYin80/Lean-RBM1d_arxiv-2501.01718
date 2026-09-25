# CONTROL — written only by the dispatcher (Cowork). The hub may only append `done:` lines under Approved instructions.

mode: HOLD
updated: 2026-09-25 14:31 UTC (H0+H1a approved by Jun)
reason: Waiting for Jun's approval of the Step-2 route decision. T0 integration commit in progress (H0+H1a approved, H1b pending review of H1-files.txt).

## Released tickets
(none)

## Approved instructions
- H0: commit the Claude-team cutover files: `.gitignore`, `AGENTS.md`, `CLAUDE.md`, `.claude/agents/*.md`, `.claude/settings.json`, `docs/DECISIONS.md`, `docs/ROUTES.md`, `docs/STATUS.md`, `docs/TASKS.md`, `docs/HANDOFF.md`, `docs/queue/CONTROL.md`, `docs/tickets/README.md`, `docs/supervisor/README.md`, `docs/claude-team/*` (incl. `paper-ledger.md`), and the moves into `docs/archive/2026-09-25-chatgpt-v6/`. Approved by Jun 2026-09-25.
- H1a: produce `docs/queue/H1-files.txt` = every untracked or modified `.lean` file transitively imported by `RBM1D.lean`, plus untracked `docs/reports/*` — do not stage anything. Approved by Jun 2026-09-25.

## Pending approval (information only — the hub must NOT act on these)
- H1b: after the dispatcher approves that list, commit exactly those files, run `lake build RBM1D` and the root axiom audit, record the hash.
