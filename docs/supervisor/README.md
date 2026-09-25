# Supervisor verdicts (written only by the supervisor scheduled task)

One file per run: `docs/supervisor/YYYY-MM-DD-HHMM.md` (UTC), containing:
- trigger: daily backstop | event (as given by the dispatcher)
- inputs read: `docs/ROUTES.md` + list of new tickets/reports since the previous verdict (+ any Lean/paper sources opened)
- verdict: PASS | RECOMMEND HOLD | RECOMMEND STOP
- for HOLD/STOP: checkable sources, the exact mathematical gap, earliest time it was visible, tickets dispatched after that
- route budget: per gate, tickets since cutover (flag ≥ 25; recommend HOLD at ≈ 50 without closure)
