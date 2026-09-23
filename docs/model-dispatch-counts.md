# New Codex task model dispatches

Count starts at 2026-09-23 16:48:14 UTC, when Jun requested tracking. T669 was dispatched before this checkpoint and is excluded. Count each newly created Codex worker or independent-audit task once, using the model actually passed to `create_thread`. Do not count follow-up messages, retries that do not create a task, or the scheduler heartbeat itself.

| Ticket | Model | Effort | Reason |
|---|---|---|---|
| T670 | GPT-6 Sol | High | Independent mathematical and Lean acceptance audit of the Hermitian encoder |
| T671 | GPT-6 Sol | High | Independent audit of the finite permutation concentration and asymptotic constants |

Current total: GPT-6 Luna 0, GPT-6 Sol 2. Ratio Luna:Sol = 0:2 (0%:100%).
