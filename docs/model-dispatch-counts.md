# New Codex task model dispatches

Count starts at 2026-09-23 16:48:14 UTC, when Jun requested tracking. T669 was dispatched before this checkpoint and is excluded. Count each newly created Codex worker or independent-audit task once, using the model actually passed to `create_thread`. Do not count follow-up messages, retries that do not create a task, or the scheduler heartbeat itself.

| Ticket | Model | Effort | Reason |
|---|---|---|---|
| T670 | GPT-6 Sol | High | Independent mathematical and Lean acceptance audit of the Hermitian encoder |
| T671 | GPT-6 Sol | High | Independent audit of the finite permutation concentration and asymptotic constants |
| T672 | GPT-6 Luna | High | Read-only Mathlib API/import inventory for the literal `jG` topology seam |
| T673 | GPT-6 Luna | High | Read-only finite-permutation probability API/import probe for the missing Fourier-tail lemma |
| T674 | GPT-6 Sol | High | Independent Lean/mathematical acceptance of the 21-name carrier-core extraction |
| T675 | GPT-6 Sol | High | Nontrivial clean Lean extraction of the doubled-argument E⊗E adapter |

Current total: GPT-6 Luna 2, GPT-6 Sol 4. Ratio Luna:Sol = 2:4 (33.3%:66.7%).
