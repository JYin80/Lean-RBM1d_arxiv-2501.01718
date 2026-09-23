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
| T676 | GPT-6 Sol | High | Pure Lean proof of exact finite Fourier swap sensitivity and sharp witness |
| T677 | GPT-6 Sol | High | Substantive pure topological Lean proof for closed hard-cutoff upper semicontinuity |
| T678 | GPT-6 Sol | High | Clean Lean continuity proof for the literal ellStar hard-cutoff threshold |
| T679 | GPT-6 Sol | High | Independent acceptance audit of the clean doubled-argument EEBridge extraction |
| T680 | GPT-6 Sol | High | Independent acceptance audit of the Fourier swap bound and sharp witness |
| T681 | GPT-6 Sol | High | Independent acceptance audit of the closed-cutoff upper-semicontinuity proof |
| T682 | GPT-6 Sol | High | Independent acceptance audit of the clean ellStar cutoff continuity proof |

Current total: GPT-6 Luna 2, GPT-6 Sol 11. Ratio Luna:Sol = 2:11 (15.4%:84.6%).
