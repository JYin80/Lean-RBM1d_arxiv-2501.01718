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
| T683 | GPT-6 Sol | High | Nontrivial dependency preflight for clean eeFun and Band.toDims extraction |
| T684 | GPT-6 Sol | High | Pure Lean finite-permutation counting mean-zero theorem for Fourier sum |
| T685 | GPT-6 Luna | High | Mechanical three-import root integration of independently audited pure helper modules |
| T686 | GPT-6 Sol | High | Pure Lean proof of nonempty finite upper-semicontinuous supremum |
| T687 | GPT-6 Luna | High | Read-only finite Fourier-character Mathlib API/import inventory, no mathematical acceptance judgment |
| T688 | GPT-6 Sol | High | Independent mathematical/Lean acceptance audit of T684 finite permutation mean |
| T689 | GPT-6 Sol | High | Independent acceptance audit of T685 root-import integration |
| T690 | GPT-6 Sol | High | Independent Lean/mathematical acceptance audit of T686 finite USC supremum |
| T691 | GPT-6 Luna | High | Mechanical five-declaration source move after accepted dependency preflight |
| T692 | GPT-6 Sol | High | Substantive Lean proof of nonzero Fourier-character orthogonality and mean |
| T693 | GPT-6 Luna | High | Mechanical two-import root integration of independently audited pure helpers |
| T694 | GPT-6 Sol | High | Substantive finite-permutation prefix-fiber bijection proof toward conditional exposure |

Current total: GPT-6 Luna 6, GPT-6 Sol 19. Ratio Luna:Sol = 6:19 (24.0%:76.0%).

Prospective target from Jun's 2026-09-23 17:35 UTC request: aim for about 50% Luna among newly created tickets **when genuinely useful, simple, tightly scoped, low-risk work exists**. Do not relabel substantive proofs, mathematical preflights, nontrivial integration, satisfiability checks, or independent acceptance audits to improve the fraction, and do not create filler tickets. Preserve the cumulative count above and separately report the post-request count. Post-request Luna 3, Sol 5; ratio 3:5 (37.5%:62.5%).
