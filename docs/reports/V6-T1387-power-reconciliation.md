# T1387 quantitative reconciliation and next exact arrow

2026-09-25 UTC. T1387 ended **INCOMPLETE**, with no source import or acceptance; T1388 closed gate-only. The focused read-only mathematical review found a valid exponent budget, not a contradiction in the manuscript. The scheduler checked its algebra against `FastDecayFlow.qBlockSize`/`qBlockErr` and `Lemma514FirstHalfQVMoments.eeGoodBound`/`qqGoodBound`; the remaining work is Lean proof of this budget and the moment split, in a new file without editing T1387's preserved source. Sole manuscript reference: Lemma 5.14, (5.92), (5.103), (5.105) in `paper/250520-YinJun-v2.pdf`.

Write `m=n+2`, `k=m-1`, `A=(band exampleGrow).scale 0 N u`, `K=N^τ`, `ell=(band exampleGrow).ell N u`, and `δ=m W L N^(-D)`. T1387's `eeGoodBound` has the exact form `C_m A^(-2m) eta_u^(-1)(K+2)+δ`. If `x=[2 exp(1)(ell K+1)cTwo52/ell]^k`, `y=[2 exp(1)(2ell K+1)cTwo52/ell]^k`, `z=(cTwo52 L/ell)^k`, and `h=exp(-cZero K)`, the two `qBlockSize`/`qBlockErr` applications expand to

`qqGoodBound = [(1+y)(1+x)+z*x*h] * eeGoodBound + [z*(2+y)+z^2*(1+h)] * δ`.

Thus multiplication by `A^(2m)` cancels the source's `A^(-2m)` exactly. On `0≤u≤1/2`, `1≤ell≤2`, `1/2≤eta_u≤1`, `A≤2W`, `WL≤N` eventually, and `0<τ≤1`, the resulting uniform profile is bounded by a fixed `C_m` times

`N^((2n+3)τ) + N^(n+1+(n+2)τ) exp(-cZero N^τ) + N^(4n+7-D)`.

Choose `D=4n+9` and, for each requested `ε>0`, `τ=min(1/8, ε/[2(2n+3)])` **after** `ε`; the exponential is absorbed using existing `SumZeroDyn.eventually_exp_small`. The good-event bound is eventually `≤ C_{n,ε} N^(ε/2)` uniformly in `u`. A fixed positive `τ` before arbitrarily small `ε` would be a stronger and generally false target; do not dispatch that quantifier order.

The deterministic global envelope in T1387 is at most `C_m N^(2n+3)` on the first half. For fixed moment order `p≥1`, take the same T1349 measurable high-probability event with complement exponent `D_bad=p(2n+5)`. Existing `LkGoodMeasurable.momNorm_le_indicator_add_env` and T1387 integrability then make the complement contribution `O(N^(-2))`, yielding the intended `∀ ε>0 ∀ p≥1 ∀ᶠ N` small-loss moment estimate. T1349's `eventually_joint_nonzero_far_witness` supplies a nondegenerate actual sample on that same event. The conclusion is a first-half `Dims.exampleGrow`, `E=0` QV-envelope prerequisite only; no moving-window Lemma 5.14, stopped Brownian identity, or full-paper theorem follows.
