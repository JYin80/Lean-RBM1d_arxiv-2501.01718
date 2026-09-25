# Even power-sum derivative: scoped successor after T1430

T1430 final INCOMPLETE left the all-order smooth-norm derivative bound (A) unproved; its partial source and T1431 gate-only verdict remain unaccepted (`docs/reports/V6-T1430-nonacceptance.md`). This preflight isolates a smaller substantive source arrow, not a renamed full T1430 attempt. The final consumer is the corrected abstract smooth-cube estimate (D) of T1424 §3, a possible internal route toward the prescribed manuscript's random-scale bound (4.12). The paper's (4.12) itself uses the unsmoothed random loop maximum; this deterministic lemma supplies neither actual loop faces nor Pr/Yr. No paper loss, time window, event or quantifier is changed.

For even `q≥2`, finite `ι`, `1≤j≤q`, `P_q(x)=Σ_i x_i^q` and directions `v : Fin j→(ι→ℝ)`, the required exact source formula is

`D^j P_q(x)[v] = (q)_j Σ_i x_i^(q-j) ∏_{m:Fin j} v_m(i)`.

The required dimension-free bound is

`|D^j P_q(x)[v]| ≤ (q)_j F_q(x)^(q-j) ∏_m F_q(v_m) ≤ q^j F_q(x)^(q-j) ∏_m F_q(v_m)`,

where `F_q(u)=(Σ_i |u_i|^q)^(1/q)` and the `j=q` endpoint omits the `x` factor before Hölder. This is exactly the inner derivative estimate used in each ordered-partition term of T1424 formula (A), including coordinates with `x_i=0`. It is independent of the outer fractional-power chain rule and of T1432's cube FTC. Do not silently replace `F_q` by the function-space sup norm, introduce a cardinality factor, or assume all coordinates positive. The upper bound is valid for every x; `x=(1,0)` in `Fin 2` and all directions the first basis vector give a nonzero j-th derivative for `j≤q` while another coordinate vanishes. The simultaneous witness needs no stochastic event because this theorem is deterministic; in a later actual-model application its arguments must come from the same sample/event.

Targeted direct-proof inventory: accepted `RBM1D/Gauss/CutoffBounds.lean` gives `smoothMax`, comparisons and first/second-order special-domain bounds, not this all-order polynomial formula. T1430's partial `SmoothNormHigherDerivatives.lean` gives notation/positivity only and is unaccepted. Mathlib `Analysis/Calculus/IteratedDeriv/Lemmas.lean` has `iteratedDeriv_pow`; `ContDiff/Operations.lean` has `iteratedFDeriv_sum_apply`; `Analysis/MeanInequalities.lean` has finite Hölder inequalities. Targeted project/Mathlib search found no direct theorem combining the explicit multilinear derivative of the finite-coordinate power sum with the required q-norm bound. Thus the edge is **mathematically proved in T1424, missing as a Lean source lemma**; no new mathematical contradiction or stronger paper assumption is inferred.

The first attempt may own only a new `RBM1D/Gauss/PowerSumHigherDerivatives.lean` and its report, with a separate Sol High PASS-gated audit report. It should import accepted source/Mathlib only, not T1430/T1432 or other in-flight/unaccepted modules. A derivative formula alone or a bound stated as a hypothesis is INCOMPLETE. A later separately audited composition must still combine this with the outer fractional-power derivatives to prove full (A), and then with T1432 to prove (D); actual Gaussian (4.12) remains HOLD.
