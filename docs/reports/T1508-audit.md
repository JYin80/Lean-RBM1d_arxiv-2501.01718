Auditor model: claude-opus-5-5[1m]

# T1508 (amend-1) — audit report

Spec: `docs/tickets/T1508-amend-1.md` (sole governing spec). Prove report: `docs/reports/T1508-prove.md`.
Branch `t/T1508`, commit `1ed0452`. Audit worktree (fresh, not the prover's): `/Users/junyin/Lean_proof/RBM1D-wt/T1508-audit`.
Audit written 2026-09-26 01:21 UTC.

## Verdicts

| Target | Verdict |
|---|---|
| (T2′) `RBM.Gauss.Grid.qv_time_sum_le` | **PASS** |
| corollary `RBM.Gauss.Grid.qv_time_sum_le'` | **PASS** |

The route deviation (pointwise bound, no `hΔ`) is a genuine, verified strengthening. My reasons are in §3; they were checked independently, not copied from the prover.

## 1. Math preflight

`T1508-prove.md` §(a) has a per-target math preflight with verdict PASS, timestamped 2026-09-26 01:03 UTC, "before any Lean". It lays out the pointwise route (K1/K2), the J-power absorption and the nearEpsilon step before the Lean section (b). Present: OK.

## 2. Statement vs ticket and paper

Compiled signature (GridQVSum.lean:591–603). Hypotheses: `|E| < 2`, `hs0`, `hst`, `ht1`, `Cond272 B E s t`, `0 < c`, and step2's `hreg`. That `hreg` is `∀ᶠ N, N^c (η_s/η_t)^30 ≤ B.scale E N (t N)`, the same as `Step2.jS_highProb`/`cond272_of_strict`. The remaining hypotheses are `0 < δ`, `δ ≤ c/24`, `0 ≤ ε`, `2ε ≤ δ`, `60 ≤ D`. Conclusion: `∀ κ > 0, ∀ᶠ N, ∀ T Kq, s N ≤ T N ≤ t N → 1 ≤ Kq N → ∀ k ≤ Kq N`,
`Σ_{j<k} step·Qd(u_j)·((1−u_j)/(1−u_k))^4 ≤ (1200/Im m(E))·N^κ·((η_s/η_{u_k})^4 + 1)`.

- **Quantifier order.** The fixed parameters (`B,E,s,t,c,δ,ε,D`, then `κ`) come before `∀ᶠ N`. The endpoint `T N = u_*`, the step count `Kq N = K` and `k ≤ K` are all quantified inside the eventual set. The eventual set (from `filter_upwards` at l.605–607) depends only on `κ, D, B, hreg`, so the bound is uniform in `u_*`, `K` and `k`, as required.
- **Grid.** `step s T Kq N = (T N − s N)/Kq N` and `time … j = s N + j·step` (GridPath.lean:48,51, merged). This matches the ticket's `u_j = s + jΔ`, `Δ = (u_* − s)/K`.
- **Summand.** It is exactly `Δ·Qd(u_j)·((1−u_j)/(1−u_k))^4`, with left endpoint `u_j` and endpoint `u_k`. OK.
- **Qd.** It is literally the ticket's `diagNearRate(ℓ_w,ℓ_s,η_w) + 2·nearEpsilon(W,L,ℓ_w,η_w,D,J w) + diagFarRate(ℓ_w,η_w,D,J w, sDet(w,ℓ_s))` with `J w = N^{2ε}·Step2.thr E s δ N w = N^{2ε}N^δR_w^4`. I checked this against `diagShape'` (APrimeNearRem.lean:714). Its first bracket is `(diagNearRate + 2ε)` times an indicator ≤ 1, and its second bracket is `diagFarRate`, both times `tailT²`. So `Qd` is `diagShape'` with the indicator dropped and `tailT²` stripped, as the ticket specifies. The `(ℓ_u/ℓ_s)^5` factor is kept, not dropped.
- **Exponent.** The exponent on `R_{u_k} = η_s/η_{u_k}` is exactly 4, in the form `(etaT E (s N) / etaT E (time … k))^4`. The constant `qvSumConst E = 1200/(mE E).im` depends only on `E`.
- **Paper.** This is the grid (Riemann-sum) form of (5.44), in the label-free `Λ_k` shape. Per supervisor 0048 §1a and pilot §6, it is what T1504 (T1″) consumes. The `N^δ` threshold is the already-recorded (5.43) delta (pilot §6(b)). There is no new Lean/paper difference beyond the discretisation the ticket itself prescribes.
- **Corollary `qv_time_sum_le'`.** It has the same hypotheses and right side, and the summand factor is `((1 − u_{j+1})/(1 − u_k))^4`. The proof dominates termwise, using `0 ≤ 1−u_{j+1} ≤ 1−u_j` for `j+1 ≤ k` and `Δ·Qd(u_j) ≥ 0` (`Qd_nonneg`), and then applies (T2′). It covers the `qv_conv_le` propagator factor. OK.
- **Hypotheses the proof does not use.** `Cond272`, `0 < c` and `0 ≤ ε` are unused (underscore-named). They are kept for interface fidelity. Unused hypotheses only make the statement weaker, never vacuous, and they are satisfied by the witness. Not a defect.

## 3. The route deviation: independent verification

**(a) Near term, exponent 4 (checked).**
- `diagNearRate B N ℓu ℓs ηu = 2 ηu⁻¹ cNear2(W,ℓu) (ℓu/ℓs)^5` (APrimeQVEndpoint.lean:807).
- K1 (`ellHat_sq_mul_one_sub_le`). With `ℓ̂(x) = min((1−x)^{-1/2}, L)` we get `ℓ̂(x)²(1−x) = min(1, L²(1−x))`, which is non-increasing in `x`. So `r_w² η_w ≤ η_s` for `r_w = ℓ_w/ℓ_s`, whether or not the cap is active. This is correct.
- K2 (`pow5_mul_pow3_le`). From K1 and `η_w ≤ η_s`: `(rη_w)² = (r²η_w)η_w ≤ η_s²`, so `rη_w ≤ η_s`. Then `r^5η_w^3 = (r²η_w)²(rη_w) ≤ η_s³`. Only natural powers are used, so nothing is hidden in an rpow. Correct.
- `near_mul_le` gives `2η_w⁻¹c2 r^5 (η_w/η_v)^4 = 2c2 r^5η_w^3/η_v^4 ≤ 2cN·η_s³/η_v⁴`.
- In the main theorem every summand is bounded by `Δ·M`, where `M = (34N^κ+1152)η_s³/η_v⁴ + 3R_v⁴`. Then `Σ_{j<k}Δ = kΔ ≤ T N − s N ≤ 1 − s N`. Since `(1 − s)η_s³/η_v⁴ = (1/Im m)·(η_s/η_v)^4` (`hXY`, using `η_s = (1−s)Im m`), the total is `≤ (34N^κ+1152)R_v⁴/Im m + 3R_v⁴`.
- Exponent 4 exactly; `final_arith` checks the constant 1200.

Why this does not contradict the ticket's warning. The ticket's integrand after `r_w ≤ R_w^{1/2}` is `η_s^{5/2}η_w^{1/2}η_{u_k}^{-4}`. It is non-increasing in `w` and maximal at `w = s`. So "length × sup of the *whole* integrand" gives `(1−s)·η_s³/η_v⁴ = R_v⁴/Im m`. The ticket's integral gives `(2/3)R_v⁴/Im m`, so the only loss is the constant factor 3/2. The `R^{6.5}` loss the ticket warns about comes from taking the sup of the factors separately at different times (`r_v^5`, `η_v^{-1}`, `R_v^4`). The prover does not do that: `r_w` and `η_w` are evaluated at the same `w` in K2. My own recomputation confirms the prover's claim.

**(b) Far terms and nearEpsilon need no Riemann machinery (checked).** Each is bounded pointwise at fixed `N`, uniformly in `s ≤ w ≤ v ≤ t` (`Qd_mul_le`):
- **Far, `η⁻¹` part** (`far_mul_le`). It reduces to `(J²A√S)² = J⁴A²S = J⁴r³/A ≤ 1` and `J³/A ≤ 1`. That gives `≤ (16cF+1152)·η_w³/η_v⁴ ≤ (16cF+1152)·η_s³/η_v⁴`, which has the same shape as the near term and is summed the same way.
  - The inputs come from `J_pow_le` with `x = N^δ`, `x^{24} ≤ N^c`, `J ≤ x²R_w⁴`, `N^cR_w^{30} ≤ A_w` and `r² ≤ R_w`.
  - `A_w ≥ A_t` is `flowScale_antitoneOn`; `A_t ≥ N^cR_t^{30}` is `hreg`; and `R_w ≤ R_t`.
- **Far, `W^{-D}` part.** `32·WL·W^{-D}J³ ≤ 32W^4·W^{-6} ≤ 1`, using `W ≥ 6`, `J³ ≤ A ≤ WL ≤ N ≤ W²` and `D ≥ 60`. Multiplied by `(η_w/η_v)^4 ≤ R_v⁴`, this gives `≤ R_v⁴`.
- **nearEpsilon.** The merged `EEDef.nearEpsilon_le_inv` (APrimeNearRem.lean:369) with `k = 1` gives `≤ W⁻¹ ≤ 1`. Every one of its premises is discharged inside `Qd_mul_le`: `N⁻¹ ≤ η_w` from `A_t ≥ 1`; `1 ≤ A_w ≤ N`; `J ≤ N`; `16 ≤ D`; and `log W ≥ (4D)²+4` from the eventual `W ≥ exp((4D)²+4)`.

No step needs `Δ` small. The only sum-level fact used is `Σ_{j<k}Δ ≤ 1 − s`.

**(c) Dropping `hΔ` is a strict strengthening (checked).** The (T2′) hypothesis list in the ticket (l.23–26) has no mesh condition; it lists only `K ≥ 1` and `u_* ∈ [s,t]`. `hΔ` appears only in the Route section, as the price of the Riemann-sum step ("add that as an explicit hypothesis", l.43). A version with `hΔ : Δ ≤ N^{-C'}` added follows from the compiled theorem by ignoring `hΔ`: same conclusion, same quantifier structure, restricted to a subset of `(T, Kq)`.

I also checked that nothing else in the statement quietly replaces `hΔ`:
- the only `(T, Kq, k)` constraints are `s N ≤ T N ≤ t N`, `1 ≤ Kq N` and `k ≤ Kq N`;
- the eventual set is independent of `T` and `Kq`;
- no structure field or extra premise restricts the mesh.

The assembly may still choose `K = ⌈N^{C'}⌉` for its own reasons (e.g. T1504/T1505 errors); this theorem applies to any such choice.

**(d) The acceptance criterion "hΔ's exponent C' is explicit".** It is not applicable, not failed. The criterion guards against an implicit or unbounded mesh condition. The compiled theorem has no mesh condition at all, so there is nothing that could be non-explicit. The ticket-writer did not make `hΔ` part of the target, so the criterion does not make it load-bearing. Removing it changes neither the target statement nor the downstream interface: any consumer holding `hΔ` just doesn't use it. So this is within a prover's discretion and does not need dispatcher sign-off.

## 4. Vacuity, hidden hypotheses, cycles

- **Witness.** I checked `qv_time_sum_le_hyps_witness` (compiled, standard axioms). It works for every `Band B`, with `E = 0`, `s = 0`, `t N = 1 − (N+1)^{-1/200}`, `c = 1/4`, `δ = 1/96 = c/24` (the extreme δ), `ε = 1/192` (`2ε = δ`), `D = 60`.
  - It gives `s N < t N` for `N ≥ 1` and `η_s/η_t = (N+1)^{1/200} → ∞`. The window is not collapsed, and the ratio is polynomial in `N`, not astronomically large.
  - `hreg` is proved from `Band.bandwidth` (`W ≥ N^{1/2+c_B}`): `N^{1/4}(N+1)^{31/200} ≤ Im m·N^{1/2}` eventually.
  - `Cond272` is derived via `Step2.cond272_of_strict`, not assumed.
  - All hypotheses of (T2′) and of the corollary are covered.
- **Boundary cases.**
  - `N = 0`: excluded by the eventual set, which includes `N ≥ 1`.
  - `k = 0`: the sum is empty and the right side is ≥ 0, so the statement is true but not a loophole, because it holds for every `k ≤ K`.
  - `T N = s N`: `Δ = 0`.
  - `K ≥ 1` is used to get `Δ ≥ 0` and `kΔ ≤ T N − s N`.
  - None of these is a loophole for the general statement.
- **Special cases.** None: general `Band`, general `E` with `|E| < 2`, general `s, t, T, K`. The witness is used only as a satisfiability check.
- **Hidden hypotheses.** None: no structure carries extra fields, and the deterministic definitions are unfolded and matched.
- **Circularity.** None: the file imports only merged modules (GridPath, APrimeNearRem, EarlyQVRateEv, Lemma57, Step2, FlowFamiliesCore) and does not import any T1504/T1512 consumer.

## 5. Dependencies

All declarations used are on `main` at the merge base `ab0763d`: `nearEpsilon_le_inv`, `flowScale_antitoneOn`, `Step2.etaT_ratio/etaT_eq/etaT_pos'/thr/tendsto_W/eventually_le_W_sq/cond272_of_strict/natCast_rpow_pow`, `sDet`, `sDet_nonneg`, `diagNearRate`, `diagFarRate`, `cNear2/cFar2(_nonneg)`, `ellHat_ofReal`, `one_le_ellHat_of_nonneg`, `Step3.ellHat_pos_of_lt_one`, `mE_im_pos/le_one`, `eventually_exp_mul_log_rpow_le`, `eventually_le_rpow`, and `Grid.step/time`. It does not redefine `tailT_mono_time`; it neither needs nor declares it.

## 6. Build, axioms, hygiene

- **Diff.** `git diff --stat main...t/T1508` shows `RBM1D/Gauss/GridQVSum.lean | 836 +` only. No frozen signature is touched.
- **Grep.** `sorry|admit|axiom|native_decide|implemented_by|unsafe` in the file: 0 hits.
- **Module build.** In the fresh audit worktree, after deleting the cached GridQVSum artifacts, `lake build RBM1D.Gauss.GridQVSum` gives `✔ Built RBM1D.Gauss.GridQVSum (8.2s)` and `Build completed successfully (3852 jobs)`. No warnings from this file.
- **Root build.** `lake build RBM1D` in the audit worktree: `Build completed successfully (9655 jobs)`.
- **Merge simulation on current main (`6415b0f`).** This `main` already has the newer GridDriftSum, GridQVConv and GridStepDecomp. I built it in a temporary detached worktree (removed afterwards) with the ticket file added: `lake build RBM1D RBM1D.Gauss.GridQVSum` completed successfully (9660 jobs). A scratch file with `import RBM1D` plus `import RBM1D.Gauss.GridQVSum` compiles, so there is no name clash for the root import.
- **Axioms.** `#print axioms` for `qv_time_sum_le`, `qv_time_sum_le'`, `qv_time_sum_le_hyps_witness` and `QVSum.Qd_mul_le` each gives `[propext, Classical.choice, Quot.sound]`.

## 7. Acceptance checklist

- Summand exactly `Qd(u_j)·((1−u_j)/(1−u_k))^4`; endpoint `u_k`; uniform in `k ≤ K` (and in `u_*` and `K`); the corollary covers `u_{j+1}`. **Yes.**
- Exponent exactly 4. **Yes**, verified by hand in §3(a).
- The δ-range `0 < δ ≤ c/24` is used for the given δ, not a fixed δ₁. **Yes**: `24δ ≤ c` gives `(N^δ)^{24} ≤ N^c` in `Qd_mul_le` l.388–390, and the J bound uses the same δ via `thr`.
- `hΔ`'s exponent explicit. **Not applicable**: there is no `hΔ`, and the theorem is strictly stronger than the version with `hΔ` (§3(c–d)).
- Joint satisfiability. **Yes**: the compiled nondegenerate witness, plus the hypothesis set being step2's own.

## 8. Notes for the dispatcher and the assembly (not defects)

1. The constant is `2·cNear2/Im m` for the near part instead of the route's `(4/3)·cNear2/Im m`. Everything is absorbed into `1200/Im m · N^κ`.
2. As the prover notes in (d)6, the R4 assembly must show that the T1512 rate `Q_j` is ≤ `Qd(u_j)` on the stopped event. That needs `jG ≤ J(u_j)` and monotonicity of the rates in `J`. This is outside T1508.
3. No `docs/paper-deltas.md` entry is needed for this ticket. The grid form of (5.44) and the `N^δ` threshold are already covered by the ticket design and pilot §6(b).
