Prover model: claude-opus-5-5[1m]

# T1508 (amend-1) — prove report: (5.44) on the grid, label-free time sum `Λ_k`

Ticket: `docs/tickets/T1508-amend-1.md` (supersedes the (T1)/(T2) targets of `T1508.md`).
Worktree: `/Users/junyin/Lean_proof/RBM1D-wt/T1508`, branch `t/T1508`.
Sole writable file: `RBM1D/Gauss/GridQVSum.lean`.
No audit report exists for this ticket yet (first run of amend-1); the prior uncommitted draft
targeted the old (T1)/(T2) shape and is replaced (its old `tailT_mono_time` duplicate is removed:
the merged T1510 declaration `RBM.Gauss.Grid.tailT_mono_time` would clash at the root import, and
the amend-1 target does not need it at all, because `Qd` has the `tailT²` factor stripped).

## (a) Math preflight (written 2026-09-26 01:03 UTC, before any Lean)

### Notation, checked against the Lean definitions (step 0)

- `η_w = etaT E w = (1 − w)·m`, `m = Im m(E) ∈ (0,1]` (`mE_im_pos`, `mE_im_le_one`).
- `ℓ_w = B.ell N w = ellHat (B.L N) w = min((1−w)^{-1/2}, L)` (`Band.ell`, `ellHat`).
- `A_w = B.scale E N w = W ℓ_w η_w` (`Band.scale`).
- `R_w = η_s/η_w = (1−s)/(1−w)` (`Step2.etaT_ratio`), `r_w = ℓ_w/ℓ_s`.
- `thr w = N^δ R_w⁴` (`Step2.thr`, Step2.lean:626); `J w = N^{2ε}·thr w`.
- `diagNearRate B N ℓ_w ℓ_s η_w = 2 η_w⁻¹ cNear2(W,ℓ_w) r_w⁵` (APrimeQVEndpoint.lean:807).
- `diagFarRate B N ℓ_w η_w D J S = 2η_w⁻¹(cFar2(W,ℓ_w)·((2J)²·(A_w·2√S)) + 72(2J)³A_w⁻¹)
  + 4 W L W^{-D} (2J)³` (APrimeQVEndpoint.lean:810).
- `sDet B E N w ℓ_s = r_w³ A_w⁻³` (EarlyQVRateEv.lean:580), so `A_w·2√S = 2√(r_w³/A_w)`.
- `nearEpsilon W L ℓ η D J = W L (2 η⁻² J² T_F²) A⁴ e^{4(log W)^{3/4}}`, `T_F = tailT` at the
  distance `ℓ** − 4ℓ*` (APrimeNearRem.lean:271).
- `Qd w := diagNearRate(ℓ_w,ℓ_s,η_w) + 2·nearEpsilon(W,L,ℓ_w,η_w,D,J w)
  + diagFarRate(ℓ_w,η_w,D,J w, sDet(w,ℓ_s))`: verbatim the RHS rate of T1497
  (`Step2QVEvent.lean:194`, `diagShape'` with the near indicator dropped and `tailT²` factored
  out) with `jG` replaced by `J w`. Checked: `diagShape' ≤ Qd·tailT²` since the indicator is
  `≤ 1` and all rates are `≥ 0`.
- step2's `hreg` (Step2.lean:1053 etc.): `∀ᶠ N, N^c (η_s/η_t)^{30} ≤ W ℓ_t η_t`. It implies
  `Cond272` (`Step2.cond272_of_strict`).
- `phi_arith` (Step2.lean:933) documents the range `δ ≤ c/24`, `D ≥ 60`; `jS_highProb` uses
  exactly `hreg`, `0 < δ`, `24δ ≤ c`, `D ≥ 60`.

### Target (T2′) `RBM.Gauss.Grid.qv_time_sum_le`

Statement to be compiled: for `|E| < 2`, `hs0, hst, ht1`, `Cond272`, step2's `hreg` with `c > 0`,
`0 < δ ≤ c/24`, `0 ≤ ε`, `2ε ≤ δ`, `60 ≤ D`: for every `κ > 0`, `∀ᶠ N`, for every endpoint
sequence `T` and step-count sequence `Kq` with `s N ≤ T N ≤ t N`, `1 ≤ Kq N`, and every
`k ≤ Kq N`, with `u_j = Grid.time s T Kq N j = s N + jΔ`, `Δ = Grid.step s T Kq N`,

  `Σ_{j<k} Δ · Qd(u_j) · ((1 − u_j)/(1 − u_k))⁴ ≤ C_E · N^κ · (R_{u_k}⁴ + 1)`,
  `C_E = 1200 / Im m(E)`.

(The endpoint/step sequences are quantified *inside* `∀ᶠ N`, which is exactly "uniformly in
`u_*`, `K`, `k ≤ K`"; any real `u_* ∈ [s N, t N]` and `K ≥ 1` is the value of such sequences at
`N`, and `Grid.time`/`Grid.step` are the GridPath definitions used by T1504/T1507/T1512.)

**Proof (pointwise domination of the whole product, then `Σ_{j<k} Δ = u_k − s ≤ 1 − s`).**
Fix `N` in the eventual set and `s ≤ w ≤ v ≤ t` (`w = u_j`, `v = u_k`). Then
`(1−w)/(1−v) = η_w/η_v =: P_w^{1/4}`.

1. *Cap-robust ratio.* `ℓ_w √(1−w) = min(1, L√(1−w))` is non-increasing, hence
   `ℓ_w²(1−w) ≤ ℓ_s²(1−s)`, i.e. `r_w² η_w ≤ η_s` (**K1**). With `r_w ≥ 0`:
   `(r_w η_w)² = (r_w² η_w)·η_w ≤ η_s²`, so `r_w η_w ≤ η_s`, hence
   `r_w⁵ η_w³ = (r_w²η_w)²·(r_w η_w) ≤ η_s³` (**K2**, only natural powers).
   Also `r_w² ≤ R_w`, and `R_w ≥ 1`, so `r_w ≤ R_w`.
2. *Near term (the sharp one).*
   `diagNearRate·P_w = 2 cNear2 r_w⁵ η_w⁻¹ (η_w/η_v)⁴ = 2 cNear2 r_w⁵ η_w³/η_v⁴ ≤ 2 cNear2 η_s³/η_v⁴`
   by K2. Summing, `Σ_{j<k} Δ = u_k − s ≤ 1 − s = η_s/m`, so the near contribution is
   `≤ (2 cNear2/m)·η_s⁴/η_v⁴ = (2 cNear2/m)·R_v⁴`. **Exponent exactly 4, no loss.**
   Remark on the route: the ticket warns against "length × sup". The loss it describes comes from
   taking the sup of each factor separately (`r_v⁵`, `η_v⁻¹`, `R_v⁴`), giving `≈ R^{6.5}`. Here the
   sup is taken of the *whole product* `r_w⁵ η_w³`, with `r_w` kept at the same time `w` as `η_w`
   (K2 is the pointwise form of `r_w ≤ (η_s/η_w)^{1/2}`); it is maximal at `w = s` and gives
   `η_s³`. Integrating instead (`∫_s^v η_w^{1/2}dw ≤ (2/3)η_s^{3/2}/m`) improves only the constant
   `1/m → (2/3)/m`, not the exponent. Consequently **no Riemann-sum error arises, and the bound
   holds for every `K ≥ 1` with no mesh condition**: the ticket's optional hypothesis
   `hΔ : Δ ≤ N^{-C'}` is not needed and is not added (dropping a hypothesis only strengthens the
   statement; the assembly may still choose `K := ⌈N^{C'}⌉`).
   `cNear2(W,ℓ) ≤ N^κ` eventually, uniformly in `ℓ ≥ 1` (stretched-exponential in `log W`,
   `W ≤ N`; draft lemma `eventually_cNear2_le_rpow`, Band-generic).
3. *J-powers (δ ≤ c/24).* Put `x = N^δ ≥ 1`, `g = N^c`. Then `x^{24} ≤ g` (uses `24δ ≤ c`,
   `N ≥ 1`). `J_w = N^{2ε} N^δ R_w⁴ ≤ x² R_w⁴` (uses `2ε ≤ δ`). `A_w ≥ A_t` (flowScale
   antitone) `≥ g R_t^{30} ≥ g R_w^{30}` (hreg; `R_w ≤ R_t`). Hence
   `J³ ≤ x⁶R^{12} ≤ g R^{30} ≤ A_w`, and `J⁴ r_w³ ≤ x⁸ R^{16}·R³ ≤ g R^{30} ≤ A_w`, and `J ≤ A_w`.
4. *Far terms.* `η_w⁻¹P_w = η_w³/η_v⁴ ≤ η_s³/η_v⁴`.
   `cFar2·(2J)²·(A·2√S) = 8 cFar2·(J² A √S)`, and `(J²A√S)² = J⁴ A² r³A⁻³ = J⁴r³/A ≤ 1`, so
   `≤ 8 cFar2`; `72(2J)³A⁻¹ = 576·J³/A ≤ 576`. So the first part of `diagFarRate·P_w` is
   `≤ (16 cFar2 + 1152)·η_s³/η_v⁴`, contributing `≤ (16 cFar2 + 1152) R_v⁴/m` after the sum;
   `cFar2 ≤ 2 cNear2 ≤ 2N^κ` (`W ≥ e`).
   The last part `4WLW^{-D}(2J)³·P_w ≤ 32·WL·W^{-D}·J³·R_v⁴` (no `η⁻¹`; `P_w ≤ R_v⁴` as
   `η_w ≤ η_s`); `WL ≤ N ≤ W²`, `J³ ≤ A_w ≤ WL ≤ N`, so `32 WL W^{-D} J³ ≤ 32 W^{4−D} ≤ 1` for
   `D ≥ 60`, `W ≥ 2`. Contribution `≤ (1 − s) R_v⁴ ≤ R_v⁴`.
5. *nearEpsilon.* Existing `EEDef.nearEpsilon_le_inv` (APrimeNearRem.lean:369) with `k = 1`:
   hypotheses `e ≤ W`, `N⁻¹ ≤ η_w` (from `η_w ≥ η_t ≥ A_t/(WL) ≥ 1/N`, `A_t ≥ 1`), `1 ≤ A_w ≤ N`
   (`η_w ≤ 1`, `ℓ_w ≤ L`), `WL ≤ N ≤ W²`, `J ≤ N^1`, `2·1 + 14 ≤ D`, `4 ≤ log W`,
   `(4D)² ≤ log W` (eventual in `N` for the fixed `D`) give `nearEpsilon ≤ W⁻¹ ≤ 1`; with
   `P_w ≤ R_v⁴` the contribution is `≤ 2 R_v⁴`.
6. *Total.* `Λ_k ≤ ((2 + 32)N^κ + 1152)/m · R_v⁴ + 3 R_v⁴ ≤ (1189/m) N^κ R_v⁴
   ≤ C_E N^κ (R_v⁴ + 1)` (`N^κ ≥ 1`, `1/m ≥ 1`). `C_E = 1200/m` depends only on `E`.

Boundary cases: `k = 0` (empty sum, RHS `≥ 0`); `w = s` (K1 with equality allowed); `v = w`;
`T N = s N` (then `Δ = 0`, all `u_j = s`, sum `= 0`); the cap `ℓ = L` active or not (K1 is
cap-robust). Quantifier order: all fixed parameters (`E, s, t, c, δ, ε, D, κ`) before `∀ᶠ N`;
`T, Kq, k` after (uniformity). Parameter use: `δ ≤ c/24` is used in step 3 (`x^{24} ≤ g`) for the
given `δ`, not a fixed `δ₁`; `2ε ≤ δ` in step 3; `D ≥ 60` in steps 4–5; `hreg` in steps 3, 5;
`|E| < 2`, `hs0`, `ht1` throughout.
Hypotheses listed by the ticket but not needed by the proof (kept for interface fidelity; they
cost nothing): `Cond272` (implied by `hreg` via `Step2.cond272_of_strict`), `0 ≤ ε`, `1 ≤ Kq N`.

Joint satisfiability: the hypothesis set is exactly step2's own (`Step2.jS_highProb`: `hreg`,
`0 < δ`, `24δ ≤ c`, `D ≥ 60`) plus `Cond272` (implied) and `0 ≤ ε ≤ δ/2` (take `ε = 0`). A
compiled nondegenerate witness is planned (any band, `E = 0`, `s = 0`,
`t N = 1 − (N+1)^{-1/200}`, `c = 1/4`, `δ = 1/96`, `ε = 0`, `D = 60`; non-collapsed window with
`R_t → ∞`).

**Verdict (T2′): PASS.**

### Target corollary `RBM.Gauss.Grid.qv_time_sum_le'`

Same conclusion with the propagator factor `((1 − u_{j+1})/(1 − u_k))⁴` produced by
`qv_conv_le`. For `j < k`: `u_j ≤ u_{j+1} ≤ u_k < 1`, so `0 ≤ 1 − u_{j+1} ≤ 1 − u_j`, and
`Δ ≥ 0`, `Qd(u_j) ≥ 0` (all three rates are sums of products of non-negative factors,
`J ≥ 0`). Termwise domination then (T2′). **Verdict: PASS.**

## (b) Declarations, build, axioms

File: `RBM1D/Gauss/GridQVSum.lean` (worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1508`), commit
`1ed0452` on branch `t/T1508`. The old draft (targets (T1)/(T2) of the original ticket, with a
`sorry`, and a duplicate `tailT_mono_time`) is fully replaced; `tailT_mono_time` is neither
redefined nor needed.

Public declarations (namespace `RBM.Gauss.Grid`):
- `qvJ E s δ ε N w := N^{2ε} · Step2.thr E s δ N w`.
- `Qd B E s δ ε D N w := diagNearRate B N ℓ_w ℓ_s η_w + 2·EEDef.nearEpsilon W L ℓ_w η_w D (qvJ …)
  + diagFarRate B N ℓ_w η_w D (qvJ …) (EarlyQVRateEv.sDet B E N w ℓ_s)` (verbatim T1497 rate).
- `qvSumConst E := 1200 / (mE E).im`.
- **`qv_time_sum_le`** (T2′):
  ```
  (B : Band Ω) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
  (_hcond : Cond272 B E s t) (_hc0 : 0 < c)
  (hreg : ∀ᶠ N in atTop, N^c * (etaT E (s N) / etaT E (t N))^30 ≤ B.scale E N (t N))
  (hδ0 : 0 < δ) (hδc : δ ≤ c/24) (_hε0 : 0 ≤ ε) (hεδ : 2*ε ≤ δ) (hD : 60 ≤ D) :
  ∀ κ, 0 < κ → ∀ᶠ N in atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ), s N ≤ T N → T N ≤ t N → 1 ≤ Kq N →
    ∀ k ≤ Kq N,
      ∑ j ∈ range k, step s T Kq N * Qd B E s δ ε D N (time s T Kq N j) *
          ((1 - time s T Kq N j) / (1 - time s T Kq N k))^4
        ≤ qvSumConst E * N^κ * ((etaT E (s N) / etaT E (time s T Kq N k))^4 + 1)
  ```
  (`step`/`time` are the GridPath definitions: `Δ = (T N − s N)/Kq N`, `u_j = s N + jΔ`.)
- **`qv_time_sum_le'`**: same hypotheses and right side; summand
  `step * Qd(u_j) * ((1 - time s T Kq N (j+1)) / (1 - time s T Kq N k))^4`.
- `qv_time_sum_le_hyps_witness (B : Band Ω)`: for every band, `E = 0`, `s = 0`,
  `t N = 1 − (N+1)^{-1/200}`, `c = 1/4`, `δ = 1/96 = c/24`, `ε = 1/192` (`2ε = δ`), `D = 60`
  satisfy all hypotheses of (T2′) simultaneously (`Cond272` derived via
  `Step2.cond272_of_strict`), with `s N < t N` for `N ≥ 1` and
  `η_s/η_t = (N+1)^{1/200} → ∞` (non-collapsed window, non-trivial ratio).
Helpers (namespace `RBM.Gauss.Grid.QVSum`): `ellHat_mul_sqrt_one_sub`,
`ellHat_mul_sqrt_one_sub_le`, `ellHat_sq_mul_one_sub_le` (K1), `cNear2_le_of_one_le`,
`cFar2_le_two_cNear2`, `eventually_cNear2_le_rpow`, `pow5_mul_pow3_le` (K2), `near_mul_le`,
`far_mul_le`, `J_pow_le`, `Qd_mul_le` (pointwise domination at fixed `N`), `final_arith`,
`Qd_nonneg`.

Build: `cd /Users/junyin/Lean_proof/RBM1D-wt/T1508 && lake build RBM1D.Gauss.GridQVSum` →
`✔ Built RBM1D.Gauss.GridQVSum`, `Build completed successfully (3852 jobs)`. No warnings from
this file. `grep sorry|admit|axiom` → 0.

`#print axioms` (all of `qv_time_sum_le`, `qv_time_sum_le'`, `qv_time_sum_le_hyps_witness`,
`Qd_mul_le`, `Qd_nonneg`, `eventually_cNear2_le_rpow`, `final_arith`, `J_pow_le`, `far_mul_le`,
`near_mul_le`): `[propext, Classical.choice, Quot.sound]`.

Acceptance checklist:
- summand exactly `Qd(u_j)·((1−u_j)/(1−u_k))⁴`, endpoint `u_k`, uniform in `k ≤ K` (and in the
  endpoint and in `K`, quantified inside `∀ᶠ N`): yes.
- corollary `qv_time_sum_le'` covers the `u_{j+1}` propagator factor: yes.
- exponent exactly 4: yes (`(η_s/η_{u_k})^4`).
- δ-range `0 < δ ≤ c/24` used (in `Qd_mul_le` via `24δ ≤ c` ⇒ `(N^δ)^{24} ≤ N^c`), not a fixed
  `δ₁`: yes.
- `hΔ`: not needed and not added — the bound holds for every `K ≥ 1` (no Riemann-sum error;
  see preflight step 2). This is a strengthening of the ticket's shape; the assembly may still
  choose `K := ⌈N^{C'}⌉` for its own reasons.
- joint satisfiability: compiled witness `qv_time_sum_le_hyps_witness`, and the hypothesis set is
  step2's own (`Step2.jS_highProb`: `hreg`, `0 < δ`, `24δ ≤ c`, `D ≥ 60`).

## (c) Key lemmas used

`RBM.EEDef.nearEpsilon_le_inv` (APrimeNearRem.lean:369, with `k = 1`); `RBM.Step2.etaT_ratio`,
`etaT_eq`, `etaT_pos'`, `natCast_rpow_pow`, `tendsto_W`, `eventually_le_W_sq`,
`cond272_of_strict`; `RBM.flowScale_antitoneOn`; `RBM.Step3.ellHat_pos_of_lt_one`;
`RBM.one_le_ellHat_of_nonneg`; `RBM.ellHat_ofReal`; `RBM.EarlyQVRateEv.sDet_nonneg`;
`RBM.Lemma57.cNear2_nonneg`, `cFar2_nonneg`; `RBM.mE_im_pos`, `mE_im_le_one`;
`RBM.eventually_exp_mul_log_rpow_le`, `RBM.eventually_le_rpow`; Mathlib
`isLittleO_log_rpow_rpow_atTop`, `Real.le_log_iff_exp_le`.

## (d) Open issues / notes for the auditor and the assembly

1. Route deviation from the ticket's notes (not from its target): no integral/Riemann sum. The
   near term is bounded by the pointwise inequality `r_w⁵η_w³ ≤ η_s³` (K2), which keeps `r_w` at
   the same time as `η_w`; the total is `(2 cNear2/Im m)·R_{u_k}⁴`, versus `(4/3)·cNear2/Im m`
   from the integral — same exponent 4, constant larger by 3/2. Hence no `hΔ`.
2. Hypotheses listed by the ticket but unused in the proof (kept, underscore-named, for interface
   fidelity): `Cond272` (implied by `hreg`), `0 < c` (implied by `0 < δ ≤ c/24`), `0 ≤ ε`.
   `1 ≤ Kq N` is used (positivity of `Kq N` for `Δ ≥ 0`, `kΔ ≤ T N − s N`).
3. `qvSumConst E = 1200/Im m(E)`: depends only on `E`. `κ` absorbs only `cNear2`, `cFar2`
   (`W^{o(1)}`), as the ticket requires.
4. Special-case status: none. General `Band`, general `E` with `|E| < 2`, general `s, t`, general
   endpoint and `K`; the witness (`E = 0`, `s = 0`) is only the satisfiability check.
5. Paper deltas: no new Lean/paper statement difference beyond those already carried by the
   inputs (the `N^δ` threshold of (5.43), pilot §6(b); Lemma 5.7 at proof-level exponents via
   T1497). `docs/paper-deltas.md` not edited (outside this ticket's writable files).
6. Downstream (R4 assembly): `Σ_j c k b j = xiK² T_{u_k}(b)² Λ'_k` with `Λ'_k` the sum of
   `qv_time_sum_le'`, bounded by `qvSumConst E · N^κ · (R_{u_k}⁴ + 1)`. The assembly must provide
   `Qd(u_j)` as the rate `Q_j` of T1512 (i.e. evaluate T1497 with `jG ≤ J(u_j) = N^{2ε} thr(u_j)`
   on the stopped event; `Qd` is monotone in `J`, which the assembly must check or prove).

Verdict: (T2′) PASS, built; corollary PASS, built.
