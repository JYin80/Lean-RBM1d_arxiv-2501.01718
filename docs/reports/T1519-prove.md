Prover model: claude-opus-5-5

# T1519 — prove report (R4c-1: grid stopping time and the good event)

Repair stage (2026-09-26, after 10:53 UTC): spec `docs/tickets/T1519-amend-1.md` supersedes (T3), (T4), (T6) of
`docs/tickets/T1519.md`; (T1), (T2), (T5) are kept unchanged (PASS below). No audit report exists (the ticket
never reached an audit stage). The original prove-stage sections are kept; the superseded (T3)/(T4)/(T6)
verdicts are retained under "Superseded" for the record.

Ticket: `docs/tickets/T1519.md`. Worktree: `../RBM1D-wt/T1519`, branch `t/T1519`.
Sole writable file: `RBM1D/Gauss/GridGoodEvent.lean`.
No returning audit report exists (fresh prove stage).

## (a) Math preflight (written before any Lean)

Notation: `u_j := time s u K N j`, `Δ := step s u K N`, `T_v(a) := tT (band d) E N D v (zdist (a 0 - a 1))
= tailT W (ellHat L v) ((1-v)·Im m) D (zdist …)`, `R_v := η_s/η_v`, `thr(v) := Step2.thr E s δ N v
= N^δ R_v^4`, `G(v) := goodSet d E N v ℓ_s τ₁ ε ζCtr τ3 τ57 D` with `ℓ_s := (band d).ell N (s N)`
(the T1513 convention, exactly what `highProb_grid_goodSet` produces).

### Step 0 interface checks

| Interface | Result |
|---|---|
| `isStoppingTime_min_firstHit_grid`, `lt_min_firstHit_grid_measurableSet` (GridStopFilt) | match; `F` may depend on `j`; horizon `K N`. `lt_min_firstHit_imp` (GridStop) gives the pointwise consequences. |
| `jSMat` measurable (`measurable_jSMat`); `goodSet` measurable (`measurableSet_goodSet`, needs `|E| < 2`) | match |
| **hreg form** | T1513's `highProb_grid_goodSet` uses the plain `N^c ≤ scale(t)`; T1508's `qv_time_sum_le'` and step2 (`step2_gauss_of_grid`, T1517) use the gained (Cond272′) `N^c R_t^30 ≤ scale(t)`. Resolution: take the gained form (step2's own hypothesis) and derive the plain one by `Step2.eventually_R4_le_scale`, exactly as `step2_gauss_of_pointwise` does. The gained form is also what `thr ≤ N^{1/2}` needs (below). No mismatch after this. |
| **ℓs scaling** | `qvSet` passes `ℓ_s = (band d).ell N (s N)` into `sDet … u ℓ_s`; `quadVar_step_le` (T1514) takes the same free `ℓs`; `Qd` (T1508) hard-codes `B.ell N (s N)`. With `B = band d` the rate `Q′_j` of T1514 at `J = qvJ E s δ ε N u_j = N^{2ε} thr(u_j)` is literally `2 N^{τ₁} Qd(band d) E s δ ε D N u_j + 2 Csh(u_{j+1})² Δ² W^{2D}`. Match. |
| `hqv` forms | `qvSet`'s bound is on `qvVal = quadVar((band d).toDims)(lkFun u_j a)` at Hermitian `M`; `quadVar_step_le`'s `hqv` is the same expression with `J′ := jGMat(u_j, M)`. `v_Ab_le_H`'s `hqv` is on `quadVar d N (Φgrid u_{j+1} a)`; `Φgrid = loopObs − Kv` has the same `coordD1` as `loopObs`, and `quadVar_lkFun_eq_quadVar_loopObs` identifies it with `quadVar(lkFun u_{j+1} a)` at Hermitian `M`. The `tailT` arguments agree after `Band.ell = ellHat`, `etaT E v = (1-v)·Im m`, `u_j + Δ = u_{j+1}`. Glue only. |
| `v_Ab_le_H` kernel vs `ukerMat` | `v_Ab_le_H` uses `U b a = (∏ᵢ edgeKer 1 u v (b i)(a i)).re`; `ukerMat L u v b a = (Uker … (Pi.single a 1) b).re` is the same entry (`Uker_apply`; T1516's `Uker_one_single` is private, re-proved locally). |
| `stepZ_ukerMat_eq_Uker` (T1516) | holds for every ω (no null set), needs `0 ≤ u_{j+1} ≤ u_k < 1`. |
| `stepDecomp_Z_subG` (T1505) | any `c ≥ Δ·v N (Ab …)` on an `F_j`-event; so the positive floor `+ Δ N^{-C_c}` is free. |
| `stopped_duhamel_cheb_tail` (T1504 T2) | **mismatch**: its event is a sup-norm event at the random target `u_{τ(ω)}` with threshold `2^n x`; it is not a fixed-target, per-label bound at `u_k`. With `τ′ = min(τ,k)` its target is `u_{min(τ,k)} ≠ u_k`. See T4. |
| `HighProb` | `∀ D > 0, ∀ᶠ N, P(Ξ N)ᶜ ≤ N^{-D}` (every `D`). |

### Target verdicts

**(T1) `gridTau`, `isStoppingTime_gridTau`, `lt_gridTau_measurableSet`, `lt_gridTau_imp` — PASS.**
`gridTau ω = min (firstHit (j ↦ jSMat(u_j,H_j) − thr(u_j)) 0 (K N)) (firstHit (j ↦ 1_{G(u_j)ᶜ}(H_j)) (1/2) (K N))`.
Both `F j := jSMat(u_j,·) − thr(u_j)` and `F′ j := 1_{G(u_j)ᶜ}` are measurable (the second needs `|E| < 2`).
`j < gridTau ω` gives `F j (H_j) < 0` and `F′ j (H_j) < 1/2`, i.e. `jSMat < thr` and `H_j ∈ G(u_j)`.
Boundary: `gridTau ≤ K N`; no hypothesis beyond `|E| < 2`.

**(T2) `hsubG_gridTau` (+ `thr_le_sqrtN`) — PASS (eventually in `N`).**
- `thr_le_sqrtN`: gained hreg and `scale(t) ≤ W L ≤ N` (`B.dim`) give `R_t^30 ≤ N^{1−c}`, so for
  `u ∈ [s,t]`, `thr(u) = N^δ R_u^4 ≤ N^δ R_t^4 ≤ N^{δ + 4(1−c)/30} ≤ N^{δ + 2/15 − 2c/15} ≤ N^{1/2}`
  whenever `δ ≤ c/24` (then `δ − 2c/15 < 0`); no `c ≤ 1` needed. Eventually in `N`, uniformly in `u`.
- On `{j < τ}` (an `F_j` set by T1): `jSMat(u_j,H_j) < thr(u_j) ≤ N^{1/2}` and `H_j ∈ G(u_j)`, so
  `qvSet` gives the `hqv` of `quadVar_step_le` with `J′ = jGMat(u_j,H_j)`; `jgSet` gives
  `1 ≤ J′ ≤ N^{2ε} jSMat < N^{2ε} thr(u_j) = qvJ(u_j) =: J`. `quadVar_step_le` then bounds
  `quadVar(lkFun u_{j+1} a)(H_j) ≤ Q′_j T_{u_{j+1}}(a)²`; with the `Φgrid` bridge this is `v_Ab_le_H`'s
  `hqv` at `u := u_{j+1}`, `vt := u_k`, `W := W N`, `m := Im m_E ∈ (0,1]`, `hAuv` from
  `flowScale_antitoneOn`, `exp 1 ≤ W N` eventually. So `Δ·v N (Ab … ukerMat(u_{j+1},u_k) a) ≤
  Δ(√Q′_j ((1−u_{j+1})/(1−u_k))² xiK T_{u_k}(a))² ≤ c k a j` on `{j<τ}`.
- Real part: `(1_{j<τ} Uker(u_{j+1},u_k) Zvec_{j+1})_a` is, for every ω, the real
  `1_{j<τ} stepZ j (Φgrid u_{j+1}) ukerMat(u_{j+1},u_k) a` (`stepZ_ukerMat_eq_Uker`), so
  `stepDecomp_Z_subG` with `E := {j<τ}` applies. Imaginary part: identically `0`; it is
  sub-Gaussian with any variance (via `stepDecomp_Z_subG` at the zero kernel, whose `stepZ ≡ 0`).
- `c k a j := Δ·(√Q′_j ((1−u_{j+1})/(1−u_k))² xiK(L,W,Im m) T_{u_k}(a))² + Δ·N^{-C_c}` with
  `Q′_j = 2 N^{τ₁} Qd(band d) E s δ ε D N u_j + 2 Csh(u_{j+1})² Δ² W^{2D}`, `C_c ∈ ℝ` free.
  Positive floor present (`> 0` iff `Δ > 0`, i.e. `s N < u N`, `K N ≠ 0`).
- Quantifiers: all parameters fixed, then `∀ᶠ N`, then `∀ k ≤ K N, ∀ a, ∀ j < k`. Uniform in `k`, `a`.
- Satisfiability: the only hypotheses are step2's (`|E| ≤ 2−κ`, `0 ≤ s ≤ t < 1`, gained hreg with
  `c > 0`) plus parameter constraints `0 < δ ≤ c/24`, `D ≥ 64`, `τ₁, ε, ζCtr, τ3, τ57 > 0`,
  `s ≤ u ≤ t`, `K N ≠ 0`; jointly satisfiable (e.g. T1508's compiled
  `qv_time_sum_le_hyps_witness`: `E = 0`, `s = 0`, `t N = 1 − (N+1)^{-1/200}`, `c = 1/4`, `δ = c/24`,
  then `u := t`, `K N := N + 1`). No random hypothesis is added. `BoundsCore` is not needed by T2.

**(T5) `highProb_init_grid` — PASS.**
`hB.decay D` at `τ = δ/16` gives, w.h.p. on the flow, `lkErr(s, pmLoop b) ≤ N^{δ/16} scale(s)^{-2}
decayProf(s,D,b) ≤ N^{δ/16} T_s(b)` (`decayProf_le_tT`, needs `1 ≤ scale(s)`, eventually true since
`scale(s) ≥ scale(t) ≥ N^c ≥ 1`). The matrix set `{M | ∀ b, ‖Lval s M b − Kv s b‖ ≤ N^{δ/16} T_s(b)}`
is measurable (`measurable_gloop_matrix`), and `H_0 = √s X_0` has the law of `Hflow(s)` (`map_H_eq`
at `k = 0`, `time 0 = s`), so the grid probability equals the flow probability. On the event,
`jSMat(u_0,H_0) = 1 + sup_b ‖A_0 b‖/T_s(b) ≤ 1 + N^{δ/16} < N^δ = thr(u_0)` for `N` large (`δ > 0`).
Hypotheses: `hB`, `|E| < 2`, `0 ≤ s ≤ t < 1`, gained hreg, `δ > 0`, `D > 0`, `s ≤ u`, `K N ≠ 0`.

### Superseded targets of the original ticket (kept for the record)

**(T3) `highProb_azuma_grid` — FAIL (the statement as written is false).**
The event is `{∀ k ≤ K, ∀ a, ‖(Σ_{j<min(k,τ)} Uker 1 u_{j+1} u_k Z_{j+1}) a‖ < x k a}` with
`x k a := N^{δ/16}·√(4 Σ_{j<k} c k a j)`. At `k = 0` (always `≤ K`) the sum is empty, so the left
side is `‖0‖ = 0`, and `x 0 a = N^{δ/16}·√(4·0) = 0`; `0 < 0` is false. Hence the event is **empty for
every `N`** and `HighProb` fails (a `HighProb` family is eventually nonempty, `HighProb.nonempty`).
This contradicts the ticket's own remark in (T2) that "`x 0 a > 0` handles the `k = 0` term".
Independently, when `u N = s N` (allowed: `u(N) ∈ [s_N,t_N]`) one has `Δ = 0`, so `c ≡ 0` and
`x k a = 0` for all `k`, and the event is again empty.
Negative statement compiled: `not_highProb_azuma_grid_literal` (see (b)).
Everything else in the (T3) route checks out once the defect is repaired: for `k ≥ 1` and `Δ > 0`,
`Σ_{j<k} c k a j ≥ kΔN^{-C_c} > 0`, the (T1″) bound per term is `4 exp(−N^{δ/8})`, the union has
`≤ (K+1)·L² ≤ N^{C+2}` terms, so the complement is super-polynomially small; the deterministic
`x k a ≤ Mm (R_k²+1) T_{u_k}(a)` follows from `qv_time_sum_le'` (`Σ_j Δ Qd(u_j) r⁴ ≤ qvSumConst·N^{κ′}(R⁴+1)`),
`Σ_j Δ³ Csh² W^{2D} r⁴ ≤ KΔ³ poly` and `KΔN^{-C_c} ≤ W^{-2D} ≤ T²` for `C_c, C_K` large, giving
`Mm = 2N^{δ/16} xiK √(2 qvSumConst N^{τ₁+κ′} + 2) ≤ N^{δ/8}` eventually when `τ₁ + κ′ < δ/8` (`xiK ≤ N^{o(1)}`).
**Suggested amendment (dispatcher):** state the event with `≤` (T1518's `hZ` is a `≤` bound, so
nothing downstream changes; `k = 0` and `Δ = 0` become trivial), or keep `<` with
`x k a := N^{δ/16}√(4 Σ_{j<k} c k a j) + N^{-C}` and restrict to `1 ≤ k`.

**(T4) `highProb_cheb_grid` — BLOCKED (the prescribed route cannot give the target).**
Three independent obstacles:
1. `HighProb` quantifies over **every** `D`. A second-moment (Chebyshev) bound with the fixed grid
   `K N = ⌈N^{C_K}⌉` gives a failure probability `≲ poly(N)·W^{2D}·K^{-1}` with a *fixed* polynomial
   rate; it can never be `≤ N^{-D}` for all `D`. The downstream consumer (`GridPointwise`, T1517)
   needs `StochDom`, i.e. every `D` with one `K`, so the ticket's "probability `≥ 1 − N^{-D₀}`"
   version would not be usable either.
2. Even for one fixed `D₀`, the union over `k` destroys the gain: per `(k,a)`,
   `P ≤ Σ_{j<k} e_j / T² ≤ k Δ² C W^{2D}`; summing over `k = 1..K` gives `≈ (KΔ)² C W^{2D}/2 =
   (u−s)² C W^{2D}/2`, which is not small. The ticket's "`≤ K Δ² poly W^{2D}`" is the per-`(k,a)` bound.
3. Interface: `stopped_duhamel_cheb_tail` is a sup-norm event at the random target `u_{τ(ω)}`; it
   does not produce the fixed-target, per-label event at `u_k` (see the Step 0 table).
The statement itself is plausibly true (the `Y`-increments are `O(Δ‖X‖²)` with Gaussian tails), but
proving it needs a super-polynomial concentration for the `Y`-martingale that no merged input
provides (e.g. truncation of `‖X_{j+1}‖` at `N^ε` on a `HighProb` event + Azuma for bounded
differences, or the backward-kernel factorisation + a maximal inequality with super-polynomial
per-term bounds). That is new mathematics outside this ticket's route. Not attempted in Lean.

**(T6) `highProb_goodEvent` — BLOCKED** (it is the intersection of (T3), (T4), (T5) and
`highProb_grid_goodSet`; (T3) is false as written and (T4) is blocked). Not written.

### Preflight for the amended targets (T1519-amend-1), written before any new Lean

Notation as above; in addition `ξ := Step2.xiK (L N) (W N) (Im m_E)`, `R_k := η_s/η_{u_k}`,
`qvC := qvSumConst E = 1200/Im m_E`, `r_{j,k} := (1−u_{j+1})/(1−u_k)`, `Csh_j := qvTimeShiftConst(u_{j+1})
= 16√2·card(Idx N)²·(1+η_{u_{j+1}}^{-1})^6`, `cZ` = (T2)'s constants (floor `Δ N^{-C_c}`).

Step-0 checks done for the amend:
- `stopped_duhamel_cheb_tail` (GridDuhamelTail:448): random target `u_{τ(ω)}`, event `∃a, 2ⁿx ≤ ‖·‖`,
  bound `Lⁿ Σ_{j<K} e_j / x²`, hypotheses per label `b` and `j < K` at the **fixed** target `t = u_K`. Matches the
  amended (T4′) exactly (no union over `k`).
- `stopped_duhamel_azuma_union` (GridDuhamelTail:347): needs `StandardBorelSpace (Ωg d)` — holds
  (`inferInstance` checked), `hx0 : ∀ a, 0 < x 0 a` — holds with the floor.
- Both lemmas need `hZ/hY : ∀ i, StronglyMeasurable[filt d i] (Z i)` for **all** `i`, including `i = 0`.
  `Zvec 0 = stepZ` at step `0−1 = 0` depends on `ω 1`, so it is not `filt 0`-measurable. Glue: feed
  `Z' i := if i = 0 then 0 else Zvec i` (same for `Y`); only `Z' (j+1) = Zvec (j+1)` enters the sums and the
  hypotheses, so the statements are unchanged. No interface mismatch after this.
- `stepDecomp_Y_sq` (T1505) + `stepY_ukerMat_eq_Uker_ae` (T1516) + `norm_Uker_apply_le` (Kernel.lean, row
  bound `C = (1−u_{j+1})/(1−u_K)`) give `hYbound`; `stepDecomp` part 4 gives the mean zero; the needed
  `Integrable stepZ` is re-proved locally (T1516's `stepZ_integrable` is private).
- `∫‖X‖⁴ dP ≤ ∫ frobSq(X²) = Σ_i ∫ colSq X 2 i ≤ 3·card(Idx N) ≤ 3N` (`integral_norm_Xmat_pow_le`,
  `integral_colSq_le`, `traceConst 2 = 3`).
- `η_t^{-1} ≤ N` eventually: T1511 `etaT_inv_le_of_hreg` (GridNetLift). `ξ ≤ N^θ` eventually for every `θ>0`:
  `eventually_xiK_le`. `T_v(a) ≥ W^{-D} ≥ N^{-D}` (`rpow_neg_le_tailT`, `W ≤ N`, `D ≥ 0`).

**(T3′) `highProb_azuma_grid'` — PASS.**
Definition `xZ … N k a := N^{δ/16}·√(4 Σ_{j<k} cZ … N k a j + N^{-C_x})`.
Statement: under (T2)'s hypotheses (`|E|<2`, `0 ≤ s ≤ t < 1`, gained hreg, `0 < δ ≤ c/24`, `0 ≤ D`, `s ≤ u ≤ t`,
`K N ≠ 0`) and `K N + 1 ≤ N^C` eventually (`C ≥ 0`), for any `C_c, C_x ∈ ℝ`:
`HighProb (Pg d) {ω | ∀ k ≤ K N, ∀ a, ‖(Σ_{j<min(k,τ ω)} Uker 1 u_{j+1} u_k Zvec_{j+1} ω) a‖ < xZ … N k a}`.
- `k = 0`: empty sum, `0 < xZ 0 a` since `N^{-C_x} > 0` (`N ≥ 1`). `Δ = 0` (i.e. `u N = s N`): `Zvec_{j+1} = √Δ·(…) = 0`,
  every sum is `0 < xZ`, so the complement is empty. Both boundary cases are true, not vacuous.
- `Δ > 0`, `1 ≤ k ≤ K`: `Σ_{j<k} cZ ≥ kΔN^{-C_c} > 0` and `xZ² = N^{δ/8}(4Σ + N^{-C_x}) ≥ N^{δ/8}·4Σ`, so each
  (T1″) summand is `≤ 4 exp(−N^{δ/8})`; the union has `K·L² ≤ N^{C+2}` summands; `4N^{C+2}e^{−N^{δ/8}} ≤ N^{-D'}`
  eventually for every `D' > 0` (`SumZeroDyn.eventually_exp_small`). So the statement is `HighProb` (all `D'`).
- Hypotheses of (T1″): `hsubG` = (T2) `hsubG_gridTau` (eventually, uniform in `k ≤ K`, `a`, `j<k`), `hτmeas` = (T1).
Deterministic consequence `xZ_le_Mm` — PASS, with `Mm N := N^{δ/16}·√(4ξ²(2 qvC N^{τ₁+δ/64} + 2) + 5)`:
extra hypotheses `Cond272`, `0 ≤ ε`, `2ε ≤ δ`, `60 ≤ D`, `0 ≤ τ₁`, `2D ≤ C_c`, `2D ≤ C_x`, and
`Δ ≤ N^{-(D+10)}` eventually. Proof: `Σ_{j<k} cZ = ξ²T²·Σ_j ΔQ′_j r_j⁴ + kΔN^{-C_c}`;
`Σ_j Δ·2N^{τ₁}Qd(u_j) r_j⁴ ≤ 2N^{τ₁} qvC N^{δ/64}(R_k⁴+1)` (`qv_time_sum_le'` at `κ = δ/64`);
`Σ_j 2Csh_j²Δ³W^{2D} r_j⁴ ≤ 2·(2^{11}N^8)²·N^{-2D-20}·N^{2D}·R_k⁴ ≤ R_k⁴` (`r_j ≤ R_k` by `etaT_ratio`,
`card ≤ N`, `η_{u}^{-1} ≤ η_t^{-1} ≤ N`, `kΔ ≤ 1`, `N ≥ 64`); `4kΔN^{-C_c} + N^{-C_x} ≤ 5N^{-2D} ≤ 5T²`. Hence
`4Σ + N^{-C_x} ≤ T²(R⁴+1)[4ξ²(2qvC N^{τ₁+δ/64}+2)+5]` and `√(R⁴+1) ≤ R²+1`, giving
`xZ k a ≤ Mm (R_k²+1) T_{u_k}(a)` for all `k ≤ K`, `a`, eventually. `Mm ≤ N^{δ/8}` eventually iff
`4ξ²(…)+5 ≤ N^{δ/8}`: with `τ₁ ≤ δ/32` and `ξ ≤ N^{δ/128}` the left side is `≤ (8qvC+13)N^{δ/16}` — PASS
(`azumaMm_le`, hypotheses `|E| < 2`, `0 < δ`, `0 ≤ τ₁ ≤ δ/32`).
The ticket's `C_x ≥ 2D+2` is used in (T6′) (`C_c = C_x = 2D+2`); the proof only needs `≥ 2D`.
The literal-negation lemmas of the original (T3) are kept but relabelled as counterexamples to the original spec.

**(T4′) `cheb_grid_at_tau` — PASS.**
`CK D D₁ := D₁ + 2D + 80`, `gridK D D₁ N := max 1 ⌈N^{CK D D₁}⌉₊` (`= ⌈N^{C_K}⌉` for `N ≥ 1`; the `max 1` only
fixes `N = 0`, needed for `K N ≠ 0` in (T1)/(T2)). `C_K` depends only on `D, D₁` (and is explicit).
Statement: under `|E|<2`, `0 ≤ s ≤ t < 1`, gained hreg with `c > 0`, `0 ≤ D`, `s ≤ u ≤ t`, with `K := gridK D D₁`
and `τ := gridTau … K` (all good-set parameters and `δ` free): `∀ D₁ > 0, ∀ᶠ N,
(Pg d){ω | ∃ a, T_{u_{τω}}(a) ≤ ‖(Σ_{j<τ ω} Uker 1 u_{j+1} u_{τω} Yvec_{j+1} ω) a‖} ≤ N^{-D₁}`.
Route: `stopped_duhamel_cheb_tail` (n = 2, ξ ≡ 1, `t := u_K = u N`, `x := W^{-D}/4`, so `2²x = W^{-D} ≤ T`);
`e_j := 4(R′² C₂/2)² Δ² ∫‖X‖⁴` with `R′ := (1−s)/(1−u N) ≤ η_t^{-1} ≤ N` (row sum via `norm_Uker_apply_le`),
`C₂ := 16 card (1+η_t^{-1})^6` (`Φgrid_bdd2` at `η = η_t ≤ Im zt(u_{j+1})`), `∫‖X‖⁴ ≤ 3N`; so
`e_j ≤ 2^{22}N^{19}Δ²`, `Σ_{j<K} e_j ≤ 2^{22}N^{19}Δ` (`KΔ ≤ 1`), and the bound is
`16L²W^{2D}Σe_j ≤ 2^{26}N^{2D+21}Δ ≤ 2^{26}N^{2D+21−C_K} = 2^{26}N^{-D₁-59} ≤ N^{-D₁}`. Mean zero: `{j<τ} ∈ F_j`
(`condExp_indicator`) and `E[stepY|F_j] = 0` (T1505 part 4) with the a.e. identity
`Uker(u_{j+1},u_K)Yvec_{j+1} = stepY(ukerMat(u_{j+1},u_K))` (T1516). `MemLp 2`: `‖stepY‖ ≤ g + E[g|F_j]`,
`g = C‖X_{j+1}‖² ∈ L²`. Only polynomial smallness in `Δ`; that is why `K` depends on `D₁` (amend). No union over `k`.
Boundary: `τ ω = 0` gives the empty sum `0 < T`, consistent. Nondegenerate: `Δ > 0` whenever `s N < u N`.

**(T6′) `goodEvent_grid` — PASS.**
Hypotheses = step2's list (`κ > 0`, `|E| ≤ 2−κ`, `hB : BoundsCore`, `hs0`, `hst`, `ht1`, `Cond272`, `c > 0`,
gained hreg) + `0 < δ ≤ c/24`, `60 ≤ D`, `0 < τ₁ ≤ δ/32`, `0 < ε`, `2ε ≤ δ`, `ζCtr, τ3, τ57 > 0`, `s ≤ u ≤ t`.
For every `D₁ > 0`, with `K := gridK D (D₁+1)` (chosen after `D₁`, independent of `ω`), `C_c = C_x = 2D+2`,
`G N := {(T3′) event} ∩ {(T4′) event fails, i.e. ∀a, ‖Y-sum at τ‖ < T_{u_τ}(a)} ∩ {∀ j ≤ K, H_j ∈ G(u_j)} ∩
{(T5) event}`; conclusion `∀ᶠ N, (Pg d)(G N)ᶜ ≤ N^{-D₁}`. Proof: (T3′) (K polynomial: `K+1 ≤ N^{C_K+2}`
eventually), `highProb_grid_goodSet` (plain hreg from the gained one by `Step2.eventually_R4_le_scale`), (T5) are
`HighProb`, so their intersection has complement `≤ N^{-(D₁+1)}` eventually; (T4′) at `D₁+1` gives
`≤ N^{-(D₁+1)}`; `2N^{-(D₁+1)} ≤ N^{-D₁}` for `N ≥ 2`.
Deterministic consequences on `G N` (`goodEvent_grid_imp`), eventually in `N`, for every `ω ∈ G N`, in T1518 (T1)'s
shapes with endpoint `t := u`: `hinit` (`Mi = N^{δ/16}`), `hZ` at `k = τ ω` (`Mm N`, from (T3′) at `k = τω ≤ K`,
`min(τω,τω) = τω`, and `xZ_le_Mm`, whose `Δ ≤ N^{-(D+10)}` holds since `Δ ≤ 1/K ≤ N^{-C_K}`), `hY` at `k = τ ω`,
good-set membership and `J < thr` for `j < τ ω`, good-set membership for all `j ≤ K`, `J_0 < thr(u_0)`; plus the
side conditions of T1518 (T3): `1 ≤ K N`, `Δ ≤ N^{-(2D+76)}`, `Mm N ≤ N^{δ/8}`.
Satisfiability: the new parameter constraints (`τ₁ ≤ δ/32`, `2ε ≤ δ`, `C_c = C_x = 2D+2`) are jointly satisfiable
with step2's analytic hypotheses; compiled witness `goodEvent_grid_params_witness` (from T1508's
`qv_time_sum_le_hyps_witness`: `E = 0`, `s = 0`, `t N = 1−(N+1)^{-1/200}`, `c = 1/4`, `δ = 1/96`, `ε = δ/2`,
`D = 60`, `τ₁ = δ/32`, `u := t`). `hB : BoundsCore` is step2's own hypothesis (Step 1 output), not new.
No hypothesis is added to any accepted result; (T1), (T2), (T5) are untouched.

## (b) Lean

File: `RBM1D/Gauss/GridGoodEvent.lean` (2268 lines), branch `t/T1519`. Commits: `04d312a` (T1, T2, T5, original
T3 negation) and `d6116e3` (repair: T3′, T4′, T6′). Imports: `GridGoodSet`, `GridExpansion`, `GridQVForm`,
`GridQVStep`, `GridQVSum`, `GridDuhamelTail`, and (new) `GridNetLift` (T1511, for `etaT_inv_le_of_hreg`).

Kept from the prove stage (unchanged statements): (T1) `gridTau`, `isStoppingTime_gridTau`,
`lt_gridTau_measurableSet`, `lt_gridTau_imp`, `gridTau_le`; (T2) `thr_le_sqrtN`, `Qprime`, `cZ`, `cZ_nonneg`,
`floor_le_cZ`, `hsubG_gridTau`, `hsubG_gridTau_hyps_witness`; (T5) `initSet`, `measurableSet_initSet`,
`jSMat_le_of_mem_initSet`, `highProb_init_grid`; glue `time_succ_eq`, `time_mono_of_le`, `ukerMat_eq_prod_re`,
`quadVar_Φgrid_eq`, `jGMat_nonneg`. The original (T3) negations `not_highProb_azuma_grid_literal(')` are kept but
their section/docstrings now say "counterexample to the superseded original (T3) spec, not part of the (T3′) API".

New declarations (all in `RBM.Gauss.Grid`, section `Amend`):

| Target | Declaration | Hypotheses (as in the signature) / content |
|---|---|---|
| T3′ | `xZ d E s u K δ ε D τ₁ Cc Cx N k a` (def) | `N^{δ/16}·√(4 Σ_{j<k} cZ … N k a j + N^{-Cx})` |
| T3′ | `xZ_pos`, `xZ_sq` | `1 ≤ N`, `s N ≤ u N`: `0 < xZ`; `xZ² = N^{δ/8}(4Σ + N^{-Cx})` |
| T3′ | `highProb_azuma_grid'` | `|E|<2`, `0 ≤ s ≤ t < 1`, gained hreg, `0 < δ ≤ c/24`, `0 ≤ D`, good-set params free, `s ≤ u ≤ t`, `K N ≠ 0`, `∀ᶠ N, K N + 1 ≤ N^C`, `Cc Cx ∈ ℝ` free; concl. `HighProb (Pg d) {ω | ∀ k ≤ K N, ∀ a, ‖(Σ_{j<min k (gridTau ω)} Uker 1 u_{j+1} u_k (Zvec (j+1) ω)) a‖ < xZ … N k a}` |
| T3′ | `azumaMm d E δ τ₁ N` (def), `azumaMm_nonneg` | `N^{δ/16}·√(4 xiK²(2 qvSumConst E·N^{τ₁+δ/64} + 2) + 5)` |
| T3′ | `xZ_le_azumaMm` | as `highProb_azuma_grid'` + `Cond272`, `c > 0`, `0 ≤ ε`, `2ε ≤ δ`, `60 ≤ D`, `∀ᶠ N, Δ ≤ N^{-(D+10)}`, `2D ≤ Cc`, `2D ≤ Cx`; concl. `∀ᶠ N, ∀ k ≤ K N, ∀ a, xZ … N k a ≤ azumaMm … N * ((η_s/η_{u_k})² + 1) * tT (band d) E N D u_k (zdist(a0−a1))` |
| T3′ | `azumaMm_le` | `|E|<2`, `0 < δ`, `τ₁ ≤ δ/32`; concl. `∀ᶠ N, azumaMm … N ≤ N^{δ/8}` |
| T4′ | `CK D D₁ := D₁ + 2D + 80`, `gridK D D₁ N := max 1 ⌈N^{CK D D₁}⌉₊` (defs) | `gridK_ne_zero`, `rpow_CK_le_gridK`, `step_gridK_le` (`Δ ≤ N^{-CK}` for `N ≥ 1`, `u−s ≤ 1`), `gridK_card_le` (`K+1 ≤ N^{CK+2}` eventually, `CK ≥ 0`) |
| T4′ | `cheb_grid_at_tau` | `|E|<2`, `0 ≤ s ≤ t < 1`, `c > 0`, gained hreg, `0 ≤ D`, `δ` and good-set params free, `s ≤ u ≤ t`; concl. `∀ D₁ > 0, ∀ᶠ N, Pg {ω | ∃ a, tT(u_{τω})(a) ≤ ‖(Σ_{j<τω} Uker 1 u_{j+1} u_{τω} (Yvec (j+1) ω)) a‖} ≤ ofReal(N^{-D₁})` with `K = gridK D D₁`, `τ = gridTau … K` |
| T6′ | `goodEventGrid d E D δ τ₁ ε ζCtr τ3 τ57 s u K Cc Cx N` (def) | (T3′ event ∀ k ≤ K) ∩ (∀ a, Y-sum at τ `<` T_{u_τ}(a)) ∩ (∀ k : Fin (K+1), H_k ∈ G(u_k)) ∩ (T5 event) |
| T6′ | `goodEvent_grid` | step2's list: `κ > 0`, `|E| ≤ 2−κ`, `hB : BoundsCore`, `hs0`, `hst`, `ht1`, `Cond272`, `c > 0`, gained hreg; `0 < δ ≤ c/24`, `60 ≤ D`, `τ₁, ε, ζCtr, τ3, τ57 > 0`, `s ≤ u ≤ t`; concl. `∀ D₁ > 0, ∀ᶠ N, Pg (goodEventGrid … (gridK D (D₁+1)) (2D+2) (2D+2) N)ᶜ ≤ ofReal(N^{-D₁})` |
| T6′ | `goodEvent_grid_imp` | `|E|<2`, `hs0`, `hst`, `ht1`, `Cond272`, `c > 0`, gained hreg, `0 < δ ≤ c/24`, `60 ≤ D`, `τ₁ ≤ δ/32`, `0 ≤ ε`, `2ε ≤ δ`, `s ≤ u ≤ t`; concl. `∀ D₁ > 0, ∀ᶠ N, (1 ≤ K N ∧ Δ ≤ N^{-(2D+76)} ∧ 0 ≤ Mm ∧ Mm ≤ N^{δ/8}) ∧ ∀ ω ∈ goodEventGrid …, hinit ∧ hZ(k=τω) ∧ hY(k=τω) ∧ (∀ j<τω, J<thr ∧ H_j∈G) ∧ (∀ j ≤ K N, H_j ∈ G) ∧ J_0 < thr(u_0)`, all with `K = gridK D (D₁+1)`, `Mm = azumaMm`, in T1518 (T1)'s literal shapes (endpoint `t := u`) |
| T6′ | `goodEvent_grid_params_witness` | compiled nondegenerate witness of all non-`BoundsCore` hypotheses of T3′/T4′/T6′ (`η_s/η_t = (N+1)^{1/200}`, `s N < u N` for `N ≥ 1`) |
| glue | `measurable_coord_filt`, `measurable_lin`, `measurable_stepZ_filt`, `measurable_stepY_filt`, `ZvecCut`, `ZvecCut_succ`, `stronglyMeasurable_ZvecCut`, `YvecCut`, `YvecCut_succ`, `stronglyMeasurable_YvecCut`, `time_lt_one_of_le`, `card_loopArg_two`, `Zvec_succ_eq_zero_of_step`, `Uker_apply_eq_zero_of`, `eventually_mul_exp_neg_rpow_le`, `card_idx_le`, `qvTimeShiftConst_le` (`Csh ≤ 1536N⁸`), `two_Csh_sq_step_sq_le`, `sum_le_affine_sum`, `sqrt_floor_arith`, `integrable_stepZ'`, `integrable_stepY'`, `memLp_stepY'`, `condExp_indicator_stepY_re/im`, `integral_sq_indicator_stepY_le`, `integral_norm_Xmat_incr_four_le` (`∫‖X‖⁴ ≤ 3·#Idx`), `sum_abs_ukerMat_le`, `cheb_e_le` | deterministic / measure-theoretic helpers |

`ZvecCut`/`YvecCut` (`= Zvec i`/`Yvec i` for `1 ≤ i ≤ K N`, `0` otherwise) are only fed to T1504's lemmas to
meet their `∀ i, StronglyMeasurable[filt i]` hypothesis; every public statement is in terms of `Zvec`/`Yvec`.

Build: `cd /Users/junyin/Lean_proof/RBM1D-wt/T1519 && lake build RBM1D.Gauss.GridGoodEvent` →
`Build completed successfully (3959 jobs)`; 0 errors, 0 warnings in `GridGoodEvent.lean` (one
`set_option maxHeartbeats 1000000 in` on `xZ_le_azumaMm`, with a comment). `grep sorry|admit|^axiom`: none.

Axioms (`#print axioms` at the end of the file, for every public declaration, old and new):
`[propext, Classical.choice, Quot.sound]` for all 71 printed declarations (including `highProb_azuma_grid'`,
`xZ_le_azumaMm`, `azumaMm_le`, `cheb_grid_at_tau`, `goodEvent_grid`, `goodEvent_grid_imp`,
`goodEvent_grid_params_witness`).

Acceptance points of the amend:
- (T3′) holds at `k = 0` (the event quantifies over all `k ≤ K N`; `0 < xZ 0 a`) and at `Δ = 0` (case split in
  the proof: the complement is empty) — both inside the single `HighProb` statement.
- (T4′)'s `C_K = D₁ + 2D + 80` is explicit and depends only on `D, D₁`.
- (T6′) is stated `∀ D₁ > 0, ∀ᶠ N, …` with `K = gridK D (D₁+1)` fixed after `D₁`, independent of `ω`.
- No union over `k` in the `Y` bound: `cheb_grid_at_tau` is one application of `stopped_duhamel_cheb_tail` at the
  fixed target `u_K` with the backward kernel, giving the event at the random target `u_τ`.

## (c) Key lemmas used

- T1504: `stopped_duhamel_azuma_union` (T1″), `stopped_duhamel_cheb_tail` (T2).
- T1505: `stepDecomp` (part 4, mean zero), `stepDecomp_Y_sq`, `stepY_eq_ae`, `stepY_norm_le_ae`, `g_eq_pointwise`,
  `integrable_h0`, `integrable_Rlabel_sum`, `integrable_normPow4_incr`, `measurable_Ab`.
- T1516: `Zvec`, `Yvec`, `Zvec_succ`, `stepY_ukerMat_eq_Uker_ae`, `ukerMat_nonneg`, `Φgrid_testFun`,
  `Φgrid_im_eq_zero`, `Φgrid_bdd2`.
- T1508: `qv_time_sum_le'`, `Qd_nonneg`, `qvSumConst`, `qv_time_sum_le_hyps_witness`.
- T1514: `qvTimeShiftConst`. T1511: `etaT_inv_le_of_hreg`. T1513: `highProb_grid_goodSet`.
- (T1), (T2), (T5) of this ticket; `Step2.eventually_R4_le_scale`, `Step2FarInputs.eventually_xiK_le`,
  `Step2.etaT_ratio`, `rpow_neg_le_tailT`, `norm_Uker_apply_le`, `integral_norm_Xmat_pow_le`,
  `integral_colSq_le`, `SumZeroDyn.eventually_exp_small`, `map_incr`, `HighProb.inter`, `condExp_indicator`,
  `ContinuousLinearMap.comp_condExp_comm`, `MemLp.condExp`.

## (d) Open issues (for the dispatcher)

1. `goodEvent_grid` uses the grid `gridK D (D₁+1)` (the `+1` absorbs the sum of the four failure probabilities);
   downstream (T1520/R4c-2b) should take `K` from the same expression. T1518 (T3)'s side conditions `1 ≤ K N`,
   `Δ ≤ N^{-(2D+76)}`, `Mm ≤ N^{δ/8}` are delivered by `goodEvent_grid_imp`.
2. `gridK` is `max 1 ⌈N^{C_K}⌉₊` rather than the literal `⌈N^{C_K}⌉₊`: the two agree for `N ≥ 1`; the `max 1`
   only makes `K 0 ≠ 0`, which (T1)/(T2) require for every `N`.
3. New parameter constraints (all compiled satisfiable, `goodEvent_grid_params_witness`): `τ₁ ≤ δ/32` (for
   `Mm ≤ N^{δ/8}`), `2ε ≤ δ` and `Cond272` (inputs of T1508 `qv_time_sum_le'`), `C_c = C_x = 2D+2`.
   `goodEvent_grid_imp` needs neither `κ` nor `BoundsCore`; `goodEvent_grid` needs step2's full list.
4. Paper deltas: the Chebyshev step gives only polynomial smallness, so the grid size depends on the target
   exponent `D₁` (`K = ⌈N^{D₁+2D+80}⌉`); the paper argues in continuous time and has no such grid. This is a
   formalization-route choice made by the amend (T1519-amend-1, T1520 amend note), not a change of any paper
   statement. My file scope does not include `docs/paper-deltas.md`; if the dispatcher wants it recorded, a
   `T1519a` entry would read: "Step 2 on the grid: `K` depends on `(D, D₁)`; the remainder `Y` is controlled
   only at the stopping index by Chebyshev (polynomial rate)".
