/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CutHypTheta
import RBM1D.Gauss.Step6Hyp

/-!
# Step 2's first pass: the deterministic envelope, and why the unconditional walk cannot close
(T230, step 0)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.39)–(5.47).

## What this file settles

T222 (`RBM.CutHypTheta`) reduced `RBM.MomentDuhamelCut.CutHyp.moment` to a moment bound
**restricted to the prefix event** (`RBM.CutHypTheta.CutHypCond.condMoment`) and showed that
the *truncated* unconditional variant cannot close (`RBM.CutHypTheta.no_unconditional_stepwise`:
the cutoff's support width `2θ` forces `c < 2θ`, and then the premise a step needs is strictly
stronger than the conclusion it delivers).  T230 asks whether **dropping the truncation** — an
unconditional `L^{2p}` bound whose drift is split as `‖F·1_G‖ + ‖F·1_{Gᶜ}‖`, with the bad half
paid by a *deterministic polynomial envelope* of `J*` — escapes that no-go.

The three questions of step 0, answered:

1. **`J*` does have a deterministic polynomial envelope.**  `RBM.tailT` carries the `W^{-D}`
   floor by definition (`RBM.rpow_neg_le_tailT`), so the ratio (5.29) is bounded by
   `W^D · max_a |(L-K)_a| + 1`, and the numerator has the deterministic envelope of T77.
   `jStar_le_of_bdd`, `jS_le_of_bdd`, `jS_le_rpow`, `exists_jS_envelope`.
2. **The §13 no-go is *not* specific to truncation.**  Its hypothesis `c < 2θ` came from
   `cutTrunc θ ≤ 2θ`; the envelope route has the *same* hypothesis in the form `c < env`, and
   it is forced for exactly the same reason — if `env ≤ c` the bootstrap's conclusion is
   already deterministic and no probability is needed (`envelope_dichotomy`).  With
   `θ := env/2` the T222 statement applies verbatim: `no_envelope_stepwise`,
   `routeB_step_no_go`, `jS_routeB_step_no_go`.
3. **Uniformity of `N₀` in the net index `k` is not the obstruction.**
   `RBM.CutHypTheta.netGood_highProb` already chooses `p` once and proves the per-index bound
   for all `k ∈ Finset.range (n+1)` inside a single `Filter.Eventually`; the "first bad index"
   decomposition is what buys that.  The *decoupled-exponent* repair of (2) destroys it again,
   because the order needed at step `k` grows with `k` (see below).

## The sharper, route-specific no-go

Worse than (2): the unconditional walk feeds its own bad mass forward **multiplicatively**.
One step delivers `ρ_{k+1} ≤ ρ_k + (M + env^{2p} ρ_k)/c^{2p}`, which is *identically*
`ρ_k (1 + (env/c)^{2p}) + M/c^{2p}` (`chebyshev_union_shape`), and `c < env` makes the
amplification factor `≥ 2` (`one_le_ratio_pow`).  So the bound this argument produces grows
like `g · 2^k` (`bootBad_ge`) and exceeds `1` — i.e. becomes vacuous — after `O(log(1/g))`
net points, while the net of (5.46) has `⌊(t_N - s_N) m_N⌋` of them, which tends to infinity
(`routeB_walk_vacuous`).  **Choosing the moment order `p` differently at different steps does
not help**: `(env/c)^{2p} ≥ 1` for every `p`, so the factor is `≥ 2` whatever `p` is used.

## Route (A′): the smooth weight (§4–§8)

Route (A′) replaces the *indicator* of the prefix event by a **smooth weight** that is `1`
where the a priori bound holds.  Because the flow is `H_u = √u·X` with one fixed Gaussian `X`,
the whole trajectory is a function of `X`, so the prefix event already *is* an event of `X`;
the only obstruction to integrating by parts is that its indicator is not differentiable.
With a weight there is **no bad-event term at all** — the recursion is the `q ≡ 0` one, which
is linear, not geometric (`bootBad_le_of_q_zero`).

Two weights are built.

* §4, the **product** weight `Φ_k = ∏_{j<k} χ(ρ_j)` (`cutProd`).  Its support statements are
  the ones that say *where* the a priori bound may be used — `lt_two_of_cutProd_ne_zero` on
  the weight, `gap_of_cutProdTerm_ne_zero` on each term of its derivative — and they are what
  the `∇χ` terms of the Stein computation consume.  Its defect is `abs_derivProd_le`: the
  derivative is a sum over **all** `N^{Ccard}` net points times `L²` loop indices, a
  cardinality loss the cross terms cannot absorb.
* §6, the **ℓ^q soft maximum** `J̃_k = (∑_{j<k}∑_a ρ_{j,a}^q)^{1/q}` with `q = 2r` even and
  `w_k = χ(J̃_k/Θ)` (`softMax`, `softW`).  `le_softMax` and `softMax_le` bracket it between
  the maximum and `(card)^{1/q}` times the maximum, and `rpow_card_le_exp_one` calibrates
  `q ≍ log N` so that the loss is `e`; hence the cutoff sits at `Θ = e·Λ` (`one_le_softW`) and
  the support statement `abs_le_two_mul_of_softW_ne_zero` still gives `max ≤ 2Θ`.  Its
  derivative (`hasDerivAt_softMax`) obeys `|∂J̃| ≤ Λ·J̃` from `|∂ρ_i| ≤ Λ|ρ_i|`
  (`abs_deriv_softMax_le`) — a convex combination of logarithmic derivatives, with **no**
  cardinality factor.  `cutChiD_softW_eq_zero` records that `χ` is never differentiated at
  `J̃ = 0`, so the `y ↦ y^{1/q}` singularity at the origin is invisible.

§7 is the interface consequence, and it is **parametric in the weight**:
`condMoment_of_weightedMoment` turns an unconditional weighted moment bound
(`WeightedMoment`) into `RBM.CutHypTheta.CutHypCond.condMoment` verbatim.  Nothing in this
file is evidence that the *estimate* (A′) needs can be proved; what is compiled is that the
interface step is free and that the two no-gos of §2–§3 do not reach it.

## Main results

* `jStar_le_of_bdd`, `jS_le_of_bdd` — the `W^{-D}` floor of `RBM.tailT` turns any pointwise
  bound on `L-K` into a bound on `J*_{u,D}`.
* `jS_le_rpow`, `exists_jS_envelope` — **the deterministic polynomial envelope of `J*`**, for
  every `ω`, with no exceptional set (`W_N ≤ N` is reused from
  `RBM.Step45.eventually_W_le`, not re-proved).  This is the datum the `env` / `env_le` fields of
  `RBM.Step2Moment.MomentHyp` ask for, as a theorem.
* `envelope_dichotomy`, `no_envelope_stepwise`, `routeB_step_no_go`, `jS_routeB_step_no_go` —
  T222 §13 without truncation: **the no-go survives**.
* `bootBad`, `chebyshev_union_shape`, `bootBad_ge`, `routeB_walk_vacuous`,
  `routeB_walk_vacuous_of_envelope` — the geometric amplification of the bad mass along the
  net, which is route B's own, stronger obstruction.  The last one is the whole chain in one
  statement: its hypotheses are only `0 < c`, `c < env`, a positive floor on the per-step
  Chebyshev output, and a growing net.
* `bootBad_le_of_q_zero` — the contrast that isolates what (A′) would have to buy.
* `cutProd`, `gap_of_cutProdTerm_ne_zero`, `abs_derivProd_le` — the product weight, where its
  a priori bound may be used, and its cardinality loss.
* `softMax`, `le_softMax`, `softMax_le`, `rpow_card_le_exp_one`, `hasDerivAt_softMax`,
  `abs_deriv_softMax_le` — the ℓ^q soft maximum and its cardinality-loss-free derivative bound.
* `softW`, `one_le_softW`, `abs_le_two_mul_of_softW_ne_zero`, `softW_eq_zero` — the weight of
  route (A′), `1` on the prefix event, `0` past `2Θ`.
* `prefNet`, `prefixEvent_subset_prefNet`, `measurableSet_prefNet`,
  `setIntegral_le_integral_weight` — the measure-theoretic reduction, which needs only the
  *finite* net event to be measurable.
* `WeightedMoment`, `condMoment_of_weightedMoment` — **`RBM.CutHypTheta.CutHypCond.condMoment`
  is a theorem of an unconditional weighted moment bound.**
* `one_lt_ratR`, `sat_StepSide_gt_one`, `sat_StepSideSharp_gt_one`, `sat_stepRhs_div_gt_one` —
  the one-step side conditions of (5.39)–(5.44) at `R > 1`, all eight constraints tight
  (T222's `RBM.CutHypTheta.sat_StepSide` is the degenerate `R = 1` case).
* `APrimeHyp`, `APrimeHyp.toCutHypCondEv`, `APrimeHyp.toCutHypEv`, `APrimeHyp.toCutHypEv'`,
  `momentHypCutEv_of_aprime`, `jS_stochDom_of_aprime` — **the `cut` field of
  `RBM.MomentDuhamelCut.MomentHypCutEv` produced by a theorem**, from an interface with no
  event-restricted field.  `stochDom_of_aprime` is the same for a general `J`, which is the
  shape T243's third slot (`Ξ^{(L-K)}_{·,2}` at `A_s^{1/2}`) asks for.
* `MomentHypCut2Ev`, `stochDom_jSnorm2_of_bluntEv`, `jS_stochDom_sharp_of_cut2Ev`,
  `momentHypCut2Ev_of_aprime`, `jS_stochDom_sharp_of_aprime` — the same for the second pass,
  and (5.47) sharp end to end from two `APrimeHyp` plus (2.69).
* `sum_gvar_mul_le_sqrt_quadVar` — Cauchy–Schwarz for `RBM.Gauss.quadVar`, the step that
  splits route (A′)'s mixed-time cross term into two same-time quadratic-variation rates.
* `LogDerivBound`, `abs_deriv_softMax_le_of_logDerivBound`, `logDerivBound_gives_softMax` —
  the interface with `RBM1D/Gauss/APrimeTestFun.lean` (§12).  ⚠ T250 **refuted** the purely
  multiplicative shape on the loops; the usable one is affine, and §12 records both.
* `satAPrimeHyp`, `satCutHypEv_of_aprime`, `sat_stochDom_of_aprime`, `sat_satWval_eq_zero` —
  a compiled `APrimeHyp` **with the soft-max weight**, on the time-dependent `J_u = 2u⁺` that
  no `∀ N` interface of `RBM1D/Gauss/CutHypTheta.lean` can carry, and the chain run end to end
  on it (§13).
* `APrimeHypOn`, `weightOn`, `APrimeHypOn.toAPrimeHyp`, `stochDom_of_aprimeOn`,
  `APrimeHypOn.of_aprime`, `satAPrimeHypOn`, `sat_stochDom_of_aprimeOn` — **the T249 repair**:
  the modulus asserted only on an event `Good N` (in the application `{‖X‖ ≤ N}`), transferred
  through `RBM.MomentDuhamelCut.onEvent` and routed back at the cost of one `N^{-1}` (§14–§15).
  ⚠ This is only *half* of what T249 forces; the other half is `0 < s N`, which `APrimeHyp`
  does **not** imply — see §14.

## Non-vacuity (compiled)

* `one_le_of_jS_le` — any envelope of `J*` is `≥ 1`, since `J* ≥ 1` identically
  (`RBM.Step2Moment.one_le_jS`).  So `jS_le_rpow` is a bound at the critical scale from below,
  not a statement about a functional that happens to vanish.
* `thr_lt_env` — in the repository's own parameters the bootstrap threshold `N^δ - 1` is
  **strictly** below the envelope `C N^K` as soon as `δ ≤ K`, so the hypothesis `c < env` of
  `no_envelope_stepwise` is met, not hypothetical: the no-go is not vacuous.
* `sat_no_envelope_stepwise`, `sat_bootBad_vacuous` — explicit numeric instances of both
  no-gos, pinned by `norm_num`.

## Deviations from the paper

* `T230a`.  (5.43) is printed with a stopping time `T`; this file does not use it.  The
  statements here are about the *interface* of the first pass (which moment field can be
  produced from which data), not about (5.43) itself, so no renumbering is involved.  The
  record it adds is negative: the shape "unconditional moment bound + high-probability prefix
  + deterministic envelope" is not a possible reading of (5.39)–(5.47).
* `T230a` (continued).  The smooth weight of §4–§7 is **not in the paper**: (5.43) conditions
  on the stopping time `T`, and the weight is a formalization device that removes the need for
  it.  The interface it feeds (`RBM.CutHypTheta.CutHypCond`) is unchanged, so no statement of
  the paper is altered and nothing is renumbered; what changes is *which* hypothesis a
  producer has to discharge.  Jun's ruling (2026-09-22) is that the stopping time only plays
  the role of a continuity bootstrap, so this is a change of proof, not of statement.
-/

namespace RBM

namespace Step2Bootstrap

open MeasureTheory Filter Real

/-! ### 1. The deterministic polynomial envelope of `J*_{u,D}` (step 0, question (i))

`RBM.tailT` is `(W ℓ_u η_u)^{-2} e^{-√(ℓ/ℓ_u)} + W^{-D}`: the `W^{-D}` floor is part of the
definition of (5.27), and `RBM.rpow_neg_le_tailT` is it.  So the denominator of (5.29) is
never smaller than `W^{-D}`, and any pointwise bound on the numerator `|(L-K)_{u,(+,-),a}|`
becomes a bound on `J*_{u,D}` at the price of one factor `W^D`.

The numerator's deterministic bound is T77's: a loop is a trace of a product of Green
functions and block projections, `‖G_u‖ ≤ η_u^{-1}` holds for **every** `ω` because `H_u` is
Hermitian pointwise (`RBM.Gauss.norm_gloop_le_det`), and `K` is not random at all.  The
combination is `RBM.Gauss.lkErr_le_rpow`.
-/

section Envelope

/-- **The `W^{-D}` floor of (5.27) turns a pointwise bound into a bound on `J*`.**

If `f ≤ Bd` pointwise then `J*` of (5.29) is at most `W^D Bd + 1`, because the denominator
`T_{u,D}` is never below `W^{-D}` (`RBM.rpow_neg_le_tailT`).  No decay of `f` is used: this is
the crude, *deterministic* half of (5.31). -/
theorem jStar_le_of_bdd {L : ℕ} [NeZero L] {f : LoopArg L 2 → ℝ} {W ℓu ηu D Bd : ℝ}
    (hW : 0 < W) (hBd : 0 ≤ Bd) (hf : ∀ a, f a ≤ Bd) :
    Step2.jStar L f W ℓu ηu D ≤ W ^ D * Bd + 1 := by
  refine Step2.jStar_le hW (c := W ^ D * Bd) fun a => ?_
  have hWD : (0 : ℝ) < W ^ D := Real.rpow_pos_of_pos hW D
  have hprod : W ^ D * W ^ (-D) = 1 := by
    rw [← Real.rpow_add hW]; simp
  have hfloor : W ^ (-D) ≤ tailT W ℓu ηu D (zdist L (a 0 - a 1)) := rpow_neg_le_tailT _
  have hmul : W ^ D * Bd * W ^ (-D) ≤ W ^ D * Bd * tailT W ℓu ηu D (zdist L (a 0 - a 1)) :=
    mul_le_mul_of_nonneg_left hfloor (by positivity)
  have hid : W ^ D * Bd * W ^ (-D) = Bd := by
    rw [mul_comm (W ^ D) Bd, mul_assoc, hprod, mul_one]
  calc f a ≤ Bd := hf a
    _ = W ^ D * Bd * W ^ (-D) := hid.symm
    _ ≤ W ^ D * Bd * tailT W ℓu ηu D (zdist L (a 0 - a 1)) := hmul

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `J*_{u,D} ≤ W^D · Bd + 1` from a pointwise bound `Bd` on `|(L-K)_{u,(+,-),a}|`. -/
theorem jS_le_of_bdd (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {Bd : ℝ} (hBd : 0 ≤ Bd)
    (hf : ∀ a : LoopArg (B.L N) 2,
      X.lkErr E N u ω (LoopData.idx (Step2.sigPM, a)) ≤ Bd) :
    Step2.jS X E D N u ω ≤ (B.W N : ℝ) ^ D * Bd + 1 := by
  have hW : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  exact jStar_le_of_bdd (f := fun a => ‖Step2.lk X E N u ω a‖) hW hBd hf

/-- **⭐ The deterministic polynomial envelope of `J*_{u,D}` (step 0, question (i): yes).**

For **every** `ω` — no exceptional set, no filtration, no stopping time —
`J*_{u,D} ≤ (1 + C_K) N^{D + 2c} + 1`, where `N^{-c} ≤ η_u` is the (non-free) statement that
`η_u` is not super-polynomially small and `C_K` is the constant of (2.59).

The two ingredients are the `W^{-D}` floor of (5.27) (`jS_le_of_bdd`) and T77's deterministic
loop envelope (`RBM.Gauss.lkErr_le_rpow`). -/
theorem jS_le_rpow (X : Sample B) {E : ℝ} (hE : |E| < 2) {D : ℝ} (hD : 0 ≤ D) {N : ℕ}
    (hN : 1 ≤ N) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {cη : ℝ} (hcη : 0 ≤ cη)
    (hη : (N : ℝ) ^ (-cη) ≤ etaT E u) (hWN : (B.W N : ℝ) ≤ (N : ℝ)) (ω : Ω) {CK : ℝ}
    (hCK0 : 0 ≤ CK)
    (hK : ∀ a : LoopArg (B.L N) 2,
      ‖B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖ ≤ CK * (B.scale E N u)⁻¹ ^ 1) :
    Step2.jS X E D N u ω ≤ (1 + CK) * (N : ℝ) ^ (D + 2 * cη) + 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hBd : ∀ a : LoopArg (B.L N) 2,
      X.lkErr E N u ω (LoopData.idx (Step2.sigPM, a)) ≤ (1 + CK) * (N : ℝ) ^ (cη * 2) := by
    intro a
    have hlen : (LoopData.idx (Step2.sigPM, a)).length = 2 :=
      LoopData.idx_length (Step2.sigPM, a)
    have h := Gauss.lkErr_le_rpow X hE hN hu0 hu1 hcη hη ω
      (I := LoopData.idx (Step2.sigPM, a)) (LoopData.idx_wf _) (by rw [hlen]; omega) hCK0
      (by rw [hlen]; exact hK a)
    rw [hlen] at h
    simpa using h
  have h2 := jS_le_of_bdd X E D N u ω (Bd := (1 + CK) * (N : ℝ) ^ (cη * 2)) (by positivity) hBd
  have hWD : (B.W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
    Real.rpow_le_rpow (by positivity) hWN hD
  have heq : (N : ℝ) ^ D * ((N : ℝ) ^ (cη * 2)) = (N : ℝ) ^ (D + 2 * cη) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hpos : (0 : ℝ) ≤ (1 + CK) * (N : ℝ) ^ (cη * 2) := by positivity
  calc Step2.jS X E D N u ω
      ≤ (B.W N : ℝ) ^ D * ((1 + CK) * (N : ℝ) ^ (cη * 2)) + 1 := h2
    _ ≤ (N : ℝ) ^ D * ((1 + CK) * (N : ℝ) ^ (cη * 2)) + 1 := by nlinarith
    _ = (1 + CK) * (N : ℝ) ^ (D + 2 * cη) + 1 := by rw [← heq]; ring

/-- **The envelope in the shape the `env` / `env_le` fields of `RBM.Step2Moment.MomentHyp`
ask for**: a single `C > 0` and a single exponent `D + 2c`, valid for every time of the window
and every `ω`.  The constant of (2.59) is supplied by `RBM.Band.norm_Kval_le` at `n = 2`, and
`W_N ≤ N` by `RBM.Step45.eventually_W_le` (already in the repository — not re-proved here).

The only input that is not a theorem of `RBM.Band` is `hη`, i.e. `N^{-c} ≤ η_u` — the form in
which `W ℓ_u η_u ≥ 1` enters, exactly as in `RBM.Gauss.lkErr_le_rpow`. -/
theorem exists_jS_envelope (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {D : ℝ} (hD : 0 ≤ D) {cη : ℝ} (hcη : 0 ≤ cη)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N), (N : ℝ) ^ (-cη) ≤ etaT E u) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N), ∀ ω : Ω,
      Step2.jS X E D N u ω ≤ C * (N : ℝ) ^ (D + 2 * cη) := by
  have hE : |E| < 2 := by linarith
  obtain ⟨CK, hCK0, hCK⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 2) (by norm_num)
  refine ⟨2 + CK, by linarith, ?_⟩
  filter_upwards [hη, Step45.eventually_W_le B, eventually_ge_atTop 1] with N hηN hWN hN1
  intro u hu ω
  have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hK : ∀ a : LoopArg (B.L N) 2,
      ‖B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖ ≤ CK * (B.scale E N u)⁻¹ ^ 1 := by
    intro a
    have h := hCK N u hu0 hu1 (LoopData.idx (Step2.sigPM, a)) (LoopData.idx_wf _)
      (LoopData.idx_length (Step2.sigPM, a))
    simpa using h
  have h := jS_le_rpow X hE hD hN1 hu0 hu1 hcη (hηN u hu) hWN ω hCK0 hK
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (D + 2 * cη) := Real.one_le_rpow hNR (by linarith)
  nlinarith

/-- **Any envelope of `J*` is at least `1`.**  `J*_{u,D} ≥ 1` identically
(`RBM.Step2Moment.one_le_jS`), so `jS_le_rpow` constrains a functional that is bounded below
at the critical scale — it is not a statement about something that vanishes. -/
theorem one_le_of_jS_le (X : Sample B) {E D : ℝ} (N : ℕ) (u : ℝ) (ω : Ω) {Bd : ℝ}
    (h : Step2.jS X E D N u ω ≤ Bd) : 1 ≤ Bd :=
  le_trans (Step2Moment.one_le_jS X N u ω) h

end Envelope

/-! ### 2. T222 §13 without truncation: the no-go survives (step 0, question (ii))

`RBM.CutHypTheta.no_unconditional_stepwise` is an arithmetic statement with hypothesis
`c < 2θ`.  In T222 that hypothesis came from `RBM.CutHypTheta.lt_two_mul_of_lt_cutTrunc`, i.e.
from `cutTrunc θ ≤ 2θ`: **the width of the cutoff's support**.  Route B has no cutoff, so the
question is whether the hypothesis disappears with it.

It does not.  Route B pays the bad half of the split with the deterministic envelope `env`, so
the quantity playing the role of `2θ` is `env`, and the analogue of
`lt_two_mul_of_lt_cutTrunc` is the trivial `lt_env_of_exists_lt` — with the *same* meaning:
if `env ≤ c` then the conclusion `J ≤ c` holds for every `ω` already, so there is nothing to
bootstrap (`conclusion_of_env_le`).  The bootstrap is non-trivial exactly when `c < env`,
which is exactly when the no-go bites.
-/

section NoGoEnvelope

variable {Ω : Type*}

/-- **If the envelope is below the threshold, the conclusion is deterministic.**  This is the
half of the dichotomy in which no probability is needed at all. -/
theorem conclusion_of_env_le {J : Ω → ℝ} {env c : ℝ} (hJ : ∀ ω, J ω ≤ env) (h : env ≤ c) :
    ∀ ω, J ω ≤ c := fun ω => (hJ ω).trans h

/-- **The non-truncated analogue of `RBM.CutHypTheta.lt_two_mul_of_lt_cutTrunc`.**  If the bad
event `{J > c}` is non-empty at all, then `c < env`. -/
theorem lt_env_of_exists_lt {J : Ω → ℝ} {env c : ℝ} (hJ : ∀ ω, J ω ≤ env)
    (hbad : ∃ ω, c < J ω) : c < env := by
  obtain ⟨ω, hω⟩ := hbad
  exact lt_of_lt_of_le hω (hJ ω)

/-- **The dichotomy**: either the bootstrap's conclusion is already deterministic, or the
no-go's hypothesis `c < env` holds.  There is no third case. -/
theorem envelope_dichotomy {J : Ω → ℝ} {env c : ℝ} (hJ : ∀ ω, J ω ≤ env) :
    (∀ ω, J ω ≤ c) ∨ c < env := by
  rcases le_or_gt env c with h | h
  · exact Or.inl (conclusion_of_env_le hJ h)
  · exact Or.inr h

/-- **⭐ T222 §13, restated with the deterministic envelope in place of the cutoff width: it
still holds.**

`(n+1) · g ≤ r` — the union bound over `n + 1` net points of the Chebyshev output
`g = C M / c^{2p}`, fitting inside the premise `r = M / env^{2p}` that the next step's
bad-event term needs — is **impossible**, for every threshold `c > 0`, every envelope
`env > c`, every target `M > 0`, every constant `C ≥ 1` and every `p ≥ 1`.  As in T222 it
already fails at `n = 0`.

This is `RBM.CutHypTheta.no_unconditional_stepwise` at `θ := env/2`: dropping the truncation
changes the *name* of the wide scale, not the arithmetic. -/
theorem no_envelope_stepwise {c env M C : ℝ} (hc : 0 < c) (hce : c < env) (hM : 0 < M)
    (hC : 1 ≤ C) {p n : ℕ} (hp : 1 ≤ p) :
    ¬ (((n : ℝ) + 1) * (C * M / c ^ (2 * p)) ≤ M / env ^ (2 * p)) := by
  have hθ : c < 2 * (env / 2) := by linarith
  have h := CutHypTheta.no_unconditional_stepwise (θ := env / 2) hc hθ hM hC (n := n) hp
  have he : 2 * (env / 2) = env := by ring
  rwa [he] at h

/-- The no-go at the repository's own one-step constant `RBM.Step2MomentStep.cStep'`. -/
theorem no_envelope_stepwise_phi {c env M m : ℝ} (hc : 0 < c) (hce : c < env) (hM : 0 < M)
    (hm : 0 < m) {p n : ℕ} (hp : 1 ≤ p) :
    ¬ (((n : ℝ) + 1) * (Step2MomentStep.cStep' m ^ (2 * p) * M / c ^ (2 * p))
        ≤ M / env ^ (2 * p)) :=
  no_envelope_stepwise hc hce hM (CutHypTheta.one_le_cStep'_pow hm p) hp

/-- **The no-go in the form route B is stated in**: the only extra input over
`no_envelope_stepwise` is that the bad event is non-empty, i.e. that the bootstrap has
something to prove. -/
theorem routeB_step_no_go {J : Ω → ℝ} {env c M C : ℝ} (hJ : ∀ ω, J ω ≤ env)
    (hbad : ∃ ω, c < J ω) (hc : 0 < c) (hM : 0 < M) (hC : 1 ≤ C) {p n : ℕ} (hp : 1 ≤ p) :
    ¬ (((n : ℝ) + 1) * (C * M / c ^ (2 * p)) ≤ M / env ^ (2 * p)) :=
  no_envelope_stepwise hc (lt_env_of_exists_lt hJ hbad) hM hC hp

variable {Ω' : Type*} [MeasurableSpace Ω'] {B : Band Ω'}

/-- The same, at `RBM.Step2.jS` itself, with the envelope coming from `jS_le_rpow`. -/
theorem jS_routeB_step_no_go (X : Sample B) {E D : ℝ} {N : ℕ} {u : ℝ} {env c M C : ℝ}
    (henv : ∀ ω : Ω', Step2.jS X E D N u ω ≤ env)
    (hbad : ∃ ω : Ω', c < Step2.jS X E D N u ω) (hc : 0 < c) (hM : 0 < M) (hC : 1 ≤ C)
    {p n : ℕ} (hp : 1 ≤ p) :
    ¬ (((n : ℝ) + 1) * (C * M / c ^ (2 * p)) ≤ M / env ^ (2 * p)) :=
  routeB_step_no_go henv hbad hc hM hC hp

/-- **The no-go's hypothesis is met in the repository's own parameters, not hypothetical.**
The bootstrap threshold of `RBM.CutHypTheta.netGood_highProb` is `(N^δ - 1) Θ_N`; at the
control `Θ_N = 1` it is `N^δ - 1`, and the envelope of `jS_le_rpow` is `C N^K` with
`K = D + 2c ≥ δ` and `C ≥ 1`.  Then `c < env` strictly. -/
theorem thr_lt_env {δ K C : ℝ} (hδK : δ ≤ K) (hC : 1 ≤ C) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ δ - 1 < C * (N : ℝ) ^ K := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ K := Real.rpow_le_rpow_of_exponent_le hNR hδK
  have h2 : (0 : ℝ) < (N : ℝ) ^ K := Real.rpow_pos_of_pos (by linarith) _
  nlinarith

/-- An explicit numeric instance of `no_envelope_stepwise`: `c = 1`, `env = 2`, `M = C = 1`,
`p = 1`, `n = 0`.  The premise the step needs is `1/4`, the conclusion it delivers is `1`. -/
theorem sat_no_envelope_stepwise :
    ¬ (((0 : ℕ) + 1 : ℝ) * ((1 : ℝ) * 1 / (1 : ℝ) ^ (2 * 1)) ≤ (1 : ℝ) / (2 : ℝ) ^ (2 * 1)) :=
  no_envelope_stepwise (c := 1) (env := 2) (M := 1) (C := 1) one_pos one_lt_two one_pos
    le_rfl (n := 0) le_rfl

/-- The numbers of `sat_no_envelope_stepwise`, independently: `1 ≤ 1/4` is false. -/
theorem sat_no_envelope_numbers :
    ((0 : ℕ) + 1 : ℝ) * ((1 : ℝ) * 1 / (1 : ℝ) ^ (2 * 1)) = 1
      ∧ (1 : ℝ) / (2 : ℝ) ^ (2 * 1) = 1 / 4 := by
  norm_num

end NoGoEnvelope

/-! ### 3. Route B's own, stronger obstruction: the bad mass amplifies along the net

The step of route B is: an unconditional `L^{2p}` bound whose drift is split on the good event
`G_k` and its complement, the bad half paid by `env^{2p} P(G_kᶜ)`, followed by Chebyshev at the
threshold `c` and a union bound.  Writing `ρ_k` for the bound on `P(G_kᶜ)` this argument
produces, one step gives

`ρ_{k+1} ≤ ρ_k + (M + env^{2p} ρ_k)/c^{2p}`,

which is **identically** `ρ_k (1 + (env/c)^{2p}) + M/c^{2p}` (`chebyshev_union_shape`).  By
§2, `c < env`, so `(env/c)^{2p} ≥ 1` for every `p` (`one_le_ratio_pow`) and the factor is
`≥ 2`.  Hence `ρ` grows at least like `g · 2^k` (`bootBad_ge`) and passes `1` — becomes
vacuous as a probability bound — after `O(log(1/g))` steps, while the net of (5.46) has
`⌊(t_N - s_N) m_N⌋` points, which tends to infinity (`routeB_walk_vacuous`).

Note what this rules out that §2 does not: **using a different moment order at each step does
not help.**  The amplification factor is `1 + (env/c)^{2p_k} ≥ 2` whatever `p_k` is, so the
"take `p` large enough at step `k`" repair of §2 is already covered — `bootBad` quantifies over
a *sequence* `q`.
-/

section Walk

/-- The recursion the walk of route B produces for the bound on `P(G_kᶜ)`: at step `k` the
previous bound is amplified by `1 + q k` (the ratio `(env/c)^{2p_k}` of §2, plus the one unit
of the union bound) and the fresh Chebyshev output `g k` is added.  `q` and `g` are sequences,
so a different moment order at each step is covered. -/
noncomputable def bootBad (q g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => bootBad q g k * (1 + q k) + g k

@[simp] theorem bootBad_zero (q g : ℕ → ℝ) : bootBad q g 0 = 0 := rfl

theorem bootBad_succ (q g : ℕ → ℝ) (k : ℕ) :
    bootBad q g (k + 1) = bootBad q g k * (1 + q k) + g k := rfl

/-- **The shape of the recursion is forced**: Chebyshev plus the union bound *is*
`ρ ↦ ρ (1 + (env/c)^{2p}) + M/c^{2p}`.  Nothing is given away in passing to `bootBad`. -/
theorem chebyshev_union_shape (ρ M c env : ℝ) (hc : c ≠ 0) (p : ℕ) :
    ρ + (M + env ^ (2 * p) * ρ) / c ^ (2 * p)
      = ρ * (1 + (env / c) ^ (2 * p)) + M / c ^ (2 * p) := by
  have hcp : c ^ (2 * p) ≠ 0 := pow_ne_zero _ hc
  rw [div_pow]
  field_simp
  ring

/-- **The amplification factor is at least `2`, for every moment order.**  This is where
`c < env` of §2 is used, and it is why choosing `p` differently at each step cannot help. -/
theorem one_le_ratio_pow {c env : ℝ} (hc : 0 < c) (hce : c < env) (p : ℕ) :
    1 ≤ (env / c) ^ (2 * p) :=
  one_le_pow₀ ((one_le_div hc).2 hce.le)

/-- **⭐ The bound the walk produces grows geometrically.**  If every amplification factor is
`≥ 1` (i.e. `1 + q k ≥ 2`) and every fresh Chebyshev output is `≥ g₀ ≥ 0`, then after `k + 1`
steps the bound is at least `g₀ 2^k`. -/
theorem bootBad_ge {q g : ℕ → ℝ} {g₀ : ℝ} (hg0 : 0 ≤ g₀) (hq : ∀ k, 1 ≤ q k)
    (hg : ∀ k, g₀ ≤ g k) : ∀ k : ℕ, g₀ * 2 ^ k ≤ bootBad q g (k + 1) := by
  intro k
  induction k with
  | zero => simpa [bootBad_succ] using hg 0
  | succ k ih =>
      have h0 : 0 ≤ bootBad q g (k + 1) :=
        le_trans (mul_nonneg hg0 (by positivity)) ih
      have h2 : (2 : ℝ) ≤ 1 + q (k + 1) := by linarith [hq (k + 1)]
      have hgk := hg (k + 1)
      rw [bootBad_succ]
      calc g₀ * 2 ^ (k + 1) = (g₀ * 2 ^ k) * 2 := by ring
        _ ≤ bootBad q g (k + 1) * 2 := by linarith
        _ ≤ bootBad q g (k + 1) * (1 + q (k + 1)) := mul_le_mul_of_nonneg_left h2 h0
        _ ≤ bootBad q g (k + 1) * (1 + q (k + 1)) + g (k + 1) := by linarith

/-- **The bound becomes vacuous** — it exceeds `1`, so it says nothing about a probability —
as soon as `g₀ 2^k > 1`. -/
theorem bootBad_not_le_one {q g : ℕ → ℝ} {g₀ : ℝ} (hg0 : 0 ≤ g₀) (hq : ∀ k, 1 ≤ q k)
    (hg : ∀ k, g₀ ≤ g k) {k : ℕ} (hk : 1 < g₀ * 2 ^ k) : ¬ (bootBad q g (k + 1) ≤ 1) := by
  intro h
  linarith [bootBad_ge hg0 hq hg k]

/-- **The contrast that isolates what the smooth-weight route (A′) would have to buy.**  If
there is *no* bad-event term — `q ≡ 0`, i.e. the a priori bound holds pathwise on the support
of the weight and of its derivative, so no mass is fed forward — the same walk is **linear**
in the number of steps, and a net with `N^{Ccard}` points costs one polynomial factor, which
is a single `≺`-loss. -/
theorem bootBad_le_of_q_zero {q g : ℕ → ℝ} {g₁ : ℝ} (hq : ∀ k, q k = 0)
    (hg : ∀ k, g k ≤ g₁) : ∀ k : ℕ, bootBad q g k ≤ (k : ℝ) * g₁ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [bootBad_succ, hq k]
      have hgk := hg k
      push_cast
      nlinarith

/-- `g₀ 2^k > 1` eventually in `k`, for every `g₀ > 0`: the number of net points the walk can
afford is `O(log(1/g₀))`. -/
theorem eventually_one_lt_mul_two_pow {g₀ : ℝ} (hg0 : 0 < g₀) :
    ∀ᶠ k : ℕ in atTop, 1 < g₀ * 2 ^ k := by
  have h : Tendsto (fun k : ℕ => g₀ * (2 : ℝ) ^ k) atTop atTop :=
    Tendsto.const_mul_atTop hg0 (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact h.eventually_gt_atTop 1

/-- The net of (5.46) has `⌊(t_N - s_N) m_N⌋` points; if the mesh does its job the count tends
to infinity. -/
theorem cutNetTop_atTop {s t mesh : ℕ → ℝ}
    (h : Tendsto (fun N => (t N - s N) * mesh N) atTop atTop) :
    Tendsto (fun N => CutHypTheta.cutNetTop s t mesh N) atTop atTop := by
  simpa [CutHypTheta.cutNetTop, Function.comp_def] using tendsto_nat_floor_atTop.comp h

/-- **⭐⭐ Route B's walk is vacuous on the net of (5.46).**

Given a positive floor `g₀` on the per-step Chebyshev output and the amplification factors of
§2, the bound the walk produces at the last net point exceeds `1` for all large `N` — i.e. it
is not a probability bound at all.  The hypothesis on the mesh is the one
`RBM.CutHypTheta.CutHypCond.mesh_fine` forces (the net must be fine enough for the modulus of
continuity to cost at most `Θ_N` per mesh).

The quantifiers matter: `q` and `g` are *sequences*, so this covers choosing the moment order
`p` separately at every step. -/
theorem routeB_walk_vacuous {q g : ℕ → ℝ} {g₀ : ℝ} (hg0 : 0 < g₀) (hq : ∀ k, 1 ≤ q k)
    (hg : ∀ k, g₀ ≤ g k) {s t mesh : ℕ → ℝ}
    (hm : Tendsto (fun N => (t N - s N) * mesh N) atTop atTop) :
    ∀ᶠ N : ℕ in atTop, ¬ (bootBad q g (CutHypTheta.cutNetTop s t mesh N) ≤ 1) := by
  have hcut := cutNetTop_atTop hm
  have hsub : Tendsto (fun N => CutHypTheta.cutNetTop s t mesh N - 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun m => by
      obtain ⟨i, hi⟩ := tendsto_atTop_atTop.1 hcut (m + 1)
      exact ⟨i, fun a ha => by have := hi a ha; omega⟩
  filter_upwards [hsub.eventually (eventually_one_lt_mul_two_pow hg0),
    hcut.eventually_ge_atTop 1] with N hN1 hN2
  have hEq : CutHypTheta.cutNetTop s t mesh N = (CutHypTheta.cutNetTop s t mesh N - 1) + 1 := by
    omega
  rw [hEq]
  exact bootBad_not_le_one hg0.le hq hg hN1

/-- The amplification hypothesis of `bootBad_ge` is exactly what §2 delivers, for **any**
choice of moment order at each step. -/
theorem routeB_hq {c env : ℝ} (hc : 0 < c) (hce : c < env) (pf : ℕ → ℕ) :
    ∀ k, 1 ≤ (env / c) ^ (2 * pf k) :=
  fun k => one_le_ratio_pow hc hce (pf k)

/-- **⭐⭐⭐ Route B, assembled: the walk's own bound on `P(G_kᶜ)` is vacuous for large `N`.**

The hypotheses are exactly the data route B has: a positive threshold `c`, an envelope
`env > c` (forced by `envelope_dichotomy` whenever the bootstrap is not already deterministic),
a moment order `pf k` chosen freely at each step, a positive floor `g₀` on the per-step
Chebyshev output, and a mesh fine enough that the net's cardinality grows.  The conclusion is
that the bound this argument produces at the last net point exceeds `1`.

**Epistemic status** (as for `RBM.CutHypTheta.no_unconditional_stepwise`): this says the
*bound the strategy produces* is vacuous, not that the underlying probability is large.  It is
the precise location of an obstruction in a proof strategy, not an unprovability result. -/
theorem routeB_walk_vacuous_of_envelope {c env : ℝ} (hc : 0 < c) (hce : c < env) (pf : ℕ → ℕ)
    {g : ℕ → ℝ} {g₀ : ℝ} (hg0 : 0 < g₀) (hg : ∀ k, g₀ ≤ g k) {s t mesh : ℕ → ℝ}
    (hm : Tendsto (fun N => (t N - s N) * mesh N) atTop atTop) :
    ∀ᶠ N : ℕ in atTop,
      ¬ (bootBad (fun k => (env / c) ^ (2 * pf k)) g (CutHypTheta.cutNetTop s t mesh N) ≤ 1) :=
  routeB_walk_vacuous hg0 (routeB_hq hc hce pf) hg hm

/-- An explicit numeric instance: with amplification factor `2` (`q ≡ 1`) and per-step output
`2^{-10}` the walk's bound passes `1` at step `12`. -/
theorem sat_bootBad_vacuous :
    ¬ (bootBad (fun _ => 1) (fun _ => (2 : ℝ) ^ (-10 : ℤ)) 12 ≤ 1) := by
  refine bootBad_not_le_one (g₀ := (2 : ℝ) ^ (-10 : ℤ)) (by positivity)
    (fun _ => le_rfl) (fun _ => le_rfl) (k := 11) ?_
  norm_num

end Walk

/-! ### 4. Route (A′): the smooth prefix weight

§2 and §3 rule out paying for the complement of the prefix event.  Route (A′) never opens
that account.  Because the flow is `H_u = √u · X` with one fixed Gaussian `X`, the whole
trajectory `u ↦ J_u(ω)` is a function of `X` alone, so the prefix event *is* an event of `X`;
what obstructs integration by parts is not its `u`-dependence but the fact that its
**indicator is not differentiable**.  Replace the indicator by a product of copies of T158's
`C²` profile `RBM.Cutoff.cutChi`, one per earlier net point:

`Φ_k(ω) = ∏_{j<k} χ(ρ_j(ω))`,  `ρ_j = J_{w_j}/Λ_{w_j}` (or its square, `§5`).

Then

* `Φ_k` is a weight, `0 ≤ Φ_k ≤ 1` (`cutProd_nonneg`, `cutProd_le_one`);
* `Φ_k = 1` on the prefix event (`cutProd_eq_one`, `prefW_eq_one_of_mem_prefixEvent`), so the
  *conditional* moment of `condMoment` is dominated by the **full-measure** weighted moment
  (`condMoment_of_weightedMoment`) — there is no complement term at all;
* on the support of `Φ_k` **and of each term of `Φ_k'`** the a priori bound holds pathwise
  (`le_two_mul_of_cutProd_ne_zero`, `gap_of_cutProdTerm_ne_zero`), which is the datum the
  `∇χ` terms of the Stein computation need and the only place where the bootstrap's own
  hypothesis is used;
* `Φ_k` is differentiable along any curve along which the `ρ_j` are, with the explicit
  derivative `hasDerivAt_cutProd`, and both `Φ_k` and `Φ_k'` are **bounded**
  (`abs_cutProd_le_one`, `abs_derivProd_le`) — which is exactly the pair of hypotheses
  `RBM.Gauss.MatrixStein.stein` asks for.

`WeightedMoment` is the resulting moment field: `CutHypCond.condMoment` with the restriction
to `prefixEvent` replaced by the weight, i.e. an **unconditional** integral.
-/

section SmoothWeight

variable {Ω : Type*}

open Cutoff

/-- **The smooth prefix weight, abstractly**: the product of `χ` over a finite family of
ratios.  `k = 0` gives the empty product `1`. -/
noncomputable def cutProd (ρ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range k, cutChi (ρ j ω)

@[simp] theorem cutProd_zero (ρ : ℕ → Ω → ℝ) (ω : Ω) : cutProd ρ 0 ω = 1 := by
  simp [cutProd]

theorem cutProd_succ (ρ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    cutProd ρ (k + 1) ω = cutProd ρ k ω * cutChi (ρ k ω) := by
  simp [cutProd, Finset.prod_range_succ]

theorem cutProd_nonneg (ρ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : 0 ≤ cutProd ρ k ω :=
  Finset.prod_nonneg fun _ _ => cutChi_nonneg _

theorem cutProd_le_one (ρ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : cutProd ρ k ω ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => cutChi_nonneg _) (fun _ _ => cutChi_le_one _)

/-- The weight is bounded by `1` in absolute value — the first boundedness hypothesis of
`RBM.Gauss.MatrixStein.stein`. -/
theorem abs_cutProd_le_one (ρ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : |cutProd ρ k ω| ≤ 1 :=
  abs_le.2 ⟨by linarith [cutProd_nonneg ρ k ω], cutProd_le_one ρ k ω⟩

/-- **The weight is `1` where all the ratios are below the threshold.**  This is the half that
replaces "restrict to the prefix event". -/
theorem cutProd_eq_one {ρ : ℕ → Ω → ℝ} {k : ℕ} {ω : Ω} (h : ∀ j < k, ρ j ω ≤ 1) :
    cutProd ρ k ω = 1 :=
  Finset.prod_eq_one fun j hj => cutChi_eq_one (h j (Finset.mem_range.1 hj))

/-- **The a priori bound on the support of the weight.**  If the weight does not vanish then
every ratio is `< 2`: the bootstrap's own hypothesis holds *pathwise*, with the constant `2`
of the profile's gap. -/
theorem lt_two_of_cutProd_ne_zero {ρ : ℕ → Ω → ℝ} {k j : ℕ} {ω : Ω} (hj : j < k)
    (h : cutProd ρ k ω ≠ 0) : ρ j ω < 2 := by
  by_contra hc
  exact h (Finset.prod_eq_zero (Finset.mem_range.2 hj) (cutChi_eq_zero (not_lt.1 hc)))

/-! #### The derivative, and the a priori bound on *its* support -/

/-- The `j`-th summand of the product rule for `cutProd`. -/
noncomputable def cutProdTerm (r : ℕ → ℝ) (r' : ℕ → ℝ) (k j : ℕ) : ℝ :=
  (∏ i ∈ (Finset.range k).erase j, cutChi (r i)) * (cutChiD (r j) * r' j)

/-- **`cutProd` is differentiable along any curve along which the ratios are**, with the
product rule as its derivative.  Only `C¹` of the profile is used. -/
theorem hasDerivAt_cutProd {k : ℕ} {R : ℕ → ℝ → ℝ} {r' : ℕ → ℝ} {x : ℝ}
    (h : ∀ j ∈ Finset.range k, HasDerivAt (R j) (r' j) x) :
    HasDerivAt (fun y => ∏ j ∈ Finset.range k, cutChi (R j y))
      (∑ j ∈ Finset.range k, cutProdTerm (fun i => R i x) r' k j) x := by
  have hcomp : ∀ j ∈ Finset.range k,
      HasDerivAt (fun y => cutChi (R j y)) (cutChiD (R j x) * r' j) x := by
    intro j hj
    exact (hasDerivAt_cutChi (R j x)).comp x (h j hj)
  have key := HasDerivAt.fun_finsetProd (u := Finset.range k)
    (f := fun j y => cutChi (R j y)) (f' := fun j => cutChiD (R j x) * r' j) hcomp
  refine key.congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cutProdTerm, smul_eq_mul]

/-- **⭐ The key datum of route (A′): on the support of each `∇χ` term the a priori bound
holds pathwise, and with *room*.**

If the `j`-th summand of the product rule does not vanish then the `j`-th ratio lies strictly
inside the profile's gap, `1 < r j < 2`, and **every** ratio of the product is `< 2`.  So the
transition-band term of the Stein computation may be estimated with the bootstrap's own bound
already available for every sample point of its support — no exceptional set, no truncation.
-/
theorem gap_of_cutProdTerm_ne_zero {k j : ℕ} {r r' : ℕ → ℝ}
    (h : cutProdTerm r r' k j ≠ 0) :
    (1 < r j ∧ r j < 2) ∧ ∀ i < k, r i < 2 := by
  rw [cutProdTerm] at h
  have hprod : (∏ i ∈ (Finset.range k).erase j, cutChi (r i)) ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hD : cutChiD (r j) ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have h1 : 1 < r j := by
    by_contra hc
    exact hD (cutChiD_eq_zero_left (not_lt.1 hc))
  have h2 : r j < 2 := by
    by_contra hc
    exact hD (cutChiD_eq_zero_right (not_lt.1 hc))
  refine ⟨⟨h1, h2⟩, fun i hi => ?_⟩
  by_cases hij : i = j
  · exact hij ▸ h2
  · by_contra hc
    exact hprod (Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij, Finset.mem_range.2 hi⟩)
      (cutChi_eq_zero (not_lt.1 hc)))

/-- **The derivative of the weight is bounded** by `C_χ = 15/8` times the total variation of
the ratios — the second boundedness hypothesis of `RBM.Gauss.MatrixStein.stein`.  The bound
uses `|χ| ≤ 1` on the untouched factors and `|χ'| ≤ 15/8` (`RBM.Cutoff.abs_cutChiD_le`). -/
theorem abs_derivProd_le (k : ℕ) (r r' : ℕ → ℝ) :
    |∑ j ∈ Finset.range k, cutProdTerm r r' k j| ≤ 15 / 8 * ∑ j ∈ Finset.range k, |r' j| := by
  have hterm : ∀ j ∈ Finset.range k, |cutProdTerm r r' k j| ≤ 15 / 8 * |r' j| := by
    intro j _
    rw [cutProdTerm, abs_mul, abs_mul]
    have hp : |∏ i ∈ (Finset.range k).erase j, cutChi (r i)| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => cutChi_nonneg _)]
      exact Finset.prod_le_one₀ (fun _ _ => cutChi_nonneg _) (fun _ _ => cutChi_le_one _)
    have hd : |cutChiD (r j)| ≤ 15 / 8 := abs_cutChiD_le _
    have h0 : (0 : ℝ) ≤ |r' j| := abs_nonneg _
    calc |∏ i ∈ (Finset.range k).erase j, cutChi (r i)| * (|cutChiD (r j)| * |r' j|)
        ≤ 1 * (15 / 8 * |r' j|) := by
          refine mul_le_mul hp (by nlinarith) (by positivity) (by norm_num)
      _ = 15 / 8 * |r' j| := by ring
  calc |∑ j ∈ Finset.range k, cutProdTerm r r' k j|
      ≤ ∑ j ∈ Finset.range k, |cutProdTerm r r' k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, 15 / 8 * |r' j| := Finset.sum_le_sum hterm
    _ = 15 / 8 * ∑ j ∈ Finset.range k, |r' j| := by rw [Finset.mul_sum]

end SmoothWeight

/-! ### 5. The weight at the net of (5.46), and the reduction of `condMoment`

The abstract weight of §4 is instantiated at the net points `w_j = s_N + j/m_N`, with the
ratio `J_{w_j}/Λ_{w_j}` at the bootstrap's own a priori level `Λ`.  Two facts then reduce
`RBM.CutHypTheta.CutHypCond.condMoment` — an integral **restricted to the prefix event** — to
an **unconditional** integral against the weight:

* `prefixEvent … ⊆ prefNet …` and `prefW = 1` on `prefNet`, so `1_{prefixEvent} ≤ prefW`;
* `prefNet` is a *finite* intersection, hence measurable as soon as the functional is —
  no continuity of the paths, no `RBM.Gauss.measCore`-style argument.

`condMoment_of_weightedMoment` is the reduction.  Its conclusion is the `condMoment` field of
`RBM.CutHypTheta.CutHypCond` **verbatim**, so the two producers of §9′ of
`RBM1D/Gauss/CutHypTheta.lean` apply unchanged: see §7.
-/

section Reduction

open MomentDuhamelCut CutHypTheta Cutoff

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The ratio family of route (A′): the functional at the net points of index `< k`, read in
units of the a priori level `Λ`. -/
noncomputable def netRatio (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ) (Λ : ℕ → ℝ → ℝ) (N j : ℕ)
    (ω : Ω) : ℝ :=
  J N (cutNetPt s mesh N j) ω / Λ N (cutNetPt s mesh N j)

/-- **The smooth prefix weight of route (A′)**, at the net of (5.46). -/
noncomputable def prefW (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ) (Λ : ℕ → ℝ → ℝ) (N k : ℕ)
    (ω : Ω) : ℝ :=
  cutProd (netRatio J s mesh Λ N) k ω

/-- **The finite event the weight sees**: the a priori bound at the net points of index `< k`
only.  Unlike `RBM.CutHypTheta.prefixEvent` this is a finite intersection, hence measurable as
soon as the functional is (`measurableSet_prefNet`); it is `RBM.CutHypTheta.netGoodLt` with a
`u`-dependent level and with `≤` in place of `<`. -/
def prefNet (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ) (Λ : ℕ → ℝ → ℝ) (N k : ℕ) : Set Ω :=
  {ω | ∀ j < k, J N (cutNetPt s mesh N j) ω ≤ Λ N (cutNetPt s mesh N j)}

variable {J : ℕ → ℝ → Ω → ℝ} {s mesh : ℕ → ℝ} {Λ : ℕ → ℝ → ℝ} {N k : ℕ} {ω : Ω}

omit [MeasurableSpace Ω] in
theorem prefW_nonneg : 0 ≤ prefW J s mesh Λ N k ω := cutProd_nonneg _ _ _

omit [MeasurableSpace Ω] in
theorem prefW_le_one : prefW J s mesh Λ N k ω ≤ 1 := cutProd_le_one _ _ _

omit [MeasurableSpace Ω] in
/-- Earlier net points lie in the window `[s_N, w_k]`. -/
theorem cutNetPt_mem_Icc (hm : 0 < mesh N) {j : ℕ} (hjk : j ≤ k) :
    cutNetPt s mesh N j ∈ Set.Icc (s N) (cutNetPt s mesh N k) := by
  have hR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hpos : (0 : ℝ) ≤ (j : ℝ) / mesh N := by positivity
  refine ⟨by simp only [cutNetPt]; linarith, ?_⟩
  simp only [cutNetPt]
  gcongr

omit [MeasurableSpace Ω] in
/-- **The prefix event is contained in the finite net event.** -/
theorem prefixEvent_subset_prefNet (hm : 0 < mesh N) :
    prefixEvent J s Λ N (cutNetPt s mesh N k) ⊆ prefNet J s mesh Λ N k :=
  fun _ hω _ hj => hω _ (cutNetPt_mem_Icc hm hj.le)

omit [MeasurableSpace Ω] in
/-- **⭐ The weight is `1` on the finite net event** — hence, by
`prefixEvent_subset_prefNet`, on the prefix event.  This is what replaces "restrict the
integral". -/
theorem prefW_eq_one_of_mem_prefNet (hΛ : ∀ j < k, 0 < Λ N (cutNetPt s mesh N j))
    (hω : ω ∈ prefNet J s mesh Λ N k) : prefW J s mesh Λ N k ω = 1 :=
  cutProd_eq_one fun j hj => (div_le_one (hΛ j hj)).2 (hω j hj)

omit [MeasurableSpace Ω] in
/-- **The a priori bound on the support of the weight**, pathwise: if the weight does not
vanish then `J_{w_j} ≤ 2 Λ_{w_j}` at every earlier net point. -/
theorem le_two_mul_of_prefW_ne_zero {j : ℕ} (hjk : j < k)
    (hΛ : 0 < Λ N (cutNetPt s mesh N j)) (h : prefW J s mesh Λ N k ω ≠ 0) :
    J N (cutNetPt s mesh N j) ω ≤ 2 * Λ N (cutNetPt s mesh N j) :=
  le_of_lt (by
    have := lt_two_of_cutProd_ne_zero (ρ := netRatio J s mesh Λ N) hjk h
    rw [netRatio, div_lt_iff₀ hΛ] at this
    linarith)

theorem measurableSet_prefNet (hJ : ∀ u : ℝ, Measurable fun ω => J N u ω) :
    MeasurableSet (prefNet J s mesh Λ N k) := by
  have hrw : prefNet J s mesh Λ N k
      = ⋂ j ∈ (Finset.range k : Finset ℕ),
          {ω | J N (cutNetPt s mesh N j) ω ≤ Λ N (cutNetPt s mesh N j)} := by
    ext x; simp [prefNet]
  rw [hrw]
  exact MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ =>
    measurableSet_le (hJ _) measurable_const

/-! #### The measure-theoretic core -/

/-- **The conditional integral is dominated by the weighted unconditional one.**

`A ⊆ G`, `G` measurable, `W ≥ 0` everywhere and `W ≥ 1` on `G`, the integrand nonnegative:
then `∫_A f ≤ ∫ W f`.  No measurability of `A` is used — only of the *finite* event `G`. -/
theorem setIntegral_le_integral_weight {P : Measure Ω} {A G : Set Ω} {W f : Ω → ℝ}
    (hAG : A ⊆ G) (hG : MeasurableSet G) (hf : ∀ x, 0 ≤ f x) (hW0 : ∀ x, 0 ≤ W x)
    (hWG : ∀ x ∈ G, 1 ≤ W x) (hfi : Integrable f P) (hi : Integrable (fun x => W x * f x) P) :
    ∫ x in A, f x ∂P ≤ ∫ x, W x * f x ∂P := by
  have h1 : ∫ x in A, f x ∂P ≤ ∫ x in G, f x ∂P :=
    setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hf)
      (Filter.Eventually.of_forall hAG)
  have h2 : ∫ x in G, f x ∂P = ∫ x, G.indicator f x ∂P := (integral_indicator hG).symm
  have h3 : ∫ x, G.indicator f x ∂P ≤ ∫ x, W x * f x ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall
      (Set.indicator_nonneg fun x _ => hf x)) hi (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
      nlinarith [hf x, hWG x hx]
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (hW0 x) (hf x)
  rw [h2] at h1
  linarith

/-! #### Integrability: for free, from the truncation and the weight

Both factors are bounded — `|Φ| ≤ 1` and `|χ(J/θ)J| ≤ 2θ` — so on a finite measure the only
input is measurability of the functional.  This is `RBM.MomentDuhamelCut.integrable_cutTrunc_pow`
with the weight carried along. -/

theorem aestronglyMeasurable_prefW {P : Measure Ω}
    (hJ : ∀ u : ℝ, AEStronglyMeasurable (fun ω => J N u ω) P) :
    AEStronglyMeasurable (fun ω => prefW J s mesh Λ N k ω) P := by
  have hcont : Continuous cutChi := differentiable_cutChi.continuous
  have h := Finset.aestronglyMeasurable_prod (μ := P) (Finset.range k)
    (f := fun j ω => cutChi (netRatio J s mesh Λ N j ω))
    (fun j _ => (hcont.comp (continuous_id.div_const
      (Λ N (cutNetPt s mesh N j)))).comp_aestronglyMeasurable (hJ (cutNetPt s mesh N j)))
  have hEq : (fun ω => prefW J s mesh Λ N k ω)
      = ∏ j ∈ Finset.range k, (fun ω => cutChi (netRatio J s mesh Λ N j ω)) := by
    funext x; simp [prefW, cutProd, Finset.prod_apply]
  rw [hEq]
  exact h

theorem integrable_abs_cutTrunc_pow {P : Measure Ω} [IsFiniteMeasure P] {g : Ω → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (hg0 : ∀ ω, 0 ≤ g ω) (hg : AEStronglyMeasurable g P) (q : ℕ) :
    Integrable (fun ω => |cutTrunc θ (g ω)| ^ q) P := by
  refine Integrable.mono' (integrable_const ((2 * θ) ^ q))
    (((continuous_abs.comp (continuous_cutTrunc θ)).pow q).comp_aestronglyMeasurable hg)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ (hg0 ω)) q

theorem integrable_prefW_mul {P : Measure Ω} [IsFiniteMeasure P] {v θ : ℝ} (hθ : 0 < θ)
    (hJ0 : ∀ u ω, 0 ≤ J N u ω) (hJ : ∀ u : ℝ, AEStronglyMeasurable (fun ω => J N u ω) P)
    (q : ℕ) :
    Integrable (fun ω => prefW J s mesh Λ N k ω * |cutTrunc θ (J N v ω)| ^ q) P := by
  refine Integrable.mono' (integrable_const ((2 * θ) ^ q))
    ((aestronglyMeasurable_prefW hJ).mul
      (((continuous_abs.comp (continuous_cutTrunc θ)).pow q).comp_aestronglyMeasurable (hJ v)))
    (Filter.Eventually.of_forall fun ω => ?_)
  have hb : |cutTrunc θ (J N v ω)| ^ q ≤ (2 * θ) ^ q :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ (hJ0 v ω)) q
  have h0 : (0 : ℝ) ≤ |cutTrunc θ (J N v ω)| ^ q := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg prefW_nonneg,
    abs_of_nonneg h0]
  calc prefW J s mesh Λ N k ω * |cutTrunc θ (J N v ω)| ^ q
      ≤ 1 * |cutTrunc θ (J N v ω)| ^ q :=
        mul_le_mul_of_nonneg_right prefW_le_one h0
    _ = |cutTrunc θ (J N v ω)| ^ q := one_mul _
    _ ≤ (2 * θ) ^ q := hb

end Reduction

/-! ### 6. The ℓ^q soft maximum, and the weight route (A′) actually uses

§4's *product* of cutoffs, `∏_{j<k} ∏_a χ(…)`, has one defect: its derivative is a sum over
**all** pairs `(j, a)`, and the net has `N^{Ccard}` points while the loop index runs over `L²`
values, so the cross terms carry a factor of the cardinality.  §4 is kept because its support
statements (`gap_of_cutProdTerm_ne_zero`) are the ones that say *where* the a priori bound may
be used, but the weight of route (A′) is built from a single cutoff applied to an **ℓ^q soft
maximum** of the same ratios:

`J̃_k := (∑_{j<k} ∑_a (|(L-K)_{u_j,a}|/T_{u_j,a})^q)^{1/q}`,  `q = 2r ≍ log N`,
`w_k := χ(J̃_k/(κΘ))`.

Three facts make this the right object, and all three are compiled below.

1. **`J̃` is the maximum up to `e^{O(1)}`.**  `le_softMax` gives `max ≤ J̃`; `softMax_le` gives
   `J̃ ≤ (card)^{1/q}·max`; and `rpow_card_le_exp_one` calibrates `q`: if the family has at
   most `N^A` members and `q = 2⌈A log N⌉` then `(card)^{1/q} ≤ e`.  So `κ := e` suffices, and
   the level inside the cutoff is `eΘ` rather than `Θ` — an `O(1)` change of constant, **not**
   a power of `N`.
2. **The derivative has no cardinality loss.**  `hasDerivAt_softMax` is the chain rule, and
   `abs_deriv_softMax_le` is the estimate: the derivative of `J̃` is `J̃` times a *convex
   combination* of the logarithmic derivatives of the entries, so a pointwise bound
   `|∂ρ_i| ≤ Λ·|ρ_i|` on the entries gives `|∂J̃| ≤ Λ·J̃` with **no** factor of the number of
   entries.  This is the estimate the product weight of §4 cannot deliver.
3. **`χ` never has to be differentiated at `J̃ = 0`.**  `χ' = 0` on `(-∞,1]`, so the weight is
   locally constant near `J̃ = 0` and the `y ↦ y^{1/q}` singularity at the origin is invisible:
   `hasDerivAt_softW` only needs `0 < ∑ ρ_i^q`, which `softW_deriv_eq_zero_of_small` shows is
   automatic wherever the derivative is not already `0`.
-/

section SoftMax

variable {ι : Type*}

/-- **The ℓ^q soft maximum**, at the even order `q = 2r` (so that `x ↦ x^q` is a polynomial and
no absolute value is differentiated). -/
noncomputable def softMax (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) : ℝ :=
  (∑ i ∈ S, ρ i ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)))

theorem even_pow_nonneg (x : ℝ) (r : ℕ) : 0 ≤ x ^ (2 * r) := by
  rw [pow_mul]; positivity

theorem sum_even_pow_nonneg (S : Finset ι) (ρ : ι → ℝ) (r : ℕ) :
    0 ≤ ∑ i ∈ S, ρ i ^ (2 * r) :=
  Finset.sum_nonneg fun _ _ => even_pow_nonneg _ _

theorem softMax_nonneg (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) : 0 ≤ softMax r S ρ :=
  Real.rpow_nonneg (sum_even_pow_nonneg _ _ _) _

theorem abs_even_pow (x : ℝ) (r : ℕ) : |x| ^ (2 * r) = x ^ (2 * r) := by
  rw [← abs_pow, abs_of_nonneg (even_pow_nonneg x r)]

/-- `(|x|^{2r})^{1/(2r)} = |x|`. -/
theorem rpow_inv_even_pow {r : ℕ} (hr : 1 ≤ r) (x : ℝ) :
    ((|x| ^ (2 * r) : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) = |x| := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  rw [← Real.rpow_natCast |x| (2 * r), ← Real.rpow_mul (abs_nonneg x)]
  push_cast
  rw [mul_one_div, div_self hr0.ne', Real.rpow_one]

/-- **The soft maximum dominates the maximum.** -/
theorem le_softMax {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {i : ι} (hi : i ∈ S) :
    |ρ i| ≤ softMax r S ρ := by
  have h1 : |ρ i| ^ (2 * r) ≤ ∑ j ∈ S, ρ j ^ (2 * r) := by
    rw [abs_even_pow]
    exact Finset.single_le_sum (fun j _ => even_pow_nonneg _ _) hi
  have h2 := Real.rpow_le_rpow (even_pow_nonneg |ρ i| r) h1
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)))
  rwa [rpow_inv_even_pow hr] at h2

/-- **The soft maximum is the maximum up to `(card)^{1/q}`.** -/
theorem softMax_le {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ S, |ρ i| ≤ M) :
    softMax r S ρ ≤ ((S.card : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) * M := by
  have hsum : ∑ i ∈ S, ρ i ^ (2 * r) ≤ (S.card : ℝ) * M ^ (2 * r) := by
    have := Finset.sum_le_card_nsmul S (fun i => ρ i ^ (2 * r)) (M ^ (2 * r)) fun i hi => by
      rw [← abs_even_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (h i hi) _
    simpa [nsmul_eq_mul] using this
  have h2 := Real.rpow_le_rpow (sum_even_pow_nonneg S ρ r) hsum
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)))
  refine h2.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (even_pow_nonneg M r)]
  congr 1
  rw [← abs_of_nonneg hM, rpow_inv_even_pow hr, abs_of_nonneg hM]

/-- **The calibration `q ≍ log N`.**  If the family has at most `N^A` members then the loss
`(card)^{1/q}` of `softMax_le` is at most `e` as soon as `q ≥ A log N`.  So the soft maximum
may be used in place of the maximum at the price of a *constant*. -/
theorem rpow_card_le_exp_one {A c q : ℝ} (hc0 : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    (hcard : c ≤ (N : ℝ) ^ A) (hA : 0 < A) (hq : A * Real.log N ≤ q) :
    c ^ ((1 : ℝ) / q) ≤ Real.exp 1 := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hlogc : Real.log c ≤ A * Real.log N := by
    have h := Real.log_le_log hc0 hcard
    rwa [Real.log_rpow (by linarith)] at h
  rw [Real.rpow_def_of_pos hc0]
  refine Real.exp_le_exp.2 ?_
  rw [mul_one_div, div_le_one hq0]
  linarith

/-! #### The derivative: a convex combination, hence no cardinality loss -/

/-- The derivative of the soft maximum, at a point where the sum is positive. -/
theorem hasDerivAt_softMax {r : ℕ} {S : Finset ι} {R : ι → ℝ → ℝ} {r' : ι → ℝ} {x : ℝ}
    (h : ∀ i ∈ S, HasDerivAt (R i) (r' i) x)
    (hY : 0 < ∑ i ∈ S, R i x ^ (2 * r)) :
    HasDerivAt (fun y => softMax r S (fun i => R i y))
      ((∑ i ∈ S, ((2 * r : ℕ) : ℝ) * R i x ^ (2 * r - 1) * r' i) *
        ((1 : ℝ) / (2 * (r : ℝ))) *
        (∑ i ∈ S, R i x ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1)) x := by
  have hsum : HasDerivAt (fun y => ∑ i ∈ S, R i y ^ (2 * r))
      (∑ i ∈ S, ((2 * r : ℕ) : ℝ) * R i x ^ (2 * r - 1) * r' i) x := by
    have hcomp : ∀ i ∈ S, HasDerivAt (fun y => R i y ^ (2 * r))
        (((2 * r : ℕ) : ℝ) * R i x ^ (2 * r - 1) * r' i) x :=
      fun i hi => by simpa using (h i hi).fun_pow (2 * r)
    have key := HasDerivAt.fun_sum (u := S) (A := fun i y => R i y ^ (2 * r))
      (A' := fun i => ((2 * r : ℕ) : ℝ) * R i x ^ (2 * r - 1) * r' i) hcomp
    exact key
  exact hsum.rpow_const (Or.inl hY.ne')

/-- **⭐⭐ The derivative of the soft maximum is bounded with no cardinality loss.**

If every entry satisfies the *logarithmic* bound `|∂ρ_i| ≤ Λ|ρ_i|` then `|∂J̃| ≤ Λ J̃`.  The
reason is that `∂J̃/J̃` is a convex combination `∑_i λ_i ∂ρ_i/ρ_i` with `λ_i = ρ_i^q/∑ρ_j^q`,
so no factor of the *number* of entries can appear — which is exactly what the product weight
of §4 fails to achieve. -/
theorem abs_deriv_softMax_le {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ ρ' : ι → ℝ} {Λ : ℝ}
    (h : ∀ i ∈ S, |ρ' i| ≤ Λ * |ρ i|) (hY : 0 < ∑ i ∈ S, ρ i ^ (2 * r)) :
    |(∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i) * ((1 : ℝ) / (2 * (r : ℝ))) *
        (∑ i ∈ S, ρ i ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1)|
      ≤ Λ * softMax r S ρ := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set Y : ℝ := ∑ i ∈ S, ρ i ^ (2 * r) with hYdef
  -- the numerator is at most `2r · Λ · Y`
  have hnum : |∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i|
      ≤ (2 * (r : ℝ)) * (Λ * Y) := by
    have hbd : ∀ i ∈ S, |((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i|
        ≤ (2 * (r : ℝ)) * (Λ * ρ i ^ (2 * r)) := by
      intro i hi
      have hcast : |((2 * r : ℕ) : ℝ)| = 2 * (r : ℝ) := by
        rw [Nat.cast_mul]; simp [abs_of_nonneg, hr0.le]
      rw [abs_mul, abs_mul, hcast]
      have hpow : |ρ i ^ (2 * r - 1)| = |ρ i| ^ (2 * r - 1) := (abs_pow _ _)
      rw [hpow]
      have hstep : |ρ i| ^ (2 * r - 1) * |ρ' i| ≤ |ρ i| ^ (2 * r - 1) * (Λ * |ρ i|) :=
        mul_le_mul_of_nonneg_left (h i hi) (by positivity)
      have hid : |ρ i| ^ (2 * r - 1) * (Λ * |ρ i|) = Λ * ρ i ^ (2 * r) := by
        have hcnt : 2 * r - 1 + 1 = 2 * r := by omega
        calc |ρ i| ^ (2 * r - 1) * (Λ * |ρ i|)
            = Λ * (|ρ i| ^ (2 * r - 1) * |ρ i| ^ 1) := by ring
          _ = Λ * |ρ i| ^ (2 * r) := by rw [← pow_add, hcnt]
          _ = Λ * ρ i ^ (2 * r) := by rw [abs_even_pow]
      calc 2 * (r : ℝ) * |ρ i| ^ (2 * r - 1) * |ρ' i|
          = 2 * (r : ℝ) * (|ρ i| ^ (2 * r - 1) * |ρ' i|) := by ring
        _ ≤ 2 * (r : ℝ) * (|ρ i| ^ (2 * r - 1) * (Λ * |ρ i|)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = 2 * (r : ℝ) * (Λ * ρ i ^ (2 * r)) := by rw [hid]
    calc |∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i|
        ≤ ∑ i ∈ S, |((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, (2 * (r : ℝ)) * (Λ * ρ i ^ (2 * r)) := Finset.sum_le_sum hbd
      _ = (2 * (r : ℝ)) * (Λ * Y) := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- `Y^{1/(2r)-1} · Y = Y^{1/(2r)} = J̃`
  have hYpow : Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1) * Y = softMax r S ρ := by
    have h1 : Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1) * Y ^ (1 : ℝ)
        = Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1 + 1) := (Real.rpow_add hY _ _).symm
    rw [Real.rpow_one] at h1
    rw [softMax, ← hYdef, h1, sub_add_cancel]
  have hYp0 : 0 ≤ Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1) := Real.rpow_nonneg hY.le _
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ)/(2*(r:ℝ))),
    abs_of_nonneg hYp0]
  calc |∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i| *
        ((1 : ℝ) / (2 * (r : ℝ))) * Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1)
      ≤ (2 * (r : ℝ)) * (Λ * Y) * ((1 : ℝ) / (2 * (r : ℝ))) *
          Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1) := by
        gcongr
    _ = Λ * (Y ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1) * Y) := by
        field_simp
    _ = Λ * softMax r S ρ := by rw [hYpow]

end SoftMax

/-! #### The soft-max weight, and where the a priori bound may be used -/

section SoftWeight

variable {ι : Type*}

open Cutoff

/-- **The weight of route (A′)**: one cutoff, applied to the ℓ^q soft maximum. -/
noncomputable def softW (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) (Θ : ℝ) : ℝ :=
  cutChi (softMax r S ρ / Θ)

theorem softW_nonneg (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) (Θ : ℝ) : 0 ≤ softW r S ρ Θ :=
  cutChi_nonneg _

theorem softW_le_one (r : ℕ) (S : Finset ι) (ρ : ι → ℝ) (Θ : ℝ) : softW r S ρ Θ ≤ 1 :=
  cutChi_le_one _

/-- **⭐ The weight is `1` where the a priori bound holds — at the level `κΛ`, `κ = e`.**

`softMax_le` costs `(card)^{1/q}`, so the cutoff has to sit at `κΛ` rather than `Λ`; by
`rpow_card_le_exp_one` the calibration `q ≥ A log N` makes `κ = e` admissible when the family
has at most `N^A` members.  This is the `Θ = e·Λ` of the ticket. -/
theorem one_le_softW {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {Λ κ : ℝ} (hΛ : 0 < Λ)
    (hκ0 : 0 < κ) (hκ : ((S.card : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) ≤ κ)
    (h : ∀ i ∈ S, |ρ i| ≤ Λ) :
    1 ≤ softW r S ρ (κ * Λ) := by
  have hcard : softMax r S ρ ≤ ((S.card : ℝ)) ^ ((1 : ℝ) / (2 * (r : ℝ))) * Λ :=
    softMax_le hr hΛ.le h
  have hle : softMax r S ρ ≤ κ * Λ :=
    hcard.trans (mul_le_mul_of_nonneg_right hκ hΛ.le)
  exact le_of_eq (cutChi_eq_one ((div_le_one (by positivity)).2 hle)).symm

/-- **⭐ The a priori bound on the support of the weight, pathwise and with no cardinality
loss.**  If the weight does not vanish then *every* entry is `≤ 2Θ`, because the soft maximum
dominates the maximum (`le_softMax`).  This is the datum the `∇χ` term of the Stein
computation consumes. -/
theorem abs_le_two_mul_of_softW_ne_zero {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ}
    {Θ : ℝ} (hΘ : 0 < Θ) (hne : softW r S ρ Θ ≠ 0) {i : ι} (hi : i ∈ S) :
    |ρ i| ≤ 2 * Θ :=
  (le_softMax hr hi).trans (MomentDuhamelCut.le_two_mul_of_cutChi_ne_zero hΘ hne)

/-- The weight is continuous in the soft maximum, hence measurable in `ω` once the entries
are; and it is **locally constant near `J̃ = 0`**, so the `y ↦ y^{1/q}` singularity of the
soft maximum at the origin is never differentiated (`cutChiD_eq_zero_left`). -/
theorem cutChiD_softW_eq_zero {r : ℕ} {S : Finset ι} {ρ : ι → ℝ} {Θ : ℝ} (hΘ : 0 < Θ)
    (h : softMax r S ρ ≤ Θ) : cutChiD (softMax r S ρ / Θ) = 0 :=
  cutChiD_eq_zero_left ((div_le_one hΘ).2 h)

end SoftWeight

/-! ### 7. `WeightedMoment`, and `condMoment` as a theorem

`WeightedMoment` is `RBM.CutHypTheta.CutHypCond.condMoment` with the restriction to
`prefixEvent` replaced by a weight: an integral over the **whole** sample space.  That is the
entire structural content of route (A′) — Stein's identity (`RBM.Gauss.MatrixStein.stein`) is
an identity of full-measure integrals, and this is the shape it can be applied to.

The statement is **parametric in the weight**: the only properties used are `0 ≤ W ≤ 1` and
`W ≥ 1` where the a priori bound holds at the net points of index `< k`.  Both the product
weight of §4 and the soft-max weight of §6 satisfy them, so the choice of weight is a question
about the *estimate*, not about the interface.

`N₀` is uniform in the net index `k`: the `∀ k` sits **inside** the `∀ᶠ N in atTop`, exactly
as `condMoment`'s `∀ ws ∈ netFinset` does, which is why
`RBM.CutHypTheta.netGood_highProb_of_condMoment` can take its union bound over all net points
at one and the same `N₀`.
-/

section Weighted

open MomentDuhamelCut CutHypTheta MeasureTheory Cutoff

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The moment field of route (A′): unconditional, against a weight.**

Compare `RBM.CutHypTheta.CutHypCond.condMoment`, which is the same statement with
`∫ ω in prefixEvent …` in place of `∫ ω, W δ N k ω · …`.  The loss `N^{δ/2·p}` and the control
`Θ_N^{2p}` are unchanged — `RBM.CutHypTheta.condMoment_of_oneStep` produces exactly this
exponent from `RBM.Step2MomentStep.phi_arith'`. -/
def WeightedMoment (P : Measure Ω) (J : ℕ → ℝ → Ω → ℝ) (s t mesh : ℕ → ℝ)
    (lev : ℕ → ℝ → ℝ) (Θ : ℕ → ℝ) (δ₀ : ℝ) (W : ℝ → ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ k ≤ cutNetTop s t mesh N,
      ∫ ω, W δ N k ω * |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
            (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p))

variable {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ} {lev : ℕ → ℝ → ℝ}
  {Θ : ℕ → ℝ}

theorem integrable_weight_mul [IsFiniteMeasure P] {W g : Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1) (hWm : AEStronglyMeasurable W P)
    (hg0 : ∀ ω, 0 ≤ g ω) (hgm : AEStronglyMeasurable g P) (q : ℕ) :
    Integrable (fun ω => W ω * |cutTrunc θ (g ω)| ^ q) P := by
  refine Integrable.mono' (integrable_const ((2 * θ) ^ q))
    (hWm.mul (((continuous_abs.comp (continuous_cutTrunc θ)).pow q).comp_aestronglyMeasurable hgm))
    (Filter.Eventually.of_forall fun ω => ?_)
  have hb : |cutTrunc θ (g ω)| ^ q ≤ (2 * θ) ^ q :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_cutTrunc_le hθ (hg0 ω)) q
  have h0 : (0 : ℝ) ≤ |cutTrunc θ (g ω)| ^ q := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 ω), abs_of_nonneg h0]
  calc W ω * |cutTrunc θ (g ω)| ^ q ≤ 1 * |cutTrunc θ (g ω)| ^ q :=
        mul_le_mul_of_nonneg_right (hW1 ω) h0
    _ = |cutTrunc θ (g ω)| ^ q := one_mul _
    _ ≤ (2 * θ) ^ q := hb

/-- **⭐⭐ The conditional moment field of `RBM.CutHypTheta.CutHypCond` is a *theorem* of the
unconditional weighted one.**

This is the point of route (A′): the bootstrap's own hypothesis enters through a weight that
is `1` where the hypothesis holds, so **no complement of any event is ever estimated** and the
geometric amplification of §3 (`routeB_walk_vacuous`) has nothing to amplify.  The conclusion
is the `condMoment` field of `CutHypCond` verbatim.

Regularity used: only `Measurable` of the functional at each fixed time (for the *finite* net
event `prefNet`) and `AEStronglyMeasurable` of the weight.  No continuity of the paths, no
measurability of `prefixEvent`. -/
theorem condMoment_of_weightedMoment [IsFiniteMeasure P] {δ₀ : ℝ} {W : ℝ → ℕ → ℕ → Ω → ℝ}
    (hmesh : ∀ N, 0 < mesh N) (hΘ : ∀ N, 0 < Θ N) (hwin : ∀ N, s N ≤ t N)
    (hlev : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u)
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω) (hJm : ∀ (N : ℕ) (u : ℝ), Measurable fun ω => J N u ω)
    (hWm : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => W δ N k ω) P)
    (hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω) (hW1 : ∀ δ N k ω, W δ N k ω ≤ 1)
    (hWdom : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω),
      ω ∈ prefNet J s mesh (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N k → 1 ≤ W δ N k ω)
    (H : WeightedMoment P J s t mesh lev Θ δ₀ W) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ netFinset s t mesh N,
        ∫ ω in prefixEvent J s (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N ws,
          |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N ws) (J N ws ω)| ^ (2 * p) ∂P
          ≤ C * ((N : ℝ) ^ (δ / 2 * p) * Θ N ^ (2 * p)) := by
  intro δ hδ0 hδ p
  obtain ⟨C, hC0, hC⟩ := H δ hδ0 hδ p
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with N hN hN1 ws hws
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos (by linarith) _
  have hlevpos : ∀ j : ℕ, j ≤ cutNetTop s t mesh N →
      0 < (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N j) := by
    intro j hj
    have hmem : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
      netFinset_subset_Icc (hwin N) (hmesh N) _ (cutNetPt_mem_netFinset hj)
    exact mul_pos hrp (lt_of_lt_of_le (hΘ N) (hlev N _ hmem))
  obtain ⟨k, hk, rfl⟩ := exists_cutNetPt_eq hws
  have hθ : 0 < (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k) := hlevpos k hk
  have hfi : Integrable (fun ω => |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
      (J N (cutNetPt s mesh N k) ω)| ^ (2 * p)) P :=
    integrable_abs_cutTrunc_pow hθ (fun ω => hJ0 N _ ω)
      ((hJm N (cutNetPt s mesh N k)).aestronglyMeasurable) (2 * p)
  have hi : Integrable (fun ω => W δ N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
        (J N (cutNetPt s mesh N k) ω)| ^ (2 * p)) P :=
    integrable_weight_mul hθ (hW0 δ N k) (hW1 δ N k) (hWm δ N k) (fun ω => hJ0 N _ ω)
      ((hJm N (cutNetPt s mesh N k)).aestronglyMeasurable) (2 * p)
  refine le_trans (setIntegral_le_integral_weight
    (prefixEvent_subset_prefNet (Λ := fun N u => (N : ℝ) ^ (2 * δ) * lev N u) (k := k)
      (hmesh N))
    (measurableSet_prefNet (Λ := fun N u => (N : ℝ) ^ (2 * δ) * lev N u) (k := k) (hJm N))
    (fun _ => by positivity) (fun _ => hW0 δ N k _)
    (fun x hx => hWdom δ N k x hx) hfi hi) (hN k hk)

omit [MeasurableSpace Ω] in
/-- The product weight of §4 meets the three hypotheses of `condMoment_of_weightedMoment`
(`prefW_nonneg`, `prefW_le_one`, `prefW_eq_one_of_mem_prefNet`) — so route (A′) with the
product weight is an instance of the reduction. -/
theorem prefW_dominates {δ : ℝ} (hΘ : ∀ N, 0 < Θ N) (hmesh : ∀ N, 0 < mesh N)
    (hwin : ∀ N, s N ≤ t N) (hlev : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u)
    {N k : ℕ} (hk : k ≤ cutNetTop s t mesh N) (hN : 1 ≤ N) (ω : Ω)
    (hω : ω ∈ prefNet J s mesh (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N k) :
    1 ≤ prefW J s mesh (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N k ω := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos (by linarith) _
  refine le_of_eq (prefW_eq_one_of_mem_prefNet (fun j hj => ?_) hω).symm
  have hmem : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hwin N) (hmesh N) _
      (cutNetPt_mem_netFinset (le_trans hj.le hk))
  exact mul_pos hrp (lt_of_lt_of_le (hΘ N) (hlev N _ hmem))

end Weighted

/-! ### 8. Non-vacuity, and the one-step side conditions at `R > 1`

T222's `RBM.CutHypTheta.sat_StepSide` is a witness at `R = 1`, i.e. at a *collapsed* window
where `η_s = η_v`; it says nothing about the `R`-powers of (5.39)–(5.44), which are the whole
content of the accounting.  `sat_StepSide_gt_one` is the witness at an arbitrary `R ≥ 1`
(so in particular at `R > 1`, which `one_lt_ratR` shows is the generic case strictly inside
the window), and **every one of the eight constraints is met at equality** — `Ξ = x`,
`A = x^17R^10`, `ε = (x^17R^10)^{-1}`, `q = R²`, `β = (x^8R^2)^{-1}`, `γ = (x^12R^4)^{-1}`,
`Jv = x^8R^4` — so no slot is satisfied by being trivial.
-/

section Sat

open CutHypTheta Cutoff

/-- **`R = η_s/η_u > 1` strictly inside the window**, so the `R = 1` witness of T222 is the
degenerate case. -/
theorem one_lt_ratR {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hsu : s N < u) (hu : u < 1) : 1 < Step2Moment.ratR E s N u := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  rw [Step2Moment.ratR, Step2.etaT_ratio hE, lt_div_iff₀ h1u]
  linarith

/-- **⭐ The one-step side conditions of (5.39)–(5.44) are satisfiable at every `R ≥ 1`, with
all eight constraints tight.** -/
theorem sat_StepSide_gt_one {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    StepSide x R x (x ^ 17 * R ^ 10) (x ^ 17 * R ^ 10)⁻¹ (R ^ 2)
      (x ^ 8 * R ^ 2)⁻¹ (x ^ 12 * R ^ 4)⁻¹ (x ^ 8 * R ^ 4) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  exact
    { R_ge := hR
      Ξ_nonneg := hx0.le
      Ξ_le := le_rfl
      A_ge := le_rfl
      ε_nonneg := by positivity
      ε_le := by
        rw [mul_assoc, inv_mul_cancel₀ (by positivity)]
      q_nonneg := by positivity
      q_le := le_rfl
      β_nonneg := by positivity
      β_le := by rw [inv_mul_cancel₀ (by positivity)]
      γ_nonneg := by positivity
      γ_le := by rw [inv_mul_cancel₀ (by positivity)]
      Jv_nonneg := by positivity
      Jv_le := le_rfl }

/-- The same for the second pass (`RBM.Step2Near47.phi_arith_second_pass`), at `R ≥ 1`. -/
theorem sat_StepSideSharp_gt_one {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    StepSideSharp m x R x (x ^ 17 * R ^ 10) (x ^ 17 * R ^ 10)⁻¹ (2 * m⁻¹ * R ^ 2)
      (x ^ 8 * R ^ 4)⁻¹ (x ^ 12 * R ^ 6)⁻¹ (x ^ 8 * R ^ 4) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  exact
    { R_ge := hR
      Ξ_nonneg := hx0.le
      Ξ_le := le_rfl
      A_ge := le_rfl
      ε_nonneg := by positivity
      ε_le := by rw [mul_assoc, inv_mul_cancel₀ (by positivity)]
      qI_nonneg := by positivity
      qI_le := le_rfl
      β_nonneg := by positivity
      β_le := by rw [inv_mul_cancel₀ (by positivity)]
      γ_nonneg := by positivity
      γ_le := by rw [inv_mul_cancel₀ (by positivity)]
      Jv_nonneg := by positivity
      Jv_le := le_rfl }

/-- The one-step output at the `R > 1` witness, in the blunt normalization: `≤ cStep' m · x²`,
which is `RBM.CutHypTheta.condMoment_of_sq_bound`'s hypothesis shape. -/
theorem sat_stepRhs_div_gt_one {m x R : ℝ} (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R) :
    stepRhs m x R x (x ^ 17 * R ^ 10) (x ^ 17 * R ^ 10)⁻¹ (R ^ 2)
        (x ^ 8 * R ^ 2)⁻¹ (x ^ 12 * R ^ 4)⁻¹ (x ^ 8 * R ^ 4) / R ^ 4
      ≤ Step2MomentStep.cStep' m * x ^ 2 :=
  stepRhs_div_le hx hm (sat_StepSide_gt_one hx hR)

/-- A concrete instance at `x = 1`, `R = 2`: the window is genuinely non-degenerate. -/
theorem sat_StepSide_two : StepSide 1 2 1 (1 ^ 17 * 2 ^ 10) ((1 : ℝ) ^ 17 * 2 ^ 10)⁻¹ (2 ^ 2)
    ((1 : ℝ) ^ 8 * 2 ^ 2)⁻¹ ((1 : ℝ) ^ 12 * 2 ^ 4)⁻¹ (1 ^ 8 * 2 ^ 4) :=
  sat_StepSide_gt_one le_rfl one_le_two

/-! #### The weight really is a weight: it vanishes somewhere -/

/-- **The soft-max weight vanishes as soon as one entry exceeds `2Θ`** — so the interface is
not the trivial one with `W ≡ 1`, and `abs_le_two_mul_of_softW_ne_zero` is sharp. -/
theorem softW_eq_zero {ι : Type*} {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ : ι → ℝ} {Θ : ℝ}
    (hΘ : 0 < Θ) {i : ι} (hi : i ∈ S) (h : 2 * Θ ≤ |ρ i|) : softW r S ρ Θ = 0 :=
  cutChi_eq_zero (by
    rw [le_div_iff₀ hΘ]
    have := le_softMax (ρ := ρ) hr hi
    linarith)

end Sat

/-! ### 9. `APrimeHyp`: the interface of route (A′), and the `cut` fields it produces

`APrimeHyp` is `RBM.CutHypTheta.CutHypCondEv` with the one field that is not deterministic —
`condMoment`, an integral **restricted to the prefix event** — replaced by the weight and the
**unconditional** `WeightedMoment`.  Every other field is verbatim, except that `meas` asks
for `Measurable` rather than `AEStronglyMeasurable`: that is what the *finite* net event
`prefNet` needs, and `RBM.Gauss.measurable_lk` supplies it for a general `Sample`.

T232 showed the `∀ N` reading of `modulus` is unsatisfiable for a genuinely time-dependent
functional (`RBM.CutHypTheta.sat_no_cutHypCond`), so `APrimeHyp` carries the `∀ᶠ N in atTop`
reading and the chain it feeds is the `Ev` one:

`APrimeHyp → CutHypCondEv → RBM.MomentDuhamelCut.CutHypEv → MomentHypCutEv → (5.47)`.

**Nothing in this chain is a free field of route (A′) that `CutHypCondEv` did not already
have**: `WeightedMoment` *replaces* `condMoment`, it is not added to it.
-/

section APrime

open MomentDuhamelCut CutHypTheta MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}

/-- **The interface of route (A′).**  Field for field `RBM.CutHypTheta.CutHypCondEv`, with
`condMoment` replaced by a weight `W` and the unconditional `WeightedMoment`. -/
structure APrimeHyp (P : Measure Ω) (J : ℕ → ℝ → Ω → ℝ) (s t : ℕ → ℝ) (lev : ℕ → ℝ → ℝ)
    (Θ : ℕ → ℝ) where
  /-- The window is non-degenerate. -/
  window : ∀ N, s N ≤ t N
  /-- The range `0 < δ ≤ δ₀` of bootstrap margins. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  Θ_pos : ∀ N, 0 < Θ N
  /-- The truncation level dominates the control, on the window. -/
  lev_ge : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u
  /-- The state functional is nonnegative. -/
  J_nonneg : ∀ N u ω, 0 ≤ J N u ω
  /-- **`Measurable`, not merely `AEStronglyMeasurable`** — what `measurableSet_prefNet` uses. -/
  meas : ∀ (N : ℕ) (u : ℝ), Measurable fun ω => J N u ω
  /-- The mesh of the net of (5.46). -/
  mesh : ℕ → ℝ
  mesh_pos : ∀ N, 0 < mesh N
  /-- The exponent of the deterministic modulus of continuity. -/
  Kmod : ℝ
  /-- Its Hölder exponent. -/
  γ : ℝ
  γ_pos : 0 < γ
  /-- The modulus of continuity, for every `ω` and for large `N`. -/
  modulus : ∀ᶠ N : ℕ in atTop, ∀ ω : Ω, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    |J N v ω - J N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ
  /-- The net is fine enough, for large `N`. -/
  mesh_fine : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ N
  /-- The exponent of the net's cardinality. -/
  Ccard : ℝ
  /-- The net is polynomially large. -/
  card_le : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard
  /-- The exponent bounding the truncation level against the control. -/
  Clev : ℝ
  Clev_nonneg : 0 ≤ Clev
  levpoly : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
    2 * lev N ws ≤ (N : ℝ) ^ Clev * Θ N
  /-- **The weight of route (A′)**, indexed by the bootstrap margin `δ`, the scale `N` and the
  net index `k`.  Both weights of this file — the product `prefW` of §5 and the soft-max
  `softW` of §6 — fit here. -/
  W : ℝ → ℕ → ℕ → Ω → ℝ
  W_meas : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => W δ N k ω) P
  W_nonneg : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω), 0 ≤ W δ N k ω
  W_le_one : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω), W δ N k ω ≤ 1
  /-- **The weight is `≥ 1` where the a priori bound holds at the earlier net points.**  This
  is the only property of the weight the interface uses, and it is what replaces restricting
  the integral to the prefix event. -/
  W_dom : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω),
    ω ∈ prefNet J s mesh (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N k → 1 ≤ W δ N k ω
  /-- **The moment field, unconditional.**  This is the *only* field that differs from
  `RBM.CutHypTheta.CutHypCondEv`. -/
  weightedMoment : WeightedMoment P J s t mesh lev Θ δ₀ W

/-- **⭐⭐ Route (A′) produces `RBM.CutHypTheta.CutHypCondEv`** — the conditional moment field
is discharged by `condMoment_of_weightedMoment`, not assumed. -/
noncomputable def APrimeHyp.toCutHypCondEv [IsFiniteMeasure P] (H : APrimeHyp P J s t lev Θ) :
    CutHypCondEv P J s t lev Θ where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  lev_ge := H.lev_ge
  J_nonneg := H.J_nonneg
  meas := fun N u => (H.meas N u).aestronglyMeasurable
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := H.modulus
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  Clev := H.Clev
  Clev_nonneg := H.Clev_nonneg
  levpoly := H.levpoly
  condMoment := condMoment_of_weightedMoment H.mesh_pos H.Θ_pos H.window H.lev_ge H.J_nonneg
    H.meas H.W_meas H.W_nonneg H.W_le_one H.W_dom H.weightedMoment

/-- **`RBM.MomentDuhamelCut.CutHypEv` from route (A′)** — the `cut` field of `MomentHypCutEv`,
as a theorem. -/
noncomputable def APrimeHyp.toCutHypEv [IsProbabilityMeasure P] (H : APrimeHyp P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    MomentDuhamelCut.CutHypEv P J s t Θ :=
  cutHypEv_of_condMomentEv H.toCutHypCondEv hΘ1 hinit

/-- **`RBM.CutHypTheta.CutHypEv'` from route (A′)** — the shape the second pass consumes. -/
noncomputable def APrimeHyp.toCutHypEv' [IsProbabilityMeasure P] (H : APrimeHyp P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    CutHypEv' P J s t lev Θ :=
  cutHypEv'_of_condMomentEv H.toCutHypCondEv hΘ1 hinit

/-- **`J ≺ Θ` uniformly on the window, from route (A′) alone.**  This is the form T243's third
slot asks for, with `J := Ξ^{(L-K)}_{·,2}` and `Θ := A_s^{1/2}`: the statement is quantified
over an arbitrary nonnegative `J`, so the same interface serves it and the `J*` of (5.29). -/
theorem stochDom_of_aprime [IsProbabilityMeasure P] (H : APrimeHyp P J s t lev Θ)
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) :=
  stochDom_of_condMomentEv H.toCutHypCondEv hΘ1 hinit

variable {B : Band Ω} {E : ℝ}

/-- **⭐⭐⭐ `RBM.MomentDuhamelCut.MomentHypCutEv` from route (A′).**

Both of its fields are now accounted for: `init` is (2.69), and `cut` — T197's named
hypothesis, T222's `condMoment`, this ticket's target — is **produced by a theorem** from an
interface with no event-restricted field. -/
noncomputable def momentHypCutEv_of_aprime {X : Sample B} {D : ℝ}
    (H : APrimeHyp B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    MomentDuhamelCut.MomentHypCutEv X E s t D :=
  letI := B.isProbabilityMeasure
  { cut := H.toCutHypEv (Filter.Eventually.of_forall fun _ => le_rfl) hinit
    init := hinit }

/-- **(5.47) from route (A′), end to end**: `J*_{u,D} ≺ (η_s/η_u)^4` uniformly on the window,
with no named moment hypothesis left — only `WeightedMoment` and (2.69). -/
theorem jS_stochDom_of_aprime {X : Sample B} {D : ℝ}
    (H : APrimeHyp B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ)))
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 4) :=
  letI := B.isProbabilityMeasure
  MomentDuhamelCut.jS_stochDom_cutEv (momentHypCutEv_of_aprime H hinit) hE hst ht1

end APrime

/-! ### 10. The second pass from route (A′)

`RBM.CutHypTheta.MomentHypCut2` is stated against the `∀ N` interface `CutHyp'`, which T232
showed unsatisfiable for a genuinely time-dependent functional
(`RBM.CutHypTheta.sat_no_cutHyp'`).  `MomentHypCut2Ev` is it with `CutHypEv'`, and the two
consumers are reproved verbatim from the `Ev` machinery of §4 of `RBM1D/Gauss/CutHypTheta.lean`.
No new hypothesis appears: `stochDom_jSnorm2_of_bluntEv` still takes the *blunt* conclusion as
its prefix, so the sharp pass still costs no second bootstrap and no second initial condition.
-/

section Sharp2

open MomentDuhamelCut CutHypTheta MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
  {X : Sample B} {D : ℝ}

/-- **The second-pass interface, asymptotic**: `RBM.CutHypTheta.MomentHypCut2` with
`CutHypEv'` in place of `CutHyp'`. -/
structure MomentHypCut2Ev (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- The truncated moment Duhamel for `jSnorm2`, truncated at the blunt level. -/
  cut : CutHypEv' B.P (fun N u ω => Step2Near47.jSnorm2 X E D s N u ω) s t (levSharp E s)
    (fun _ => 1)

/-- **The second pass, for `J*`, from the asymptotic interface** — `stochDom_jSnorm2_of_blunt`
word for word. -/
theorem stochDom_jSnorm2_of_bluntEv (H2 : MomentHypCut2Ev X E s t D) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    (hblunt : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2Moment.jSnorm X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2Near47.jSnorm2 X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  have := B.isProbabilityMeasure
  refine stochDom_of_cutHypEv'_of_prefix H2.cut fun δ hδ0 _ => ?_
  refine prefix_of_stochDom hblunt (fun N u hu => ?_) (fun N u hu ω => ?_) hδ0
  · exact pow_pos (Step2Moment.ratR_pos hE ((H2.cut.window N).trans_lt (ht1 N))
      (hu.2.trans_lt (ht1 N))) 2
  · exact le_of_eq (jSnorm2_eq_mul X hE ((H2.cut.window N).trans_lt (ht1 N))
      (hu.2.trans_lt (ht1 N)) ω)

/-- **(5.47) sharp from the asymptotic interfaces** — `jS_stochDom_sharp_of_cut2` word for
word. -/
theorem jS_stochDom_sharp_of_cut2Ev (H2 : MomentHypCut2Ev X E s t D) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    (hblunt : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2Moment.jSnorm X E D s N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2) := by
  refine StochDom.of_subset (stochDom_jSnorm2_of_bluntEv H2 hE ht1 hblunt) fun τ hτ =>
    ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (H2.cut.window N).trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N (u : ℝ) ^ 2 :=
    pow_pos (Step2Moment.ratR_pos hE hs1 (u.2.2.trans_lt (ht1 N))) 2
  change (N : ℝ) ^ τ * 1 < Step2.jS X E D N (u : ℝ) ω / Step2Moment.ratR E s N (u : ℝ) ^ 2
  rw [mul_one, lt_div_iff₀ hR]
  exact hu

/-- **⭐ `MomentHypCut2Ev` from route (A′).**  The second `cut` field of the ticket, produced
by a theorem. -/
noncomputable def momentHypCut2Ev_of_aprime (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (H : APrimeHyp B.P (fun N u ω => Step2Near47.jSnorm2 X E D s N u ω) s t (levSharp E s)
      (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    MomentHypCut2Ev X E s t D :=
  letI := B.isProbabilityMeasure
  { cut := H.toCutHypEv' (Filter.Eventually.of_forall fun _ => le_rfl) (by
      have hfun : (fun N (_ : Unit) (ω : Ω) => Step2Near47.jSnorm2 X E D s N (s N) ω)
          = fun N (_ : Unit) (ω : Ω) => Step2Moment.jSnorm X E D s N (s N) ω := by
        funext N _ ω
        exact Step2Near47.jSnorm2_left X hE ((H.window N).trans_lt (ht1 N)) ω
      rw [hfun]
      exact hinit) }

/-- **⭐⭐⭐ (5.47) sharp, end to end from route (A′) alone.**

`J*_{u,D} ≺ (η_s/η_u)²` uniformly on the window, from two `APrimeHyp` — one per pass — and
(2.69).  **No event-restricted hypothesis and no named moment hypothesis is left**: the only
remaining input is the unconditional `WeightedMoment` of each pass. -/
theorem jS_stochDom_sharp_of_aprime (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (H1 : APrimeHyp B.P (fun N u ω => Step2Moment.jSnorm X E D s N u ω) s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1))
    (H2 : APrimeHyp B.P (fun N u ω => Step2Near47.jSnorm2 X E D s N u ω) s t (levSharp E s)
      (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2Moment.jSnorm X E D s N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N (u : ℝ) ω)
      (fun N u _ => (etaT E (s N) / etaT E (u : ℝ)) ^ 2) :=
  letI := B.isProbabilityMeasure
  jS_stochDom_sharp_of_cut2Ev (momentHypCut2Ev_of_aprime hE ht1 H2 hinit) hE ht1
    (MomentDuhamelCut.stochDom_jSnorm_cutEv (momentHypCutEv_of_aprime H1 hinit))

end Sharp2

/-! ### 11. Cauchy–Schwarz for the quadratic-variation rate

The cross term route (A′) adds to the Duhamel — `E[χ'(J̃/Θ)·Θ^{-1}·∑_α S_α ∂_α J̃ ∂_α|Ψ_u|^{2p}]`,
the mixed covariation of the earlier times `u_j` with the current time `u` — is split by
Cauchy–Schwarz into two **same-time** quadratic-variation rates.  `RBM.Gauss.quadVar` is that
rate (`∑_α S_α ‖∂_α F‖²`, `RBM1D/Gauss/MomentGronwall.lean`), and this is the inequality that
performs the split.  It was not in the repository.
-/

section CauchySchwarz

open Gauss

/-- **Cauchy–Schwarz for `RBM.Gauss.quadVar`.**  The weighted pairing of two coordinate
gradients is at most the geometric mean of their quadratic-variation rates.  This is the step
that turns a mixed-time covariation into two same-time rates. -/
theorem sum_gvar_mul_le_sqrt_quadVar (d : Dims) (N : ℕ)
    (F G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
        (‖coordD1 d N F M q‖ * ‖coordD1 d N G M q‖)
      ≤ √(quadVar d N F M) * √(quadVar d N G M) := by
  set a : d.Idx N × d.Idx N × Bool → ℝ :=
    fun q => √((gvar d (crd d N q) : ℝ)) * ‖coordD1 d N F M q‖ with ha
  set b : d.Idx N × d.Idx N × Bool → ℝ :=
    fun q => √((gvar d (crd d N q) : ℝ)) * ‖coordD1 d N G M q‖ with hb
  have hgv : ∀ q, (0 : ℝ) ≤ (gvar d (crd d N q) : ℝ) := fun q => (gvar d (crd d N q)).2
  have hsq : ∀ q, √((gvar d (crd d N q) : ℝ)) ^ 2 = (gvar d (crd d N q) : ℝ) :=
    fun q => Real.sq_sqrt (hgv q)
  have hA : ∑ q ∈ usedCoord d N, a q ^ 2 = quadVar d N F M := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ha]
    rw [mul_pow, hsq q]
  have hB : ∑ q ∈ usedCoord d N, b q ^ 2 = quadVar d N G M := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hb]
    rw [mul_pow, hsq q]
  have hprod : ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
      (‖coordD1 d N F M q‖ * ‖coordD1 d N G M q‖) = ∑ q ∈ usedCoord d N, a q * b q := by
    refine Finset.sum_congr rfl fun q _ => ?_
    have hmm : √((gvar d (crd d N q) : ℝ)) * √((gvar d (crd d N q) : ℝ))
        = (gvar d (crd d N q) : ℝ) := Real.mul_self_sqrt (hgv q)
    have hexp : a q * b q = (gvar d (crd d N q) : ℝ) *
        (‖coordD1 d N F M q‖ * ‖coordD1 d N G M q‖) := by
      simp only [ha, hb]
      calc (√((gvar d (crd d N q) : ℝ)) * ‖coordD1 d N F M q‖) *
            (√((gvar d (crd d N q) : ℝ)) * ‖coordD1 d N G M q‖)
          = (√((gvar d (crd d N q) : ℝ)) * √((gvar d (crd d N q) : ℝ))) *
            (‖coordD1 d N F M q‖ * ‖coordD1 d N G M q‖) := by ring
        _ = (gvar d (crd d N q) : ℝ) * (‖coordD1 d N F M q‖ * ‖coordD1 d N G M q‖) := by
            rw [hmm]
    rw [hexp]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (usedCoord d N) a b
  rw [hA, hB] at hcs
  have hnn : 0 ≤ ∑ q ∈ usedCoord d N, a q * b q := by
    refine Finset.sum_nonneg fun q _ => ?_
    rw [ha, hb]
    positivity
  rw [hprod, ← Real.sqrt_mul (quadVar_nonneg F M)]
  calc ∑ q ∈ usedCoord d N, a q * b q
      = √((∑ q ∈ usedCoord d N, a q * b q) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ √(quadVar d N F M * quadVar d N G M) := Real.sqrt_le_sqrt hcs

end CauchySchwarz

/-! ### 12. The interface with `RBM1D/Gauss/APrimeTestFun.lean` (T250: **both items settled**)

Two statements turn `WeightedMoment` from an interface into a theorem.  Both are now in
`RBM1D/Gauss/APrimeTestFun.lean`, which imports this file, so the names below are *downstream*
and cannot be cited by a `theorem` here — only by the assembly, which lives there.

**⚠ The target this section first asked for was refuted.**  It asked for a **purely
multiplicative** ("logarithmic") derivative bound `‖∂_α F‖ ≤ Λ‖F‖`, on the reasoning that an
absolute bound would reintroduce the `(card)^{1/q}` of `softMax_le`.  That shape is **false**
on the loop error, and not for a quantitative reason: at a Hermitian `M` where `L = K` the
right-hand side vanishes while `∂_α(L-K) = ∂_α L` has no reason to
(`RBM.Gauss.not_coordD1_le_mul_norm`, and abstractly
`RBM.Step2Bootstrap.not_logDerivBound_of_zero`).  `∂_α K = 0` makes this **worse**, not better.
So `LogDerivBound` below, and `abs_deriv_softMax_le_of_logDerivBound` /
`logDerivBound_gives_softMax` that consume it, are correct statements with **no instance on
the loops**; they are kept only because they are what `abs_deriv_softMax_le` literally says.

**(i) The bound the model does supply is *affine*:**

    ‖∂_α F‖ ≤ 0 · ‖F‖ + a₁ · ‖B_α‖        (`RBM.Gauss.abs_coordD1_le_affine`)

and the corresponding estimate on the soft maximum is
`RBM.Step2Bootstrap.abs_deriv_softMax_le_affine`:

    (∀ i ∈ S, |ρ' i| ≤ Λ|ρ i| + K) → |∂J̃| ≤ Λ · J̃ + (card)^{1/(2r)} · K.

⭐ **What the soft maximum actually buys is therefore not the factor `Λ` — it is the absence of
`card`.**  The naive route sends the additive part to `∑_i 2r|ρ_i|^{2r-1}K`, i.e. `card · K`;
the Hölder step `RBM.Step2Bootstrap.sum_abs_pow_pred_le` turns it into `(card)^{1/(2r)} · K`,
which `rpow_card_le_exp_one` calibrates to `e·K` at `q = 2r ≍ log N`.  **This works at `Λ = 0`,
which is the case the model is in.**  The product weight of §4 cannot do this
(`abs_derivProd_le` is a bare sum over the net).

**(ii) The `RBM.Gauss.TestFun` instance**, `RBM.Gauss.testFun_softW_mul`:

    TestFun d N (fun M => ((softW r S (fun i => ρ i M) Θ : ℝ) : ℂ) * Ψ M)

from `BddC2C (fun M => ∑ i ∈ S, ρ i M ^ (2r))` and `BddC2C Ψ`.  **This is where the soft
maximum is indispensable**: the product weight of §4 is built from `J* = max_a …`, which is
not `C¹`, so `TestFun` is unreachable for it; `J̃^{2r} = ∑_i ρ_i^{2r}` is a *polynomial* in the
entries of `Re G` and `Im G`, and `y ↦ y^{1/(2r)}` is smooth away from `0` —
`cutChiD_softW_eq_zero` records that the origin is the one place where `χ'` already vanishes,
so the singularity is never met.  T250 also checked that `ContDiff ℝ 2` is **used to the
letter** by `RBM.Gauss.hasDerivAt_integral_Phi`, so the order cannot be lowered to `C¹`.

**What is still missing** is the *model-level* instance: `BddC2C` for the concrete ratio
`ρ_{(j,a)}(M) = ‖(L-K)_{u_j,(+,-),a}(M)‖ / (Θ_N · T_{u_j,D}(a))`, with its constants pinned in
terms of `lkFun`, `band d` and `η_u`.  That lives in `RBM1D/Gauss/MomentDuhamel.lean` /
`RBM1D/Flow/Hypotheses.lean`, neither of which is writable from here.
-/

section Interface

variable {ι : Type*}

/-- **The hypothesis `abs_deriv_softMax_le` literally consumes.**

⚠ **It has no instance on the loop ratios** (T250): at a point where `ρ i = 0` but `ρ' i ≠ 0`
it is false for *every* `Λ` (`RBM.Step2Bootstrap.not_logDerivBound_of_zero`, downstream), and
`L = K` is such a point.  The shape the model supplies is the **affine** one,
`|ρ' i| ≤ Λ|ρ i| + K`, handled by `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine`.  Kept
because it is what `abs_deriv_softMax_le` says; see §12. -/
def LogDerivBound (S : Finset ι) (ρ ρ' : ι → ℝ) (Λ : ℝ) : Prop :=
  ∀ i ∈ S, |ρ' i| ≤ Λ * |ρ i|

/-- `LogDerivBound` is exactly what the cardinality-loss-free derivative estimate needs. -/
theorem abs_deriv_softMax_le_of_logDerivBound {r : ℕ} (hr : 1 ≤ r) {S : Finset ι}
    {ρ ρ' : ι → ℝ} {Λ : ℝ} (h : LogDerivBound S ρ ρ' Λ)
    (hY : 0 < ∑ i ∈ S, ρ i ^ (2 * r)) :
    |(∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i) * ((1 : ℝ) / (2 * (r : ℝ))) *
        (∑ i ∈ S, ρ i ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1)|
      ≤ Λ * softMax r S ρ :=
  abs_deriv_softMax_le hr h hY

/-- Under `LogDerivBound` every entry's derivative is controlled by the soft maximum with no
cardinality factor.  ⚠ Vacuous on the loops, for the reason recorded on `LogDerivBound`; the
usable statement is `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine`. -/
theorem logDerivBound_gives_softMax {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} {ρ ρ' : ι → ℝ}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (h : LogDerivBound S ρ ρ' Λ) {i : ι} (hi : i ∈ S) :
    |ρ' i| ≤ Λ * softMax r S ρ :=
  (h i hi).trans (mul_le_mul_of_nonneg_left (le_softMax hr hi) hΛ)

end Interface

/-! ### 13. A compiled `APrimeHyp`

The satisfiability discipline: `APrimeHyp` adds four hypotheses on the weight to
`RBM.CutHypTheta.CutHypCondEv`, and they pull against each other — `W_le_one` caps the
weight, `W_dom` forces it up on the finite net event, and `weightedMoment` has to survive
both.  The witness below meets all four **with the soft-max weight of §6**, not with the
trivial `W ≡ 1`, and on the time-dependent functional `J_u = 2u⁺` of T232 — which **no `∀ N`
interface of `RBM1D/Gauss/CutHypTheta.lean` can carry at all**
(`RBM.CutHypTheta.sat_no_cutHypCond`).

The cutoff level is `√(card) + 1`, i.e. the honest `(card)^{1/q}` of `softMax_le` at the fixed
order `q = 2`; in the application `q ≍ log N` replaces it by `e` (`rpow_card_le_exp_one`).
That the weight is not trivially `1` is `softW_eq_zero`: it vanishes as soon as one entry
exceeds `2Θ`.
-/

section SatAPrime

open MomentDuhamelCut CutHypTheta MeasureTheory Cutoff

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The witness's ratio at the `j`-th net point: `J_{w_j}` in units of the a priori level. -/
noncomputable def satRatio (δ : ℝ) (N j : ℕ) : ℝ :=
  2 * max (cutNetPt (fun _ => (0 : ℝ)) satMeshEv N j) 0 / ((N : ℝ) ^ (2 * δ) * 1)

/-- The witness's weight, as a number: the soft maximum of §6 at order `q = 2`, cut off at
`√(card) + 1`. -/
noncomputable def satWval (δ : ℝ) (N k : ℕ) : ℝ :=
  softW 1 (Finset.range k) (satRatio δ N) (Real.sqrt (Finset.range k).card + 1)

/-- The witness's weight, as a function of the sample — constant, since the witness's `J` is. -/
noncomputable def satW (δ : ℝ) (N k : ℕ) (_ω : Ω) : ℝ := satWval δ N k

omit [MeasurableSpace Ω] in
theorem satW_nonneg (δ : ℝ) (N k : ℕ) (ω : Ω) : 0 ≤ satW δ N k ω := softW_nonneg _ _ _ _

omit [MeasurableSpace Ω] in
theorem satW_le_one (δ : ℝ) (N k : ℕ) (ω : Ω) : satW δ N k ω ≤ 1 := softW_le_one _ _ _ _

/-- The calibration of the witness's cutoff level, at the fixed order `q = 2`. -/
theorem satW_kappa (k : ℕ) :
    ((Finset.range k).card : ℝ) ^ ((1 : ℝ) / (2 * ((1 : ℕ) : ℝ)))
      ≤ Real.sqrt (Finset.range k).card + 1 := by
  have hcast : ((1 : ℝ) / (2 * ((1 : ℕ) : ℝ))) = 1 / 2 := by norm_num
  rw [hcast, ← Real.sqrt_eq_rpow]
  linarith

omit [MeasurableSpace Ω] in
/-- **The weight is `≥ 1` on the finite net event.**  The degenerate case is where the a priori
level vanishes (`N = 0` with `δ ≠ 0`): there the net event forces the functional to vanish too,
so the ratio is `0/0 = 0` and the weight is still `1`. -/
theorem one_le_satW (δ : ℝ) (N k : ℕ) (ω : Ω)
    (hω : ω ∈ prefNet (fun _ _u (_ : Ω) => 2 * max _u 0) (fun _ => (0 : ℝ)) satMeshEv
      (fun N _u => (N : ℝ) ^ (2 * δ) * (1 : ℝ)) N k) :
    1 ≤ satW δ N k ω := by
  have hz : ∀ j ∈ Finset.range k, |satRatio δ N j| ≤ 1 := by
    intro j hj
    have hle : 2 * max (cutNetPt (fun _ => (0 : ℝ)) satMeshEv N j) 0
        ≤ (N : ℝ) ^ (2 * δ) * 1 := hω j (Finset.mem_range.1 hj)
    have hnum : (0 : ℝ) ≤ 2 * max (cutNetPt (fun _ => (0 : ℝ)) satMeshEv N j) 0 := by positivity
    have hden : (0 : ℝ) ≤ (N : ℝ) ^ (2 * δ) * 1 := le_trans hnum hle
    rcases eq_or_lt_of_le hden with h0 | hpos
    · have hnz : 2 * max (cutNetPt (fun _ => (0 : ℝ)) satMeshEv N j) 0 = 0 := by linarith
      rw [satRatio, hnz, zero_div, abs_zero]
      norm_num
    · rw [satRatio, abs_of_nonneg (div_nonneg hnum hpos.le), div_le_one hpos]
      exact hle
  have h := one_le_softW (r := 1) le_rfl (Λ := 1) one_pos (by positivity) (satW_kappa k) hz
  rw [mul_one] at h
  exact h

/-- **⭐ A compiled `APrimeHyp`, with the soft-max weight.** -/
noncomputable def satAPrimeHyp (P : Measure Ω) [IsProbabilityMeasure P] :
    APrimeHyp P (fun _ u (_ : Ω) => 2 * max u 0) (fun _ => 0) (fun _ => 1)
      (fun _ _ => (1 : ℝ)) (fun _ => 1) where
  window := fun _ => zero_le_one
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  lev_ge := fun _ _ _ => le_rfl
  J_nonneg := fun _ u _ => by positivity
  meas := fun _ _ => measurable_const
  mesh := satMeshEv
  mesh_pos := satMeshEv_pos
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := (satCutHypEv P).modulus
  mesh_fine := (satCutHypEv P).mesh_fine
  Ccard := 3
  card_le := (satCutHypEv P).card_le
  Clev := 1
  Clev_nonneg := by norm_num
  levpoly := CutHypTheta.levpoly_const (Θ := fun _ => (1 : ℝ)) (fun _ => one_pos)
  W := satW
  W_meas := fun _ _ _ => aestronglyMeasurable_const
  W_nonneg := satW_nonneg
  W_le_one := satW_le_one
  W_dom := fun δ N k ω hω => one_le_satW δ N k ω hω
  weightedMoment := by
    intro δ hδ0 _ p
    refine ⟨2 ^ (2 * p) + 1, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop 1,
      eventually_le_rpow (2 : ℝ) (by positivity : (0 : ℝ) < 2 * δ)] with N hN hN2 k hk
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hwsIcc : cutNetPt (fun _ => (0 : ℝ)) satMeshEv N k ∈ Set.Icc (0 : ℝ) 1 :=
      netFinset_subset_Icc (by norm_num) (satMeshEv_pos N) _ (cutNetPt_mem_netFinset hk)
    set ws : ℝ := cutNetPt (fun _ => (0 : ℝ)) satMeshEv N k with hwsdef
    have hmax : max ws 0 = ws := max_eq_left hwsIcc.1
    have hlev : 2 * max ws 0 ≤ (N : ℝ) ^ (2 * δ) * 1 := by
      rw [hmax, mul_one]; linarith [hwsIcc.2]
    have hlev0 : (0 : ℝ) < (N : ℝ) ^ (2 * δ) * 1 := by rw [mul_one]; linarith
    have hcut : cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (2 * max ws 0) = 2 * max ws 0 :=
      cutTrunc_eq_self hlev0 hlev
    have hb : |2 * max ws 0| ^ (2 * p) ≤ 2 ^ (2 * p) := by
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      rw [hmax, abs_of_nonneg (by linarith [hwsIcc.1])]
      linarith [hwsIcc.2]
    have hnn : (0 : ℝ) ≤ |2 * max ws 0| ^ (2 * p) := by positivity
    have hδp : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2 * p) := Real.one_le_rpow hN1 (by positivity)
    have hI : ∫ _ω : Ω, satWval δ N k *
        |cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (2 * max ws 0)| ^ (2 * p) ∂P
          = satWval δ N k * |cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (2 * max ws 0)| ^ (2 * p) := by
      simp
    have hval : satWval δ N k * |cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (2 * max ws 0)| ^ (2 * p)
        ≤ 2 ^ (2 * p) := by
      rw [hcut]
      calc satWval δ N k * |2 * max ws 0| ^ (2 * p)
          ≤ 1 * |2 * max ws 0| ^ (2 * p) :=
            mul_le_mul_of_nonneg_right (softW_le_one _ _ _ _) hnn
        _ = |2 * max ws 0| ^ (2 * p) := one_mul _
        _ ≤ 2 ^ (2 * p) := hb
    have hpow : (0 : ℝ) < 2 ^ (2 * p) := by positivity
    calc ∫ ω : Ω, satW δ N k ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (2 * max ws 0)| ^ (2 * p) ∂P
        = satWval δ N k * |cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (2 * max ws 0)| ^ (2 * p) := hI
      _ ≤ 2 ^ (2 * p) := hval
      _ ≤ (2 ^ (2 * p) + 1) * ((N : ℝ) ^ (δ / 2 * p) * 1 ^ (2 * p)) := by
          rw [one_pow, mul_one]
          nlinarith

/-- **`RBM.MomentDuhamelCut.CutHypEv` really does come out of `satAPrimeHyp`**: the chain
`APrimeHyp → CutHypCondEv → CutHypEv` is non-vacuous end to end. -/
noncomputable def satCutHypEv_of_aprime (P : Measure Ω) [IsProbabilityMeasure P] :
    MomentDuhamelCut.CutHypEv P (fun _ u (_ : Ω) => 2 * max u 0) (fun _ => 0) (fun _ => 1)
      (fun _ => 1) :=
  (satAPrimeHyp P).toCutHypEv (Filter.Eventually.of_forall fun _ => le_rfl)
    (MomentDuhamelCut.sat_init_ev P)

/-- **And `J ≺ Θ` comes out**: `stochDom_of_aprime` on the witness. -/
theorem sat_stochDom_of_aprime (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (u : TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) N) (_ : Ω) =>
        2 * max (u : ℝ) 0)
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_aprime (satAPrimeHyp P) (Filter.Eventually.of_forall fun _ => le_rfl)
    (MomentDuhamelCut.sat_init_ev P)

/-- **The witness's weight is a genuine weight**: at an entry above `2Θ` it vanishes, so
`W_dom` and `W_le_one` are not met by `W ≡ 1`. -/
theorem sat_satWval_eq_zero {δ : ℝ} {N k : ℕ} {j : ℕ} (hj : j ∈ Finset.range k)
    (h : 2 * (Real.sqrt (Finset.range k).card + 1) ≤ |satRatio δ N j|) :
    satWval δ N k = 0 :=
  softW_eq_zero le_rfl (by positivity) hj h

end SatAPrime

/-! ### 14. The event-restricted interface (T249)

T249 compiled `RBM.not_cutHypEv_swapSample_of_far`: **no `CutHypEv` at all carries the far
functional on a window with `s ≡ 0`**, and the mechanism is the `∀ ω` of `modulus`, not the
`∀ N`.  Two independent repairs are needed, and route (A′) needs both:

* **the left endpoint must be positive.**  Nothing in `APrimeHyp` forces `0 < s N` — `window`
  only asks `s N ≤ t N`, and `lev_ge` only compares `lev` to `Θ` — so it is **not** implied,
  and a producer on the real chain has to supply it.  Route (A′)'s own reduction
  (`condMoment_of_weightedMoment`) never touches `modulus` and never touches the left
  endpoint, so the requirement is inherited from the fields `APrimeHyp` shares with
  `RBM.CutHypTheta.CutHypCondEv`, not created by the weight.  **Starting condition: `s_N > 0`
  (in the application `s_N ≥ N^{-C}`), plus `J_{s_N} ≺ 1`, which is (2.69).**
* **the modulus must be asserted on an event.**  `APrimeHypOn` is `APrimeHyp` with `modulus`
  restricted to `Good N` (in the application `{ω | ‖X(ω)‖ ≤ N}`), exactly as
  `RBM.MomentDuhamelCut.CutHypEvOn` is for `CutHypEv`, and by the same device: the cut-down
  functional `RBM.MomentDuhamelCut.onEvent J Good` satisfies the **unrestricted** interface,
  because off `Good N` it is constantly `0`.

`APrimeHypOn.toAPrimeHyp` performs that transfer — the moment field costs nothing, because
the restricted integrand is dominated by the unrestricted one pointwise — and
`stochDom_of_aprimeOn` routes the conclusion back, paying one `N^{-1}` for `Good`.
-/

section APrimeOn

open MomentDuhamelCut CutHypTheta MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ → ℝ → Ω → ℝ} {s t : ℕ → ℝ}
  {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ} {Good : ℕ → Set Ω}

/-- **`APrimeHyp` with the modulus restricted to an event** (T249).  The one change: `modulus`
is asked only for `ω ∈ Good N`. -/
structure APrimeHypOn (P : Measure Ω) (J : ℕ → ℝ → Ω → ℝ) (s t : ℕ → ℝ) (lev : ℕ → ℝ → ℝ)
    (Θ : ℕ → ℝ) (Good : ℕ → Set Ω) where
  /-- The window is non-degenerate. -/
  window : ∀ N, s N ≤ t N
  /-- The range `0 < δ ≤ δ₀` of bootstrap margins. -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  Θ_pos : ∀ N, 0 < Θ N
  /-- The truncation level dominates the control, on the window. -/
  lev_ge : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u
  /-- The state functional is nonnegative. -/
  J_nonneg : ∀ N u ω, 0 ≤ J N u ω
  meas : ∀ (N : ℕ) (u : ℝ), Measurable fun ω => J N u ω
  /-- The event the modulus is asserted on. -/
  good_meas : ∀ N, MeasurableSet (Good N)
  /-- The mesh of the net of (5.46). -/
  mesh : ℕ → ℝ
  mesh_pos : ∀ N, 0 < mesh N
  /-- The exponent of the modulus of continuity. -/
  Kmod : ℝ
  /-- Its Hölder exponent (`1` for the Lipschitz bound on `s_N ≥ N^{-C}`). -/
  γ : ℝ
  γ_pos : 0 < γ
  /-- **The modulus, only on `Good N`.** -/
  modulus : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N, ∀ v ∈ Set.Icc (s N) (t N),
    ∀ w ∈ Set.Icc (s N) (t N),
    |J N v ω - J N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ
  mesh_fine : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ N
  /-- The exponent of the net's cardinality. -/
  Ccard : ℝ
  card_le : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard
  /-- The exponent bounding the truncation level against the control. -/
  Clev : ℝ
  Clev_nonneg : 0 ≤ Clev
  levpoly : ∀ᶠ N : ℕ in atTop, ∀ ws ∈ netFinset s t mesh N,
    2 * lev N ws ≤ (N : ℝ) ^ Clev * Θ N
  /-- The weight of route (A′). -/
  W : ℝ → ℕ → ℕ → Ω → ℝ
  W_meas : ∀ (δ : ℝ) (N k : ℕ), AEStronglyMeasurable (fun ω => W δ N k ω) P
  W_nonneg : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω), 0 ≤ W δ N k ω
  W_le_one : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω), W δ N k ω ≤ 1
  W_dom : ∀ (δ : ℝ) (N k : ℕ) (ω : Ω),
    ω ∈ prefNet J s mesh (fun N u => (N : ℝ) ^ (2 * δ) * lev N u) N k → 1 ≤ W δ N k ω
  /-- **The moment field, unconditional.**  Unchanged from `APrimeHyp`: the event restriction
  costs nothing here (`APrimeHypOn.toAPrimeHyp`). -/
  weightedMoment : WeightedMoment P J s t mesh lev Θ δ₀ W

/-- The weight transported to the cut-down functional: `W` on `Good N`, `1` off it. -/
noncomputable def weightOn (W : ℝ → ℕ → ℕ → Ω → ℝ) (Good : ℕ → Set Ω)
    (δ : ℝ) (N k : ℕ) (ω : Ω) : ℝ :=
  1 - Set.indicator (Good N) (fun ω => 1 - W δ N k ω) ω

omit [MeasurableSpace Ω] in
theorem weightOn_of_mem {W : ℝ → ℕ → ℕ → Ω → ℝ} {δ : ℝ} {N k : ℕ} {ω : Ω}
    (h : ω ∈ Good N) : weightOn W Good δ N k ω = W δ N k ω := by
  rw [weightOn, Set.indicator_of_mem h]; ring

omit [MeasurableSpace Ω] in
theorem weightOn_of_notMem {W : ℝ → ℕ → ℕ → Ω → ℝ} {δ : ℝ} {N k : ℕ} {ω : Ω}
    (h : ω ∉ Good N) : weightOn W Good δ N k ω = 1 := by
  rw [weightOn, Set.indicator_of_notMem h, sub_zero]

omit [MeasurableSpace Ω] in
theorem weightOn_nonneg {W : ℝ → ℕ → ℕ → Ω → ℝ} (hW : ∀ δ N k ω, 0 ≤ W δ N k ω)
    (δ : ℝ) (N k : ℕ) (ω : Ω) : 0 ≤ weightOn W Good δ N k ω := by
  by_cases h : ω ∈ Good N
  · rw [weightOn_of_mem h]; exact hW δ N k ω
  · rw [weightOn_of_notMem h]; norm_num

omit [MeasurableSpace Ω] in
theorem weightOn_le_one {W : ℝ → ℕ → ℕ → Ω → ℝ} (hW : ∀ δ N k ω, W δ N k ω ≤ 1)
    (δ : ℝ) (N k : ℕ) (ω : Ω) : weightOn W Good δ N k ω ≤ 1 := by
  by_cases h : ω ∈ Good N
  · rw [weightOn_of_mem h]; exact hW δ N k ω
  · rw [weightOn_of_notMem h]

/-- **⭐ The event-restricted interface produces the unrestricted one, for the cut-down
functional.**  Off `Good N` the functional is constantly `0`, so the modulus is free there and
the moment only drops (`cutTrunc θ 0 = 0`). -/
noncomputable def APrimeHypOn.toAPrimeHyp [IsProbabilityMeasure P]
    (H : APrimeHypOn P J s t lev Θ Good) :
    APrimeHyp P (onEvent J Good) s t lev Θ where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  lev_ge := H.lev_ge
  J_nonneg := by
    intro N u ω
    by_cases h : ω ∈ Good N
    · rw [onEvent_of_mem h]; exact H.J_nonneg N u ω
    · rw [onEvent_of_notMem h]
  meas := fun N u => (H.meas N u).indicator (H.good_meas N)
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := by
    filter_upwards [H.modulus] with N hN ω v hv w hw
    by_cases h : ω ∈ Good N
    · rw [onEvent_of_mem h, onEvent_of_mem h]
      exact hN ω h v hv w hw
    · rw [onEvent_of_notMem h, onEvent_of_notMem h, sub_self, abs_zero]
      positivity
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  Clev := H.Clev
  Clev_nonneg := H.Clev_nonneg
  levpoly := H.levpoly
  W := weightOn H.W Good
  W_meas := by
    intro δ N k
    exact (aestronglyMeasurable_const.sub
      (((aestronglyMeasurable_const.sub (H.W_meas δ N k)).indicator (H.good_meas N))))
  W_nonneg := weightOn_nonneg H.W_nonneg
  W_le_one := weightOn_le_one H.W_le_one
  W_dom := by
    intro δ N k ω hω
    by_cases h : ω ∈ Good N
    · rw [weightOn_of_mem h]
      refine H.W_dom δ N k ω fun j hj => ?_
      have := hω j hj
      rwa [onEvent_of_mem h] at this
    · rw [weightOn_of_notMem h]
  weightedMoment := by
    intro δ hδ0 hδ p
    obtain ⟨C, hC0, hC⟩ := H.weightedMoment δ hδ0 hδ p
    rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · -- `p = 0`: the integrand is the weight itself, which is at most `1`.
      subst hp0
      refine ⟨C + 1, by linarith, Filter.Eventually.of_forall fun N k _ => ?_⟩
      have hle : ∫ ω : Ω, weightOn H.W Good δ N k ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k))
            (onEvent J Good N (cutNetPt s H.mesh N k) ω)| ^ (2 * 0) ∂P
            ≤ ∫ _ω : Ω, (1 : ℝ) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          (integrable_const 1) (Filter.Eventually.of_forall fun ω => ?_)
        · exact mul_nonneg (weightOn_nonneg H.W_nonneg δ N k ω) (by positivity)
        · dsimp only
          simpa using weightOn_le_one H.W_le_one δ N k ω
      have hone : ∫ _ω : Ω, (1 : ℝ) ∂P = 1 := by simp
      rw [hone] at hle
      refine hle.trans ?_
      have h1 : (N : ℝ) ^ (δ / 2 * ((0 : ℕ) : ℝ)) = 1 := by
        norm_num
      have h2 : Θ N ^ (2 * 0) = 1 := by norm_num
      rw [h1, h2]
      linarith
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hC, eventually_ge_atTop 1] with N hN hN1 k hk
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hrp : (0 : ℝ) < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos (by linarith) _
    have hmem : cutNetPt s H.mesh N k ∈ Set.Icc (s N) (t N) :=
      netFinset_subset_Icc (H.window N) (H.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
    have hθ : 0 < (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k) :=
      mul_pos hrp (lt_of_lt_of_le (H.Θ_pos N) (H.lev_ge N _ hmem))
    have hRi : Integrable (fun ω => H.W δ N k ω *
        |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s H.mesh N k))
          (J N (cutNetPt s H.mesh N k) ω)| ^ (2 * p)) P :=
      integrable_weight_mul hθ (H.W_nonneg δ N k) (H.W_le_one δ N k) (H.W_meas δ N k)
        (fun ω => H.J_nonneg N _ ω)
        ((H.meas N (cutNetPt s H.mesh N k)).aestronglyMeasurable) (2 * p)
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hRi
      (Filter.Eventually.of_forall fun ω => ?_)) (hN k hk)
    · exact mul_nonneg (weightOn_nonneg H.W_nonneg δ N k ω) (by positivity)
    · dsimp only
      by_cases h : ω ∈ Good N
      · rw [weightOn_of_mem h, onEvent_of_mem h]
      · rw [weightOn_of_notMem h, onEvent_of_notMem h, cutTrunc_zero, abs_zero,
          zero_pow (by omega : 2 * p ≠ 0), mul_zero]
        have := H.W_nonneg δ N k ω
        positivity

/-- **⭐⭐ `J ≺ Θ` from the event-restricted interface of route (A′).**

`stochDom_of_aprime` on the cut-down functional, then the conclusion is transported back
across `Good`, which costs one extra `N^{-1}` in the union bound.  This is
`RBM.MomentDuhamelCut.stochDom_of_cutHypEvOn`'s argument, for route (A′)'s interface. -/
theorem stochDom_of_aprimeOn [IsProbabilityMeasure P] (H : APrimeHypOn P J s t lev Θ Good)
    (hgood : HighProb P Good) (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom P (fun N (_ : Unit) ω => J N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom P (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) := by
  have hle : ∀ N u ω, onEvent J Good N u ω ≤ J N u ω := by
    intro N u ω
    by_cases h : ω ∈ Good N
    · rw [onEvent_of_mem h]
    · rw [onEvent_of_notMem h]; exact H.J_nonneg N u ω
  have hinit' : StochDom P (fun N (_ : Unit) ω => onEvent J Good N (s N) ω)
      (fun _ _ _ => (1 : ℝ)) := by
    intro τ hτ D hD
    filter_upwards [hinit τ hτ D hD] with N hN
    refine le_trans (measure_mono ?_) hN
    rintro ω ⟨u, hu⟩
    exact ⟨u, lt_of_lt_of_le hu (hle N (s N) ω)⟩
  have hmain := stochDom_of_aprime H.toAPrimeHyp hΘ1 hinit'
  intro τ hτ D hD
  filter_upwards [hmain τ hτ (D + 1) (by linarith), hgood (D + 1) (by linarith),
    eventually_ge_atTop 2] with N hbad hgd hN2
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hsub : badSet (fun N (u : TimeIcc s t N) ω => J N (u : ℝ) ω) (fun N _ _ => Θ N) τ N
      ⊆ badSet (fun N (u : TimeIcc s t N) ω => onEvent J Good N (u : ℝ) ω)
          (fun N _ _ => Θ N) τ N ∪ (Good N)ᶜ := by
    rintro ω ⟨u, hu⟩
    by_cases h : ω ∈ Good N
    · refine Or.inl ⟨u, ?_⟩
      simp only
      rwa [onEvent_of_mem h]
    · exact Or.inr h
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
  refine le_trans (add_le_add hbad hgd) ?_
  rw [← ENNReal.ofReal_add hp hp]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hN2'
  calc (N : ℝ) ^ (-(D + 1)) + (N : ℝ) ^ (-(D + 1)) = 2 * (N : ℝ) ^ (-(D + 1)) := by ring
    _ ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(D + 1)) := mul_le_mul_of_nonneg_right h2 hp
    _ = (N : ℝ) ^ (-D) := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- The unrestricted interface is the `Good = univ` case, so `APrimeHypOn` is not vacuous:
`satAPrimeHyp` transports to it. -/
noncomputable def APrimeHypOn.of_aprime (H : APrimeHyp P J s t lev Θ) :
    APrimeHypOn P J s t lev Θ (fun _ => Set.univ) where
  window := H.window
  δ₀ := H.δ₀
  δ₀_pos := H.δ₀_pos
  Θ_pos := H.Θ_pos
  lev_ge := H.lev_ge
  J_nonneg := H.J_nonneg
  meas := H.meas
  good_meas := fun _ => MeasurableSet.univ
  mesh := H.mesh
  mesh_pos := H.mesh_pos
  Kmod := H.Kmod
  γ := H.γ
  γ_pos := H.γ_pos
  modulus := by
    filter_upwards [H.modulus] with N hN ω _ v hv w hw
    exact hN ω v hv w hw
  mesh_fine := H.mesh_fine
  Ccard := H.Ccard
  card_le := H.card_le
  Clev := H.Clev
  Clev_nonneg := H.Clev_nonneg
  levpoly := H.levpoly
  W := H.W
  W_meas := H.W_meas
  W_nonneg := H.W_nonneg
  W_le_one := H.W_le_one
  W_dom := H.W_dom
  weightedMoment := H.weightedMoment

/-- `Good = univ` is `HighProb`. -/
theorem highProb_univ : HighProb P (fun _ : ℕ => (Set.univ : Set Ω)) := by
  intro D _
  filter_upwards with N
  simp

end APrimeOn

/-! ### 15. The event-restricted chain, run on the witness -/

section SatAPrimeOn

open MomentDuhamelCut CutHypTheta MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`APrimeHypOn` is non-vacuous**, at `Good = univ`. -/
noncomputable def satAPrimeHypOn (P : Measure Ω) [IsProbabilityMeasure P] :
    APrimeHypOn P (fun _ u (_ : Ω) => 2 * max u 0) (fun _ => 0) (fun _ => 1)
      (fun _ _ => (1 : ℝ)) (fun _ => 1) (fun _ => Set.univ) :=
  APrimeHypOn.of_aprime (satAPrimeHyp P)

/-- **The event-restricted chain runs end to end on the witness.** -/
theorem sat_stochDom_of_aprimeOn (P : Measure Ω) [IsProbabilityMeasure P] :
    StochDom P
      (fun N (u : TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) N) (_ : Ω) =>
        2 * max (u : ℝ) 0)
      (fun _ _ _ => (1 : ℝ)) :=
  stochDom_of_aprimeOn (satAPrimeHypOn P) highProb_univ
    (Filter.Eventually.of_forall fun _ => le_rfl) (MomentDuhamelCut.sat_init_ev P)

end SatAPrimeOn

end Step2Bootstrap

end RBM
