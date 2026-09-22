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

## What is *not* blocked

The smooth-weight variant (A′) of the ticket — replacing the prefix indicator by
`∏_{j<k} χ(J*_{u_j}/Θ)` — has **no bad-event term at all**: the weight is a fixed function of
the Gaussian (not of the current time `u`), Stein's identity applies against the full measure,
and on the support of the weight *and of its derivative* the a priori bound holds pathwise.
Its recursion is therefore the `q ≡ 0` one, which is linear, not geometric
(`bootBad_le_of_q_zero`).  Nothing in this file is evidence that (A′) works; what is compiled
here is only that the two no-gos do not reach it.

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

end Step2Bootstrap

end RBM
