/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2
import RBM1D.Analysis.Bootstrap
import RBM1D.Gauss.Envelope

/-!
# Step 2 without the stopping time: the moment route

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3, redone along the **moment
route** (no Itô calculus, no martingales, and in particular **no optional stopping**).

`RBM1D/Hierarchy/Step2.lean` (T61) proves Step 2 through the stopping time (5.43)
`T = inf{u : J*_{u,D} > Λ(u)}`: the pathwise bound `RBM.Step2.step_bound` improves `J*` at a
time `v ≤ T`, the deterministic `RBM.Step2.self_improving` closes the loop, and the martingale
hypothesis `RBM.Step2.Hyp.mart` is asserted *stopped at* `T`.

Here the bootstrapped quantity is the **deterministic** function

  `φ_q(u) = E[(J*_{u,D})^q]`   (`RBM.Step2Moment.phi`)

instead of the random path `u ↦ J*_{u,D}`.  A deterministic function has no filtration, no
stopping time and no optional stopping theorem attached to it: once `φ_q` is *continuous* in
`u`, the argument of p. 59 is literally continuous induction, `RBM.le_of_bootstrap_prefix`
(T78, `RBM1D/Analysis/Bootstrap.lean`).  The stopping time is gone — it is replaced by the
sup-of-a-closed-set argument inside that lemma.

## What is proved here

* `le_of_bootstrap_weight` — continuous induction with a **varying** threshold
  `Λ(u) = Λ · w(u)`, which is the shape of (5.43) (`w(u) = (η_s/η_u)^4`).  It is
  `RBM.le_of_bootstrap_prefix` applied to `φ/w`; the paper's time-dependent threshold is
  exactly what normalizing by `w` removes.
* `phi` **(the moment of (5.29))**, `phiN` (normalized by `(η_s/η_u)^{4q}`),
  `phiN_eq_phi_div`, `continuousOn_phi`, `continuousOn_phiN` — `φ_q` is continuous by
  dominated convergence: the paths are continuous **for every `ω`** (no exceptional set — the
  flow `H_u = √u X` of `RBM1D/Gauss/Model.lean` is deterministic in `u`, see
  `RBM.Gauss.norm_Hflow_sub`) and the integrand is dominated by the deterministic envelope
  `RBM.Gauss.norm_gloop_le_det` of T77.
* `stochDom_timeIcc_of_holder` — moments uniform in `u ∈ [s_N, t_N]` plus a deterministic
  modulus of continuity give `≺` with Definition 2.1 (i)'s *uncountable* union intact.  This
  is `RBM.Gauss.stochDom_Icc_of_holder` (T73) for an `N`-dependent interval; it is the second
  place where the moment route pays off (the net of (5.46) replaces a pathwise argument).
* `phi_le`, `phiN_le` — the bootstrap: `E[(J*_{u,D})^q] ≤ B_q(N) (η_s/η_u)^{4q}` on all of
  `[s, t]`.
* `jS_stochDom` — **(5.47)** `J*_{u,D} ≺ (η_s/η_u)^4`, in *exactly* the shape of
  `RBM.Step2.jS_stochDom`.
* `aprioriDecay` — **(2.76)**, `step2` — **(2.75)** and **(2.76)**, in exactly the shapes of
  the fields `RBM.Steps.aprioriDecay` and `RBM.Steps.localLaw`, so that the two routes are
  interchangeable.  ((2.75) is `RBM.Step2.localLaw`, which already takes (2.76) and (2.74) as
  hypotheses and is therefore route-independent.)

## Hypotheses (`MomentHyp`; never axioms)

`MomentHyp X E s t D` collects what the moment route must supply.  Compared with
`RBM.Step2.Hyp` the *stopped* martingale field `mart` and the *high-probability* continuity
field `cont` are both gone; what replaces them is deterministic:

* `cont` — continuity of `u ↦ (L-K)_{u,a}` **for every `ω`** (not w.h.p.).
* `holder` — a deterministic modulus of continuity `|J*_u - J*_{u'}| ≤ N^K |u-u'|^γ` for every
  `ω`, i.e. the input of the net of (5.46); `γ = 1/2` for `H_u = √u X`
  (`RBM.Gauss.abs_sqrt_sub_sqrt_le`).
* `env` — the deterministic envelope of `J*` (T77: `RBM.Gauss.norm_gloop_le_det`,
  `RBM.Gauss.norm_gloop_sub_le_det` and `RBM.Step2.jStar_le`).
* `meas` — measurability of `ω ↦ J*_{u,D}`.
* `init`, `step`, `bnd`, `thr`, `bnd_lt_thr`, `bnd_poly` — **the one-step moment improvement**,
  i.e. (5.39)–(5.41) together with (5.45) in moment form: *if* `E[(J*_u/(η_s/η_u)^4)^q] ≤ Λ_q`
  for all `u ≤ v`, *then* `E[(J*_v/(η_s/η_v)^4)^q] ≤ B_q < Λ_q`.  This is the one input that
  cannot be supplied from what is in the repository today: `RBM1D/Gauss/Hierarchy.lean` (T76)
  gives `∂_u E[L_u]`, while `RBM.SumZeroDyn.Hierarchy.duhamel` — the form `RBM.Step2.step_bound`
  consumes — is a *pathwise* integral identity with a martingale field.  Bridging the two is
  T74/T76 work and is deliberately **not** faked here.  See `docs/paper-deltas.md`.

## Deviations from the paper

* The bootstrapped quantity is `E[(J*_u)^q]`, not the path `J*_u`; (5.43)–(5.46) (the stopping
  time, the stopped martingale, optional stopping) are not used at all.
* The threshold still carries the `N^δ`-type margin of T61 — here in the form of the gap
  `B_q(N) < Λ_q(N)` — because `≺` still has to beat an `N^τ` loss; continuous induction removes
  the stopping time, not the margin.
* The `N^c` gain in (2.72) (`hreg`) is inherited unchanged from T61: it is used by
  `RBM.Step2.cond272_of_strict` and `RBM.Step2.eventually_R4_le_scale` in the passage from
  (5.47) to (2.76), which is route-independent.
-/

namespace RBM

namespace Step2Moment

open MeasureTheory Filter

/-! ### Continuous induction with a varying threshold -/

section Bootstrap

/-- **Continuous induction, varying threshold.**  This is the shape of the paper's (5.43),
where the threshold `Λ(u) = N^δ (η_s/η_u)^4` depends on the time: if `φ` starts below `B·w`,
`w` is continuous and positive, and the a priori bound `φ ≤ C·w` on `[a, u]` improves itself to
`φ(u) ≤ B·w(u)` with `B < C`, then `φ ≤ B·w` throughout.

Dividing by the weight turns the varying threshold into a constant one, so this is
`RBM.le_of_bootstrap_prefix` (T78) applied to `φ/w`.  **No stopping time occurs**: the only
random object of the paper's argument, the path `u ↦ J*_u`, has been replaced by the
deterministic function `φ`. -/
theorem le_of_bootstrap_weight {a b B C : ℝ} {φ w : ℝ → ℝ} (hab : a ≤ b)
    (hcφ : ContinuousOn φ (Set.Icc a b)) (hcw : ContinuousOn w (Set.Icc a b))
    (hw : ∀ u ∈ Set.Icc a b, 0 < w u) (hBC : B < C) (h0 : φ a ≤ B * w a)
    (hstep : ∀ u ∈ Set.Icc a b, (∀ v ∈ Set.Icc a u, φ v ≤ C * w v) → φ u ≤ B * w u) :
    ∀ u ∈ Set.Icc a b, φ u ≤ B * w u := by
  have key : ∀ u ∈ Set.Icc a b, (fun u => φ u / w u) u ≤ B := by
    refine le_of_bootstrap_prefix hab (hcφ.div hcw fun u hu => (hw u hu).ne') hBC ?_ ?_
    · rw [div_le_iff₀ (hw a (Set.left_mem_Icc.2 hab))]; exact h0
    · intro u hu hprefix
      rw [div_le_iff₀ (hw u hu)]
      refine hstep u hu fun v hv => ?_
      have hvIcc : v ∈ Set.Icc a b := ⟨hv.1, hv.2.trans hu.2⟩
      have := hprefix v hv
      rwa [div_le_iff₀ (hw v hvIcc)] at this
  intro u hu
  have := key u hu
  rwa [div_le_iff₀ (hw u hu)] at this

end Bootstrap

/-! ### The moment `φ_q(u) = E[(J*_{u,D})^q]` -/

section Phi

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The weight `(η_s/η_u)^4` of the threshold (5.43): `R_u = η_s/η_u ≥ 1`. -/
noncomputable def ratR (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ := etaT E (s N) / etaT E u

theorem ratR_pos {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {N : ℕ} (hs : s N < 1) {u : ℝ}
    (hu : u < 1) : 0 < ratR E s N u :=
  div_pos (Step2.etaT_pos' hE hs) (Step2.etaT_pos' hE hu)

theorem continuousOn_ratR {E : ℝ} (hE : |E| < 2) (s : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hb : b < 1) :
    ContinuousOn (ratR E s N) (Set.Icc a b) := by
  unfold ratR
  refine ContinuousOn.div continuousOn_const (by unfold etaT; fun_prop) fun u hu => ?_
  exact (Step2.etaT_pos' hE (hu.2.trans_lt hb)).ne'

/-- `J*_{u,D}` normalized by the weight of the threshold: `J*_{u,D} / (η_s/η_u)^4`.  The
bootstrap is run on this, so that the threshold becomes a constant. -/
noncomputable def jSnorm (X : Sample B) (E D : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  Step2.jS X E D N u ω / ratR E s N u ^ 4

/-- **The bootstrapped quantity of the moment route**: `φ_q(u) = E[(J*_{u,D})^q]`.  Unlike the
path `u ↦ J*_{u,D}` this is a deterministic function of `u`. -/
noncomputable def phi (X : Sample B) (E D : ℝ) (N q : ℕ) (u : ℝ) : ℝ :=
  ∫ ω, Step2.jS X E D N u ω ^ q ∂B.P

/-- `φ_q` normalized by the weight: `E[(J*_{u,D}/(η_s/η_u)^4)^q]`. -/
noncomputable def phiN (X : Sample B) (E D : ℝ) (s : ℕ → ℝ) (N q : ℕ) (u : ℝ) : ℝ :=
  ∫ ω, jSnorm X E D s N u ω ^ q ∂B.P

variable (X : Sample B) {E D : ℝ} {s : ℕ → ℝ}

theorem phiN_eq_phi_div (N q : ℕ) (u : ℝ) :
    phiN X E D s N q u = phi X E D N q u / ratR E s N u ^ (4 * q) := by
  unfold phiN phi jSnorm
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [div_pow, pow_mul]

/-- `1 ≤ J*_{u,D}` (`RBM.Step2.one_le_jStar`); in particular `J*` is non-negative. -/
theorem one_le_jS (N : ℕ) (u : ℝ) (ω : Ω) : 1 ≤ Step2.jS X E D N u ω := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  exact Step2.one_le_jStar hW fun _ => norm_nonneg _

theorem jSnorm_nonneg (hE : |E| < 2) {N : ℕ} (hs : s N < 1) {u : ℝ} (hu : u < 1) (ω : Ω) :
    0 ≤ jSnorm X E D s N u ω := by
  have h1 := one_le_jS X (E := E) (D := D) N u ω
  have h2 := ratR_pos (s := s) (N := N) hE hs hu
  unfold jSnorm
  positivity

/-- **`φ_q` is continuous.**  This is where the moment route pays off: `φ_q` is a deterministic
function, and its continuity is dominated convergence applied to paths that are continuous for
**every** `ω` (the flow `H_u = √u X` is a deterministic function of `u`) and dominated by the
deterministic envelope of T77 — no exceptional set, no filtration, no stopping. -/
theorem continuousOn_phi (hE : |E| < 2) (N q : ℕ) {a b : ℝ} (hb : b < 1)
    (hcont : ∀ (ω : Ω) (x : LoopArg (B.L N) 2),
      ContinuousOn (fun u => Step2.lk X E N u ω x) (Set.Icc a b))
    {M : ℝ} (hM : ∀ u ∈ Set.Icc a b, ∀ ω : Ω, Step2.jS X E D N u ω ≤ M)
    (hmeas : ∀ u : ℝ, AEStronglyMeasurable (fun ω => Step2.jS X E D N u ω) B.P) :
    ContinuousOn (phi X E D N q) (Set.Icc a b) := by
  have := B.isProbabilityMeasure
  refine continuousOn_of_dominated (bound := fun _ => M ^ q) (fun u _ => (hmeas u).pow q)
    (fun u hu => Filter.Eventually.of_forall fun ω => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun ω => ?_)
  · have h1 : 0 ≤ Step2.jS X E D N u ω := by linarith [one_le_jS X (E := E) (D := D) N u ω]
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1 q)]
    exact pow_le_pow_left₀ h1 (hM u hu ω) q
  · exact (Step2.continuousOn_jS X hE D N ω hb (hcont ω)).pow q

theorem continuousOn_phiN (hE : |E| < 2) (N q : ℕ) {a b : ℝ} (hb : b < 1) (hs : s N < 1)
    (hcont : ∀ (ω : Ω) (x : LoopArg (B.L N) 2),
      ContinuousOn (fun u => Step2.lk X E N u ω x) (Set.Icc a b))
    {M : ℝ} (hM : ∀ u ∈ Set.Icc a b, ∀ ω : Ω, Step2.jS X E D N u ω ≤ M)
    (hmeas : ∀ u : ℝ, AEStronglyMeasurable (fun ω => Step2.jS X E D N u ω) B.P) :
    ContinuousOn (phiN X E D s N q) (Set.Icc a b) := by
  have heq : Set.EqOn (phiN X E D s N q)
      (fun u => phi X E D N q u / ratR E s N u ^ (4 * q)) (Set.Icc a b) :=
    fun u _ => phiN_eq_phi_div X N q u
  refine ContinuousOn.congr ?_ heq
  refine (continuousOn_phi X hE N q hb hcont hM hmeas).div
    (((continuousOn_ratR hE s N hb)).pow (4 * q)) fun u hu => ?_
  exact pow_ne_zero _ (ratR_pos (s := s) (N := N) hE hs (hu.2.trans_lt hb)).ne'

end Phi

/-! ### From moments to `≺`, uniformly in `u ∈ [s_N, t_N]`: the net of (5.46) -/

section Net

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- The `k`-th point of the uniform net of (5.46) on the **`N`-dependent** interval
`[s_N, t_N]`.  The net of `RBM1D/Gauss/Domination.lean` lives on a fixed `[0, T]`; shifting it
by `s_N` and clipping at `t_N` keeps it inside `[s_N, t_N]` without assuming `s_N < t_N`. -/
noncomputable def netTime (s t : ℕ → ℝ) (A : ℝ) (N : ℕ)
    (k : Fin (Gauss.netSize A N + 1)) : ℝ :=
  min (t N) (s N + Gauss.netPt 1 A N k)

theorem netTime_mem {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) (A : ℝ) (N : ℕ)
    (k : Fin (Gauss.netSize A N + 1)) : netTime s t A N k ∈ Set.Icc (s N) (t N) := by
  refine ⟨le_min (hst N) ?_, min_le_left _ _⟩
  have := (Gauss.netPt_mem_Icc (T := 1) zero_le_one A N k).1
  linarith

/-- Every time of `[s_N, t_N]` is within `1/m` of a net point, `m = netSize A N`. -/
theorem exists_netTime_close {s t : ℕ → ℝ} (hlen : ∀ N, t N - s N ≤ 1) (A : ℝ) (N : ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    ∃ k, |u - netTime s t A N k| ≤ 1 / (Gauss.netSize A N : ℝ) := by
  have hmem : u - s N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen N]⟩
  obtain ⟨k, hk⟩ := Gauss.exists_netPt_close (T := 1) one_pos A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s N + Gauss.netPt 1 A N k)| ≤ 1 / (Gauss.netSize A N : ℝ) := by
    have : u - (s N + Gauss.netPt 1 A N k) = u - s N - Gauss.netPt 1 A N k := by ring
    rw [this]; exact hk
  unfold netTime
  rcases le_or_gt (s N + Gauss.netPt 1 A N k) (t N) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

/-- **Definition 2.1 (i) with the uncountable union intact, on an `N`-dependent interval.**

This is `RBM.Gauss.stochDom_Icc_of_holder` (T73) for the time interval `[s_N, t_N]` of the
flow.  The inputs are the moment bounds — which is what the moment route produces — and a
**deterministic** modulus of continuity `|Y(N,u,ω) - Y(N,u',ω)| ≤ N^K |u-u'|^γ`, valid for
every `ω`: for `H_u = √u X` that is `RBM.Gauss.norm_Hflow_sub` with `γ = 1/2`.  No path
regularity in probability, no stopping time. -/
theorem stochDom_timeIcc_of_holder {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N)
    (hlen : ∀ N, t N - s N ≤ 1) {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Y : ℕ → ℝ → Ω → ℝ}
    (hHol : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (s N) (t N), ∀ u' ∈ Set.Icc (s N) (t N),
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N), ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * (N : ℝ) ^ (ε * p)) :
    StochDom P (U := fun N => TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  set A : ℝ := (K + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + 1 := by rw [hA_def]; field_simp
  -- the moment bound on the (finite) net
  have hnet : StochDom P (fun (N : ℕ) (k : Fin (Gauss.netSize A N + 1)) ω =>
      Y N (netTime s t A N k) ω) (fun _ _ _ => (1 : ℝ)) := by
    refine Gauss.stochDom_one_of_momentDom (Gauss.card_net_le hA)
      (fun p N k => hint p N _ (netTime_mem hst A N k)) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    exact ⟨C, hC0, by filter_upwards [hCN] with N hN k using hN _ (netTime_mem hst A N k)⟩
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hsub : ∀ᶠ N : ℕ in atTop,
      badSet (U := fun N => TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
        (fun _ _ _ => (1 : ℝ)) τ N ⊆
      badSet (fun (N : ℕ) (k : Fin (Gauss.netSize A N + 1)) ω => Y N (netTime s t A N k) ω)
        (fun _ _ _ => (1 : ℝ)) (τ / 2) N := by
    filter_upwards [eventually_ge_atTop 1, eventually_le_rpow 2 hτ2] with N hN1 hN2
    have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < N := by linarith
    have hm : (0 : ℝ) < (Gauss.netSize A N : ℝ) := by exact_mod_cast Gauss.netSize_pos A N
    have hNA : (0 : ℝ) < (N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
    have hmge : (N : ℝ) ^ A ≤ (Gauss.netSize A N : ℝ) := Gauss.rpow_le_netSize A N
    have hr2 : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
    -- the net error is at most `N^{-1} ≤ N^{τ/2}`
    have herr : (N : ℝ) ^ K * (1 / (Gauss.netSize A N : ℝ)) ^ γ ≤ (N : ℝ) ^ (τ / 2) := by
      have h1 : (1 : ℝ) / (Gauss.netSize A N : ℝ) ≤ 1 / (N : ℝ) ^ A :=
        div_le_div_of_nonneg_left zero_le_one hNA hmge
      have h2 : (1 / (Gauss.netSize A N : ℝ)) ^ γ ≤ (1 / (N : ℝ) ^ A) ^ γ :=
        Real.rpow_le_rpow (by positivity) h1 hγ.le
      have h3 : (1 / (N : ℝ) ^ A) ^ γ = (N : ℝ) ^ (-(K + 1)) := by
        rw [Real.div_rpow zero_le_one hNA.le, Real.one_rpow, ← Real.rpow_mul hNpos.le, hAγ,
          Real.rpow_neg hNpos.le, one_div]
      have h4 : (N : ℝ) ^ K * (N : ℝ) ^ (-(K + 1)) = (N : ℝ) ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hNpos]; congr 1; ring
      have h5 : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (τ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      calc (N : ℝ) ^ K * (1 / (Gauss.netSize A N : ℝ)) ^ γ
          ≤ (N : ℝ) ^ K * (N : ℝ) ^ (-(K + 1)) := by
            rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ (-(1 : ℝ)) := h4
        _ ≤ _ := h5
    have hdouble : 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
      have heq := UnifDetDom.rpow_half_mul_rpow_half N hτ
      nlinarith [hr2.le]
    rintro ω ⟨u, hu⟩
    obtain ⟨k, hk⟩ := exists_netTime_close (s := s) (t := t) hlen A N u.2
    refine ⟨k, ?_⟩
    have hhol := hHol N ω u.1 u.2 (netTime s t A N k) (netTime_mem hst A N k)
    have hle : |Y N (u : ℝ) ω - Y N (netTime s t A N k) ω| ≤ (N : ℝ) ^ (τ / 2) := by
      refine hhol.trans (le_trans ?_ herr)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
        (Real.rpow_nonneg hNpos.le K)
    have hdiff : Y N (u : ℝ) ω - Y N (netTime s t A N k) ω ≤ (N : ℝ) ^ (τ / 2) :=
      (le_abs_self _).trans hle
    simp only [mul_one] at hu ⊢
    linarith
  filter_upwards [hsub, hnet (τ / 2) hτ2 D hD] with N h1 h2
  exact (measure_mono h1).trans h2

end Net

/-! ### The inputs of the moment route -/

section Hyp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The inputs of Step 2 along the moment route** (CLAUDE.md rule 6: hypotheses, never
axioms).  Compared with `RBM.Step2.Hyp`, the *stopped* martingale field `mart` and the
*high-probability* path-continuity field `cont` are gone; their replacements are deterministic.

* `cont` — continuity of `u ↦ (L-K)_{u,a}` for **every** `ω` (not with high probability): for
  the flow `H_u = √u X` this is a deterministic statement, `RBM.Gauss.norm_Hflow_sub`.
* `holder`, `Kmod`, `gam` — a deterministic modulus of continuity for the normalized
  `J*_{u,D}`, the input of the net of (5.46); `gam = 1/2` for `H_u = √u X`
  (`RBM.Gauss.abs_sqrt_sub_sqrt_le`).
* `env`, `env_le` — the deterministic envelope of `J*` (T77, `RBM.Gauss.norm_gloop_le_det`
  together with `RBM.Step2.jStar_le`): it makes dominated convergence available, hence the
  continuity of `φ_q`.

  ⚠ **Quantifier audit (T235).**  `env_le` is the one field of this structure that quantifies
  over *every* `ω`, with no `Good` event, no `HighProb` and no `≺`.  That is **not** the
  defect the satisfiability discipline warns about, for two reasons.  (i) `env : ℕ → ℝ` is a
  *data* field, i.e. the bound is existentially quantified — `env_le` asks only that `J*` be
  *finite* uniformly in `ω`, not that it be small; a pointwise-for-all-`ω` inequality against
  a fixed small right-hand side is what fails at `ω = 0`, and this is not one.  (ii) The time
  quantifier is windowed (`u ∈ Set.Icc (s N) (t N)`), which is what makes (i) true: for
  `t N < 1` the flow Green's functions obey `‖G_u‖ ≤ η_u⁻¹ ≤ η_{t N}⁻¹` for every `ω`.
  The compiled witness is `RBM.Step2Bootstrap.jS_le_rpow`, whose statement is literally
  `∀ ω, Step2.jS X E D N u ω ≤ (1 + C_K) N^{D + 2c_η} + 1`; so `env` may be taken to be that
  right-hand side, and the field is satisfiable rather than vacuous.

  There is deliberately **no** `p` here: `env_le` is not an asymptotic condition, so it is not
  of the forbidden `∀ p N, …` shape and needs no `∀ p, ∀ᶠ N in atTop, …`.  The asymptotic
  fields of this structure (`bnd_lt_thr`, `init`, `step`, `bnd_poly`) already have it.
* `meas` — measurability of `ω ↦ J*_{u,D}`.
* `bnd`, `thr`, `bnd_lt_thr`, `init`, `step`, `bnd_poly` — **(5.39)–(5.41) together with (5.45)
  in moment form**: the a priori bound `E[(J*_u/(η_s/η_u)^4)^q] ≤ Λ_q(N)` on `[s, v]` improves
  itself to `E[(J*_v/(η_s/η_v)^4)^q] ≤ B_q(N) < Λ_q(N)`.  This is the one input that the
  repository cannot supply today: `RBM1D/Gauss/Hierarchy.lean` (T76) produces `∂_u E[L_u]`,
  whereas `RBM.SumZeroDyn.Hierarchy.duhamel` — the pathwise integral identity consumed by
  `RBM.Step2.step_bound` — carries a martingale field and has no moment counterpart yet.
  Bridging the two is T74/T76 work; it is deliberately not faked here. -/
structure MomentHyp (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) where
  /-- Continuity of the paths `u ↦ (L-K)_{u,a}`, for every `ω`. -/
  cont : ∀ (N : ℕ) (ω : Ω) (x : LoopArg (B.L N) 2),
    ContinuousOn (fun u => Step2.lk X E N u ω x) (Set.Icc (s N) (t N))
  /-- The exponent of the deterministic modulus of continuity. -/
  Kmod : ℝ
  /-- The Hölder exponent of the deterministic modulus of continuity (`1/2` for `H_u = √u X`). -/
  gam : ℝ
  Kmod_nonneg : 0 ≤ Kmod
  gam_pos : 0 < gam
  /-- The deterministic modulus of continuity of the normalized `J*`, valid for every `ω`. -/
  holder : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (s N) (t N), ∀ u' ∈ Set.Icc (s N) (t N),
    |jSnorm X E D s N u ω - jSnorm X E D s N u' ω| ≤ (N : ℝ) ^ Kmod * |u - u'| ^ gam
  /-- The deterministic envelope of `J*_{u,D}` (T77). -/
  env : ℕ → ℝ
  env_le : ∀ (N : ℕ), ∀ u ∈ Set.Icc (s N) (t N), ∀ ω : Ω, Step2.jS X E D N u ω ≤ env N
  /-- Measurability of `ω ↦ J*_{u,D}`. -/
  meas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => Step2.jS X E D N u ω) B.P
  /-- The improved bound `B_q(N)` of one step. -/
  bnd : ℕ → ℕ → ℝ
  /-- The a priori threshold `Λ_q(N)` of the bootstrap (the moment form of (5.43)'s `Λ`). -/
  thr : ℕ → ℕ → ℝ
  bnd_lt_thr : ∀ q : ℕ, ∀ᶠ N : ℕ in atTop, bnd q N < thr q N
  /-- The initial bound at `u = s`, from (2.69). -/
  init : ∀ q : ℕ, ∀ᶠ N : ℕ in atTop, phiN X E D s N q (s N) ≤ bnd q N
  /-- **The one-step moment improvement**, (5.39)–(5.41) + (5.45). -/
  step : ∀ q : ℕ, ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (s N) (t N),
    (∀ u ∈ Set.Icc (s N) v, phiN X E D s N q u ≤ thr q N) → phiN X E D s N q v ≤ bnd q N
  /-- `B_q(N)` loses at most `N^{εp}` for every `ε > 0` (the `≺`-margin). -/
  bnd_poly : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    bnd (2 * p) N ≤ C * (N : ℝ) ^ (ε * p)

variable (X : Sample B) {E D : ℝ} {s t : ℕ → ℝ}

/-- `1 ≤ (η_s/η_u)^4` for `s ≤ u < 1`: the weight of the threshold is at least one. -/
theorem one_le_ratR (hE : |E| < 2) {N : ℕ} {u : ℝ} (hsu : s N ≤ u) (hu : u < 1) :
    1 ≤ ratR E s N u := by
  have h1u : 0 < 1 - u := by linarith
  rw [ratR, Step2.etaT_ratio hE, le_div_iff₀ h1u]
  linarith

/-- On `[s, t]` the normalized `J*` is controlled by the deterministic envelope of `J*`. -/
theorem jSnorm_le_env (Hy : MomentHyp X E s t D) (hE : |E| < 2) {N : ℕ} (ht1 : t N < 1)
    {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) (ω : Ω) :
    jSnorm X E D s N u ω ≤ Hy.env N := by
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hR1 : 1 ≤ ratR E s N u := one_le_ratR (s := s) hE hu.1 hu1
  have hR4 : 1 ≤ ratR E s N u ^ 4 := one_le_pow₀ hR1
  have hJ0 : 0 ≤ Step2.jS X E D N u ω := by linarith [one_le_jS X (E := E) (D := D) N u ω]
  calc jSnorm X E D s N u ω ≤ Step2.jS X E D N u ω := by
        rw [jSnorm, div_le_iff₀ (by linarith)]
        nlinarith
    _ ≤ Hy.env N := Hy.env_le N u hu ω

theorem integrable_jSnorm_pow (Hy : MomentHyp X E s t D) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (p N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    Integrable (fun ω => |jSnorm X E D s N u ω| ^ (2 * p)) B.P := by
  have := B.isProbabilityMeasure
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := lt_of_le_of_lt hu.1 hu1
  refine Integrable.mono' (g := fun _ => Hy.env N ^ (2 * p)) (integrable_const _) ?_ ?_
  · have hg : Continuous fun y : ℝ => |y / ratR E s N u ^ 4| ^ (2 * p) := by fun_prop
    exact hg.comp_aestronglyMeasurable (Hy.meas N u)
  · refine Filter.Eventually.of_forall fun ω => ?_
    have h0 : 0 ≤ jSnorm X E D s N u ω := jSnorm_nonneg X hE hs1 hu1 ω
    have hle := jSnorm_le_env X Hy hE (ht1 N) hu ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg h0]
    exact pow_le_pow_left₀ h0 hle _

end Hyp

/-! ### The bootstrap, and (5.47) -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E D : ℝ} {s t : ℕ → ℝ}

/-- **The bootstrap, in the paper's shape (5.43)**: the moment of `J*` stays below
`B_q(N) (η_s/η_u)^{4q}` on the whole of `[s, t]`.

This is the step that used to be the stopping time.  `φ_q` is deterministic and continuous, so
`le_of_bootstrap_weight` — i.e. `RBM.le_of_bootstrap_prefix` — applies directly: the set of
times where the improved bound holds is closed (continuity) and open (self-improvement) in
`[s, t]`, hence all of it.  No optional stopping. -/
theorem phi_le (Hy : MomentHyp X E s t D) (hE : |E| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (q : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      phi X E D N q u ≤ Hy.bnd q N * ratR E s N u ^ (4 * q) := by
  filter_upwards [Hy.bnd_lt_thr q, Hy.init q, Hy.step q] with N h1 h2 h3
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hw : ∀ u ∈ Set.Icc (s N) (t N), 0 < ratR E s N u ^ (4 * q) := fun u hu =>
    pow_pos (ratR_pos hE hs1 (hu.2.trans_lt (ht1 N))) _
  refine le_of_bootstrap_weight (hst N)
    (continuousOn_phi X hE N q (ht1 N) (Hy.cont N) (Hy.env_le N) (Hy.meas N))
    ((continuousOn_ratR hE s N (ht1 N)).pow (4 * q)) hw h1 ?_ ?_
  · rw [← div_le_iff₀ (hw (s N) (Set.left_mem_Icc.2 (hst N))), ← phiN_eq_phi_div]
    exact h2
  · intro v hv hprefix
    rw [← div_le_iff₀ (hw v hv), ← phiN_eq_phi_div]
    refine h3 v hv fun u hu => ?_
    have huIcc : u ∈ Set.Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
    rw [phiN_eq_phi_div, div_le_iff₀ (hw u huIcc)]
    exact hprefix u hu

/-- The bootstrap in normalized form: `E[(J*_{u,D}/(η_s/η_u)^4)^q] ≤ B_q(N)` on `[s, t]`. -/
theorem phiN_le (Hy : MomentHyp X E s t D) (hE : |E| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (q : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N), phiN X E D s N q u ≤ Hy.bnd q N := by
  filter_upwards [phi_le X Hy hE hst ht1 q] with N hN u hu
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hw : 0 < ratR E s N u ^ (4 * q) :=
    pow_pos (ratR_pos hE hs1 (hu.2.trans_lt (ht1 N))) _
  rw [phiN_eq_phi_div, div_le_iff₀ hw]
  exact hN u hu

/-- The moment bounds for `J*_{u,D}/(η_s/η_u)^4` produced by the bootstrap, in the shape
`RBM.Gauss.MomentDom` asks for (`ε` outside `p`). -/
theorem moment_bound (Hy : MomentHyp X E s t D) (hE : |E| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      ∫ ω, |jSnorm X E D s N u ω| ^ (2 * p) ∂B.P ≤ C * (N : ℝ) ^ (ε * p) := by
  intro ε hε p
  obtain ⟨C, hC0, hC⟩ := Hy.bnd_poly ε hε p
  refine ⟨C, hC0, ?_⟩
  filter_upwards [phiN_le X Hy hE hst ht1 (2 * p), hC] with N hN hCN u hu
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  have habs : ∫ ω, |jSnorm X E D s N u ω| ^ (2 * p) ∂B.P = phiN X E D s N (2 * p) u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show |jSnorm X E D s N u ω| ^ (2 * p) = jSnorm X E D s N u ω ^ (2 * p)
    rw [abs_of_nonneg (jSnorm_nonneg X hE hs1 hu1 ω)]
  rw [habs]
  exact (hN u hu).trans hCN

/-- `J*_{u,D}/(η_s/η_u)^4 ≺ 1`, uniformly in `u ∈ [s, t]`: the moment bounds of the bootstrap
plus the deterministic modulus of continuity, through the net of (5.46). -/
theorem stochDom_jSnorm (Hy : MomentHyp X E s t D) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (U := fun N => TimeIcc s t N)
      (fun N u ω => jSnorm X E D s N (u : ℝ) ω) (fun _ _ _ => (1 : ℝ)) := by
  have := B.isProbabilityMeasure
  refine stochDom_timeIcc_of_holder hst (fun N => by linarith [hs0 N, ht1 N])
    Hy.Kmod_nonneg Hy.gam_pos Hy.holder
    (fun p N u hu => integrable_jSnorm_pow X Hy hE ht1 p N hu)
    (moment_bound X Hy hE hst ht1)

/-- **(5.47)**: `J*_{u,D} ≺ (η_s/η_u)^4`, uniformly in `u ∈ [s, t]`, in *exactly* the shape of
`RBM.Step2.jS_stochDom` — but obtained by continuous induction on the deterministic moment
`φ_q`, with no stopping time anywhere. -/
theorem jS_stochDom (Hy : MomentHyp X E s t D) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4) := by
  refine StochDom.of_subset (stochDom_jSnorm X Hy hE hs0 hst ht1) fun τ hτ => ⟨τ, hτ, ?_⟩
  refine Filter.Eventually.of_forall fun N ω hω => ?_
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hR : 0 < ratR E s N (u : ℝ) ^ 4 :=
    pow_pos (ratR_pos hE hs1 (u.2.2.trans_lt (ht1 N))) 4
  show (N : ℝ) ^ τ * 1 < Step2.jS X E D N (u : ℝ) ω / ratR E s N (u : ℝ) ^ 4
  rw [mul_one, lt_div_iff₀ hR]
  exact hu

end Main

/-! ### (2.76) and Step 2 -/

section Conclusions

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **(2.76) from (5.47), from the bare (2.72).**  `RBM.Step2Moment.aprioriDecay_of_jS` with
`hregS` replaced by `RBM.Cond272`: the original's only use of `hregS` is
`RBM.Step2.cond272_of_strict`, so no gain was ever needed here.  The proof script is
unchanged.

(T235: moved here from `RBM.StepGlue.aprioriDecay_of_jS_of_cond272`, which is now the
one-line corollary at the old name.) -/
theorem aprioriDecay_of_jS_of_cond272 (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hJ : ∀ D : ℝ, 60 ≤ D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  intro D₀ hD₀
  set D := max (D₀ + 4) 60 with hDdef
  have hD : 60 ≤ D := le_max_right _ _
  have hDD : D₀ + 4 ≤ D := le_max_left _ _
  have hJD := (hJ D hD).precomp_param
    (V := fun N => TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) fun N p => p.1
  have hW0 : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have hT0 : ∀ N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω),
      0 ≤ Step2.tT B E N D p.1 (zdist (B.L N) (p.2.1 - p.2.2)) :=
    fun N p _ => tailT_nonneg (hW0 N).le _
  have hR0 : ∀ N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω),
      0 ≤ (etaT E (s N) / etaT E p.1) ^ 4 := fun N p _ => by
    have := div_pos (Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N)))
      (Step2.etaT_pos' hE (p.1.2.2.trans_lt (ht1 N)))
    positivity
  have hmul := StochDom.mul hT0 hR0 hJD (StochDom.refl hT0)
  have h272 : Cond272 B E s t := hcond
  refine Step3.stochDom_mono (ζ := fun N p ω => (etaT E (s N) / etaT E p.1) ^ 4 *
      Step2.tT B E N D p.1 (zdist (B.L N) (p.2.1 - p.2.2))) ?_ 1 ?_ ?_
  · intro N p ω
    have := hR0 N p ω
    have hA := B.scale_nonneg E N (p.1.2.2.trans (ht1 N).le)
    have : 0 ≤ B.decayProf N p.1 D₀ p.2.1 p.2.2 := by unfold Band.decayProf; positivity
    positivity
  · filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 h272, Step2.eventually_le_W_sq B] with
      N hcr hW2 p ω
    obtain ⟨-, -, -, hsc⟩ := hcr
    rw [one_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hR0 N p ω)
    exact Step2.tT_le_decayProf hDD (hsc p.1).1 ((hsc p.1).2.1.trans hW2) _ _
  · refine StochDom.of_le_left (fun N p ω => ?_) hmul
    simp only [Pi.mul_apply]
    have h := Step2.le_jStar_mul (f := fun b => ‖Step2.lk X E N p.1 ω b‖) (ℓu := B.ell N p.1)
      (ηu := etaT E p.1) (D := D) (hW0 N) ![p.2.1, p.2.2]
    rw [Step2.norm_lk_eq] at h
    simpa [Step2.jS, Step2.tT] using h

/-- **(2.76) from (5.47)**, route-independent.  The passage from `J*_{u,D} ≺ (η_s/η_u)^4` to
(2.76) uses nothing but the definition (5.29) of `J*` and the deterministic estimates of
`RBM1D/Hierarchy/Step2.lean`; it is the proof of `RBM.Step2.aprioriDecay` with (5.47) taken as
an input, so that either route may supply it. -/
theorem aprioriDecay_of_jS (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hJ : ∀ D : ℝ, 60 ≤ D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1
    (Step2.cond272_of_strict hE hst ht1 hc0 hreg) hJ

/-! #### `rfl`-probe: (2.76) from (5.47) is unchanged (T235)

`RBM.Step2Moment.aprioriDecay_of_jS` is now the one-line corollary of
`RBM.Step2Moment.aprioriDecay_of_jS_of_cond272` along `RBM.Step2.cond272_of_strict` — the
original script's only use of `hreg`.  The probe type-checks only if the two sides are proofs
of the same `Prop`. -/
example (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hJ : ∀ D : ℝ, 60 ≤ D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4)) :
    aprioriDecay_of_jS X hE hs0 hst ht1 hc0 hreg hJ =
      aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1
        (Step2.cond272_of_strict hE hst ht1 hc0 hreg) hJ := rfl

/-- **(2.76)** along the moment route, in exactly the shape of the field
`RBM.Steps.aprioriDecay`. -/
theorem aprioriDecay (Hy : ∀ D : ℝ, 60 ≤ D → MomentHyp X E s t D) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  aprioriDecay_of_jS X hE hs0 hst ht1 hc0 hreg
    fun D hD => jS_stochDom X (Hy D hD) hE hs0 hst ht1

/-- **Step 2 of Theorem 2.21 along the moment route**: (2.75) and (2.76), in exactly the shapes
of the fields `RBM.Steps.localLaw` and `RBM.Steps.aprioriDecay` — the same conclusion as
`RBM.Step2.step2`, with the stopping time (5.43) replaced by continuous induction on the
deterministic moment `φ_q(u) = E[(J*_{u,D})^q]`.

(2.75) is `RBM.Step2.localLaw`, which takes (2.76) and (2.74) as hypotheses and is therefore
common to both routes; (2.74) comes from `RBM.Step1.weakLaw` as in T61. -/
theorem step2 {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentHyp X E s t D) (h1 : Step1.Hyp X E s t)
    (hB : BoundsCore X E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : |E| < 2 := by linarith
  have h276 := aprioriDecay X Hy hE hs0 hst ht1 hc0 hreg
  have hc272 := Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := B) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have h274 := Step1.weakLaw X hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hreg' h1
  exact ⟨Step2.localLaw X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg h276 h274 h1.lemma41, h276⟩

end Conclusions

end Step2Moment

end RBM
