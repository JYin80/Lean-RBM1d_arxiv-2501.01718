/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6EnvWindow
import RBM1D.Gauss.DriftEnvelope
import RBM1D.Gauss.MomentDuhamelHypGauss
import RBM1D.Gauss.Step6DriftSplit

/-!
# Time continuity of `E(L-K)` and interval integrability of `U ∘ E E^{(·)}` (T247)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.129)–(5.131).

## The gap this closes

`RBM.Gauss.bounds_step_gauss_window''` (T234) still carried three analytic hypotheses, the only
ones of its list that belong to no Step of the proof:

* `hcont` — `q ↦ E(L-K)_{q,σ,b}` is continuous on `[s_N, u]`;
* `hintU1` — `v ↦ (U_{v,u} ∘ E E^{((L-K)×(L-K))}_v)_a` is interval integrable on `[s_N, u]`;
* `hintU2` — the same for `E E^{(G)}_v`.

All three are **theorems** for the moment-route model, with no hypothesis beyond the window
(`0 ≤ s_N`, `s_N ≤ u`, `u < 1`).  Nothing is assumed here, so nothing can be vacuous: the three
slots are removed from the hypothesis list of the step theorem rather than restated.

## The route

The three statements are the *expectation* counterparts of the pathwise regularity the moment
route already had, and the exchange is dominated convergence in each case:

1. pathwise, `q ↦ (L-K)_q(ω)`, `q ↦ E^{((L-K)×(L-K))}_q(ω)` and `q ↦ E^{(G)}_q(ω)` are
   continuous on the window and continuous in `ω` at each time —
   `RBM.Gauss.continuousOn_gloop_path`,
   `RBM.Gauss.continuousOn_Kval_path`, `RBM.Gauss.continuousOn_primBil` and
   `RBM.Gauss.continuousOn_eGterm_path` of `RBM1D/Gauss/MomentDuhamelHypGauss.lean` do all of it,
   in the time variable and in the sample variable at once (§1);
2. the crude counting envelopes of T238 (`RBM1D/Gauss/DriftEnvelope.lean`) dominate the
   integrands by a *constant* on `[s, v]`, `v < 1`, uniformly in `ω`, because the flow envelope
   is `η_v^{-m}` and `η_v > 0` (§2);
3. `MeasureTheory.continuousOn_of_dominated` then moves the continuity through `E` (§3), and
   `RBM.Gauss.continuous_edgeKer_time` carries it through `RBM.Uker`, whose sum is finite, so
   `ContinuousOn.intervalIntegrable` closes `hintU1`/`hintU2` (§4).

The measurability chain of T244 (`RBM1D/Flow/Eq548Producer.lean`) is the sibling of §1 for the
`ω` variable; nothing had to be rebuilt because the path lemmas are stated along an arbitrary
continuous Hermitian path and cover both.

## Main results

* `RBM.Gauss.continuousOn_lkT_expect_time` — `hcont`.
* `RBM.Gauss.intervalIntegrable_uker_driftELK`, `intervalIntegrable_uker_driftEG` —
  `hintU1`, `hintU2`.
* `RBM.Gauss.hcont_gauss`, `hintU1_gauss`, `hintU2_gauss` — the same, in the shape
  `RBM.Gauss.bounds_step_gauss_window''` consumes.
* `RBM.Gauss.bounds_step_gauss_window_analytic` — **the step theorem with those three slots
  gone**; what is left is Steps 1–5's own deliverables and the induction data.
* `RBM.Gauss.hcont_hintU_grid` — the non-vacuity witness: all three hold on the non-degenerate
  grid window `[1 - (N+2)⁻¹, 1 - (N+3)⁻¹]`, on which `s_N > 0` and `η_{t_N} → 0`.

## Deviations

None.  These are Lean-internal regularity statements about (5.129)–(5.131); the paper states
the integrated hierarchy and does not name the measurability/continuity side conditions Lean's
`intervalIntegral` asks for, so there is no paper statement to deviate from.
-/

open Filter MeasureTheory

namespace RBM.Gauss

/-! ### §1  The pathwise pieces: `L - K` in `ω` and in time -/

section PathPieces

variable {d : Dims}

/-- `ω ↦ (L - K)_{v}(ω)` at a fixed time along the flow.  This is `RBM.lkPath` read on the
moment-route sample; it is the integrand of `RBM.driftELK` and `RBM.driftEG` seen in `ω`. -/
theorem continuous_lkPath_omega (d : Dims) (E : ℝ) (N : ℕ) {v : ℝ} (hz : (zt E v).im ≠ 0)
    (J : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω : Ω d => lkPath (sample d) E N v ω J := by
  have h : Continuous fun ω : Ω d => gloop (d.L N) (d.W N) (Hflow d N v ω) (zt E v) J :=
    continuous_gloop_Hflow d N v hz J
  have hfun : (fun ω : Ω d => lkPath (sample d) E N v ω J)
      = fun ω : Ω d => gloop (d.L N) (d.W N) (Hflow d N v ω) (zt E v) J
          - (band d).Kval E N v J := rfl
  rw [hfun]
  exact h.sub continuous_const

/-- `q ↦ (L - K)_q(ω)` on a window `[s, v]`, `0 ≤ s`, `v < 1`, along the flow: both the matrix
and the spectral parameter move, and `RBM.Gauss.continuousOn_gloop_path` covers both. -/
theorem continuousOn_lkPath_time (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) (ω : Ω d) (J : LoopIdx (ZMod (d.L N))) (hJ : J.WF) :
    ContinuousOn (fun q : ℝ => lkPath (sample d) E N q ω J) (Set.Icc s v) := by
  have hg : ContinuousOn (fun q : ℝ => gloop (d.L N) (d.W N) (Hflow d N q ω) (zt E q) J)
      (Set.Icc s v) :=
    continuousOn_gloop_path (X := ℝ) d N E (τ := id) (Mt := fun q => Hflow d N q ω)
      continuousOn_id (continuous_Hflow_time d N ω).continuousOn
      (fun q => Hflow_isHermitian d N q ω) (fun q hq => window_im_ne_zero hE hv1 q hq) J
  have hK : ContinuousOn (fun q : ℝ => (band d).Kval E N q J) (Set.Icc s v) :=
    continuousOn_Kval_path (X := ℝ) (band d) E N (τ := id) continuousOn_id
      (fun q hq => window_norm_mul_lt hE.le hs0 hv1 q hq) J hJ
  have hfun : (fun q : ℝ => lkPath (sample d) E N q ω J)
      = fun q : ℝ => gloop (d.L N) (d.W N) (Hflow d N q ω) (zt E q) J
          - (band d).Kval E N q J := rfl
  rw [hfun]
  exact hg.sub hK

/-- `ω ↦ E^{((L-K)×(L-K))}_{v}(ω)` at a fixed time along the flow. -/
theorem continuous_primBil_lkPath_omega (d : Dims) (E : ℝ) (N : ℕ) {v : ℝ}
    (hz : (zt E v).im ≠ 0) (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) :
    Continuous fun ω : Ω d => primBil (d.L N) (d.W N) (lkPath (sample d) E N v ω)
      (lkPath (sample d) E N v ω) I := by
  rw [← continuousOn_univ]
  exact continuousOn_primBil (X := Ω d) (d.W N) I hI
    (fun J _ => (continuous_lkPath_omega d E N hz J).continuousOn)
    (fun J _ => (continuous_lkPath_omega d E N hz J).continuousOn)

/-- `q ↦ E^{((L-K)×(L-K))}_q(ω)` on a window. -/
theorem continuousOn_primBil_lkPath_time (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) (ω : Ω d) (I : LoopIdx (ZMod (d.L N))) (hI : I.WF) :
    ContinuousOn (fun q : ℝ => primBil (d.L N) (d.W N) (lkPath (sample d) E N q ω)
      (lkPath (sample d) E N q ω) I) (Set.Icc s v) :=
  continuousOn_primBil (X := ℝ) (d.W N) I hI
    (fun J hJ => continuousOn_lkPath_time d hE N hs0 hv1 ω J hJ)
    (fun J hJ => continuousOn_lkPath_time d hE N hs0 hv1 ω J hJ)

/-- **The `E^{(G)}` integrand of `RBM.driftEG` is `RBM.Gauss.eGterm`.**  `RBM.lkPath` is the
`X` of `RBM.Decay.eG` and the `G`-loop is its `Y`; `RBM.DriftDef.eGterm_eq_eG` is exactly this
identification, read at the flow. -/
theorem eG_lkPath_eq_eGterm (d : Dims) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω d)
    (I : LoopIdx (ZMod (d.L N))) :
    Decay.eG (d.L N) (d.W N) (lkPath (sample d) E N v ω)
        (gloop (d.L N) (d.W N) ((sample d).H N v ω) (zt E v)) I
      = eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N v ω) (zt E v) I :=
  (DriftDef.eGterm_eq_eG (mSigma E) v (Hflow d N v ω) (zt E v) I).symm

/-- `ω ↦ E^{(G)}_v(ω)` at a fixed time along the flow. -/
theorem continuous_eGterm_omega (d : Dims) (E : ℝ) (N : ℕ) {v : ℝ} (hz : (zt E v).im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω : Ω d => eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N v ω) (zt E v) I := by
  rw [← continuousOn_univ]
  exact continuousOn_eGterm_path (X := Ω d) d N E (τ := fun _ => v)
    (Mt := fun ω => Hflow d N v ω) continuousOn_const (continuous_Hflow d N v).continuousOn
    (fun ω => Hflow_isHermitian d N v ω) (fun _ _ => hz) I

/-- `q ↦ E^{(G)}_q(ω)` on a window. -/
theorem continuousOn_eGterm_time (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hv1 : v < 1) (ω : Ω d) (I : LoopIdx (ZMod (d.L N))) :
    ContinuousOn (fun q : ℝ => eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N q ω) (zt E q) I)
      (Set.Icc s v) :=
  continuousOn_eGterm_path (X := ℝ) d N E (τ := id) (Mt := fun q => Hflow d N q ω)
    continuousOn_id (continuous_Hflow_time d N ω).continuousOn
    (fun q => Hflow_isHermitian d N q ω) (fun q hq => window_im_ne_zero hE hv1 q hq) I

end PathPieces

/-! ### §2  The two drift integrands, bounded uniformly on the window

The bounds are the crude counting bounds of T238 (`RBM1D/Gauss/DriftEnvelope.lean`), not the
sharp estimates of Lemma 5.10: dominated convergence only needs *some* integrable dominating
function, and on a window `[s, v]` with `v < 1` the flow envelope `η_v^{-m}` is a constant.
Note that the bound is uniform in `ω` — it holds at **every** Hermitian matrix — so this is a
deterministic inequality, not a stochastic one in disguise. -/

section Envelopes

/-- **The envelope of `E^{((L-K)×(L-K))}` along the flow**, uniform on the window and in `ω`. -/
theorem exists_norm_primBil_lkPath_win (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d, ∀ (σ : Fin 2 → Bool)
      (b : LoopArg (d.L N) 2),
        ‖primBil (d.L N) (d.W N) (lkPath (sample d) E N u ω) (lkPath (sample d) E N u ω)
          (LoopData.idx (σ, b))‖ ≤ C := by
  obtain ⟨CK, hCK0, hCK⟩ := exists_norm_Kval_le_win (band d) hE 2
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  set MD : ℝ := (etaT E v)⁻¹ ^ 3 + CK * (etaT E v)⁻¹ ^ 2 with hMD
  have hMD0 : 0 ≤ MD := by rw [hMD]; positivity
  refine ⟨(d.W N : ℝ) * (2 : ℝ) ^ 2 * ((d.L N : ℝ) * (MD * MD)), by positivity, ?_⟩
  intro u hu ω σ b
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hu.1
  have hI : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hIlen : (LoopData.idx (σ, b)).length = 2 := LoopData.idx_length _
  have hD : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length →
      J.length ≤ (LoopData.idx (σ, b)).length → ‖lkPath (sample d) E N u ω J‖ ≤ MD := by
    intro J hJ hJ2 hJle
    rw [hIlen] at hJle
    have hg : ‖gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) J‖ ≤ (etaT E v)⁻¹ ^ 3 :=
      norm_gloop_le_win (Hflow_isHermitian d N u ω) hE hu0 hu.2 hv1 3 J hJ (by omega) (by omega)
    have hk : ‖(band d).Kval E N u J‖ ≤ CK * (etaT E v)⁻¹ ^ 2 :=
      hCK N u v hu0 hu.2 hv1 J hJ hJ2 hJle
    have : lkPath (sample d) E N u ω J
        = gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) J - (band d).Kval E N u J := rfl
    rw [this, hMD]
    exact (norm_sub_le _ _).trans (add_le_add hg hk)
  have h := norm_primBil_le_crude (L := d.L N) (d.three_le_L N) (d.W N)
    (lkPath (sample d) E N u ω) (lkPath (sample d) E N u ω) hI hMD0 hMD0 hD hD
  rw [hIlen] at h
  exact_mod_cast h

/-- **The envelope of `E^{(G)}` along the flow**, uniform on the window and in `ω`. -/
theorem exists_norm_eGterm_win (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc s v, ∀ ω : Ω d, ∀ (σ : Fin 2 → Bool)
      (b : LoopArg (d.L N) 2),
        ‖eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N u ω) (zt E u)
          (LoopData.idx (σ, b))‖ ≤ C := by
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  set MG : ℝ := (etaT E v)⁻¹ ^ 3 with hMG
  have hMG0 : 0 ≤ MG := by rw [hMG]; positivity
  refine ⟨(d.W N : ℝ) * (2 : ℝ) * ((d.L N : ℝ) * ((MG + 1) * MG)), by positivity, ?_⟩
  intro u hu ω σ b
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hu.1
  have hI : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hIlen : (LoopData.idx (σ, b)).length = 2 := LoopData.idx_length _
  have hg : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 1 ≤ J.length → J.length ≤ 3 →
      ‖gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) J‖ ≤ MG :=
    fun J hJ h1 h3 => norm_gloop_le_win (Hflow_isHermitian d N u ω) hE hu0 hu.2 hv1 3 J hJ h1 h3
  have h := norm_eGterm_le_crude (L := d.L N) (W := d.W N) (d.three_le_L N)
    (M := Hflow d N u ω) hE (u := u) hI hMG0 hMG0
    (fun s' a => hg _ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length]))
    (fun k hk1 hk2 b' => hg _ (LoopIdx.WF.cutGlue b' hI hk1 hk2)
      (by have := LoopIdx.length_cutGlue (LoopData.idx (σ, b)) b' hk2; omega)
      (by have := LoopIdx.length_cutGlue (LoopData.idx (σ, b)) b' hk2; omega))
  rw [hIlen] at h
  exact_mod_cast h

end Envelopes

/-! ### §3  The expectations: dominated convergence in the time variable

Nothing here is `ω`-quantified as an inequality: the continuity statements are structural and
hold at every sample point, and the only inequality used is §2's deterministic envelope. -/

section Expectations

/-- **`v ↦ E E^{((L-K)×(L-K))}_{v,σ,b}` is continuous on the window.** -/
theorem continuousOn_driftELK_time (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) (σ : Fin 2 → Bool) (b : LoopArg (d.L N) 2) :
    ContinuousOn (fun q : ℝ => driftELK (sample d) E N q σ b) (Set.Icc s v) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_primBil_lkPath_win d hE N hs0 hv1
  have hI : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hEq : ∀ q : ℝ, driftELK (sample d) E N q σ b
      = ∫ ω, primBil (d.L N) (d.W N) (lkPath (sample d) E N q ω)
          (lkPath (sample d) E N q ω) (LoopData.idx (σ, b)) ∂(P d) := fun _ => rfl
  simp only [hEq]
  refine MeasureTheory.continuousOn_of_dominated (bound := fun _ => C)
    (fun q hq => (continuous_primBil_lkPath_omega d E N
      (window_im_ne_zero hE hv1 q hq) _ hI).aestronglyMeasurable)
    (fun q hq => Filter.Eventually.of_forall fun ω => hC q hq ω σ b)
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω =>
      continuousOn_primBil_lkPath_time d hE N hs0 hv1 ω _ hI)

/-- **`v ↦ E E^{(G)}_{v,σ,b}` is continuous on the window.** -/
theorem continuousOn_driftEG_time (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) (σ : Fin 2 → Bool) (b : LoopArg (d.L N) 2) :
    ContinuousOn (fun q : ℝ => driftEG (sample d) E N q σ b) (Set.Icc s v) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_eGterm_win d hE N hs0 hv1
  have hEq : ∀ q : ℝ, driftEG (sample d) E N q σ b
      = ∫ ω, eGterm (d.L N) (d.W N) (mSigma E) (Hflow d N q ω) (zt E q)
          (LoopData.idx (σ, b)) ∂(P d) := by
    intro q
    change ∫ ω, Decay.eG (d.L N) (d.W N) (lkPath (sample d) E N q ω)
      (gloop (d.L N) (d.W N) ((sample d).H N q ω) (zt E q)) (LoopData.idx (σ, b)) ∂(P d) = _
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun ω => eG_lkPath_eq_eGterm d E N q ω _)
  simp only [hEq]
  refine MeasureTheory.continuousOn_of_dominated (bound := fun _ => C)
    (fun q hq => (continuous_eGterm_omega d E N
      (window_im_ne_zero hE hv1 q hq) _).aestronglyMeasurable)
    (fun q hq => Filter.Eventually.of_forall fun ω => hC q hq ω σ b)
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω => continuousOn_eGterm_time d hE N hv1 ω _)

/-- **`q ↦ E(L-K)_{q,σ,b}` is continuous on the window** — the `hcont` slot.

`E L_q` is a Bochner integral of the `G`-loop (`RBM.Gauss.integrable_sample_Lval`), so the
statement is dominated convergence again, with `K_q` coming out of the integral because `P` is
a probability measure. -/
theorem continuousOn_lkT_expect_time (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) (σ : Fin 2 → Bool) (b : LoopArg (d.L N) 2) :
    ContinuousOn (fun q : ℝ => Step6.lkT (sample d) E N q σ b) (Set.Icc s v) := by
  obtain ⟨CK, hCK0, hCK⟩ := exists_norm_Kval_le_win (band d) hE 2
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one hE hv1
  have hI : (LoopData.idx (σ, b)).WF := LoopData.idx_wf _
  have hIlen : (LoopData.idx (σ, b)).length = 2 := LoopData.idx_length _
  have hlen : (LoopData.idx (σ, b)).a.length = 2 := hIlen
  -- the integral form of `E(L-K)` on the window
  have hEq : ∀ q ∈ Set.Icc s v, Step6.lkT (sample d) E N q σ b
      = ∫ ω, lkPath (sample d) E N q ω (LoopData.idx (σ, b)) ∂(P d) := by
    intro q hq
    have hq0 : (0 : ℝ) ≤ q := hs0.trans hq.1
    have hq1 : q < 1 := lt_of_le_of_lt hq.2 hv1
    have hint : Integrable
        (fun ω : Ω d => (sample d).Lval E N q ω (LoopData.idx (σ, b))) (P d) :=
      integrable_sample_Lval (etaT_pos_of_lt_one hE hq1) (abs_im_zt E hE hq1).ge _ hI
        (by simp [LoopData.idx])
    have hfun : (fun ω : Ω d => lkPath (sample d) E N q ω (LoopData.idx (σ, b)))
        = fun ω : Ω d => (sample d).Lval E N q ω (LoopData.idx (σ, b))
            - (band d).Kval E N q (LoopData.idx (σ, b)) := rfl
    rw [hfun, integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    rfl
  -- dominated convergence for the integral form
  have hcont : ContinuousOn
      (fun q : ℝ => ∫ ω, lkPath (sample d) E N q ω (LoopData.idx (σ, b)) ∂(P d))
      (Set.Icc s v) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun _ => (etaT E v)⁻¹ ^ 3 + CK * (etaT E v)⁻¹ ^ 2)
      (fun q hq => (continuous_lkPath_omega d E N
        (window_im_ne_zero hE hv1 q hq) _).aestronglyMeasurable)
      (fun q hq => Filter.Eventually.of_forall fun ω => ?_)
      (integrable_const _)
      (Filter.Eventually.of_forall fun ω =>
        continuousOn_lkPath_time d hE N hs0 hv1 ω _ hI)
    have hq0 : (0 : ℝ) ≤ q := hs0.trans hq.1
    have hg : ‖gloop (d.L N) (d.W N) (Hflow d N q ω) (zt E q) (LoopData.idx (σ, b))‖
        ≤ (etaT E v)⁻¹ ^ 3 :=
      norm_gloop_le_win (Hflow_isHermitian d N q ω) hE hq0 hq.2 hv1 3 _ hI
        (by simp) (by simp)
    have hk : ‖(band d).Kval E N q (LoopData.idx (σ, b))‖ ≤ CK * (etaT E v)⁻¹ ^ 2 :=
      hCK N q v hq0 hq.2 hv1 _ hI (LoopData.idx_length _).ge (LoopData.idx_length _).le
    have hrw : lkPath (sample d) E N q ω (LoopData.idx (σ, b))
        = gloop (d.L N) (d.W N) (Hflow d N q ω) (zt E q) (LoopData.idx (σ, b))
          - (band d).Kval E N q (LoopData.idx (σ, b)) := rfl
    rw [hrw]
    exact (norm_sub_le _ _).trans (add_le_add hg hk)
  exact hcont.congr hEq

end Expectations

/-! ### §4  The propagator applied to a continuous tensor -/

section UkerInt

/-- `RBM.Uker` with a **moving** running time and a continuously varying tensor is continuous:
the kernel is `RBM.Gauss.continuous_edgeKer_time` in the running time, and the sum is finite. -/
theorem continuousOn_uker_of_tensor {L n : ℕ} [NeZero L] (ξ : Fin n → ℂ) (t : ℂ)
    {S : Set ℝ} {A : ℝ → LoopArg L n → ℂ}
    (hA : ∀ b : LoopArg L n, ContinuousOn (fun q : ℝ => A q b) S) (a : LoopArg L n) :
    ContinuousOn (fun q : ℝ => Uker L ξ ((q : ℝ) : ℂ) t (A q) a) S := by
  simp only [Uker]
  refine continuousOn_finsetSum _ fun b _ => ?_
  exact ((continuous_finsetProd _ fun i _ =>
    continuous_edgeKer_time (ξ i) t (a i) (b i)).continuousOn).mul (hA b)

/-- **The `hintU1` slot**: `v ↦ (U_{v,u} ∘ E E^{((L-K)×(L-K))}_v)_a` is interval integrable. -/
theorem intervalIntegrable_uker_driftELK (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) (σ : Fin 2 → Bool)
    (a : LoopArg ((band d).L N) 2) :
    IntervalIntegrable (fun q : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((q : ℝ) : ℂ)
      ((v : ℝ) : ℂ) (driftELK (sample d) E N q σ) a) volume s v := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hsv]
  exact continuousOn_uker_of_tensor _ _
    (fun b => continuousOn_driftELK_time d hE N hs0 hv1 σ b) a

/-- **The `hintU2` slot**: `v ↦ (U_{v,u} ∘ E E^{(G)}_v)_a` is interval integrable. -/
theorem intervalIntegrable_uker_driftEG (d : Dims) {E : ℝ} (hE : |E| < 2) (N : ℕ) {s v : ℝ}
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) (σ : Fin 2 → Bool)
    (a : LoopArg ((band d).L N) 2) :
    IntervalIntegrable (fun q : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((q : ℝ) : ℂ)
      ((v : ℝ) : ℂ) (driftEG (sample d) E N q σ) a) volume s v := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hsv]
  exact continuousOn_uker_of_tensor _ _
    (fun b => continuousOn_driftEG_time d hE N hs0 hv1 σ b) a

end UkerInt

/-! ### §5  The step theorem with the three analytic slots removed -/

section Assembly

/-- **The `hcont` slot of `RBM.Gauss.bounds_step_gauss_window`, discharged.** -/
theorem hcont_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT (sample d) E N q σ b)
        (Set.Icc (s N) ((u : ℝ))) :=
  fun N u σ b =>
    continuousOn_lkT_expect_time d hE N (hs0 N) (lt_of_le_of_lt u.2.2 (ht1 N)) σ b

/-- **The `hintU1` slot of `RBM.Gauss.bounds_step_gauss_window`, discharged.** -/
theorem hintU1_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK (sample d) E N v σ) a) volume (s N) (u : ℝ) :=
  fun N u σ a =>
    intervalIntegrable_uker_driftELK d hE N (hs0 N) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 N)) σ a

/-- **The `hintU2` slot of `RBM.Gauss.bounds_step_gauss_window`, discharged.** -/
theorem hintU2_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg ((band d).L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG (sample d) E N v σ) a) volume (s N) (u : ℝ) :=
  fun N u σ a =>
    intervalIntegrable_uker_driftEG d hE N (hs0 N) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 N)) σ a

/-- **`RBM.Gauss.bounds_step_gauss_window''` with `hcont`, `hintU1` and `hintU2` discharged.**

Every hypothesis left is either Steps 1–5's own deliverable (`hFI`, `H`, `h0`, `h12`, `h514`,
`h1`, `h2`, `hlmk`) or the induction data (`hc`, `hη`, `hBC`, `hB`).  **No hypothesis of this
theorem is analytic**: the three slots T234 left open are theorems of §3–§4 above, so the list
shrinks from ten (`RBM.Gauss.bounds_step_gauss_window`) to seven (T234) to four-plus-data. -/
theorem bounds_step_gauss_window_analytic (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hFI : LKDecayQuant.FlowInputs (sample d) E s t)
    (H : Step3.Hyp (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowXiL (sample d) E s t) (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t)
      (Step3.flowA (band d) E s t))
    (h0 : ∀ m, 1 ≤ m → Step3.S (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t) (Step3.flowA (band d) E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t) (Step3.flowA (band d) E s t) m l)
    (h514 : Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) 2)
    (h1 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 1) fun _ _ _ => (1 : ℝ))
    (h2 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2)
      fun N u _ => Step3.flowA (band d) E s t N u ^ ((1 : ℝ) / 4))
    (hlmk : SharpLmKFlow (sample d) E s t)
    (hBC : BoundsCore (sample d) E t) (hB : Bounds (sample d) E s) :
    Bounds (sample d) E t := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  exact bounds_step_gauss_window'' d hκ0 hκ1 hEκ hs0 hst ht1 hc hc0 hη
    (hcont_gauss d hE hs0 ht1) (hintU1_gauss d hE hs0 ht1) (hintU2_gauss d hE hs0 ht1)
    hFI H h0 h12 h514 h1 h2 hlmk hBC hB

/-- **Satisfiability witness.**  The three slots are *theorems*, so there is no new hypothesis to
satisfy; what could still be empty is the **window**.  On T227/T234's non-degenerate grid window
`[1 - (N+2)⁻¹, 1 - (N+3)⁻¹]` at `E = 0` — the window with `s_N > 0`, `s_N < t_N` and
`1 - t_N ≍ N^{-1}`, so that `η_{t_N} → 0` and the envelopes of §2 blow up — all three hold
simultaneously.  They are therefore not statements about a collapsed window or about a scale
bounded away from the spectral edge. -/
theorem hcont_hintU_grid (d : Dims) :
    (∀ N (u : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool) (b : LoopArg ((band d).L N) 2),
        ContinuousOn (fun q : ℝ => Step6.lkT (sample d) 0 N q σ b)
          (Set.Icc (envWinS N) ((u : ℝ)))) ∧
      (∀ N (u : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool)
          (a : LoopArg ((band d).L N) 2),
        IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma 0) σ) ((v : ℝ) : ℂ)
          (((u : ℝ)) : ℂ) (driftELK (sample d) 0 N v σ) a) volume (envWinS N) (u : ℝ)) ∧
      (∀ N (u : TimeIcc envWinS envWinT N) (σ : Fin 2 → Bool)
          (a : LoopArg ((band d).L N) 2),
        IntervalIntegrable (fun v : ℝ => Uker ((band d).L N) (xiOf (mSigma 0) σ) ((v : ℝ) : ℂ)
          (((u : ℝ)) : ℂ) (driftEG (sample d) 0 N v σ) a) volume (envWinS N) (u : ℝ)) ∧
      (∀ N, 0 < envWinS N) ∧ (∀ N, envWinS N < envWinT N) ∧ (∀ N, envWinT N < 1) := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hs0 : ∀ N, (0 : ℝ) ≤ envWinS N := fun N => (envWinS_pos N).le
  exact ⟨hcont_gauss d hE hs0 envWinT_lt_one, hintU1_gauss d hE hs0 envWinT_lt_one,
    hintU2_gauss d hE hs0 envWinT_lt_one, envWinS_pos, envWinS_lt_envWinT, envWinT_lt_one⟩

end Assembly

end RBM.Gauss
