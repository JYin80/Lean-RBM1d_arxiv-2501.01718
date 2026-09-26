/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridGoodSet
import RBM1D.Gauss.GridExpansion
import RBM1D.Gauss.GridQVForm
import RBM1D.Gauss.GridQVStep
import RBM1D.Gauss.GridQVSum
import RBM1D.Gauss.GridDuhamelTail
import RBM1D.Gauss.GridNetLift

/-!
# T1519 — the grid stopping time and the good event (R4c-1)

Ticket `docs/tickets/T1519.md` with `docs/tickets/T1519-amend-1.md` (the amend supersedes the
original (T3), (T4), (T6)); supervisor `docs/supervisor/2026-09-26-0048.md` §1e, §1f, §1g,
§2 R4, §3.
Report: `docs/reports/T1519-prove.md`.

Fixed data: `d : Dims`, an energy `E`, times `s ≤ u ≤ t < 1` (`u` is the grid endpoint sequence),
a grid size `K`, `u_j := time s u K N j`, `Δ := step s u K N`, the threshold
`thr(v) := Step2.thr E s δ N v = N^δ (η_s/η_v)^4`, and the good set
`G(v) := goodSet d E N v ℓ_s τ₁ ε ζCtr τ3 τ57 D` of T1513 with `ℓ_s := (band d).ell N (s N)`.

## Main results

* (T1) `gridTau`, `isStoppingTime_gridTau`, `lt_gridTau_measurableSet`, `lt_gridTau_imp`,
  `gridTau_le`: the grid stopping time
  `τ = min (firstHit (jSMat(u_j,H_j) − thr(u_j)) 0 K) (firstHit (1_{G(u_j)ᶜ}(H_j)) (1/2) K)`.
* (T2) `thr_le_sqrtN`, `hsubG_gridTau`: T1504 (T1″)'s `hsubG` for `Z := Zvec` (T1516) and
  `τ := gridTau`, with the explicit constants `cZ` (positive floor `Δ N^{-C_c}` included,
  `floor_le_cZ`) built from `Qprime` (T1514's rate at `J = N^{2ε} thr(u_j)`, via T1508's `Qd`),
  eventually in `N`, uniformly in `k ≤ K N`, labels `a` and `j < k`; the hypotheses are jointly
  satisfiable (`hsubG_gridTau_hyps_witness`). Glue lemmas: `ukerMat_eq_prod_re`,
  `quadVar_Φgrid_eq`, `jGMat_nonneg`, `time_succ_eq`, `time_mono_of_le`.
* (T3′) `highProb_azuma_grid'`: the Azuma event with the threshold
  `xZ k a = N^{δ/16} √(4 Σ_{j<k} cZ k a j + N^{-C_x})` (floor inside the root) holds with high
  probability for all `k ≤ K N` (including `k = 0` and `Δ = 0`), for any polynomial grid; the
  deterministic consequence `xZ_le_azumaMm` (`xZ k a ≤ Mm (R_k²+1) T_{u_k}(a)` with the explicit
  `Mm = azumaMm`) and `azumaMm_le` (`Mm ≤ N^{δ/8}` for `τ₁ ≤ δ/32`).
* (T4′) `cheb_grid_at_tau`: for every `D₁ > 0`, on the grid `gridK D D₁ = ⌈N^{C_K}⌉` with
  `C_K = CK D D₁ = D₁ + 2D + 80`, the Chebyshev event for the stopped remainder **at the random
  target `u_τ`** has probability `≤ N^{-D₁}` eventually (no union over targets).
* (T5) `highProb_init_grid`: the initial value on the grid, `‖A_0 b‖ ≤ N^{δ/16} T_{u_0}(b)` and
  `jSMat(u_0,H_0) < thr(u_0)`, with high probability.
* (T6′) `goodEventGrid`, `goodEvent_grid`, `goodEvent_grid_imp`: for every `D₁ > 0`, with
  `K = gridK D (D₁+1)` and `C_c = C_x = 2D+2`, the complement of the good event has probability
  `≤ N^{-D₁}` eventually; on it, T1518 (T1)'s `hinit`, `hZ`, `hY` hold at `k = τ(ω)`, together with
  the good-set memberships and the side conditions of T1518 (T3). Joint satisfiability of the
  parameter constraints: `goodEvent_grid_params_witness`.
* The original (T3) was false as written (`x 0 a = 0`, event `‖0‖ < 0`); its negation is kept only
  as the counterexample `not_highProb_azuma_grid_literal(')` to the superseded spec, and is not part
  of the (T3′) API.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable (d : Dims)

/-! ## (T1) : the grid stopping time -/

section T1

/-- **(T1) `gridTau`**: the first grid index at which either `J*` reaches the time-dependent
threshold, `jSMat(u_j, H_j) ≥ thr(u_j)`, or the grid state leaves the good set, `H_j ∉ G(u_j)`
(`K N` if neither happens). -/
def gridTau (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) : ℕ :=
  min (firstHit (fun j (ω : Ωg d) => jSMat d E D N (time s u K N j) (H d s u K N j ω)
      - Step2.thr E s δ N (time s u K N j)) 0 (K N) ω)
    (firstHit (fun j (ω : Ωg d) =>
      (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
        (fun _ => (1 : ℝ)) (H d s u K N j ω)) (1 / 2) (K N) ω)

variable {d}

private theorem measurable_tauJ (E D δ : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      jSMat d E D N (time s u K N j) M - Step2.thr E s δ N (time s u K N j)) :=
  (measurable_jSMat d E D N _).sub measurable_const

private theorem measurable_tauG {E : ℝ} (hE : |E| < 2) (τ₁ ε ζCtr τ3 τ57 D : ℝ) (s u : ℕ → ℝ)
    (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
        (fun _ => (1 : ℝ)) M) :=
  measurable_const.indicator (measurableSet_goodSet d E N _ _ τ₁ ε ζCtr τ3 τ57 D hE).compl

/-- **(T1)** `gridTau` is a stopping time for the coordinate filtration. -/
theorem isStoppingTime_gridTau {E : ℝ} (hE : |E| < 2) (D δ τ₁ ε ζCtr τ3 τ57 : ℝ)
    (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) :
    IsStoppingTime (filt d) (fun ω => (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω : ℕ)) :=
  isStoppingTime_min_firstHit_grid d s u K N
    (F := fun j M => jSMat d E D N (time s u K N j) M - Step2.thr E s δ N (time s u K N j))
    (F' := fun j M => (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57
      D)ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (measurable_tauJ E D δ s u K N) (measurable_tauG hE τ₁ ε ζCtr τ3 τ57 D s u K N) 0 (1 / 2)
    (K N)

/-- **(T1)** `{j < gridTau}` is `filt d j`-measurable (T1504's `hτmeas`). -/
theorem lt_gridTau_measurableSet {E : ℝ} (hE : |E| < 2) (D δ τ₁ ε ζCtr τ3 τ57 : ℝ)
    (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    MeasurableSet[filt d j] {ω | j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω} :=
  lt_min_firstHit_grid_measurableSet d s u K N
    (F := fun j M => jSMat d E D N (time s u K N j) M - Step2.thr E s δ N (time s u K N j))
    (F' := fun j M => (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57
      D)ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (measurable_tauJ E D δ s u K N) (measurable_tauG hE τ₁ ε ζCtr τ3 τ57 D s u K N) 0 (1 / 2)
    (K N) j

/-- **(T1)** Strictly before `gridTau`, `J*` is below the threshold and the grid state is in the
good set. -/
theorem lt_gridTau_imp {E D δ τ₁ ε ζCtr τ3 τ57 : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} (h : j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω) :
    jSMat d E D N (time s u K N j) (H d s u K N j ω) < Step2.thr E s δ N (time s u K N j) ∧
      H d s u K N j ω ∈
        goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D := by
  obtain ⟨h1, h2⟩ := lt_min_firstHit_imp _ _ _ _ _ h
  refine ⟨by linarith, ?_⟩
  by_contra hmem
  have h2' : (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
      (fun _ => (1 : ℝ)) (H d s u K N j ω) < 1 / 2 := h2
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h2'
  norm_num at h2'

/-- `gridTau ≤ K N`. -/
theorem gridTau_le (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) :
    gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω ≤ K N :=
  (min_le_left _ _).trans (firstHit_le _ _ _ ω)

end T1

/-! ## Counterexample to the superseded original (T3) spec (not part of the (T3′) API) -/

section T3

variable {d}

/-- **Counterexample to the superseded original T1519 (T3) spec** (T1519-amend-1 replaces it by
(T3′) `highProb_azuma_grid'`; this lemma is not part of the (T3′) API). For *any* stopping
index `τ`, increments `Z`, and constants `c`,
the event `{∀ k ≤ K, ∀ a, ‖(Σ_{j<min(k,τ)} Uker 1 u_{j+1} u_k Z_{j+1}) a‖ <
N^{δ/16} √(4 Σ_{j<k} c k a j)}`
of the ticket's (T3) is empty for every `N`: at `k = 0` it reads `‖0‖ < N^{δ/16}·√0 = 0`. So it
does not hold with high probability. (The ticket's remark "`x 0 a > 0` handles the `k = 0` term"
contradicts its own formula for `x`.) See the report for the suggested amendment. -/
theorem not_highProb_azuma_grid_literal (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℝ)
    (τ : ℕ → Ωg d → ℕ) (Z : ∀ N, ℕ → Ωg d → LoopArg (d.L N) 2 → ℂ)
    (c : ∀ N, ℕ → LoopArg (d.L N) 2 → ℕ → ℝ) :
    ¬ HighProb (Pg d) (fun N => {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (τ N ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ) (Z N (j + 1) ω)) a‖
        < (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ∑ j ∈ Finset.range k, c N k a j)}) := by
  intro h
  have hne := HighProb.nonempty (measure_univ (μ := Pg d)) h
  obtain ⟨N, hN⟩ := hne.exists
  obtain ⟨ω, hω⟩ := hN
  have h0 := hω 0 (Nat.zero_le _) (fun _ => 0)
  simp at h0

/-- **Counterexample to the superseded original (T3) spec, literal instance** (not part of the
(T3′) API): the original ticket's event with `Z := Zvec` (T1516) and `τ := gridTau`
does not hold with high probability, whatever the constants `c`. -/
theorem not_highProb_azuma_grid_literal' (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ)
    (K : ℕ → ℕ) (c : ∀ N, ℕ → LoopArg (d.L N) 2 → ℕ → ℝ) :
    ¬ HighProb (Pg d) (fun N => {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) E s u K N (j + 1) ω)) a‖
        < (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ∑ j ∈ Finset.range k, c N k a j)}) :=
  not_highProb_azuma_grid_literal s u K δ (fun N => gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N)
    (fun N i ω => Zvec (band d) E s u K N i ω) c

end T3


/-! ## (T5) : the initial value on the grid -/

section T5

variable {d}

private theorem ofFn_pm_eq_pmLoop {L : ℕ} (b : LoopArg L 2) :
    (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod L)) = pmLoop (b 0) (b 1) := by
  simp [pmLoop, List.ofFn_succ]

private theorem Lval_band_eq (E : ℝ) (N : ℕ) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (b : LoopArg (d.L N) 2) :
    Lval (band d) E N v M b = gloop (d.L N) (d.W N) M (zt E v) (pmLoop (b 0) (b 1)) := by
  change gloop (d.L N) (d.W N) M (zt E v) ⟨[true, false], List.ofFn b⟩ = _
  rw [ofFn_pm_eq_pmLoop]

private theorem Kv_band_eq (E : ℝ) (N : ℕ) (v : ℝ) (b : LoopArg (d.L N) 2) :
    Kv (band d) E N v b = (band d).Kval E N v (pmLoop (b 0) (b 1)) := by
  unfold Kv pmLoop
  congr 2

/-- The matrix set of the initial bound at time `v`, with multiplier `x`. -/
def initSet (E : ℝ) (N : ℕ) (v D x : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ b : LoopArg (d.L N) 2, ‖Lval (band d) E N v M b - Kv (band d) E N v b‖ ≤
    x * Step2.tT (band d) E N D v (zdist (d.L N) (b 0 - b 1))}

theorem measurableSet_initSet (E : ℝ) (N : ℕ) (v D x : ℝ) :
    MeasurableSet (initSet (d := d) E N v D x) := by
  have heq : initSet (d := d) E N v D x = ⋂ b : LoopArg (d.L N) 2,
      {M | ‖Lval (band d) E N v M b - Kv (band d) E N v b‖ ≤
        x * Step2.tT (band d) E N D v (zdist (d.L N) (b 0 - b 1))} := by
    exact Set.ofPred_forall _
  rw [heq]
  refine MeasurableSet.iInter fun b => measurableSet_le ?_ measurable_const
  exact ((measurable_gloop_matrix d N (zt E v) _).sub measurable_const).norm

/-- On `initSet … x`, `jSMat ≤ x + 1`. -/
theorem jSMat_le_of_mem_initSet {E : ℝ} {N : ℕ} {v D x : ℝ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M ∈ initSet (d := d) E N v D x) :
    jSMat d E D N v M ≤ x + 1 := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  unfold jSMat Step2.jStar
  refine add_le_add (Finset.sup'_le _ _ fun a _ => ?_) le_rfl
  have hT := tailT_pos (ℓu := (band d).ell N v) (ηu := etaT E v) (D := D) hW
    (zdist (d.L N) (a 0 - a 1) : ℝ)
  rw [div_le_iff₀ hT]
  have ha := hM a
  rw [Lval_band_eq, Kv_band_eq] at ha
  dsimp only
  rw [Step2.idx_sigPM]
  exact ha

/-- **(T5) `highProb_init_grid`**: with high probability, the grid initial value `A_0` obeys
`‖A_0 b‖ ≤ N^{δ/16} T_{u_0}(b)` for every label `b` (the input shape `hinit` of T1518 (T1) with
`Mi = N^{δ/16}`), and `J*` starts below the threshold, `jSMat(u_0,H_0) < thr(u_0) = N^δ`, so that
`gridTau > 0` w.h.p. Source: (2.69) at `s` (`hB.decay`), transferred to the grid by the law of
`H_0 = √s X_0` (`map_H_eq` at `k = 0`). -/
theorem highProb_init_grid {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ}
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hD : 0 < D) (hsu : ∀ N, s N ≤ u N) (K : ℕ → ℕ)
    (hK0 : ∀ N, K N ≠ 0) :
    HighProb (Pg d) (fun N => {ω |
      (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) E s u K N 0 ω b‖ ≤
        (N : ℝ) ^ (δ / 16) * Step2.tT (band d) E N D (time s u K N 0)
          (zdist (d.L N) (b 0 - b 1)))
      ∧ jSMat d E D N (time s u K N 0) (H d s u K N 0 ω)
        < Step2.thr E s δ N (time s u K N 0)}) := by
  have hδ16 : 0 < δ / 16 := by positivity
  have G := (hB.decay D hD).highProb hδ16
  set S : ∀ N, Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
    fun N => initSet (d := d) E N (s N) D ((N : ℝ) ^ (δ / 16)) with hSdef
  have hSmeas : ∀ N, MeasurableSet (S N) := fun N => measurableSet_initSet _ _ _ _ _
  have hscale : ∀ᶠ N : ℕ in atTop, 1 ≤ (band d).scale E N (s N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := band d) hE hst ht1 hc0 hreg,
      eventually_ge_atTop 1] with N hN hN1
    have h1 := (hN ⟨s N, le_rfl, hst N⟩).2
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact (Real.one_le_rpow hN1' hc0.le).trans h1
  have Gflow : HighProb (P d) (fun N => {ω | Hflow d N (s N) ω ∈ S N}) := by
    refine G.mono ?_
    filter_upwards [hscale] with N hN ω hω b
    have h1 := hω (b 0, b 1)
    have e : ‖Lval (band d) E N (s N) (Hflow d N (s N) ω) b - Kv (band d) E N (s N) b‖ =
        (sample d).lkErr E N (s N) ω (pmLoop (b 0) (b 1)) := by
      rw [Lval_band_eq, Kv_band_eq]
      rfl
    change ‖Lval (band d) E N (s N) (Hflow d N (s N) ω) b - Kv (band d) E N (s N) b‖ ≤ _
    rw [e]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Step2.decayProf_le_tT (B := band d) hN (b 0) (b 1)
  have Ggrid : HighProb (Pg d) (fun N => {ω | H d s u K N 0 ω ∈ S N}) := by
    intro D' hD'
    filter_upwards [Gflow D' hD'] with N hN
    have hHmeas : Measurable (H d s u K N 0) :=
      (H_measurable_filt d s u K N 0).mono ((filt d).le 0) le_rfl
    have hHflowmeas : Measurable (Hflow d N (s N)) := RBM.measurable_H (sample d) N (s N)
    have heq : (Pg d) {ω | H d s u K N 0 ω ∈ S N}ᶜ = (P d) {ω | Hflow d N (s N) ω ∈ S N}ᶜ := by
      change (Pg d) ((H d s u K N 0) ⁻¹' S N)ᶜ = (P d) ((Hflow d N (s N)) ⁻¹' S N)ᶜ
      rw [← Set.preimage_compl, ← Set.preimage_compl,
        ← Measure.map_apply hHmeas (hSmeas N).compl,
        ← Measure.map_apply hHflowmeas (hSmeas N).compl,
        map_H_eq s u K N 0 (hs0 N) (hsu N) (hK0 N), time_zero]
    rw [heq]; exact hN
  refine Ggrid.mono ?_
  filter_upwards [eventually_le_rpow 2 hδ16, eventually_ge_atTop 1] with N h2 hN1 ω hω
  have hω' : H d s u K N 0 ω ∈ S N := hω
  refine ⟨fun b => ?_, ?_⟩
  · have := hω' b
    change ‖Lval (band d) E N (time s u K N 0) (H d s u K N 0 ω) b
      - Kv (band d) E N (time s u K N 0) b‖ ≤ _
    rw [time_zero]
    exact this
  · rw [time_zero]
    have hj := jSMat_le_of_mem_initSet hω'
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hη : etaT E (s N) ≠ 0 := (Step2.etaT_pos' hE hs1).ne'
    have hthr : Step2.thr E s δ N (s N) = (N : ℝ) ^ δ := by
      unfold Step2.thr; rw [div_self hη]; ring
    rw [hthr]
    set y := (N : ℝ) ^ (δ / 16) with hy
    have hpow : y ^ (16 : ℕ) = (N : ℝ) ^ δ := by
      rw [hy, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 1; push_cast; ring
    have hy1 : (1 : ℝ) ≤ y := by linarith
    have h16 : y ^ (2 : ℕ) ≤ y ^ (16 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
    rw [← hpow]
    nlinarith

end T5


/-! ## (T2) : the Azuma input `hsubG` for `Zvec` and `gridTau` -/

section T2

variable {d}

/-- **`thr ≤ N^{1/2}`** (supervisor 0048 §1e, §3): with step2's gained (2.72)
`N^c (η_s/η_t)^30 ≤ scale(t)` and `0 ≤ δ ≤ c/24`, eventually in `N`, for every `v ∈ [s N, t N]`,
`thr(v) = N^δ (η_s/η_v)^4 ≤ N^{1/2}`. (Indeed `scale(t) ≤ W L ≤ N` gives `R_t^30 ≤ N^{1-c}`, and
`N^{30δ} R_t^{120} ≤ N^{30δ + 4 - 4c} ≤ N^4 ≤ N^{15}`.) This is T1497's premise `jS ≤ N^{1/2}` on
`{jS < thr}`. -/
theorem thr_le_sqrtN {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, s N ≤ v → v ≤ t N →
      Step2.thr E s δ N v ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
  filter_upwards [hreg, d.dim, eventually_ge_atTop 1] with N hN hdim hN1 v hsv hvt
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 := mE_im_pos hE
  have hm1 := mE_im_le_one (E := E) hE
  have ht1' := ht1 N
  have hs1 : s N < 1 := (hst N).trans_lt ht1'
  have hηs := Step2.etaT_pos' hE hs1
  have hηt := Step2.etaT_pos' hE ht1'
  have hηv := Step2.etaT_pos' hE (hvt.trans_lt ht1')
  have hηtv : etaT E (t N) ≤ etaT E v := by
    simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  set Rt := etaT E (s N) / etaT E (t N) with hRt
  set Rv := etaT E (s N) / etaT E v with hRv
  have hRv0 : 0 ≤ Rv := by positivity
  have hRvt : Rv ≤ Rt := div_le_div_of_nonneg_left hηs.le hηt hηtv
  have hscale : (band d).scale E N (t N) ≤ N := by
    have hℓ : (band d).ell N (t N) ≤ (d.L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hℓ0 : 0 ≤ (band d).ell N (t N) :=
      (Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) ht1').le
    have hη1 : etaT E (t N) ≤ 1 := by
      simp only [Step2.etaT_eq]
      have := hs0 N; have := hst N
      calc (1 - t N) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ (d.W N : ℝ) := Nat.cast_nonneg _
    calc (band d).scale E N (t N) = (d.W N : ℝ) * (band d).ell N (t N) * etaT E (t N) := rfl
      _ ≤ (d.W N : ℝ) * (d.L N : ℝ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hℓ hW0) hη1 hηt.le
          exact mul_nonneg hW0 (Nat.cast_nonneg _)
      _ ≤ N := by linarith
  set g := (N : ℝ) ^ c with hg
  set x := (N : ℝ) ^ δ with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hN1' hδ0
  have hxg : x ^ 24 ≤ g := by
    rw [hx, Step2.natCast_rpow_pow]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
  have hR30 : g * Rt ^ 30 ≤ N := hN.trans hscale
  unfold Step2.thr
  rw [← hx, ← hRv]
  have hX0 : 0 ≤ x * Rv ^ 4 := by positivity
  have hsq : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (30 : ℕ) = (N : ℝ) ^ (15 : ℕ) := by
    rw [Step2.natCast_rpow_pow, ← Real.rpow_natCast]; norm_num
  have key : (x * Rv ^ 4) ^ (30 : ℕ) ≤ ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (30 : ℕ) := by
    rw [hsq]
    have hRt0 : 0 ≤ Rt := hRv0.trans hRvt
    have h1 : (x * Rv ^ 4) ^ (30 : ℕ) ≤ x ^ 30 * (Rt ^ 30) ^ 4 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRv0 hRvt _) (by positivity)
    have h2 : (g * Rt ^ 30) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hR30 4
    have h3 : x ^ 96 ≤ g ^ 4 := by
      calc x ^ 96 = (x ^ 24) ^ 4 := by ring
        _ ≤ g ^ 4 := pow_le_pow_left₀ (by positivity) hxg 4
    have h4 : x ^ 30 ≤ x ^ 96 := pow_le_pow_right₀ hx1 (by norm_num)
    have h5 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 15 := pow_le_pow_right₀ hN1' (by norm_num)
    have hR0 : 0 ≤ (Rt ^ 30) ^ 4 := by positivity
    calc (x * Rv ^ 4) ^ (30 : ℕ) ≤ x ^ 30 * (Rt ^ 30) ^ 4 := h1
      _ ≤ x ^ 96 * (Rt ^ 30) ^ 4 := mul_le_mul_of_nonneg_right h4 hR0
      _ ≤ g ^ 4 * (Rt ^ 30) ^ 4 := mul_le_mul_of_nonneg_right h3 hR0
      _ = (g * Rt ^ 30) ^ 4 := by ring
      _ ≤ (N : ℝ) ^ 4 := h2
      _ ≤ (N : ℝ) ^ (15 : ℕ) := h5
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) key

/-- `u_{j+1} = u_j + Δ`. -/
theorem time_succ_eq (s u : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) :
    time s u K N (j + 1) = time s u K N j + step s u K N := by
  unfold time; push_cast; ring

/-- The real kernel entry of `ukerMat` is the product of `edgeKer` entries (T1516's private
`Uker_one_single`, re-proved). -/
theorem ukerMat_eq_prod_re (L : ℕ) [NeZero L] (v w : ℝ) (b a : LoopArg L 2) :
    ukerMat L v w b a = (∏ i : Fin 2, edgeKer L 1 (v : ℂ) (w : ℂ) (b i) (a i)).re := by
  classical
  unfold ukerMat
  congr 1
  rw [Uker_apply]
  have hterm : ∀ c : LoopArg L 2,
      (∏ i : Fin 2, edgeKer L ((fun _ => (1 : ℂ)) i) (v : ℂ) (w : ℂ) (b i) (c i))
          * (Pi.single a (1 : ℂ) : LoopArg L 2 → ℂ) c
        = if c = a then ∏ i : Fin 2, edgeKer L 1 (v : ℂ) (w : ℂ) (b i) (a i) else 0 := by
    intro c
    by_cases h : c = a
    · subst h; simp
    · simp [h]
  simp_rw [hterm]
  simp

private theorem quadVar_Φgrid_eq_aux {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ}
    (hE : |E| < 2) (N : ℕ) {w : ℝ} (hw1 : w < 1) (a : LoopArg (B.L N) 2)
    {M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ} (hM : M.IsHermitian) :
    Gauss.quadVar B.toDims N (Φgrid B E N w a) M
      = Gauss.quadVar B.toDims N
          (fun M' => MomentDuhamel.lkFun B E N w M' Step2.sigPM a) M := by
  have hz : (zt E w).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hw1
  have h := EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs (B := B) hz Step2.sigPM hM a
  refine Eq.trans ?_ h.symm
  have hidx : (toIdx (L := B.toDims.L N) Step2.sigPM a : LoopIdx (ZMod (B.toDims.L N)))
      = (⟨[true, false], List.ofFn (n := 2) (α := ZMod (B.toDims.L N)) a⟩ :
          LoopIdx (ZMod (B.toDims.L N))) := by
    change LoopData.idx (Step2.sigPM, a) = _
    rw [Step2.idx_sigPM]
    exact (ofFn_pm_eq_pmLoop a).symm
  rw [hidx]
  unfold Gauss.quadVar coordD1
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfd : fderiv ℝ (Φgrid B E N w a) M
      = fderiv ℝ (loopObs B.toDims N (zt E w)
          (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))) M := by
    unfold Φgrid
    exact fderiv_sub_const (𝕜 := ℝ)
      (f := (loopObs B.toDims N (zt E w)
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) :
          Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ → ℂ)) (x := M) (Kv B E N w a)
  rw [hfd]
  rfl

/-- The quadratic variation of `Φgrid` is that of `lkFun`, at Hermitian `M`: `Φgrid = loopObs − Kv`
has the derivative of `loopObs`, which agrees with that of `lkFun` on the used coordinates
(`EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs`). -/
theorem quadVar_Φgrid_eq {E : ℝ} (hE : |E| < 2) (N : ℕ) {w : ℝ} (hw1 : w < 1)
    (a : LoopArg (d.L N) 2) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    Gauss.quadVar d N (Φgrid (band d) E N w a) M
      = Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun (band d) E N w M' Step2.sigPM a) M :=
  quadVar_Φgrid_eq_aux (band d) hE N hw1 a hM

/-- `0 ≤ jGMat` once `ℓ_u > 0` and `W ≥ 3` (the `(0,0)` term of the supremum is `0`). -/
theorem jGMat_nonneg (E : ℝ) (N : ℕ) (u : ℝ) {ℓu ηu D : ℝ} (hℓu : 0 < ℓu)
    (hW3 : 3 ≤ d.W N) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    0 ≤ jGMat d E N u ℓu ηu D M := by
  have hW : (3 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast hW3
  have hlog : 0 < Real.log (d.W N : ℝ) := Real.log_pos (by linarith)
  have hstar : 0 < ellStar (d.W N : ℝ) ℓu := by
    unfold ellStar; exact mul_pos (Real.rpow_pos_of_pos hlog _) hℓu
  have hif : ¬ (ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) ((0 : ZMod (d.L N)) - 0) : ℝ)) := by
    simp only [sub_self]
    have : (zdist (d.L N) (0 : ZMod (d.L N)) : ℝ) = 0 := by simp [zdist]
    rw [this]; linarith
  unfold jGMat
  refine add_nonneg zero_le_one ?_
  refine Finset.le_sup'_of_le _ (Finset.mem_univ ((0 : ZMod (d.L N)), (0 : ZMod (d.L N)))) ?_
  dsimp only
  rw [ite_eq_right_iff.mpr (fun h => absurd h hif)]

/-- `time` is monotone in the grid index when `s N ≤ u N`. -/
theorem time_mono_of_le {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hsu : s N ≤ u N) {i i' : ℕ}
    (hii : i ≤ i') : time s u K N i ≤ time s u K N i' := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h : (i : ℝ) ≤ (i' : ℝ) := by exact_mod_cast hii
  unfold time
  nlinarith

variable (d) in
/-- **The rate `Q′_j`** of T1514's `quadVar_step_le`, at `J = qvJ E s δ ε N u_j = N^{2ε} thr(u_j)`
and `ℓ_s = (band d).ell N (s N)`, written through T1508's `Qd` (verbatim the same expression):
`Q′_j = 2 N^{τ₁} Qd(u_j) + 2 Csh(u_{j+1})² Δ² W^{2D}`. -/
def Qprime (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ ε D τ₁ : ℝ) (N j : ℕ) : ℝ :=
  2 * (N : ℝ) ^ τ₁ * Qd (band d) E s δ ε D N (time s u K N j)
    + 2 * qvTimeShiftConst d N E (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2
        * ((band d).W N : ℝ) ^ (2 * D)

variable (d) in
/-- **The Azuma constants of (T2)**:
`c k a j = Δ (√Q′_j ((1 − u_{j+1})/(1 − u_k))² xiK T_{u_k}(a))² + Δ N^{-C_c}`
(supervisor 0048 §1g: the positive floor `Δ N^{-C_c}`). -/
def cZ (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ ε D τ₁ Cc : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (j : ℕ) : ℝ :=
  step s u K N * (Real.sqrt (Qprime d E s u K δ ε D τ₁ N j)
      * ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2
      * Step2.xiK (d.L N) (d.W N) (mE E).im
      * Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))) ^ 2
    + step s u K N * (N : ℝ) ^ (-Cc)

theorem cZ_nonneg {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) (j : ℕ) :
    0 ≤ cZ d E s u K δ ε D τ₁ Cc N k a j := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold cZ
  have : 0 ≤ (N : ℝ) ^ (-Cc) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- The positive floor: `Δ N^{-C_c} ≤ c k a j`, so `Σ_{j<k} c k a j ≥ k Δ N^{-C_c} > 0` for
`k ≥ 1` and `Δ > 0`. -/
theorem floor_le_cZ {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) (j : ℕ) :
    step s u K N * (N : ℝ) ^ (-Cc) ≤ cZ d E s u K δ ε D τ₁ Cc N k a j := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold cZ
  have : 0 ≤ step s u K N * (Real.sqrt (Qprime d E s u K δ ε D τ₁ N j)
      * ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2
      * Step2.xiK (d.L N) (d.W N) (mE E).im
      * Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))) ^ 2 := by
    positivity
  linarith

/-- **(T2) `hsubG_gridTau`**: T1504 (T1″)'s hypothesis `hsubG` for the increments
`Z := Zvec (band d) E s u K N` (T1516), the stopping time `τ := gridTau` (T1), the filtration
`filt d` and the constants `c k a j := cZ … N k a j` (as `ℝ≥0` via `Real.toNNReal`, which is the
identity on `cZ ≥ 0`), eventually in `N`, uniformly in `k ≤ K N`, labels `a` and `j < k`.

Route: `stepZ_ukerMat_eq_Uker` (T1516) identifies the stopped component with `stepZ` at the real
kernel `ukerMat u_{j+1} u_k` (for every `ω`); on the `filt d j`-event `{j < τ}`, T1 gives
`jSMat(u_j,H_j) < thr(u_j) ≤ N^{1/2}` (`thr_le_sqrtN`) and `H_j ∈ G(u_j)`, so `qvSet` supplies the
`hqv` of `quadVar_step_le` (T1514) with `J′ = jGMat(u_j,H_j) ≤ N^{2ε} jSMat < qvJ(u_j)` (`jgSet`),
whose output feeds `v_Ab_le_H` (T1512), i.e. `hbound` of `stepDecomp_Z_subG` (T1505). The
imaginary part is identically zero. -/
theorem hsubG_gridTau {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) {D : ℝ} (hD0 : 0 ≤ D)
    (τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) (Cc : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2, ∀ j < k,
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'}.indicator
          (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N k : ℂ) (Zvec (band d) E s u K N (j + 1) ω') a) ω).re)
        (cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'}.indicator
          (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N k : ℂ) (Zvec (band d) E s u K N (j + 1) ω') a) ω).im)
        (cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) := by
  filter_upwards [thr_le_sqrtN hE hs0 hst ht1 hreg hδ0 hδc, eventually_le_W d 3]
    with N hthr hW3 k hk a j hjk
  set S : Set (Ωg d) := {ω' | j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω'} with hSdef
  have hS : MeasurableSet[filt d j] S := lt_gridTau_measurableSet hE D δ τ₁ ε ζCtr τ3 τ57 s u K N j
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have htK : time s u K N (K N) = u N := time_last s u K N (hK0 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set uv := time s u K N (j + 1) with hvdef
  set uw := time s u K N k with hwdef
  set uj := time s u K N j with hujdef
  have hsuj : s N ≤ uj := by
    have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j); rwa [time_zero] at this
  have huj0 : 0 ≤ uj := (hs0 N).trans hsuj
  have hujv : uj ≤ uv := time_mono_of_le (hsu N) (Nat.le_succ j)
  have hvw : uv ≤ uw := time_mono_of_le (hsu N) hjk
  have hwu : uw ≤ u N := by rw [← htK]; exact time_mono_of_le (hsu N) hk
  have hw1 : uw < 1 := (hwu.trans (hut N)).trans_lt (ht1 N)
  have hv1 : uv < 1 := hvw.trans_lt hw1
  have hv0 : 0 ≤ uv := huj0.trans hujv
  have huj1 : uj < 1 := hujv.trans_lt hv1
  have hujt : uj ≤ t N := (hujv.trans hvw).trans (hwu.trans (hut N))
  have hΦ : ∀ a', TestFun d N (Φgrid (band d) E N uv a') := fun a' =>
    Φgrid_testFun (band d) hE N hv1 a'
  have hc0 : 0 ≤ cZ d E s u K δ ε D τ₁ Cc N k a j := cZ_nonneg (hsu N) k a j
  have hcnn : (cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal
      = ⟨cZ d E s u K δ ε D τ₁ Cc N k a j, hc0⟩ := Real.toNNReal_of_nonneg hc0
  have hkey : ∀ ω', Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ) (uw : ℂ)
      (Zvec (band d) E s u K N (j + 1) ω') a
        = (stepZ d s u K N j (Φgrid (band d) E N uv) (ukerMat (d.L N) uv uw) a ω' : ℂ) :=
    fun ω' => (stepZ_ukerMat_eq_Uker d s u K N j (Φgrid (band d) E N uv) hv0 hvw hw1 a ω').symm
  constructor
  · -- the real part
    have hfun : (fun ω => (S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ)
        (uw : ℂ) (Zvec (band d) E s u K N (j + 1) ω') a) ω).re)
        = fun ω => S.indicator
            (fun ω => stepZ d s u K N j (Φgrid (band d) E N uv) (ukerMat (d.L N) uv uw) a ω) ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        have h := congrArg Complex.re (hkey ω)
        rw [Complex.ofReal_re] at h
        exact h
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_re]
    rw [hfun, hcnn]
    refine stepDecomp_Z_subG d s u K N j hΦ _ a S hS _ hc0 ?_
    intro ω hω
    have hU : ukerMat (d.L N) uv uw
        = fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i) (a' i)).re :=
      funext fun b' => funext fun a' => ukerMat_eq_prod_re (d.L N) uv uw b' a'
    rw [hU]
    obtain ⟨hjS, hG⟩ := lt_gridTau_imp hω
    obtain ⟨⟨⟨⟨⟨hqvS, hjg⟩, -⟩, -⟩, -⟩, -⟩ := hG
    have hM : (H d s u K N j ω).IsHermitian := H_isHermitian d s u K N j ω
    have hjS' : jSMat d E D N uj (H d s u K N j ω) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      hjS.le.trans (hthr uj hsuj hujt)
    have hqv0 := hqvS huj1 hjS'
    have hℓs : 0 < (band d).ell N (s N) := Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) hs1
    have hℓuj : 0 < (band d).ell N uj := Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) huj1
    have hJ'0 : 0 ≤ jGMat d E N uj ((band d).ell N uj) (etaT E uj) D (H d s u K N j ω) :=
      jGMat_nonneg E N uj hℓuj hW3 _
    have hJ'J : jGMat d E N uj ((band d).ell N uj) (etaT E uj) D (H d s u K N j ω)
        ≤ qvJ E s δ ε N uj := by
      refine hjg.trans ?_
      unfold qvJ
      exact mul_le_mul_of_nonneg_left hjS.le (by positivity)
    have hqv' : ∀ a' : LoopArg (d.L N) 2,
        Gauss.quadVar d N
            (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N uj M' Step2.sigPM a')
            (H d s u K N j ω)
          ≤ (N : ℝ) ^ τ₁ * APrimeQVEndpoint.diagShape' (Gauss.band d) N
              ((Gauss.band d).ell N uj) ((band d).ell N (s N)) (etaT E uj) D
              (jGMat d E N uj ((band d).ell N uj) (etaT E uj) D (H d s u K N j ω))
              (EarlyQVRateEv.sDet (Gauss.band d) E N uj ((band d).ell N (s N)))
              (EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
                ((Gauss.band d).ell N uj) (etaT E uj) D
                (jGMat d E N uj ((band d).ell N uj) (etaT E uj) D (H d s u K N j ω))) a' := by
      intro a'
      have h1 := hqv0 a'
      unfold qvVal at h1
      rw [dite_eq_left_of_eq_true (eq_true hM)] at h1
      exact h1
    have hu'1 : uj + step s u K N < 1 := by rw [hujdef, ← time_succ_eq]; exact hv1
    have hstep := quadVar_step_le d N hE huj0 hΔ0 hu'1 hD0 hℓs hJ'0 hJ'J hM hqv'
    have hm0 := mE_im_pos hE
    have hm1 := mE_im_le_one (E := E) hE
    have hQ : 0 ≤ Qprime d E s u K δ ε D τ₁ N j := by
      unfold Qprime
      have := QVSum.Qd_nonneg (band d) hE (s := s) (δ := δ) (ε := ε) (D := D) (N := N)
        hs1 huj0 huj1
      have : 0 ≤ qvTimeShiftConst d N E (time s u K N (j + 1)) := qvTimeShiftConst_nonneg _ _ _ _
      have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have hqvΦ : ∀ a' : LoopArg (d.L N) 2,
        Gauss.quadVar d N (Φgrid (band d) E N uv a') (H d s u K N j ω)
          ≤ Qprime d E s u K δ ε D τ₁ N j *
            (tailT (d.W N : ℝ) (ellHat (d.L N) (uv : ℂ)) ((1 - uv) * (mE E).im) D
              (zdist (d.L N) (a' 0 - a' 1))) ^ 2 := by
      intro a'
      rw [quadVar_Φgrid_eq hE N hv1 a' hM]
      have h1 := hstep a'
      rw [hujdef, ← time_succ_eq] at h1
      exact h1
    have hWe : Real.exp 1 ≤ (d.W N : ℝ) := by
      have h1 : (3 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast hW3
      have h2 : Real.exp 1 ≤ (3 : ℝ) := by
        have := Real.exp_one_lt_d9
        nlinarith
      linarith
    have hAuv : (d.W N : ℝ) * ellHat (d.L N) (uw : ℂ) * ((1 - uw) * (mE E).im)
        ≤ (d.W N : ℝ) * ellHat (d.L N) (uv : ℂ) * ((1 - uv) * (mE E).im) :=
      flowScale_antitoneOn (Nat.cast_nonneg _) (d.L N) E (Set.mem_Iic.2 hv1.le)
        (Set.mem_Iic.2 hw1.le) hvw
    have hvAb := v_Ab_le_H (Φ := Φgrid (band d) E N uv) hΦ
      (fun a' A hA => Φgrid_im_eq_zero (band d) hE.le N hv0 hv1 a' hA) (d.three_le_L N) hm0 hm1
      hv0 hvw (hv0.trans hvw) hw1 hWe hQ hAuv a ω hqvΦ
    have hfl : 0 ≤ step s u K N * (N : ℝ) ^ (-Cc) :=
      mul_nonneg hΔ0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc step s u K N * v N (Ab d s u K N j (Φgrid (band d) E N uv)
          (fun b' a' => (∏ i : Fin 2, edgeKer (d.L N) 1 (uv : ℂ) (uw : ℂ) (b' i) (a' i)).re) a ω)
        ≤ step s u K N * (Real.sqrt (Qprime d E s u K δ ε D τ₁ N j)
            * ((1 - uv) / (1 - uw)) ^ 2 * Step2.xiK (d.L N) (d.W N) (mE E).im
            * Step2.tT (band d) E N D uw (zdist (d.L N) (a 0 - a 1))) ^ 2 :=
          mul_le_mul_of_nonneg_left hvAb hΔ0
      _ ≤ cZ d E s u K δ ε D τ₁ Cc N k a j := by
          unfold cZ
          linarith
  · -- the imaginary part: identically zero
    have hz0 : ∀ ω, stepZ d s u K N j (Φgrid (band d) E N uv) (fun _ _ => (0 : ℝ)) a ω = 0 := by
      intro ω; simp [stepZ, Ab, lin]
    have hfun : (fun ω => (S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (uv : ℂ)
        (uw : ℂ) (Zvec (band d) E s u K N (j + 1) ω') a) ω).im)
        = fun ω => S.indicator
            (fun ω => stepZ d s u K N j (Φgrid (band d) E N uv) (fun _ _ => (0 : ℝ)) a ω) ω := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hz0]
        have h := congrArg Complex.im (hkey ω)
        rw [Complex.ofReal_im] at h
        exact h
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Complex.zero_im]
    rw [hfun, hcnn]
    refine stepDecomp_Z_subG d s u K N j hΦ _ a S hS _ hc0 ?_
    intro ω _
    have hAb : Ab d s u K N j (Φgrid (band d) E N uv) (fun _ _ => (0 : ℝ)) a ω = 0 := by
      simp [Ab]
    have hv0' : RBM.Gauss.Grid.v N (0 : Matrix (d.Idx N) (d.Idx N) ℂ) = 0 := by
      simp [Gauss.Grid.v, linVar, lin]
    rw [hAb, hv0', mul_zero]
    exact hc0

/-- **Joint satisfiability of the hypotheses of `hsubG_gridTau`**, nondegenerate: from T1508's
compiled witness (`qv_time_sum_le_hyps_witness`: a genuine window `s N < t N` for `N ≥ 1` with
`η_s/η_t = (N+1)^{1/200} → ∞`, step2's gained (2.72) with `c = 1/4`, `δ = c/24`, `D = 60`), with
endpoint `u := t` and grid size `K N := N + 1`. -/
theorem hsubG_gridTau_hyps_witness :
    ∃ (E : ℝ) (s t u : ℕ → ℝ) (c δ D : ℝ) (K : ℕ → ℕ),
      |E| < 2 ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      (∀ N : ℕ, 1 ≤ N → s N < t N) ∧
      (∀ N : ℕ, etaT E (s N) / etaT E (t N) = ((N : ℝ) + 1) ^ (1 / 200 : ℝ)) ∧
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
        (band d).scale E N (t N)) ∧
      0 < c ∧ 0 < δ ∧ δ ≤ c / 24 ∧ 0 ≤ D ∧ (∀ N, s N ≤ u N) ∧ (∀ N, u N ≤ t N) ∧
      (∀ N : ℕ, 1 ≤ N → s N < u N) ∧ (∀ N, K N ≠ 0) := by
  obtain ⟨E, s, t, c, δ, ε, D, hE, hs0, hst, ht1, hlt, hR, _hcond, hc0, hreg, hδ0, hδc, _, _, hD⟩ :=
    qv_time_sum_le_hyps_witness (band d)
  exact ⟨E, s, t, t, c, δ, D, fun N => N + 1, hE, hs0, hst, ht1, hlt, hR, hreg, hc0, hδ0, hδc,
    by linarith, hst, fun _ => le_rfl, hlt, fun N => Nat.succ_ne_zero N⟩

end T2

/-! ## (T3′), (T4′), (T6′) : T1519-amend-1 -/

section Amend

variable {d}

theorem measurable_coord_filt {k l : ℕ} (hl : l ≤ k) :
    Measurable[filt d k] (fun ω : Ωg d => ω l) := by
  have : (fun ω : Ωg d => ω l)
      = (fun g : Set.Iic k → Ω d => g ⟨l, hl⟩) ∘ (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) :=
    rfl
  rw [this]
  exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k))

theorem measurable_lin (N : ℕ) :
    Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      lin N p.1 p.2) := by
  unfold lin
  have h : ∀ i k : d.Idx N, Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ ×
      Matrix (d.Idx N) (d.Idx N) ℂ => p.1 i k * p.2 k i) := fun i k =>
    (Measurable.eval_matrix (i := i) (j := k) measurable_fst).mul
      (Measurable.eval_matrix (i := k) (j := i) measurable_snd)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Complex.measurable_re.comp ?_
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => h i k

theorem measurable_stepZ_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Measurable[filt d (j + 1)] (fun ω => stepZ d s t K N j Φ U b ω) := by
  have hA : Measurable[filt d (j + 1)] (fun ω => Ab d s t K N j Φ U b ω) :=
    (measurable_Ab d s t K N j hΦ U b).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have hX : Measurable[filt d (j + 1)] (fun ω : Ωg d => Xmat d N (ω (j + 1))) :=
    (measurable_Xmat d N).comp (measurable_coord_filt le_rfl)
  have hP : Measurable[filt d (j + 1)] (fun ω : Ωg d =>
      (Ab d s t K N j Φ U b ω, Xmat d N (ω (j + 1)))) := hA.prodMk hX
  have hL := (measurable_lin (d := d) N).comp hP
  change Measurable[filt d (j + 1)] (fun ω : Ωg d => Real.sqrt (step s t K N) *
      lin N (Ab d s t K N j Φ U b ω) (Xmat d N (ω (j + 1))))
  exact hL.const_mul _

theorem measurable_stepY_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Measurable[filt d (j + 1)] (fun ω => stepY d s t K N j Φ U b ω) := by
  have hH : Measurable[filt d (j + 1)] (fun ω => H d s t K N (j + 1) ω) :=
    H_measurable_filt d s t K N (j + 1)
  have h1 : Measurable[filt d (j + 1)] (fun ω =>
      ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω)) :=
    Finset.measurable_sum _ fun a _ =>
      ((hΦ a).contDiff.continuous.measurable.comp hH).const_mul _
  have h2 : Measurable[filt d (j + 1)] ((Pg d)[fun ω' => ∑ a : LoopArg (d.L N) 2,
      (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω') | filt d j]) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have h3 := measurable_stepZ_filt s t K N j hΦ U b
  unfold stepY stepXi
  exact (h1.sub h2).sub (Complex.measurable_ofReal.comp h3)


/-- The increments `Zvec i` with the index cut to `1 ≤ i ≤ K N` (and `0` elsewhere); on the
indices that enter the sums this is `Zvec` itself, and it is adapted for **every** index. -/
def ZvecCut (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ) (ω : Ωg d)
    (a : LoopArg (d.L N) 2) : ℂ :=
  (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) * Zvec (band d) E s u K N i ω a

theorem ZvecCut_succ {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ} (hj : j < K N) :
    ZvecCut (d := d) E s u K N (j + 1) = Zvec (band d) E s u K N (j + 1) := by
  funext ω a
  unfold ZvecCut
  have h1 : (if 1 ≤ j + 1 ∧ j + 1 ≤ K N then (1 : ℂ) else 0) = 1 := by
    simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
  rw [h1, one_mul]

theorem time_lt_one_of_le {s t u : ℕ → ℝ} (hsu : ∀ N, s N ≤ u N)
    (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℕ → ℕ} (hK0 : ∀ N, K N ≠ 0) {N i : ℕ}
    (hi : i ≤ K N) : time s u K N i < 1 := by
  have h := time_mono_of_le (K := K) (hsu N) hi
  rw [time_last s u K N (hK0 N)] at h
  exact (h.trans (hut N)).trans_lt (ht1 N)

theorem stronglyMeasurable_ZvecCut {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ}
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℕ → ℕ}
    (hK0 : ∀ N, K N ≠ 0) (N i : ℕ) :
    StronglyMeasurable[filt d i] (ZvecCut (d := d) E s u K N i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ K N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [ZvecCut_succ (by omega)]
    have hu1 : time s u K N (j + 1) < 1 :=
      time_lt_one_of_le hsu hut ht1 hK0 hi.2
    have hΦ : ∀ a, TestFun d N (Φgrid (band d) E N (time s u K N (j + 1)) a) :=
      fun a => Φgrid_testFun (band d) hE N hu1 a
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact Complex.measurable_ofReal.comp (measurable_stepZ_filt s u K N j hΦ _ a)
  · have : ZvecCut (d := d) E s u K N i = fun _ => 0 := by
      funext ω a; unfold ZvecCut; have h0 : (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]; exact hi
      rw [h0, zero_mul]; rfl
    rw [this]; exact stronglyMeasurable_const

variable (d) in
/-- **The Azuma threshold of (T3′)** with the positive floor inside the square root:
`xZ k a := N^{δ/16} · √(4 Σ_{j<k} c k a j + N^{-C_x})` (T1519-amend-1). -/
def xZ (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ ε D τ₁ Cc Cx : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  (N : ℝ) ^ (δ / 16) *
    Real.sqrt (4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx))

theorem xZ_pos {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc Cx : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) :
    0 < xZ d E s u K δ ε D τ₁ Cc Cx N k a := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 ≤ ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j :=
    Finset.sum_nonneg fun j _ => cZ_nonneg hsu k a j
  unfold xZ
  have : 0 < 4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx) := by
    have := Real.rpow_pos_of_pos hN0 (-Cx); linarith
  exact mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_pos.2 this)

theorem xZ_sq {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc Cx : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) :
    xZ d E s u K δ ε D τ₁ Cc Cx N k a ^ 2 = (N : ℝ) ^ (δ / 8) *
      (4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx)) := by
  have hS : 0 ≤ ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j :=
    Finset.sum_nonneg fun j _ => cZ_nonneg hsu k a j
  have hX : 0 ≤ 4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (-Cx); linarith
  unfold xZ
  rw [mul_pow, Real.sq_sqrt hX]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  push_cast; ring

/-- `C N^b e^{-N^a} ≤ N^{-D}` eventually. -/
theorem eventually_mul_exp_neg_rpow_le (C b : ℝ) {a : ℝ} (ha : 0 < a) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [SumZeroDyn.eventually_exp_small C (b + D) 1 one_pos ha,
    eventually_ge_atTop 1] with N h hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a)
      = (C * (N : ℝ) ^ (b + D) * Real.exp (-(1 * (N : ℝ) ^ a))) * (N : ℝ) ^ (-D) := by
    rw [one_mul, Real.rpow_add hN0]
    have : (N : ℝ) ^ D * (N : ℝ) ^ (-D) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    calc C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a)
        = C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a) * ((N : ℝ) ^ D * (N : ℝ) ^ (-D)) := by
          rw [this, mul_one]
      _ = _ := by ring
  rw [e]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hN0.le _) h


theorem card_loopArg_two (L : ℕ) [NeZero L] : Fintype.card (LoopArg L 2) = L ^ 2 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- `Zvec (j+1) ≡ 0` when the grid step is `0`. -/
theorem Zvec_succ_eq_zero_of_step {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (h0 : step s u K N = 0) (j : ℕ) (ω : Ωg d) (a : LoopArg (d.L N) 2) :
    Zvec (band d) E s u K N (j + 1) ω a = 0 := by
  change (stepZ d s u K N j (Φgrid (band d) E N (time s u K N (j + 1))) (gridDelta (d.L N)) a ω
    : ℂ) = 0
  simp [stepZ, h0]

theorem Uker_apply_eq_zero_of {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (s' t' : ℂ)
    {A : LoopArg L n → ℂ} (hA : ∀ b, A b = 0) (a : LoopArg L n) : Uker L ξ s' t' A a = 0 := by
  rw [Uker_apply]; simp [hA]

/-- **(T3′) `highProb_azuma_grid'`** (T1519-amend-1): the Azuma event for the stopped linear part
holds with high probability, **for every `k ≤ K N`, including `k = 0` and the degenerate case
`Δ = 0`**, with the threshold `xZ` that carries the positive floor `N^{-C_x}` inside the square
root. `K` may be any grid size with polynomially many points. Route: (T2) `hsubG_gridTau` feeds
T1504 (T1″) `stopped_duhamel_azuma_union`; each summand is `≤ 4 exp(−N^{δ/8})` since
`xZ² = N^{δ/8}(4Σc + N^{-C_x}) ≥ N^{δ/8}·4Σc` and `Σ_{j<k} c ≥ kΔN^{-C_c} > 0`; there are
`K·L² ≤ N^{C+2}` summands. -/
theorem highProb_azuma_grid' {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 24) {D : ℝ} (hD0 : 0 ≤ D)
    (τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) {C : ℝ}
    (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) (Cc Cx : ℝ) :
    HighProb (Pg d) (fun N => {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) E s u K N (j + 1) ω)) a‖
        < xZ d E s u K δ ε D τ₁ Cc Cx N k a}) := by
  intro D' hD'
  have hδ8 : 0 < δ / 8 := by positivity
  filter_upwards [hsubG_gridTau hE hs0 hst ht1 hreg hδ0.le hδc hD0 τ₁ ε ζCtr τ3 τ57 hsu hut K hK0
      Cc, hKcard, eventually_mul_exp_neg_rpow_le 4 (C + 2) hδ8 D', d.dim,
      eventually_ge_atTop 1] with N hsub hKN hsmall hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set τN : Ωg d → ℕ := fun ω => gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω with hτN
  set Ev : Set (Ωg d) := {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (τN ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) E s u K N (j + 1) ω)) a‖
        < xZ d E s u K δ ε D τ₁ Cc Cx N k a} with hEv
  change (Pg d) Evᶜ ≤ _
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  rcases hΔ0.eq_or_lt with hΔ | hΔ
  · -- `Δ = 0`: every sum vanishes, the event is everything
    have hall : Evᶜ = ∅ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not, hEv,
        Set.mem_ofPred_eq]
      intro k _ a
      have h0 : ∀ j, Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
          (time s u K N k : ℂ) (Zvec (band d) E s u K N (j + 1) ω) a = 0 := fun j =>
        Uker_apply_eq_zero_of _ _ _ (fun b => Zvec_succ_eq_zero_of_step (E := E) hΔ.symm j ω b) a
      rw [Finset.sum_apply]
      simp only [h0, Finset.sum_const_zero, norm_zero]
      exact xZ_pos hN1 (hsu N) k a
    rw [hall, measure_empty]; exact zero_le
  · -- `Δ > 0`
    have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j =>
      lt_gridTau_measurableSet hE D δ τ₁ ε ζCtr τ3 τ57 s u K N j
    have hZ : ∀ i, StronglyMeasurable[filt d i] (ZvecCut (d := d) E s u K N i) := fun i =>
      stronglyMeasurable_ZvecCut hE hsu hut ht1 hK0 N i
    have hsub' : ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2, ∀ j < k,
        HasCondSubgaussianMGF (filt d j) ((filt d).le j)
          (fun ω => ({ω' | j < τN ω'}.indicator
            (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
              (time s u K N k : ℂ) (ZvecCut (d := d) E s u K N (j + 1) ω') a) ω).re)
          (cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) ∧
        HasCondSubgaussianMGF (filt d j) ((filt d).le j)
          (fun ω => ({ω' | j < τN ω'}.indicator
            (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
              (time s u K N k : ℂ) (ZvecCut (d := d) E s u K N (j + 1) ω') a) ω).im)
          (cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal (Pg d) := by
      intro k hk a j hj
      rw [ZvecCut_succ (by omega)]
      exact hsub k hk a j hj
    have hx : ∀ k ≤ K N, ∀ a, 0 ≤ xZ d E s u K δ ε D τ₁ Cc Cx N k a :=
      fun k _ a => (xZ_pos hN1 (hsu N) k a).le
    have hx0 : ∀ a, 0 < xZ d E s u K δ ε D τ₁ Cc Cx N 0 a := fun a => xZ_pos hN1 (hsu N) 0 a
    have hU := stopped_duhamel_azuma_union (μ := Pg d) (d.L N) (ξ := fun _ => (1 : ℂ))
      (u := time s u K N) hτmeas hZ (K N) hsub' hx hx0
    set Sbad : Set (Ωg d) := {ω | ∃ k ≤ K N, ∃ a, xZ d E s u K δ ε D τ₁ Cc Cx N k a ≤
        ‖(∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (ZvecCut (d := d) E s u K N (j + 1) ω)) a‖} with hSbad
    have hsubset : Evᶜ ⊆ Sbad := by
      intro ω hω
      simp only [hEv, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hω
      obtain ⟨k, hk, a, ha⟩ := hω
      refine ⟨k, hk, a, ?_⟩
      have hsum : (∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (ZvecCut (d := d) E s u K N (j + 1) ω))
          = ∑ j ∈ Finset.range (min k (τN ω)), Uker (d.L N) (fun _ => (1 : ℂ))
            (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
              (Zvec (band d) E s u K N (j + 1) ω) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j < min k (τN ω) := Finset.mem_range.1 hj
        rw [ZvecCut_succ (by omega)]
      rw [hsum]; exact ha
    -- the per-summand bound
    have hterm : ∀ k ∈ Finset.Icc 1 (K N), ∀ a : LoopArg (d.L N) 2,
        4 * Real.exp (-(xZ d E s u K δ ε D τ₁ Cc Cx N k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal : ℝ)))
          ≤ 4 * Real.exp (-(N : ℝ) ^ (δ / 8)) := by
      intro k hk a
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hcoe : ∑ j ∈ Finset.range k, ((cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal : ℝ)
          = ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j :=
        Finset.sum_congr rfl fun j _ => Real.coe_toNNReal _ (cZ_nonneg (hsu N) k a j)
      rw [hcoe]
      set Sk := ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j with hSk
      have hSk0 : 0 < Sk := by
        have h1 : step s u K N * (N : ℝ) ^ (-Cc) ≤ Sk := by
          have := Finset.single_le_sum (f := fun j => cZ d E s u K δ ε D τ₁ Cc N k a j)
            (fun j _ => cZ_nonneg (hsu N) k a j) (Finset.mem_range.2 hk1)
          exact (floor_le_cZ (hsu N) k a 0).trans this
        exact lt_of_lt_of_le (mul_pos hΔ (Real.rpow_pos_of_pos hN0 _)) h1
      have hsq := xZ_sq (E := E) (K := K) (δ := δ) (ε := ε) (D := D) (τ₁ := τ₁) (Cc := Cc)
        (Cx := Cx) (hsu N) k a
      rw [← hSk] at hsq
      have hle : (N : ℝ) ^ (δ / 8) * (4 * Sk) ≤ xZ d E s u K δ ε D τ₁ Cc Cx N k a ^ 2 := by
        rw [hsq]
        have := Real.rpow_nonneg hN0.le (-Cx)
        have := Real.rpow_nonneg hN0.le (δ / 8)
        nlinarith
      have h4S : 0 < 4 * Sk := by linarith
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ h4S]
      exact hle
    have hLN : (d.L N : ℝ) ≤ N := by
      have hW : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
      have h := hdim.1
      have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast h
      nlinarith [(Nat.cast_nonneg (d.L N) : (0 : ℝ) ≤ d.L N)]
    have hsum_le : ∑ k ∈ Finset.Icc 1 (K N), ∑ a : LoopArg (d.L N) 2,
        4 * Real.exp (-(xZ d E s u K δ ε D τ₁ Cc Cx N k a) ^ 2 /
          (4 * ∑ j ∈ Finset.range k, ((cZ d E s u K δ ε D τ₁ Cc N k a j).toNNReal : ℝ)))
        ≤ (N : ℝ) ^ (-D') := by
      calc _ ≤ ∑ _k ∈ Finset.Icc 1 (K N), ∑ _a : LoopArg (d.L N) 2,
            4 * Real.exp (-(N : ℝ) ^ (δ / 8)) :=
            Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ => hterm k hk a
        _ = (K N : ℝ) * ((d.L N : ℝ) ^ 2 * (4 * Real.exp (-(N : ℝ) ^ (δ / 8)))) := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, card_loopArg_two,
              Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
            push_cast; ring
        _ ≤ (N : ℝ) ^ C * ((N : ℝ) ^ (2 : ℝ) * (4 * Real.exp (-(N : ℝ) ^ (δ / 8)))) := by
            have hK : (K N : ℝ) ≤ (N : ℝ) ^ C := by
              have : (K N : ℝ) ≤ ((K N + 1 : ℕ) : ℝ) := by push_cast; linarith
              exact this.trans hKN
            have hL2 : (d.L N : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 : ℝ) := by
              rw [Real.rpow_two]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hLN 2
            have he : 0 ≤ 4 * Real.exp (-(N : ℝ) ^ (δ / 8)) := by positivity
            have hL0 : 0 ≤ (d.L N : ℝ) ^ 2 := by positivity
            gcongr
        _ = 4 * (N : ℝ) ^ (C + 2) * Real.exp (-(N : ℝ) ^ (δ / 8)) := by
            rw [Real.rpow_add hN0]; ring
        _ ≤ (N : ℝ) ^ (-D') := hsmall
    calc (Pg d) Evᶜ ≤ (Pg d) Sbad := measure_mono hsubset
      _ = ENNReal.ofReal ((Pg d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal (hU.trans hsum_le)


/-- `#(Idx N) = L N · W N ≤ N`. -/
theorem card_idx_le {N : ℕ} (hdim : d.W N * d.L N ≤ N) :
    (Fintype.card (d.Idx N) : ℝ) ≤ N := by
  have h1 : Fintype.card (d.Idx N) = d.L N * d.W N := by simp [ZMod.card]
  have h2 : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact hdim
  rw [h1]; exact_mod_cast h2

/-- `Csh(u') ≤ 1536 N⁸` once `#(Idx N) ≤ N` and `η_{u'}^{-1} ≤ N`. -/
theorem qvTimeShiftConst_le {E u' : ℝ} {N : ℕ} (hN1 : (1 : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hη : (etaT E u')⁻¹ ≤ N)
    (hη0 : 0 ≤ (etaT E u')⁻¹) :
    qvTimeShiftConst d N E u' ≤ 1536 * (N : ℝ) ^ 8 := by
  unfold qvTimeShiftConst
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h1 : 1 + (etaT E u')⁻¹ ≤ 2 * N := by linarith
  have hc0 : (0 : ℝ) ≤ Fintype.card (d.Idx N) := Nat.cast_nonneg _
  calc 16 * Real.sqrt 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (1 + (etaT E u')⁻¹) ^ 6
      ≤ 16 * (3 / 2) * (N : ℝ) ^ 2 * (2 * N) ^ 6 := by gcongr
    _ = 1536 * (N : ℝ) ^ 8 := by ring

variable (d) in
/-- **The Azuma multiplier `Mm` of (T3′)**, explicit:
`Mm = N^{δ/16} √(4 Ξ² (2 qvSumConst N^{τ₁+δ/64} + 2) + 5)` with `Ξ = xiK(L, W, Im m)`. -/
def azumaMm (E δ τ₁ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * Step2.xiK (d.L N) (d.W N) (mE E).im ^ 2 *
    (2 * qvSumConst E * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5)

theorem azumaMm_nonneg (E δ τ₁ : ℝ) (N : ℕ) : 0 ≤ azumaMm d E δ τ₁ N := by
  unfold azumaMm
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)

/-- **(T3′), `Mm ≤ N^{δ/8}` eventually**, for `0 ≤ τ₁ ≤ δ/32`. -/
theorem azumaMm_le {E : ℝ} (hE : |E| < 2) {δ τ₁ : ℝ} (hδ0 : 0 < δ) (hτ₁δ : τ₁ ≤ δ / 32) :
    ∀ᶠ N : ℕ in atTop, azumaMm d E δ τ₁ N ≤ (N : ℝ) ^ (δ / 8) := by
  have hm0 := mE_im_pos hE
  have hq0 : 0 < qvSumConst E := by unfold qvSumConst; positivity
  filter_upwards [Step2FarInputs.eventually_xiK_le (band d) (mE E).im
      (by positivity : (0 : ℝ) < δ / 128),
    eventually_le_rpow (8 * qvSumConst E + 13) (by positivity : (0 : ℝ) < δ / 16),
    eventually_ge_atTop 1] with N hxi hC hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set ξ := Step2.xiK (d.L N) (d.W N) (mE E).im with hξ
  have hξ0 : 0 ≤ ξ := Step2.xiK_nonneg _ _ _
  have hξ' : ξ ≤ (N : ℝ) ^ (δ / 128) := hxi
  have hξ2 : ξ ^ 2 ≤ (N : ℝ) ^ (δ / 64) := by
    calc ξ ^ 2 ≤ ((N : ℝ) ^ (δ / 128)) ^ 2 := pow_le_pow_left₀ hξ0 hξ' 2
      _ = (N : ℝ) ^ (δ / 64) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hP : (N : ℝ) ^ (τ₁ + δ / 64) ≤ (N : ℝ) ^ (3 * δ / 64) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hA1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 64) := Real.one_le_rpow hN1' (by positivity)
  have hA3 : (1 : ℝ) ≤ (N : ℝ) ^ (3 * δ / 64) := Real.one_le_rpow hN1' (by positivity)
  have hmul : (N : ℝ) ^ (δ / 64) * (N : ℝ) ^ (3 * δ / 64) = (N : ℝ) ^ (δ / 16) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hB1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 16) := Real.one_le_rpow hN1' (by positivity)
  have hQ : 4 * ξ ^ 2 * (2 * qvSumConst E * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5
      ≤ (N : ℝ) ^ (δ / 8) := by
    have h1 : 4 * ξ ^ 2 * (2 * qvSumConst E * (N : ℝ) ^ (τ₁ + δ / 64) + 2)
        ≤ 4 * (N : ℝ) ^ (δ / 64) * (2 * qvSumConst E * (N : ℝ) ^ (3 * δ / 64)
          + 2 * (N : ℝ) ^ (3 * δ / 64)) := by
      have hPp : 0 ≤ (N : ℝ) ^ (τ₁ + δ / 64) := Real.rpow_nonneg hN0.le _
      gcongr
      · nlinarith
    have h2 : 4 * (N : ℝ) ^ (δ / 64) * (2 * qvSumConst E * (N : ℝ) ^ (3 * δ / 64)
          + 2 * (N : ℝ) ^ (3 * δ / 64)) = (8 * qvSumConst E + 8) * (N : ℝ) ^ (δ / 16) := by
      rw [← hmul]; ring
    have h3 : (8 * qvSumConst E + 13) * (N : ℝ) ^ (δ / 16) ≤ (N : ℝ) ^ (δ / 16) *
        (N : ℝ) ^ (δ / 16) := mul_le_mul_of_nonneg_right hC (by positivity)
    have h4 : (N : ℝ) ^ (δ / 16) * (N : ℝ) ^ (δ / 16) = (N : ℝ) ^ (δ / 8) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    nlinarith
  unfold azumaMm
  rw [← hξ]
  have hsq : Real.sqrt (4 * ξ ^ 2 * (2 * qvSumConst E * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5)
      ≤ (N : ℝ) ^ (δ / 16) := by
    rw [Real.sqrt_le_left (by positivity)]
    calc _ ≤ (N : ℝ) ^ (δ / 8) := hQ
      _ = ((N : ℝ) ^ (δ / 16)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  calc (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ξ ^ 2 *
        (2 * qvSumConst E * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5)
      ≤ (N : ℝ) ^ (δ / 16) * (N : ℝ) ^ (δ / 16) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (N : ℝ) ^ (δ / 8) := by rw [← Real.rpow_add hN0]; congr 1; ring


/-- Summing a termwise affine bound. -/
theorem sum_le_affine_sum {k : ℕ} {f g : ℕ → ℝ} (A B C D : ℝ)
    (h : ∀ j ∈ Finset.range k, f j ≤ A * (B * g j + C) + D) :
    ∑ j ∈ Finset.range k, f j ≤ A * (B * ∑ j ∈ Finset.range k, g j + (k : ℝ) * C) +
      (k : ℝ) * D := by
  calc ∑ j ∈ Finset.range k, f j ≤ ∑ j ∈ Finset.range k, (A * (B * g j + C) + D) :=
        Finset.sum_le_sum h
    _ = A * (B * ∑ j ∈ Finset.range k, g j + (k : ℝ) * C) + (k : ℝ) * D := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]

/-- The final real arithmetic of `xZ_le_azumaMm`. -/
theorem sqrt_floor_arith {ξ T R q S NC NX : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hS : S ≤ ξ ^ 2 * T ^ 2 * ((q + 2) * (R ^ 4 + 1)) + NC) (hNC : NC ≤ T ^ 2)
    (hNX : NX ≤ T ^ 2) :
    Real.sqrt (4 * S + NX) ≤ T * (R ^ 2 + 1) * Real.sqrt (4 * ξ ^ 2 * (q + 2) + 5) := by
  have hQ0 : 0 ≤ 4 * ξ ^ 2 * (q + 2) + 5 := by positivity
  have hY0 : 0 ≤ T * (R ^ 2 + 1) * Real.sqrt (4 * ξ ^ 2 * (q + 2) + 5) := by positivity
  rw [Real.sqrt_le_left hY0, mul_pow, Real.sq_sqrt hQ0]
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hsq : R ^ 4 + 1 ≤ (R ^ 2 + 1) ^ 2 := by nlinarith [sq_nonneg R]
  have hT2 : 0 ≤ T ^ 2 := by positivity
  have hX : 4 * S + NX ≤ T ^ 2 * (R ^ 4 + 1) * (4 * ξ ^ 2 * (q + 2) + 5) := by
    have e : T ^ 2 * (R ^ 4 + 1) * (4 * ξ ^ 2 * (q + 2) + 5)
        = 4 * (ξ ^ 2 * T ^ 2 * ((q + 2) * (R ^ 4 + 1))) + 5 * T ^ 2 * (R ^ 4 + 1) := by ring
    rw [e]
    have : 5 * T ^ 2 ≤ 5 * T ^ 2 * (R ^ 4 + 1) := by nlinarith
    linarith
  calc 4 * S + NX ≤ T ^ 2 * (R ^ 4 + 1) * (4 * ξ ^ 2 * (q + 2) + 5) := hX
    _ ≤ T ^ 2 * (R ^ 2 + 1) ^ 2 * (4 * ξ ^ 2 * (q + 2) + 5) := by gcongr
    _ = (T * (R ^ 2 + 1)) ^ 2 * (4 * ξ ^ 2 * (q + 2) + 5) := by ring

/-- `W^{2D} Csh² Δ² · 2 ≤ 1` for `Δ ≤ N^{-(D+10)}`, `W ≤ N`, `Csh ≤ 1536 N⁸`, `N ≥ 64`. -/
theorem two_Csh_sq_step_sq_le {N : ℕ} (hN64 : (64 : ℝ) ≤ N) {Cs Δ W D : ℝ} (hD : 0 ≤ D)
    (hCs0 : 0 ≤ Cs) (hCs : Cs ≤ 1536 * (N : ℝ) ^ 8) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ (N : ℝ) ^ (-(D + 10))) (hW1 : 1 ≤ W) (hWN : W ≤ N) :
    2 * Cs ^ 2 * Δ ^ 2 * W ^ (2 * D) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hW : W ^ (2 * D) ≤ (N : ℝ) ^ (2 * D) :=
    Real.rpow_le_rpow (by linarith) hWN (by linarith)
  have hΔ2 : Δ ^ 2 ≤ (N : ℝ) ^ (-(2 * D + 20)) := by
    calc Δ ^ 2 ≤ ((N : ℝ) ^ (-(D + 10))) ^ 2 := pow_le_pow_left₀ hΔ0 hΔ 2
      _ = (N : ℝ) ^ (-(2 * D + 20)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hCs2 : Cs ^ 2 ≤ 1536 ^ 2 * (N : ℝ) ^ (16 : ℝ) := by
    calc Cs ^ 2 ≤ (1536 * (N : ℝ) ^ 8) ^ 2 := pow_le_pow_left₀ hCs0 hCs 2
      _ = 1536 ^ 2 * (N : ℝ) ^ (16 : ℝ) := by
        rw [mul_pow, ← pow_mul, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hprod : (N : ℝ) ^ (16 : ℝ) * (N : ℝ) ^ (-(2 * D + 20)) * (N : ℝ) ^ (2 * D)
      = (N : ℝ) ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  have h4 : (N : ℝ) ^ (-4 : ℝ) ≤ 1 / (2 * 1536 ^ 2) := by
    rw [Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (64 : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hN64 4
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hW0 : 0 ≤ W ^ (2 * D) := Real.rpow_nonneg (by linarith) _
  have hN16 : 0 ≤ (N : ℝ) ^ (16 : ℝ) := Real.rpow_nonneg hN0.le _
  have hNm : 0 ≤ (N : ℝ) ^ (-(2 * D + 20)) := Real.rpow_nonneg hN0.le _
  calc 2 * Cs ^ 2 * Δ ^ 2 * W ^ (2 * D)
      ≤ 2 * (1536 ^ 2 * (N : ℝ) ^ (16 : ℝ)) * (N : ℝ) ^ (-(2 * D + 20)) * (N : ℝ) ^ (2 * D) := by
        gcongr
    _ = 2 * 1536 ^ 2 * ((N : ℝ) ^ (16 : ℝ) * (N : ℝ) ^ (-(2 * D + 20)) * (N : ℝ) ^ (2 * D)) := by
        ring
    _ ≤ 2 * 1536 ^ 2 * (1 / (2 * 1536 ^ 2)) := by rw [hprod]; gcongr
    _ = 1 := by norm_num

set_option maxHeartbeats 1000000 in
-- a long chain of `set`-bound real quantities; the default budget is not enough to elaborate it
/-- **(T3′), the deterministic consequence `xZ_le_azumaMm`**: eventually in `N`, for every
`k ≤ K N` and label `a`, `xZ k a ≤ Mm · (R_k² + 1) · T_{u_k}(a)`, with `Mm = azumaMm` and
`R_k = η_s/η_{u_k}` (the shape of T1518 (T1)'s `hZ`). Uses T1508 `qv_time_sum_le'` at
`κ = δ/64`, the explicit `Csh ≤ 1536 N⁸` (T1514's constant, `η_t^{-1} ≤ N` by T1511), the mesh
condition `Δ ≤ N^{-(D+10)}`, and `N^{-C_c}, N^{-C_x} ≤ N^{-2D} ≤ T²`. -/
theorem xZ_le_azumaMm {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ}
    (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ ε D τ₁ : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 24) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hD : 60 ≤ D) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (K : ℕ → ℕ)
    (hK0 : ∀ N, K N ≠ 0) (hΔ : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-(D + 10)))
    {Cc Cx : ℝ} (hCc : 2 * D ≤ Cc) (hCx : 2 * D ≤ Cx) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      xZ d E s u K δ ε D τ₁ Cc Cx N k a ≤ azumaMm d E δ τ₁ N *
        ((etaT E (s N) / etaT E (time s u K N k)) ^ 2 + 1) *
        Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1)) := by
  filter_upwards [qv_time_sum_le' (band d) hE hs0 hst ht1 hcond hc0 hreg hδ0 hδc hε0 hεδ hD
      (δ / 64) (by positivity), etaT_inv_le_of_hreg d hE hs0 hst ht1 hc0 hreg, hΔ, d.dim,
      eventually_ge_atTop 64] with N hqv hηt hΔN hdim hN64 k hk a
  have hN64' : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hK1 : 1 ≤ K N := Nat.one_le_iff_ne_zero.2 (hK0 N)
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have hm0 := mE_im_pos hE
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  set uk := time s u K N k with huk
  have huk1 : uk < 1 := time_lt_one_of_le hsu hut ht1 hK0 hk
  have hukt : uk ≤ t N := by
    have := time_mono_of_le (K := K) (hsu N) hk
    rw [time_last s u K N (hK0 N)] at this; linarith [hut N]
  have hkΔ : (k : ℝ) * step s u K N ≤ 1 := by
    have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 N)
    have hKΔ : (K N : ℝ) * step s u K N = u N - s N := by unfold step; field_simp
    have : (k : ℝ) ≤ K N := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right this hΔ0
    linarith [hs0 N, hut N, ht1 N]
  set R := etaT E (s N) / etaT E uk with hR
  have hRe : R = (1 - s N) / (1 - uk) := Step2.etaT_ratio hE _ _
  have h1uk : 0 < 1 - uk := by linarith
  have hR0 : 0 ≤ R := by rw [hRe]; exact div_nonneg (by linarith) h1uk.le
  have hr : ∀ j ∈ Finset.range k, 0 ≤ (1 - time s u K N (j + 1)) / (1 - uk) ∧
      (1 - time s u K N (j + 1)) / (1 - uk) ≤ R := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
    have h1 := time_mono_of_le (K := K) (hsu N) hjk
    have h2 := time_mono_of_le (K := K) (hsu N) (Nat.zero_le (j + 1))
    rw [time_zero] at h2
    rw [hRe]
    exact ⟨div_nonneg (by linarith) h1uk.le, div_le_div_of_nonneg_right (by linarith) h1uk.le⟩
  have hcard := card_idx_le hdim.1
  have hηt0 : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hWN : ((band d).W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ d.L N := by exact_mod_cast (by have := d.three_le_L N; omega : 1 ≤ d.L N)
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
    change (d.W N : ℝ) ≤ N
    nlinarith
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
  have hCsh : ∀ j ∈ Finset.range k, 2 * qvTimeShiftConst d N E (time s u K N (j + 1)) ^ 2 *
      step s u K N ^ 2 * ((band d).W N : ℝ) ^ (2 * D) ≤ 1 := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
    have hv : time s u K N (j + 1) ≤ t N := (time_mono_of_le (hsu N) hjk).trans hukt
    have hηv : etaT E (t N) ≤ etaT E (time s u K N (j + 1)) := by
      simp only [Step2.etaT_eq]; exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    have hηv0 : 0 < etaT E (time s u K N (j + 1)) := lt_of_lt_of_le hηt0 hηv
    have hinv : (etaT E (time s u K N (j + 1)))⁻¹ ≤ N := (inv_anti₀ hηt0 hηv).trans hηt
    exact two_Csh_sq_step_sq_le hN64' hD0 (qvTimeShiftConst_nonneg _ _ _ _)
      (qvTimeShiftConst_le hN1' hcard hinv (inv_nonneg.2 hηv0.le)) hΔ0 hΔN hW1 hWN
  set ξ := Step2.xiK (d.L N) (d.W N) (mE E).im with hξ
  set T := Step2.tT (band d) E N D uk (zdist (d.L N) (a 0 - a 1)) with hT
  have hTW : ((band d).W N : ℝ) ^ (-D) ≤ T := rpow_neg_le_tailT _
  have hTN : (N : ℝ) ^ (-D) ≤ T :=
    (Real.rpow_le_rpow_of_nonpos (by linarith) hWN (by linarith)).trans hTW
  have hNmD : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hT0 : 0 < T := lt_of_lt_of_le hNmD hTN
  have hT2 : (N : ℝ) ^ (-(2 * D)) ≤ T ^ 2 := by
    calc (N : ℝ) ^ (-(2 * D)) = ((N : ℝ) ^ (-D)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      _ ≤ T ^ 2 := pow_le_pow_left₀ hNmD.le hTN 2
  -- termwise bound on `cZ`
  have hcZ : ∀ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j ≤
      ξ ^ 2 * T ^ 2 * (2 * (N : ℝ) ^ τ₁ * (step s u K N * Qd (band d) E s δ ε D N
        (time s u K N j) * ((1 - time s u K N (j + 1)) / (1 - uk)) ^ 4)
        + step s u K N * R ^ 4) + step s u K N * (N : ℝ) ^ (-Cc) := by
    intro j hj
    obtain ⟨hr0, hrR⟩ := hr j hj
    set r := (1 - time s u K N (j + 1)) / (1 - uk) with hrdef
    have hjk : j < k := Finset.mem_range.1 hj
    have huj : time s u K N j < 1 :=
      (time_mono_of_le (hsu N) hjk.le).trans_lt huk1
    have huj0 : 0 ≤ time s u K N j := by
      have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le j); rw [time_zero] at this
      linarith [hs0 N]
    have hQd := QVSum.Qd_nonneg (band d) hE (s := s) (δ := δ) (ε := ε) (D := D) (N := N) hs1
      huj0 huj
    have hQ : 0 ≤ Qprime d E s u K δ ε D τ₁ N j := by
      unfold Qprime
      have := qvTimeShiftConst_nonneg d N E (time s u K N (j + 1))
      have : 0 ≤ ((band d).W N : ℝ) ^ (2 * D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have hr4 : r ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ hr0 hrR 4
    have hcsh := hCsh j hj
    have e1 : cZ d E s u K δ ε D τ₁ Cc N k a j = ξ ^ 2 * T ^ 2 *
        (step s u K N * Qprime d E s u K δ ε D τ₁ N j * r ^ 4) +
        step s u K N * (N : ℝ) ^ (-Cc) := by
      unfold cZ
      rw [← hrdef, ← huk, ← hξ, ← hT]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hQ, ← pow_mul]
      ring
    rw [e1]
    have e2 : step s u K N * Qprime d E s u K δ ε D τ₁ N j * r ^ 4 =
        2 * (N : ℝ) ^ τ₁ * (step s u K N * Qd (band d) E s δ ε D N (time s u K N j) * r ^ 4)
        + (2 * qvTimeShiftConst d N E (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2 *
          ((band d).W N : ℝ) ^ (2 * D)) * (step s u K N * r ^ 4) := by
      unfold Qprime; ring
    rw [e2]
    have h3 : (2 * qvTimeShiftConst d N E (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2 *
          ((band d).W N : ℝ) ^ (2 * D)) * (step s u K N * r ^ 4) ≤ step s u K N * R ^ 4 := by
      have hsr : 0 ≤ step s u K N * r ^ 4 := by positivity
      calc _ ≤ 1 * (step s u K N * r ^ 4) := mul_le_mul_of_nonneg_right hcsh hsr
        _ ≤ step s u K N * R ^ 4 := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hr4 hΔ0
    have hξT : 0 ≤ ξ ^ 2 * T ^ 2 := by positivity
    nlinarith
  -- summed bound
  have hqvk := hqv u K (hsu N) (hut N) hK1 k hk
  set SQ := ∑ j ∈ Finset.range k, step s u K N * Qd (band d) E s δ ε D N (time s u K N j) *
    ((1 - time s u K N (j + 1)) / (1 - uk)) ^ 4 with hSQ
  have hs := sum_le_affine_sum (ξ ^ 2 * T ^ 2) (2 * (N : ℝ) ^ τ₁) (step s u K N * R ^ 4)
    (step s u K N * (N : ℝ) ^ (-Cc)) hcZ
  rw [← hSQ] at hs
  set P0 := (N : ℝ) ^ (τ₁ + δ / 64) with hP0
  have hNτ : (N : ℝ) ^ τ₁ * (N : ℝ) ^ (δ / 64) = P0 := by rw [hP0, Real.rpow_add hN0]
  have hq0 : 0 ≤ qvSumConst E := by unfold qvSumConst; positivity
  have hSQ' : 2 * (N : ℝ) ^ τ₁ * SQ ≤ 2 * qvSumConst E * P0 * (R ^ 4 + 1) := by
    calc 2 * (N : ℝ) ^ τ₁ * SQ ≤ 2 * (N : ℝ) ^ τ₁ * (qvSumConst E * (N : ℝ) ^ (δ / 64) *
          (R ^ 4 + 1)) := mul_le_mul_of_nonneg_left hqvk (by positivity)
      _ = 2 * qvSumConst E * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (δ / 64)) * (R ^ 4 + 1) := by ring
      _ = 2 * qvSumConst E * P0 * (R ^ 4 + 1) := by rw [hNτ]
  have hkR : (k : ℝ) * (step s u K N * R ^ 4) ≤ R ^ 4 := by
    calc (k : ℝ) * (step s u K N * R ^ 4) = ((k : ℝ) * step s u K N) * R ^ 4 := by ring
      _ ≤ 1 * R ^ 4 := mul_le_mul_of_nonneg_right hkΔ (by positivity)
      _ = R ^ 4 := one_mul _
  have hNc : 0 ≤ (N : ℝ) ^ (-Cc) := Real.rpow_nonneg hN0.le _
  have hkC : (k : ℝ) * (step s u K N * (N : ℝ) ^ (-Cc)) ≤ (N : ℝ) ^ (-Cc) := by
    calc (k : ℝ) * (step s u K N * (N : ℝ) ^ (-Cc))
        = ((k : ℝ) * step s u K N) * (N : ℝ) ^ (-Cc) := by ring
      _ ≤ 1 * (N : ℝ) ^ (-Cc) := mul_le_mul_of_nonneg_right hkΔ hNc
      _ = _ := one_mul _
  have hinnerB : 2 * (N : ℝ) ^ τ₁ * SQ + (k : ℝ) * (step s u K N * R ^ 4) ≤
      (2 * qvSumConst E * P0 + 2) * (R ^ 4 + 1) := by
    have hR4 : 0 ≤ R ^ 4 := by positivity
    have e : (2 * qvSumConst E * P0 + 2) * (R ^ 4 + 1)
        = 2 * qvSumConst E * P0 * (R ^ 4 + 1) + 2 * R ^ 4 + 2 := by ring
    rw [e]; linarith
  have hsumcZ : ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j ≤
      ξ ^ 2 * T ^ 2 * ((2 * qvSumConst E * P0 + 2) * (R ^ 4 + 1)) + (N : ℝ) ^ (-Cc) := by
    have hξT : 0 ≤ ξ ^ 2 * T ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hinnerB hξT
    linarith
  have hNCc : (N : ℝ) ^ (-Cc) ≤ T ^ 2 :=
    (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)).trans hT2
  have hNCx : (N : ℝ) ^ (-Cx) ≤ T ^ 2 :=
    (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)).trans hT2
  have hsqrt := sqrt_floor_arith hT0.le
    (mul_nonneg (mul_nonneg (by norm_num) hq0) (Real.rpow_nonneg hN0.le _)) hsumcZ hNCc hNCx
  unfold xZ azumaMm
  rw [← hξ, ← hP0]
  calc (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ∑ j ∈ Finset.range k,
        cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx))
      ≤ (N : ℝ) ^ (δ / 16) * (T * (R ^ 2 + 1) *
          Real.sqrt (4 * ξ ^ 2 * (2 * qvSumConst E * P0 + 2) + 5)) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * ξ ^ 2 * (2 * qvSumConst E * P0 + 2) + 5) *
          (R ^ 2 + 1) * T := by ring


section StepYInputs

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
  {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
  (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
  (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
  (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)

include hΦ hReal hC₂ hΔ in
/-- `stepZ` is integrable (re-proof of T1516's private `stepZ_integrable`, for a general `Φ`). -/
theorem integrable_stepZ' : Integrable (stepZ d s t K N j Φ U b) (Pg d) := by
  have hg_int := integrable_h0 d s t K N (j + 1) hΦ U b
  have hh0_int := integrable_h0 d s t K N j hΦ U b
  have hR_int := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
  have hZeq : (fun ω => (stepZ d s t K N j Φ U b ω : ℂ))
      = (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω))
        - (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N j ω))
        - (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω) := by
    funext ω
    have hg := g_eq_pointwise d s t K N j hΦ hReal U b ω
    simp only [Pi.sub_apply]
    rw [hg]; ring
  have hZc_int : Integrable (fun ω => (stepZ d s t K N j Φ U b ω : ℂ)) (Pg d) := by
    rw [hZeq]; exact (hg_int.sub hh0_int).sub hR_int
  have hre : (fun ω => RCLike.re ((stepZ d s t K N j Φ U b ω : ℝ) : ℂ))
      = stepZ d s t K N j Φ U b := funext fun ω => RCLike.ofReal_re _
  rw [← hre]
  exact hZc_int.re

include hΦ hReal hC₂ hΔ in
/-- `stepY` is integrable. -/
theorem integrable_stepY' : Integrable (stepY d s t K N j Φ U b) (Pg d) := by
  have hY := stepY_eq_ae d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)
  have hRint := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
  exact (hRint.sub integrable_condExp).congr hY.symm

include hΦ hReal hC₂ hΔ in
/-- `stepY ∈ L²`: `‖stepY‖ ≤ g + E[g|F_j]` with `g = C‖X_{j+1}‖² ∈ L²`. -/
theorem memLp_stepY' : MemLp (stepY d s t K N j Φ U b) 2 (Pg d) := by
  have hbd := stepY_norm_le_ae d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)
  set g : Ωg d → ℝ := fun ω => (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
      * ‖Xmat d N (ω (j + 1))‖ ^ 2 with hgdef
  have hgmeas : Measurable g := by
    have hX : Measurable (fun ω : Ωg d => Xmat d N (ω (j + 1))) :=
      (measurable_Xmat d N).comp (measurable_pi_apply (j + 1))
    exact measurable_const.mul ((measurable_norm.comp hX).pow_const 2)
  have hg2 : MemLp g 2 (Pg d) := by
    rw [memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable]
    have : (fun ω => g ω ^ 2) = fun ω => ((∑ a : LoopArg (d.L N) 2, |U b a|) *
        ((C₂ / 2) * step s t K N)) ^ 2 * ‖Xmat d N (ω (j + 1))‖ ^ 4 := by
      funext ω; rw [hgdef]; ring
    rw [this]
    exact (integrable_normPow4_incr d N j).const_mul _
  have hsum : MemLp (fun ω => g ω + (Pg d)[g | filt d j] ω) 2 (Pg d) :=
    hg2.add (hg2.condExp (by norm_num))
  refine hsum.of_le (integrable_stepY' s t K N j hΦ hReal hC₂ hΔ U b).aestronglyMeasurable ?_
  filter_upwards [hbd] with ω hω
  exact hω.trans (le_abs_self _)

include hΦ hReal hC₂ hΔ in
/-- The stopped `stepY` has conditional mean zero (real part). -/
theorem condExp_indicator_stepY_re {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S) :
    (Pg d)[fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).re | filt d j] =ᵐ[Pg d] 0 := by
  have hint := integrable_stepY' s t K N j hΦ hReal hC₂ hΔ U b
  have hmean := (stepDecomp d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)).2.2.2
  have hfun : (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).re)
      = S.indicator (fun ω => (stepY d s t K N j Φ U b ω).re) := by
    funext ω; by_cases h : ω ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hfun]
  have hre : Integrable (fun ω => (stepY d s t K N j Φ U b ω).re) (Pg d) := hint.re
  have h1 := condExp_indicator (m := filt d j) hre hS
  have h2 : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).re | filt d j] =ᵐ[Pg d] 0 := by
    have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint
      Complex.reCLM).symm
    have hc' : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).re | filt d j]
        =ᵐ[Pg d] fun ω => ((Pg d)[stepY d s t K N j Φ U b | filt d j] ω).re := by
      simpa [Function.comp_def] using hc
    filter_upwards [hc', hmean] with ω h1 h2
    rw [h1, h2]; simp
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  by_cases h : ω ∈ S
  · rw [Set.indicator_of_mem h, hω2]
  · rw [Set.indicator_of_notMem h]; rfl

include hΦ hReal hC₂ hΔ in
/-- The stopped `stepY` has conditional mean zero (imaginary part). -/
theorem condExp_indicator_stepY_im {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S) :
    (Pg d)[fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).im | filt d j] =ᵐ[Pg d] 0 := by
  have hint := integrable_stepY' s t K N j hΦ hReal hC₂ hΔ U b
  have hmean := (stepDecomp d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)).2.2.2
  have hfun : (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).im)
      = S.indicator (fun ω => (stepY d s t K N j Φ U b ω).im) := by
    funext ω; by_cases h : ω ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hfun]
  have him : Integrable (fun ω => (stepY d s t K N j Φ U b ω).im) (Pg d) := hint.im
  have h1 := condExp_indicator (m := filt d j) him hS
  have h2 : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).im | filt d j] =ᵐ[Pg d] 0 := by
    have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint
      Complex.imCLM).symm
    have hc' : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).im | filt d j]
        =ᵐ[Pg d] fun ω => ((Pg d)[stepY d s t K N j Φ U b | filt d j] ω).im := by
      simpa [Function.comp_def] using hc
    filter_upwards [hc', hmean] with ω h1 h2
    rw [h1, h2]; simp
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  by_cases h : ω ∈ S
  · rw [Set.indicator_of_mem h, hω2]
  · rw [Set.indicator_of_notMem h]; rfl

include hΦ hReal hC₂ hΔ in
/-- The `L²` input of T1504 (T2) for the stopped `stepY`:
`∫ (1_S stepY)_re² + ∫ (1_S stepY)_im² ≤ 4 (C_r C₂/2)² Δ² ∫‖X_{j+1}‖⁴` for any row bound
`Σ_a |U(b,a)| ≤ C_r` (T1505 `stepDecomp_Y_sq`). -/
theorem integral_sq_indicator_stepY_le {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S)
    {Cr : ℝ} (hCr : ∑ a : LoopArg (d.L N) 2, |U b a| ≤ Cr) (hC₂0 : 0 ≤ C₂) :
    ∫ ω, (S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2 ∂(Pg d)
      + ∫ ω, (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2 ∂(Pg d)
      ≤ 4 * (Cr * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by
  have hm := memLp_stepY' s t K N j hΦ hReal hC₂ hΔ U b
  have hmI : MemLp (S.indicator (stepY d s t K N j Φ U b)) 2 (Pg d) :=
    hm.indicator ((filt d).le j S hS)
  have hre : Integrable (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2) (Pg d) :=
    hmI.re.integrable_sq
  have him : Integrable (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2) (Pg d) :=
    hmI.im.integrable_sq
  have hn2 : Integrable (fun ω => ‖stepY d s t K N j Φ U b ω‖ ^ 2) (Pg d) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  rw [← integral_add hre him]
  have hY2 := stepDecomp_Y_sq d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)
  have hX4 : 0 ≤ ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) :=
    integral_nonneg fun _ => by positivity
  have hU0 : 0 ≤ ∑ a : LoopArg (d.L N) 2, |U b a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ∫ ω, ((S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2
        + (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2) ∂(Pg d)
      ≤ ∫ ω, ‖stepY d s t K N j Φ U b ω‖ ^ 2 ∂(Pg d) := by
        refine integral_mono (hre.add him) hn2 fun ω => ?_
        have e : (S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2
            + (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2
            = ‖S.indicator (stepY d s t K N j Φ U b) ω‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        simp only
        rw [e]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self _ _) 2
    _ ≤ 4 * ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := hY2
    _ ≤ 4 * (Cr * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by
        have h1 : (∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2) ≤ Cr * (C₂ / 2) :=
          mul_le_mul_of_nonneg_right hCr (by linarith)
        have h2 : ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 ≤ (Cr * (C₂ / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        gcongr

end StepYInputs

/-- `∫ ‖X_{j+1}‖⁴ dPg = ∫ ‖X‖⁴ dP ≤ 3 · #(Idx N)` (the Gaussian fourth moment via the trace
moments, `traceConst 2 = 3`). -/
theorem integral_norm_Xmat_incr_four_le (N j : ℕ) :
    ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) ≤ 3 * (Fintype.card (d.Idx N) : ℝ) := by
  have hmap : ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) = ∫ x, ‖Xmat d N x‖ ^ 4 ∂(P d) := by
    rw [← map_incr d j]
    rw [integral_map (measurable_pi_apply (j + 1)).aemeasurable]
    · rw [map_incr d j]
      exact ((measurable_norm_Xmat d N).pow_const 4).aestronglyMeasurable
  rw [hmap]
  have h1 := integral_norm_Xmat_pow_le (d := d) N 1
  norm_num at h1
  have hfrob : ∀ ω : Ω d, frobSq (Xmat d N ω ^ 2) = ∑ i, colSq (Xmat d N ω) 2 i := by
    intro ω; unfold frobSq colSq; exact Finset.sum_comm
  simp only [hfrob] at h1
  rw [integral_finsetSum _ fun i _ => integrable_colSq d N 2 i] at h1
  have h2 : ∑ i : d.Idx N, ∫ ω, colSq (Xmat d N ω) 2 i ∂(P d)
      ≤ ∑ _i : d.Idx N, traceConst 2 := Finset.sum_le_sum fun i _ => integral_colSq_le d N 2 i
  have h3 : traceConst 2 = 3 := by norm_num [traceConst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h3] at h2
  linarith

/-- Row sum of the unit-charge kernel: `Σ_a |U_{v,w}(b,a)| ≤ ((1−v)/(1−w))²` for
`0 ≤ v ≤ w < 1` (`norm_Uker_apply_le` at the constant tensor `1`). -/
theorem sum_abs_ukerMat_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w)
    (hw1 : w < 1) (b : LoopArg L 2) :
    ∑ a : LoopArg L 2, |ukerMat L v w b a| ≤ ((1 - v) / (1 - w)) ^ 2 := by
  have habs : ∀ a, |ukerMat L v w b a| = ukerMat L v w b a := fun a =>
    abs_of_nonneg (ukerMat_nonneg L hL hv0 hvw hw1 b a)
  simp only [habs]
  have hsum : ∑ a : LoopArg L 2, ukerMat L v w b a
      = (Uker L (fun _ => (1 : ℂ)) (v : ℂ) (w : ℂ) (fun _ => (1 : ℂ)) b).re := by
    rw [Uker_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ukerMat_eq_prod_re, mul_one]
  rw [hsum]
  have hw0 : 0 ≤ w := hv0.trans hvw
  have h1w : 0 < 1 - w := by linarith
  have hnw : ‖(w : ℂ) * 1‖ = w := by rw [mul_one, Complex.norm_real, Real.norm_of_nonneg hw0]
  have hnvw : ‖((v : ℂ) - (w : ℂ)) * 1‖ = w - v := by
    rw [mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hB := norm_Uker_apply_le L hL (ξ := fun _ => (1 : ℂ)) (s := (v : ℂ)) (t := (w : ℂ))
    (fun _ => by rw [hnw]; exact hw1) (C := (1 - v) / (1 - w)) (M := 1) zero_le_one
    (fun _ => by
      rw [hnw, hnvw, le_div_iff₀ h1w, add_mul, one_mul, mul_assoc, inv_mul_cancel₀ h1w.ne',
        mul_one]
      linarith)
    (A := fun _ => (1 : ℂ)) (fun _ => by simp) b
  rw [mul_one] at hB
  exact (Complex.re_le_norm _).trans hB

/-- The increments `Yvec i` with the index cut to `1 ≤ i ≤ K N`. -/
def YvecCut (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ) (ω : Ωg d)
    (a : LoopArg (d.L N) 2) : ℂ :=
  (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) * Yvec (band d) E s u K N i ω a

theorem YvecCut_succ {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ} (hj : j < K N) :
    YvecCut (d := d) E s u K N (j + 1) = Yvec (band d) E s u K N (j + 1) := by
  funext ω a
  unfold YvecCut
  have h1 : (if 1 ≤ j + 1 ∧ j + 1 ≤ K N then (1 : ℂ) else 0) = 1 := by
    simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
  rw [h1, one_mul]

theorem stronglyMeasurable_YvecCut {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ}
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℕ → ℕ}
    (hK0 : ∀ N, K N ≠ 0) (N i : ℕ) :
    StronglyMeasurable[filt d i] (YvecCut (d := d) E s u K N i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ K N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [YvecCut_succ (by omega)]
    have hu1 : time s u K N (j + 1) < 1 := time_lt_one_of_le hsu hut ht1 hK0 hi.2
    have hΦ : ∀ a, TestFun d N (Φgrid (band d) E N (time s u K N (j + 1)) a) :=
      fun a => Φgrid_testFun (band d) hE N hu1 a
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact measurable_stepY_filt s u K N j hΦ _ a
  · have : YvecCut (d := d) E s u K N i = fun _ => 0 := by
      funext ω a; unfold YvecCut
      have h0 : (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]; exact hi
      rw [h0, zero_mul]; rfl
    rw [this]; exact stronglyMeasurable_const

/-- **The grid-size exponent of (T4′)**: `C_K(D, D₁) = D₁ + 2D + 80` (depends only on `D, D₁`). -/
def CK (D D₁ : ℝ) : ℝ := D₁ + 2 * D + 80

/-- **The grid size of (T4′)**: `K N = ⌈N^{C_K}⌉` (`max 1` only matters at `N = 0`). -/
def gridK (D D₁ : ℝ) (N : ℕ) : ℕ := max 1 ⌈(N : ℝ) ^ CK D D₁⌉₊

theorem gridK_ne_zero (D D₁ : ℝ) (N : ℕ) : gridK D D₁ N ≠ 0 := by
  unfold gridK; omega

theorem rpow_CK_le_gridK (D D₁ : ℝ) (N : ℕ) : (N : ℝ) ^ CK D D₁ ≤ gridK D D₁ N := by
  unfold gridK
  calc (N : ℝ) ^ CK D D₁ ≤ (⌈(N : ℝ) ^ CK D D₁⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((max 1 ⌈(N : ℝ) ^ CK D D₁⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _

/-- `Δ ≤ N^{-C_K}` on the grid `gridK`, once `0 ≤ u N − s N ≤ 1`. -/
theorem step_gridK_le {s u : ℕ → ℝ} {D D₁ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hus : u N - s N ≤ 1) : step s u (gridK D D₁) N ≤ (N : ℝ) ^ (-CK D D₁) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) ^ CK D D₁ := Real.rpow_pos_of_pos hN0 _
  have hK := rpow_CK_le_gridK D D₁ N
  have hK0 : (0 : ℝ) < gridK D D₁ N := lt_of_lt_of_le hpos hK
  unfold step
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc u N - s N ≤ 1 := hus
    _ = ((N : ℝ) ^ CK D D₁)⁻¹ * (N : ℝ) ^ CK D D₁ := (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ ((N : ℝ) ^ CK D D₁)⁻¹ * gridK D D₁ N :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- `gridK` has polynomially many points: `K N + 1 ≤ N^{C_K + 2}` eventually. -/
theorem gridK_card_le {D D₁ : ℝ} (hCK : 0 ≤ CK D D₁) :
    ∀ᶠ N : ℕ in atTop, ((gridK D D₁ N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (CK D D₁ + 2) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hA1 : (1 : ℝ) ≤ (N : ℝ) ^ CK D D₁ := Real.one_le_rpow (by linarith) hCK
  have hK : (gridK D D₁ N : ℝ) ≤ (N : ℝ) ^ CK D D₁ + 1 := by
    unfold gridK
    rcases le_total 1 ⌈(N : ℝ) ^ CK D D₁⌉₊ with h | h
    · rw [max_eq_right h]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    · rw [max_eq_left h]; push_cast; linarith
  push_cast
  rw [Real.rpow_add hN0, Real.rpow_two]
  have hN4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hN4 (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ CK D D₁)
  linarith

/-- The per-step `L²` constant of (T4′): `4 (C_r C₂/2)² Δ² M₄ ≤ 2²² N¹⁹ Δ²`. -/
theorem cheb_e_le {N : ℕ} (hN1 : (1 : ℝ) ≤ N) {Cr card ηi M4 Δ : ℝ} (hCr0 : 0 ≤ Cr)
    (hCr : Cr ≤ (N : ℝ) ^ 2) (hc0 : 0 ≤ card) (hc : card ≤ N) (hηi0 : 0 ≤ ηi) (hηi : ηi ≤ N)
    (hM0 : 0 ≤ M4) (hM : M4 ≤ 3 * card) :
    4 * (Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2)) ^ 2 * Δ ^ 2 * M4
      ≤ 2 ^ 22 * (N : ℝ) ^ 19 * Δ ^ 2 := by
  have h1 : 1 + ηi ≤ 2 * N := by linarith
  have hC2 : card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2 ≤ 512 * (N : ℝ) ^ 7 := by
    have e : card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2 = 8 * card * (1 + ηi) ^ 6 := by
      ring
    rw [e]
    calc 8 * card * (1 + ηi) ^ 6 ≤ 8 * N * (2 * N) ^ 6 := by gcongr
      _ = 512 * (N : ℝ) ^ 7 := by ring
  have hC20 : 0 ≤ card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2 := by positivity
  have hP : Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2) ≤ 512 * (N : ℝ) ^ 9 := by
    calc _ ≤ (N : ℝ) ^ 2 * (512 * (N : ℝ) ^ 7) := mul_le_mul hCr hC2 hC20 (by positivity)
      _ = 512 * (N : ℝ) ^ 9 := by ring
  have hP2 : (Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2)) ^ 2
      ≤ (512 * (N : ℝ) ^ 9) ^ 2 := pow_le_pow_left₀ (by positivity) hP 2
  have hM' : M4 ≤ 3 * N := by linarith
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  calc 4 * (Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2)) ^ 2 * Δ ^ 2 * M4
      ≤ 4 * (512 * (N : ℝ) ^ 9) ^ 2 * Δ ^ 2 * (3 * N) := by gcongr
    _ = 3 * 2 ^ 20 * (N : ℝ) ^ 19 * Δ ^ 2 := by ring
    _ ≤ 2 ^ 22 * (N : ℝ) ^ 19 * Δ ^ 2 := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ 19 * Δ ^ 2 := by positivity
        nlinarith

/-- **(T4′) `cheb_grid_at_tau`** (T1519-amend-1): the Chebyshev bound for the stopped remainder
**at the random target `u_τ`** only (no union over target indices). For every `D₁ > 0`, on the grid
`K = gridK D D₁ = ⌈N^{C_K}⌉` with the explicit `C_K = D₁ + 2D + 80`, eventually in `N`,
`P{∃ a, T_{u_τ}(a) ≤ ‖(Σ_{j<τ} U_{u_{j+1},u_τ} Y_{j+1}) a‖} ≤ N^{-D₁}`, with `τ = gridTau`.
Route: T1504 (T2) `stopped_duhamel_cheb_tail` at `x = W^{-D}/4` (`2²x = W^{-D} ≤ T`), target
`t = u_K = u N`; per step `e_j = 2²² N¹⁹ Δ²` from T1505 `stepDecomp_Y_sq` with the kernel row sum
`((1−u_{j+1})/(1−u_K))² ≤ η_t^{-2} ≤ N²` (T1511), `C₂` of `Φgrid_bdd2` at `η = η_t`, and
`∫‖X‖⁴ ≤ 3N`; mean zero from T1505 part 4 and `{j < τ} ∈ F_j`. -/
theorem cheb_grid_at_tau {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {D : ℝ} (hD0 : 0 ≤ D) (δ τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N)
    (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) E N D
            (time s u (gridK D D₁) N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω))
            (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D D₁) N (j + 1) : ℂ)
                (time s u (gridK D D₁) N
                  (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω) : ℂ)
                (Yvec (band d) E s u (gridK D D₁) N (j + 1) ω)) a‖}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  intro D₁ hD₁
  filter_upwards [etaT_inv_le_of_hreg d hE hs0 hst ht1 hc0 hreg, d.dim, eventually_ge_atTop 2]
    with N hηt hdim hN2
  set K : ℕ → ℕ := gridK D D₁ with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D D₁
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 := mE_im_pos hE
  have hm1 := mE_im_le_one (E := E) hE
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have huN1 : u N < 1 := (hut N).trans_lt (ht1 N)
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have hus : u N - s N ≤ 1 := by linarith [hs0 N]
  have hΔCK : step s u K N ≤ (N : ℝ) ^ (-CK D D₁) := step_gridK_le (by omega) hus
  have hKΔ : (K N : ℝ) * step s u K N ≤ 1 := by
    have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 N)
    have : (K N : ℝ) * step s u K N = u N - s N := by unfold step; field_simp
    rw [this]; exact hus
  set τN : Ωg d → ℕ := fun ω => gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω with hτN
  have hτK : ∀ ω, τN ω ≤ K N := fun ω => gridTau_le E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j =>
    lt_gridTau_measurableSet hE D δ τ₁ ε ζCtr τ3 τ57 s u K N j
  have hY : ∀ i, StronglyMeasurable[filt d i] (YvecCut (d := d) E s u K N i) := fun i =>
    stronglyMeasurable_YvecCut hE hsu hut ht1 hK0 N i
  have hu0 : 0 ≤ time s u K N 0 := by rw [time_zero]; exact hs0 N
  have hu_succ : ∀ j, time s u K N j ≤ time s u K N (j + 1) := fun j =>
    time_mono_of_le (hsu N) (Nat.le_succ j)
  have hutK : time s u K N (K N) = u N := time_last s u K N (hK0 N)
  have hηt0 : 0 < etaT E (t N) := Step2.etaT_pos' hE (ht1 N)
  have hcard := card_idx_le hdim.1
  set eb : ℝ := 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N ^ 2 with heb
  -- per-step inputs
  have hstep : ∀ b : LoopArg (d.L N) 2, ∀ j < K N,
      let S : Set (Ωg d) := {ω | j < τN ω}
      let Φ := Φgrid (band d) E N (time s u K N (j + 1))
      let U := ukerMat (d.L N) (time s u K N (j + 1)) (u N)
      (fun ω => S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (u N : ℂ) (YvecCut (d := d) E s u K N (j + 1) ω') b) ω)
        =ᵐ[Pg d] S.indicator (stepY d s u K N j Φ U b) ∧
      (∀ a A, A.IsHermitian → (Φ a A).im = 0) ∧ (∀ a, TestFun d N (Φ a)) ∧
      (∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ (Fintype.card (d.Idx N) : ℝ) *
          ((2 : ℝ) ^ 2 * (2 * (1 + (etaT E (t N))⁻¹) ^ 3) ^ 2)) ∧
      ∑ a : LoopArg (d.L N) 2, |U b a| ≤ (N : ℝ) ^ 2 := by
    intro b j hj S Φ U
    have hv0 : 0 ≤ time s u K N (j + 1) := hu0.trans
      (by have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le (j + 1)); rwa [time_zero] at this ⊢)
    have hvw : time s u K N (j + 1) ≤ u N := by
      rw [← hutK]; exact time_mono_of_le (hsu N) hj
    have hv1 : time s u K N (j + 1) < 1 := hvw.trans_lt huN1
    have hΦ : ∀ a, TestFun d N (Φ a) := fun a => Φgrid_testFun (band d) hE N hv1 a
    have hae := stepY_ukerMat_eq_Uker_ae d s u K N j hΦ hv0 hvw huN1
    refine ⟨?_, fun a A hA => Φgrid_im_eq_zero (band d) hE.le N hv0 hv1 a hA, hΦ, ?_, ?_⟩
    · filter_upwards [hae] with ω hω
      by_cases hωS : ω ∈ S
      · rw [Set.indicator_of_mem hωS, Set.indicator_of_mem hωS, YvecCut_succ hj, hω b]
        rfl
      · rw [Set.indicator_of_notMem hωS, Set.indicator_of_notMem hωS]
    · intro a A
      have hzη : etaT E (t N) ≤ |(zt E (time s u K N (j + 1))).im| := by
        rw [zt_im]
        refine le_trans ?_ (le_abs_self _)
        simp only [Step2.etaT_eq]
        exact mul_le_mul_of_nonneg_right (by linarith [hut N]) hm0.le
      exact Φgrid_bdd2 (band d) hE N hv1 hηt0 hzη a A
    · refine (sum_abs_ukerMat_le (d.L N) (d.three_le_L N) hv0 hvw huN1 b).trans ?_
      have h1 : (1 - time s u K N (j + 1)) / (1 - u N) ≤ N := by
        have h1u : 0 < 1 - u N := by linarith
        have h1t : 0 < 1 - t N := by linarith [ht1 N]
        calc (1 - time s u K N (j + 1)) / (1 - u N) ≤ 1 / (1 - t N) := by
              rw [div_le_div_iff₀ h1u h1t]; nlinarith [hut N]
          _ ≤ (etaT E (t N))⁻¹ := by
              rw [Step2.etaT_eq, one_div, mul_inv]
              have : 1 ≤ ((mE E).im)⁻¹ := (one_le_inv₀ hm0).2 hm1
              have h0 : 0 < (1 - t N)⁻¹ := inv_pos.2 h1t
              nlinarith
          _ ≤ N := hηt
      have h0 : 0 ≤ (1 - time s u K N (j + 1)) / (1 - u N) :=
        div_nonneg (by linarith) (by linarith)
      exact pow_le_pow_left₀ h0 h1 2
  have hηi0 : 0 ≤ (etaT E (t N))⁻¹ := inv_nonneg.2 hηt0.le
  have hM4 : ∀ j, ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) ≤ 3 * (Fintype.card (d.Idx N) : ℝ) :=
    fun j => integral_norm_Xmat_incr_four_le N j
  have hM40 : ∀ j, 0 ≤ ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) :=
    fun j => integral_nonneg fun _ => by positivity
  have hcheb := stopped_duhamel_cheb_tail (μ := Pg d) (d.L N) (d.three_le_L N)
    (ξ := fun _ => (1 : ℂ)) (fun _ => by simp) (u := time s u K N) (t := u N) hu0 hu_succ hutK
    huN1 hτK hτmeas hY (e := fun _ => eb)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hS := hτmeas j
      refine (condExp_congr_ae (hf.fun_comp Complex.re)).trans ?_
      exact condExp_indicator_stepY_re s u K N j hΦ hR hC₂ hΔ0 _ b hS)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hS := hτmeas j
      refine (condExp_congr_ae (hf.fun_comp Complex.im)).trans ?_
      exact condExp_indicator_stepY_im s u K N j hΦ hR hC₂ hΔ0 _ b hS)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hm := ((memLp_stepY' s u K N j hΦ hR hC₂ hΔ0
        (ukerMat (d.L N) (time s u K N (j + 1)) (u N)) b).indicator
        ((filt d).le j _ (hτmeas j))).re
      exact hm.ae_eq (hf.fun_comp Complex.re).symm)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, _⟩ := hstep b j hj
      have hm := ((memLp_stepY' s u K N j hΦ hR hC₂ hΔ0
        (ukerMat (d.L N) (time s u K N (j + 1)) (u N)) b).indicator
        ((filt d).le j _ (hτmeas j))).im
      exact hm.ae_eq (hf.fun_comp Complex.im).symm)
    (fun b j hj => by
      obtain ⟨hf, hR, hΦ, hC₂, hrow⟩ := hstep b j hj
      have hS := hτmeas j
      have e1 := integral_congr_ae (hf.fun_comp (fun z : ℂ => z.re ^ 2))
      have e2 := integral_congr_ae (hf.fun_comp (fun z : ℂ => z.im ^ 2))
      simp only [Function.comp_def] at e1 e2
      rw [e1, e2]
      have hC₂0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) *
          ((2 : ℝ) ^ 2 * (2 * (1 + (etaT E (t N))⁻¹) ^ 3) ^ 2) := by positivity
      refine (integral_sq_indicator_stepY_le s u K N j hΦ hR hC₂ hΔ0 _ b hS hrow hC₂0).trans ?_
      exact cheb_e_le hN1' (by positivity) le_rfl (Nat.cast_nonneg _) hcard hηi0 hηt
        (hM40 j) (hM4 j))
    (x := ((d.W N : ℝ) ^ (-D)) / 4)
    (div_pos (Real.rpow_pos_of_pos (by exact_mod_cast d.W_pos N) _) (by norm_num))
  -- the event inclusion
  set Sbad : Set (Ωg d) := {ω | ∃ a, 2 ^ 2 * (((d.W N : ℝ) ^ (-D)) / 4) ≤
      ‖(∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
        (time s u K N (τN ω) : ℂ) (YvecCut (d := d) E s u K N (j + 1) ω)) a‖} with hSbad
  have hsub : {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) E N D (time s u K N (τN ω)) (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
            (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
              (Yvec (band d) E s u K N (j + 1) ω)) a‖} ⊆ Sbad := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    refine ⟨a, ?_⟩
    have hsum : (∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
        (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
          (YvecCut (d := d) E s u K N (j + 1) ω))
        = ∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
            (Yvec (band d) E s u K N (j + 1) ω) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j < K N := lt_of_lt_of_le (Finset.mem_range.1 hj) (hτK ω)
      rw [YvecCut_succ this]
    rw [hsum]
    have hT : (d.W N : ℝ) ^ (-D) ≤
        Step2.tT (band d) E N D (time s u K N (τN ω)) (zdist (d.L N) (a 0 - a 1)) :=
      rpow_neg_le_tailT _
    calc 2 ^ 2 * (((d.W N : ℝ) ^ (-D)) / 4) = (d.W N : ℝ) ^ (-D) := by ring
      _ ≤ _ := hT
      _ ≤ _ := ha
  -- the arithmetic
  have hWN : (d.W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ d.L N := by exact_mod_cast (by have := d.three_le_L N; omega : 1 ≤ d.L N)
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
    nlinarith
  have hLN : (d.L N : ℝ) ≤ N := by
    have hW : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
    have h' : (d.W N : ℝ) * d.L N ≤ N := by exact_mod_cast hdim.1
    nlinarith [(Nat.cast_nonneg (d.L N) : (0 : ℝ) ≤ d.L N)]
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hx0 : 0 < ((d.W N : ℝ) ^ (-D)) / 4 := div_pos (Real.rpow_pos_of_pos hW0 _) (by norm_num)
  have hfinal : (d.L N : ℝ) ^ 2 * (∑ _j ∈ Finset.range (K N), eb) /
      (((d.W N : ℝ) ^ (-D)) / 4) ^ 2 ≤ (N : ℝ) ^ (-D₁) := by
    rw [div_le_iff₀ (pow_pos hx0 2), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- `x² ≥ N^{-2D}/16`
    have hWD : (N : ℝ) ^ (-D) ≤ (d.W N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
    have hx2 : (N : ℝ) ^ (-(2 * D)) / 16 ≤ (((d.W N : ℝ) ^ (-D)) / 4) ^ 2 := by
      have e : (N : ℝ) ^ (-(2 * D)) = ((N : ℝ) ^ (-D)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      rw [e, div_pow]
      have := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hWD 2
      norm_num; linarith
    -- `L² K e ≤ 2²² N²¹ Δ`
    have hKe : (K N : ℝ) * eb ≤ 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N := by
      rw [heb]
      have : (K N : ℝ) * (2 ^ 22 * (N : ℝ) ^ 19 * step s u K N ^ 2)
          = 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N * ((K N : ℝ) * step s u K N) := by ring
      rw [this]
      have h0 : 0 ≤ 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N := by positivity
      calc _ ≤ 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N * 1 := mul_le_mul_of_nonneg_left hKΔ h0
        _ = _ := mul_one _
    have hL2 : (d.L N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLN 2
    have hKe0 : 0 ≤ (K N : ℝ) * eb := by positivity
    have hA : (d.L N : ℝ) ^ 2 * ((K N : ℝ) * eb) ≤
        2 ^ 22 * (N : ℝ) ^ 21 * (N : ℝ) ^ (-CK D D₁) := by
      calc (d.L N : ℝ) ^ 2 * ((K N : ℝ) * eb)
          ≤ (N : ℝ) ^ 2 * (2 ^ 22 * (N : ℝ) ^ 19 * step s u K N) :=
            mul_le_mul hL2 hKe hKe0 (by positivity)
        _ = 2 ^ 22 * (N : ℝ) ^ 21 * step s u K N := by ring
        _ ≤ 2 ^ 22 * (N : ℝ) ^ 21 * (N : ℝ) ^ (-CK D D₁) :=
            mul_le_mul_of_nonneg_left hΔCK (by positivity)
    -- `2²⁶ N²¹ N^{-C_K} ≤ N^{-D₁} N^{-2D}`
    have hB : 2 ^ 22 * (N : ℝ) ^ 21 * (N : ℝ) ^ (-CK D D₁) ≤
        (N : ℝ) ^ (-D₁) * ((N : ℝ) ^ (-(2 * D)) / 16) := by
      have e1 : (N : ℝ) ^ (-CK D D₁) = (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D)) *
          (N : ℝ) ^ (-80 : ℝ) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; unfold CK; congr 1; ring
      have e2 : (N : ℝ) ^ 21 * (N : ℝ) ^ (-80 : ℝ) = (N : ℝ) ^ (-59 : ℝ) := by
        rw [show ((N : ℝ) ^ 21) = (N : ℝ) ^ ((21 : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_add hN0]; norm_num
      have h59 : (N : ℝ) ^ (-59 : ℝ) ≤ 1 / 2 ^ 26 := by
        rw [Real.rpow_neg hN0.le, show (59 : ℝ) = ((59 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (2 : ℝ) ^ 59 ≤ (N : ℝ) ^ 59 := pow_le_pow_left₀ (by norm_num) hN2' 59
        nlinarith
      rw [e1]
      have hP : 0 ≤ (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D)) := by positivity
      calc 2 ^ 22 * (N : ℝ) ^ 21 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D)) * (N : ℝ) ^ (-80 : ℝ))
          = 2 ^ 22 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D))) *
              ((N : ℝ) ^ 21 * (N : ℝ) ^ (-80 : ℝ)) := by ring
        _ = 2 ^ 22 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D))) * (N : ℝ) ^ (-59 : ℝ) := by
            rw [e2]
        _ ≤ 2 ^ 22 * ((N : ℝ) ^ (-D₁) * (N : ℝ) ^ (-(2 * D))) * (1 / 2 ^ 26) :=
            mul_le_mul_of_nonneg_left h59 (by positivity)
        _ = (N : ℝ) ^ (-D₁) * ((N : ℝ) ^ (-(2 * D)) / 16) := by ring
    calc (d.L N : ℝ) ^ 2 * ((K N : ℝ) * eb) ≤ _ := hA
      _ ≤ _ := hB
      _ ≤ (N : ℝ) ^ (-D₁) * (((d.W N : ℝ) ^ (-D)) / 4) ^ 2 :=
          mul_le_mul_of_nonneg_left hx2 (by positivity)
  calc (Pg d) _ ≤ (Pg d) Sbad := measure_mono hsub
    _ = ENNReal.ofReal ((Pg d).real Sbad) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := ENNReal.ofReal_le_ofReal (hcheb.trans hfinal)

variable (d) in
/-- **The good event of (T6′)** at size `N`, for a grid `K` and floor exponents `C_c, C_x`:
the (T3′) Azuma event for all `k ≤ K N` ∩ the failure of the (T4′) event at `τ` ∩ the good set at
every grid index `j ≤ K N` ∩ the (T5) initial bounds. -/
def goodEventGrid (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (Cc Cx : ℝ) (N : ℕ) :
    Set (Ωg d) :=
  {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) E s u K N (j + 1) ω)) a‖
        < xZ d E s u K δ ε D τ₁ Cc Cx N k a}
  ∩ {ω | ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω) : ℂ)
            (Yvec (band d) E s u K N (j + 1) ω)) a‖
        < Step2.tT (band d) E N D (time s u K N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω))
            (zdist (d.L N) (a 0 - a 1))}
  ∩ {ω | ∀ k : Fin (K N + 1),
      H d s u K N k ω ∈ goodSet d E N (time s u K N k) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D}
  ∩ {ω | (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) E s u K N 0 ω b‖ ≤
        (N : ℝ) ^ (δ / 16) * Step2.tT (band d) E N D (time s u K N 0)
          (zdist (d.L N) (b 0 - b 1)))
      ∧ jSMat d E D N (time s u K N 0) (H d s u K N 0 ω)
        < Step2.thr E s δ N (time s u K N 0)}

/-- **(T6′) `goodEvent_grid`** (T1519-amend-1): under step2's hypotheses, for every `D₁ > 0`,
with the grid `K = gridK D (D₁ + 1) = ⌈N^{C_K(D, D₁+1)}⌉` (chosen after `D₁`, independent of `ω`)
and `C_c = C_x = 2D + 2`, eventually in `N`, the complement of `goodEventGrid` has probability
`≤ N^{-D₁}`. The `HighProb` pieces ((T3′), T1513's good set, (T5)) are super-polynomial for the
polynomial `K`; only (T4′) (at `D₁ + 1`) sets `K`. -/
theorem goodEvent_grid {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ) {s t u : ℕ → ℝ}
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 24) (hD : 60 ≤ D)
    {τ₁ ε ζCtr τ3 τ57 : ℝ} (hτ₁ : 0 < τ₁) (hε : 0 < ε) (hζ : 0 < ζCtr) (hτ3 : 0 < τ3)
    (hτ57 : 0 < τ57) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) (goodEventGrid d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1))
        (2 * D + 2) (2 * D + 2) N)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  intro D₁ hD₁
  have hE2 : |E| < 2 := by linarith
  have hD0 : 0 ≤ D := by linarith
  set K : ℕ → ℕ := gridK D (D₁ + 1) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D (D₁ + 1)
  have hCK : 0 ≤ CK D (D₁ + 1) := by unfold CK; linarith
  have hKcard := gridK_card_le hCK
  have hregp : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := band d) hE2 hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have H3 := highProb_azuma_grid' hE2 hs0 hst ht1 hreg hδ0 hδc hD0 τ₁ ε ζCtr τ3 τ57 hsu hut K
    hK0 hKcard (2 * D + 2) (2 * D + 2)
  have HG := highProb_grid_goodSet d hκ hE hB hs0 hst ht1 hcond hc0 hregp hD hτ₁ hε hζ hτ3 hτ57
    hsu hut K hK0 (by linarith) hKcard
  have H5 := highProb_init_grid (u := u) hE2 hB hs0 hst ht1 hc0 hreg hδ0
    (by linarith : (0 : ℝ) < D) hsu K hK0
  have Hint := (H3.inter HG).inter H5
  have HY := cheb_grid_at_tau hE2 hs0 hst ht1 hc0 hreg hD0 δ τ₁ ε ζCtr τ3 τ57 hsu hut (D₁ + 1)
    (by linarith)
  filter_upwards [Hint (D₁ + 1) (by linarith), HY, eventually_ge_atTop 2] with N h1 h2 hN2
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  set G := goodEventGrid d E D δ τ₁ ε ζCtr τ3 τ57 s u K (2 * D + 2) (2 * D + 2) N with hG
  set Ybad : Set (Ωg d) := {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) E N D
            (time s u K N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω))
            (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
                (time s u K N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω) : ℂ)
                (Yvec (band d) E s u K N (j + 1) ω)) a‖} with hYbad
  set I3 := {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) E s u K N (j + 1) ω)) a‖
        < xZ d E s u K δ ε D τ₁ (2 * D + 2) (2 * D + 2) N k a} ∩
      {ω | ∀ k : Fin (K N + 1), H d s u K N k ω ∈
        goodSet d E N (time s u K N k) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D} ∩
      {ω | (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) E s u K N 0 ω b‖ ≤
        (N : ℝ) ^ (δ / 16) * Step2.tT (band d) E N D (time s u K N 0)
          (zdist (d.L N) (b 0 - b 1)))
      ∧ jSMat d E D N (time s u K N 0) (H d s u K N 0 ω)
        < Step2.thr E s δ N (time s u K N 0)} with hI3
  have hsub : Gᶜ ⊆ I3ᶜ ∪ Ybad := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hI, hYn⟩ := hcon
    apply hω
    obtain ⟨⟨hA, hGs⟩, hIn⟩ := hI
    refine ⟨⟨⟨hA, fun a => ?_⟩, hGs⟩, hIn⟩
    by_contra hlt
    exact hYn ⟨a, not_lt.1 hlt⟩
  calc (Pg d) Gᶜ ≤ (Pg d) (I3ᶜ ∪ Ybad) := measure_mono hsub
    _ ≤ (Pg d) I3ᶜ + (Pg d) Ybad := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D₁ + 1))) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        have h0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
        have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2'
        nlinarith

/-- **(T6′), the deterministic consequences on the good event** in T1518 (T1)'s hypothesis shapes
(endpoint `t := u`), **at the random target `k = τ(ω)`**: for every `D₁ > 0`, with
`K = gridK D (D₁ + 1)`, `C_c = C_x = 2D + 2` and `Mm = azumaMm`, eventually in `N`: the side
conditions of T1518 (T3) (`1 ≤ K N`, `Δ ≤ N^{-(2D+76)}`, `0 ≤ Mm ≤ N^{δ/8}`) hold, and for every
`ω` in `goodEventGrid`: `hinit` (`Mi = N^{δ/16}`), `hZ` at `k = τ ω`, `hY` at `k = τ ω`,
`J < thr` and good-set membership for `j < τ ω`, good-set membership for all `j ≤ K N`, and
`J_0 < thr(u_0)`. -/
theorem goodEvent_grid_imp {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ}
    (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    {δ D : ℝ} (hδ0 : 0 < δ) (hδc : δ ≤ c / 24) (hD : 60 ≤ D)
    {τ₁ ε : ℝ} (ζCtr τ3 τ57 : ℝ) (hτ₁δ : τ₁ ≤ δ / 32) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ)
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (1 ≤ gridK D (D₁ + 1) N ∧
        step s u (gridK D (D₁ + 1)) N ≤ (N : ℝ) ^ (-(2 * D + 76)) ∧
        0 ≤ azumaMm d E δ τ₁ N ∧ azumaMm d E δ τ₁ N ≤ (N : ℝ) ^ (δ / 8)) ∧
      ∀ ω ∈ goodEventGrid d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1))
          (2 * D + 2) (2 * D + 2) N,
        (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) E s u (gridK D (D₁ + 1)) N 0 ω b‖ ≤
          (N : ℝ) ^ (δ / 16) * Step2.tT (band d) E N D (time s u (gridK D (D₁ + 1)) N 0)
            (zdist (d.L N) (b 0 - b 1))) ∧
        (∀ b : LoopArg (d.L N) 2,
          ‖(∑ j ∈ Finset.range
                (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D (D₁ + 1)) N (j + 1) : ℂ)
                (time s u (gridK D (D₁ + 1)) N
                  (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω) : ℂ)
                (Zvec (band d) E s u (gridK D (D₁ + 1)) N (j + 1) ω)) b‖ ≤
            azumaMm d E δ τ₁ N * ((etaT E (s N) / etaT E (time s u (gridK D (D₁ + 1)) N
              (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω))) ^ 2 + 1) *
              Step2.tT (band d) E N D (time s u (gridK D (D₁ + 1)) N
                (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω))
                (zdist (d.L N) (b 0 - b 1))) ∧
        (∀ b : LoopArg (d.L N) 2,
          ‖(∑ j ∈ Finset.range
                (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D (D₁ + 1)) N (j + 1) : ℂ)
                (time s u (gridK D (D₁ + 1)) N
                  (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω) : ℂ)
                (Yvec (band d) E s u (gridK D (D₁ + 1)) N (j + 1) ω)) b‖ ≤
            Step2.tT (band d) E N D (time s u (gridK D (D₁ + 1)) N
                (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω))
                (zdist (d.L N) (b 0 - b 1))) ∧
        (∀ j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u (gridK D (D₁ + 1)) N ω,
          jSMat d E D N (time s u (gridK D (D₁ + 1)) N j)
              (H d s u (gridK D (D₁ + 1)) N j ω)
            < Step2.thr E s δ N (time s u (gridK D (D₁ + 1)) N j) ∧
          H d s u (gridK D (D₁ + 1)) N j ω ∈ goodSet d E N (time s u (gridK D (D₁ + 1)) N j)
            ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D) ∧
        (∀ j ≤ gridK D (D₁ + 1) N,
          H d s u (gridK D (D₁ + 1)) N j ω ∈ goodSet d E N (time s u (gridK D (D₁ + 1)) N j)
            ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D) ∧
        jSMat d E D N (time s u (gridK D (D₁ + 1)) N 0) (H d s u (gridK D (D₁ + 1)) N 0 ω)
          < Step2.thr E s δ N (time s u (gridK D (D₁ + 1)) N 0) := by
  intro D₁ hD₁
  have hD0 : 0 ≤ D := by linarith
  set K : ℕ → ℕ := gridK D (D₁ + 1) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D (D₁ + 1)
  have hstepCK : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-CK D (D₁ + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact step_gridK_le hN (by linarith [hs0 N, hut N, ht1 N])
  have hΔ10 : ∀ᶠ N : ℕ in atTop, step s u K N ≤ (N : ℝ) ^ (-(D + 10)) := by
    filter_upwards [hstepCK, eventually_ge_atTop 1] with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact hN.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith))
  filter_upwards [xZ_le_azumaMm hE hs0 hst ht1 hcond hc0 hreg hδ0 hδc hε0 hεδ hD hsu hut K hK0
      hΔ10 (by linarith : 2 * D ≤ 2 * D + 2) (by linarith : 2 * D ≤ 2 * D + 2),
    azumaMm_le (d := d) hE hδ0 hτ₁δ, hstepCK, eventually_ge_atTop 1]
    with N hxZ hMm hΔN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine ⟨⟨Nat.one_le_iff_ne_zero.2 (hK0 N),
    hΔN.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by unfold CK; linarith)),
    azumaMm_nonneg E δ τ₁ N, hMm⟩, ?_⟩
  intro ω hω
  obtain ⟨⟨⟨hA, hY⟩, hG⟩, hI⟩ := hω
  set τω := gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω with hτω
  have hτK : τω ≤ K N := gridTau_le E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω
  refine ⟨hI.1, fun b => ?_, fun b => (hY b).le, fun j hj => lt_gridTau_imp hj,
    fun j hj => hG ⟨j, by omega⟩, hI.2⟩
  have h1 := hA τω hτK b
  rw [min_self] at h1
  exact h1.le.trans (hxZ τω hτK b)

/-- **Joint satisfiability of the hypotheses of (T3′), (T4′), (T6′)** (other than `BoundsCore`,
which is step2's own hypothesis, the output of Step 1): from T1508's compiled witness
`qv_time_sum_le_hyps_witness` (`E = 0`, `s = 0`, `t N = 1 − (N+1)^{-1/200}` so that
`η_s/η_t = (N+1)^{1/200} → ∞`, `Cond272`, step2's gained (2.72) with `c = 1/4`, `δ = 1/96`,
`D = 60`), with `κ = (2 − |E|)/2`, `ε = δ/2`, `τ₁ = δ/32`, `ζCtr = τ3 = τ57 = 1` and endpoint
`u := t` (a genuine window `s N < u N` for `N ≥ 1`). -/
theorem goodEvent_grid_params_witness :
    ∃ (κ E : ℝ) (s t u : ℕ → ℝ) (c δ D τ₁ ε ζCtr τ3 τ57 : ℝ),
      0 < κ ∧ |E| ≤ 2 - κ ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272 (band d) E s t ∧ 0 < c ∧
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
        (band d).scale E N (t N)) ∧
      (∀ N : ℕ, etaT E (s N) / etaT E (t N) = ((N : ℝ) + 1) ^ (1 / 200 : ℝ)) ∧
      0 < δ ∧ δ ≤ c / 24 ∧ 60 ≤ D ∧ 0 < τ₁ ∧ τ₁ ≤ δ / 32 ∧ 0 < ε ∧ 2 * ε ≤ δ ∧
      0 < ζCtr ∧ 0 < τ3 ∧ 0 < τ57 ∧ (∀ N, s N ≤ u N) ∧ (∀ N, u N ≤ t N) ∧
      (∀ N : ℕ, 1 ≤ N → s N < u N) := by
  obtain ⟨E, s, t, c, δ, _ε, D, hE, hs0, hst, ht1, hlt, hR, hcond, hc0, hreg, hδ0, hδc, _, _,
    hD⟩ := qv_time_sum_le_hyps_witness (band d)
  refine ⟨(2 - |E|) / 2, E, s, t, t, c, δ, D, δ / 32, δ / 2, 1, 1, 1, by linarith, by linarith,
    hs0, hst, ht1, hcond, hc0, hreg, hR, hδ0, hδc, hD, by positivity, le_rfl, by positivity,
    by linarith, one_pos, one_pos, one_pos, hst, fun _ => le_rfl, hlt⟩

end Amend

end RBM.Gauss.Grid

end

#print axioms RBM.Gauss.Grid.gridTau
#print axioms RBM.Gauss.Grid.isStoppingTime_gridTau
#print axioms RBM.Gauss.Grid.lt_gridTau_measurableSet
#print axioms RBM.Gauss.Grid.lt_gridTau_imp
#print axioms RBM.Gauss.Grid.gridTau_le
#print axioms RBM.Gauss.Grid.not_highProb_azuma_grid_literal
#print axioms RBM.Gauss.Grid.not_highProb_azuma_grid_literal'
#print axioms RBM.Gauss.Grid.initSet
#print axioms RBM.Gauss.Grid.measurableSet_initSet
#print axioms RBM.Gauss.Grid.jSMat_le_of_mem_initSet
#print axioms RBM.Gauss.Grid.highProb_init_grid
#print axioms RBM.Gauss.Grid.thr_le_sqrtN
#print axioms RBM.Gauss.Grid.time_succ_eq
#print axioms RBM.Gauss.Grid.ukerMat_eq_prod_re
#print axioms RBM.Gauss.Grid.quadVar_Φgrid_eq
#print axioms RBM.Gauss.Grid.jGMat_nonneg
#print axioms RBM.Gauss.Grid.time_mono_of_le
#print axioms RBM.Gauss.Grid.Qprime
#print axioms RBM.Gauss.Grid.cZ
#print axioms RBM.Gauss.Grid.cZ_nonneg
#print axioms RBM.Gauss.Grid.floor_le_cZ
#print axioms RBM.Gauss.Grid.hsubG_gridTau
#print axioms RBM.Gauss.Grid.hsubG_gridTau_hyps_witness
#print axioms RBM.Gauss.Grid.measurable_coord_filt
#print axioms RBM.Gauss.Grid.measurable_lin
#print axioms RBM.Gauss.Grid.measurable_stepZ_filt
#print axioms RBM.Gauss.Grid.measurable_stepY_filt
#print axioms RBM.Gauss.Grid.ZvecCut
#print axioms RBM.Gauss.Grid.ZvecCut_succ
#print axioms RBM.Gauss.Grid.time_lt_one_of_le
#print axioms RBM.Gauss.Grid.stronglyMeasurable_ZvecCut
#print axioms RBM.Gauss.Grid.xZ
#print axioms RBM.Gauss.Grid.xZ_pos
#print axioms RBM.Gauss.Grid.xZ_sq
#print axioms RBM.Gauss.Grid.eventually_mul_exp_neg_rpow_le
#print axioms RBM.Gauss.Grid.card_loopArg_two
#print axioms RBM.Gauss.Grid.Zvec_succ_eq_zero_of_step
#print axioms RBM.Gauss.Grid.Uker_apply_eq_zero_of
#print axioms RBM.Gauss.Grid.highProb_azuma_grid'
#print axioms RBM.Gauss.Grid.card_idx_le
#print axioms RBM.Gauss.Grid.qvTimeShiftConst_le
#print axioms RBM.Gauss.Grid.azumaMm
#print axioms RBM.Gauss.Grid.azumaMm_nonneg
#print axioms RBM.Gauss.Grid.azumaMm_le
#print axioms RBM.Gauss.Grid.sum_le_affine_sum
#print axioms RBM.Gauss.Grid.sqrt_floor_arith
#print axioms RBM.Gauss.Grid.two_Csh_sq_step_sq_le
#print axioms RBM.Gauss.Grid.xZ_le_azumaMm
#print axioms RBM.Gauss.Grid.integrable_stepZ'
#print axioms RBM.Gauss.Grid.integrable_stepY'
#print axioms RBM.Gauss.Grid.memLp_stepY'
#print axioms RBM.Gauss.Grid.condExp_indicator_stepY_re
#print axioms RBM.Gauss.Grid.condExp_indicator_stepY_im
#print axioms RBM.Gauss.Grid.integral_sq_indicator_stepY_le
#print axioms RBM.Gauss.Grid.integral_norm_Xmat_incr_four_le
#print axioms RBM.Gauss.Grid.sum_abs_ukerMat_le
#print axioms RBM.Gauss.Grid.YvecCut
#print axioms RBM.Gauss.Grid.YvecCut_succ
#print axioms RBM.Gauss.Grid.stronglyMeasurable_YvecCut
#print axioms RBM.Gauss.Grid.CK
#print axioms RBM.Gauss.Grid.gridK
#print axioms RBM.Gauss.Grid.gridK_ne_zero
#print axioms RBM.Gauss.Grid.rpow_CK_le_gridK
#print axioms RBM.Gauss.Grid.step_gridK_le
#print axioms RBM.Gauss.Grid.gridK_card_le
#print axioms RBM.Gauss.Grid.cheb_e_le
#print axioms RBM.Gauss.Grid.cheb_grid_at_tau
#print axioms RBM.Gauss.Grid.goodEventGrid
#print axioms RBM.Gauss.Grid.goodEvent_grid
#print axioms RBM.Gauss.Grid.goodEvent_grid_imp
#print axioms RBM.Gauss.Grid.goodEvent_grid_params_witness
