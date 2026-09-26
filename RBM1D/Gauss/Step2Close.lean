/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridBootstrap
import RBM1D.Gauss.GridGoodEvent
import RBM1D.Gauss.GridDriftPoint
import RBM1D.Gauss.GridStepBound
import RBM1D.Gauss.Steps12Gauss
import RBM1D.Gauss.Step2Eq557

/-!
# T1524 — Step 2 closes: `GridPointwise'` and `step2_gauss` without `Hy` (R4c-2b)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3 (Step 2 of Theorem 2.21,
(2.75)–(2.76)) for the Gaussian model, along the discrete grid.

The final glue of T1518 (grid step bound and threshold improvement), T1519 (grid stopping time
and good event, amend-1), T1515 (drift bound on the good set, amend-1), T1516 (grid expansion)
and T1520 (bootstrap core and `jSMat → lkErrMat` conversion).

## Main results

* `RBM.Gauss.Grid.gridPointwise'_gauss` — (T1): `GridPointwise' d E s t` under step2's Gaussian
  hypotheses (no `Hy`, no `Step1.Hyp`).
* `RBM.Gauss.step2_gauss` — (T2): `Step2.step2`'s full conclusion for `sample d` with no `Hy`.
* `RBM.Gauss.steps12_gauss` — (T3): `Steps12 (sample d) E s t` with no `Hy`.
* (T4): an `example` checking that `step2_gauss`'s conclusion is syntactically `Step2.step2`'s
  for `sample d`, from step2's hypothesis list minus `Hy`.

## Interface bridges (see `docs/reports/T1524-prove.md`)

* `hreg_endpoint`: T1518's `grid_thr_improve` uses one sequence as both grid endpoint and the
  time of `hreg`; `hreg` at `t` implies `hreg` at any endpoint `u ∈ [s, t]`.
* `H_eq_H_zero_of_eq`, `time_eq_time_zero_of_eq`: the degenerate grid `u N = s N` (T1516's
  expansion needs `s N < u N`).
* `rowSet`, `highProb_grid_rowSet`: the row form of (5.57) (`h557R` of T1515), absent from
  T1513's `goodSet`, from T1492's `highProb_eq557_colRow`.
* `drift_of_goodSet`: T1515 (T5)'s inputs from `goodSet ∩ rowSet` with `τ3 = ζCtr = ζ`,
  `τ57 = ζ/2`, and its coefficient rewritten as T1518's `driftCoef` (`heG_coef_eq_driftCoef`).
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### Bridge 1: `hreg` at the grid endpoint -/

/-- **`hreg` at an endpoint `u ∈ [s, t]`.** `R_u ≤ R_t` and `A_t ≤ A_u` give
`N^c R_u^{30} ≤ N^c R_t^{30} ≤ A_t ≤ A_u`. -/
theorem hreg_endpoint {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (u : ∀ N, TimeIcc s t N) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (u N : ℝ)) ^ 30 ≤
      (band d).scale E N (u N : ℝ) := by
  filter_upwards [hreg] with N hN
  have hsu : s N ≤ (u N : ℝ) := (u N).2.1
  have hut : (u N : ℝ) ≤ t N := (u N).2.2
  have hu1 : (u N : ℝ) < 1 := hut.trans_lt (ht1 N)
  have ha : 0 < 1 - (u N : ℝ) := by linarith
  have ht0 : 0 < 1 - t N := by linarith [ht1 N]
  have hc0 : 0 < 1 - s N := by linarith
  have hRu : etaT E (s N) / etaT E (u N : ℝ) = (1 - s N) / (1 - (u N : ℝ)) :=
    Step2.etaT_ratio hE _ _
  have hRt : etaT E (s N) / etaT E (t N) = (1 - s N) / (1 - t N) := Step2.etaT_ratio hE _ _
  have hRut : (1 - s N) / (1 - (u N : ℝ)) ≤ (1 - s N) / (1 - t N) :=
    div_le_div_of_nonneg_left hc0.le ht0 (by linarith)
  have hRu0 : 0 ≤ (1 - s N) / (1 - (u N : ℝ)) := div_nonneg hc0.le ha.le
  have hscale : (band d).scale E N (t N) ≤ (band d).scale E N (u N : ℝ) :=
    flowScale_antitoneOn (Nat.cast_nonneg _) _ E (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) hut
  rw [hRu]
  rw [hRt] at hN
  have hNc : 0 ≤ (N : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc (N : ℝ) ^ c * ((1 - s N) / (1 - (u N : ℝ))) ^ 30
      ≤ (N : ℝ) ^ c * ((1 - s N) / (1 - t N)) ^ 30 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRu0 hRut 30) hNc
    _ ≤ (band d).scale E N (t N) := hN
    _ ≤ (band d).scale E N (u N : ℝ) := hscale

/-! ### Bridge 2: the degenerate grid `u N = s N` -/

theorem time_eq_time_zero_of_eq {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (h : s N = u N) (k : ℕ) :
    time s u K N k = time s u K N 0 := by
  simp [time, step, h]

theorem H_eq_H_zero_of_eq {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (h : s N = u N) (k : ℕ)
    (ω : Ωg d) : H d s u K N k ω = H d s u K N 0 ω := by
  simp [H, step, h]

/-! ### Bridge 3: the row form of (5.57) on the grid -/

/-- The matrix-set form of `(5.57)`, **row** orientation, at the (2.73)-reduced strength of T1492
(the row half of `Gauss.Step2.highProb_eq557_colRow`; T1513's `eq557Set` is the column half). -/
def rowSet (E : ℝ) (N : ℕ) (v ℓs τ : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ x y : ZMod (d.L N), ∀ r : ZMod (d.L N) × Fin (d.W N), r.1 = x →
    ∑ p, RBM.Lemma57.blkW (d.L N) (d.W N) p y * ‖green M (zt E v) r p‖ ≤
      (N : ℝ) ^ τ * Real.sqrt ((band d).ell N v / ℓs) * (Real.sqrt ((band d).scale E N v))⁻¹}

theorem measurableSet_rowSet (E : ℝ) (N : ℕ) (v ℓs τ : ℝ) :
    MeasurableSet (rowSet d E N v ℓs τ) := by
  have heq : rowSet d E N v ℓs τ =
      ⋂ x : ZMod (d.L N), ⋂ y : ZMod (d.L N), ⋂ r : ZMod (d.L N) × Fin (d.W N),
        {M | r.1 = x → ∑ p, RBM.Lemma57.blkW (d.L N) (d.W N) p y * ‖green M (zt E v) r p‖ ≤
          (N : ℝ) ^ τ * Real.sqrt ((band d).ell N v / ℓs) *
            (Real.sqrt ((band d).scale E N v))⁻¹} := by
    unfold rowSet; ext M; simp
  rw [heq]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    MeasurableSet.iInter fun r => ?_
  by_cases hr : r.1 = x
  · have hm : MeasurableSet {M : Matrix (d.Idx N) (d.Idx N) ℂ |
        ∑ p, RBM.Lemma57.blkW (d.L N) (d.W N) p y * ‖green M (zt E v) r p‖ ≤
          (N : ℝ) ^ τ * Real.sqrt ((band d).ell N v / ℓs) *
            (Real.sqrt ((band d).scale E N v))⁻¹} :=
      measurableSet_le (Finset.measurable_sum _ fun p _ =>
        measurable_const.mul (measurable_green_matrix d N (zt E v) r p).norm) measurable_const
    convert hm using 2
    simp [hr]
  · convert MeasurableSet.univ using 2
    simp [hr]

/-- **The grid `HighProb` of the row form of (5.57)**, uniformly over grid indices `k ≤ K N`, for
a grid endpoint `u ∈ [s, t]` and polynomially many grid points. -/
theorem highProb_grid_rowSet {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N)) (τ : ℝ) (hτ : 0 < τ)
    {u : ℕ → ℝ} (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s u K N k ω ∈ rowSet d E N (time s u K N k) ((band d).ell N (s N)) τ}) := by
  have hflow : HighProb (P d) (fun N => {ω | ∀ v : TimeIcc s t N,
      Hflow d N (v : ℝ) ω ∈ rowSet d E N (v : ℝ) ((band d).ell N (s N)) τ}) := by
    have h := Gauss.Step2.highProb_eq557_colRow d hκ hE hB hs0 hst ht1 hcond hc0 hreg τ hτ
    refine h.mono (Filter.Eventually.of_forall fun N ω hω => ?_)
    intro v x y r hr
    exact (hω v x y).2 r hr
  have hflow' := highProb_flow_restrict d hut
    (fun N v => rowSet d E N v ((band d).ell N (s N)) τ) hflow
  exact highProb_grid_of_flow d s u K hs0 hsu hK0 hC0 hKcard
    (fun N v => rowSet d E N v ((band d).ell N (s N)) τ)
    (fun N v => measurableSet_rowSet d E N v ((band d).ell N (s N)) τ) hflow'

/-! ### Bridge 4: T1515 (T5) from `goodSet ∩ rowSet`, in T1518's `driftCoef` shape -/

/-- T1515 (T5)'s coefficient is T1518's `driftCoef` at `Mg = mgDrift` (associativity only). -/
theorem heG_coef_eq_driftCoef (E : ℝ) (s : ℕ → ℝ) (δ D ζ : ℝ) (N : ℕ) (v : ℝ) :
    Real.exp 1 * Step2.thr E s δ N v ^ 2 *
        (36 * ((etaT E v)⁻¹ * ((band d).scale E N v)⁻¹)
          + ((band d).W N : ℝ) * ((band d).L N : ℝ) * ((band d).W N : ℝ) ^ (-D))
      + mgDrift (band d) ζ N * (etaT E v)⁻¹ *
        (((4 * (N : ℝ) ^ ζ * ((band d).ell N v / (band d).ell N (s N))) ^ 3 + 1)
          + ((band d).scale E N v)⁻¹ ^ ((1 : ℝ) / 3) * Step2.thr E s δ N v ^ 3)
    = driftCoef (band d) E s δ D ζ (mgDrift (band d) ζ N) N v := by
  unfold driftCoef qGrid
  ring

theorem mgDrift_nonneg (ζ : ℝ) (N : ℕ) : 0 ≤ mgDrift (band d) ζ N := by
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
  unfold mgDrift
  have h1 := Lemma57.cNear_nonneg hW1 (one_pos : (0 : ℝ) < 1)
  have h2 := Lemma57.cFar_nonneg hW1 (one_pos : (0 : ℝ) < 1)
  positivity

/-- **The drift bound at a grid index from the good set.** T1515 (T5) `drift_point_le_heG` at
`M := H_j ω`, `u := u_j`, with its per-matrix inputs read off `goodSet` (`τ3 = ζCtr = ζ`,
`τ57 = ζ/2`) and `rowSet` (at `ζ/2`), `hjG` from `jgSet` and `jSMat ≤ thr`, and its
coefficient rewritten as `driftCoef` (`heG_coef_eq_driftCoef`). -/
theorem drift_of_goodSet {E : ℝ} (hE : |E| < 2) {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} {δ ε ζ D τ₁ : ℝ}
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsv : s N ≤ time s u K N j)
    (hv1 : time s u K N j < 1)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ) (hD : 8 + 2 * ζ ≤ D)
    (hW8 : 8 ≤ ((band d).W N : ℝ)) (hLW : ((band d).L N : ℝ) ≤ (band d).W N)
    (hNW : (N : ℝ) ≤ ((band d).W N : ℝ) ^ 2) (hlog : 2 * D ^ 2 ≤ Real.log ((band d).W N : ℝ))
    (hJA : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s u K N j) ≤
      (band d).scale E N (time s u K N j))
    (hDreg : ((band d).L N : ℝ) * √(((band d).W N : ℝ) ^ (-D)) ≤
      (band d).ell N (time s u K N j) * ((band d).scale E N (time s u K N j))⁻¹)
    (hG : H d s u K N j ω ∈
      goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζ ζ (ζ / 2) D)
    (hR : H d s u K N j ω ∈ rowSet d E N (time s u K N j) ((band d).ell N (s N)) (ζ / 2))
    (hjS : jSMat d E D N (time s u K N j) (H d s u K N j ω) ≤
      Step2.thr E s δ N (time s u K N j)) :
    ∀ b : LoopArg ((band d).L N) 2, ‖Dgrid (band d) E s u K N j ω b‖ ≤
      driftCoef (band d) E s δ D ζ (mgDrift (band d) ζ N) N (time s u K N j) *
        Step2.tT (band d) E N D (time s u K N j) (zdist ((band d).L N) (b 0 - b 1)) := by
  intro b
  set v := time s u K N j with hv
  set M := H d s u K N j ω with hMdef
  have hM : M.IsHermitian := H_isHermitian d s u K N j ω
  obtain ⟨⟨⟨⟨⟨_hqv, hjg⟩, _h554⟩, hone⟩, h273⟩, h557⟩ := hG
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hℓs1 : 1 ≤ (band d).ell N (s N) := one_le_ellHat_of_nonneg ((band d).one_le_L N) hs0 hs1
  have hℓs0 : 0 < (band d).ell N (s N) := by linarith
  have hℓv1 : 1 ≤ (band d).ell N v := one_le_ellHat_of_nonneg ((band d).one_le_L N) hv0 hv1
  have hA0 : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN1 hζ0
  set g := 4 * (N : ℝ) ^ ζ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have e : (band d).ell N v / ((band d).ell N (s N) / g)
      = g * ((band d).ell N v / (band d).ell N (s N)) := by
    field_simp
  have hrat0 : 0 ≤ (band d).ell N v / (band d).ell N (s N) := by positivity
  -- `h273`
  have h273' : ∀ x y c : ZMod ((band d).L N),
      ‖gloop ((band d).L N) ((band d).W N) M (zt E v) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ ((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹ := by
    intro x y c
    have h := h273 ((![false, true, true], ![y, c, x]) : LoopData (d.L N) 3)
    have hidx : LoopData.idx ((![false, true, true], ![y, c, x]) : LoopData (d.L N) 3)
        = ⟨[false, true, true], [y, c, x]⟩ := by
      simp [LoopData.idx, List.ofFn_succ]
    rw [hidx] at h
    refine h.trans ?_
    rw [← hg, e, mul_pow, inv_pow]
    have hNg : (N : ℝ) ^ ζ ≤ g ^ 2 := by rw [hg]; nlinarith
    have h0 : 0 ≤ ((band d).ell N v / (band d).ell N (s N)) ^ 2 * (((band d).scale E N v) ^ 2)⁻¹ :=
      by positivity
    calc (N : ℝ) ^ ζ * ((band d).ell N v / (band d).ell N (s N)) ^ (3 - 1) *
          (((band d).scale E N v) ^ (3 - 1))⁻¹
        = (N : ℝ) ^ ζ * (((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹) := by norm_num; ring
      _ ≤ g ^ 2 * (((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹) := mul_le_mul_of_nonneg_right hNg h0
      _ = g ^ 2 * ((band d).ell N v / (band d).ell N (s N)) ^ 2 *
          (((band d).scale E N v) ^ 2)⁻¹ := by ring
  -- `N^{ζ/2} √(ℓ_v/ℓ_s) ≤ √(ℓ_v/ℓ_s')`
  have hsq : (N : ℝ) ^ (ζ / 2) ≤ Real.sqrt g := by
    have e2 : (N : ℝ) ^ (ζ / 2) = Real.sqrt ((N : ℝ) ^ ζ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
    rw [e2]
    exact Real.sqrt_le_sqrt (by rw [hg]; linarith)
  have hkey : (N : ℝ) ^ (ζ / 2) * Real.sqrt ((band d).ell N v / (band d).ell N (s N)) ≤
      Real.sqrt ((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) := by
    rw [← hg, e, Real.sqrt_mul hg0.le]
    exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
  have hisq0 : 0 ≤ (Real.sqrt ((band d).scale E N v))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have h557C : ∀ (x y : ZMod ((band d).L N)) (p : (band d).Idx N), p.1 = y →
      ∑ r : (band d).Idx N, Lemma57.blkW ((band d).L N) ((band d).W N) r x *
          ‖green M (zt E v) r p‖ ≤
        √((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) *
          (√((band d).scale E N v))⁻¹ := by
    intro x y p hp
    exact (h557 x y p hp).trans (mul_le_mul_of_nonneg_right hkey hisq0)
  have h557R : ∀ (x y : ZMod ((band d).L N)) (r : (band d).Idx N), r.1 = x →
      ∑ p : (band d).Idx N, Lemma57.blkW ((band d).L N) ((band d).W N) p y *
          ‖green M (zt E v) r p‖ ≤
        √((band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ))) *
          (√((band d).scale E N v))⁻¹ := by
    intro x y r hr
    exact (hR x y r hr).trans (mul_le_mul_of_nonneg_right hkey hisq0)
  -- `hone`, `hκ`
  have hone' : ∀ (σ : Bool) (b' : ZMod (d.L N)), ‖Matrix.trace ((Gsig M (zt E v) σ
        - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b')‖
      ≤ ((N : ℝ) ^ ζ * (2 * ((band d).ell N v / (band d).ell N (s N)))) *
        ((band d).scale E N v)⁻¹ := by
    intro σ b'
    exact (hone σ b').trans (le_of_eq (by ring))
  have hκ : 2 * ((N : ℝ) ^ ζ * (2 * ((band d).ell N v / (band d).ell N (s N)))) ≤
      (band d).ell N v / ((band d).ell N (s N) / (4 * (N : ℝ) ^ ζ)) := by
    rw [← hg, e, hg]; apply le_of_eq; ring
  -- `hjG`
  have hjG : jGMat (band d).toDims E N v ((band d).ell N v) (etaT E v) D M
      ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N v :=
    hjg.trans (mul_le_mul_of_nonneg_left hjS (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  have hmain := drift_point_le_heG (B := band d) hE hM hN1 hs0 hsv hv1 hδ0 hε0 hεδ hζ0 hD hW8
    hLW hNW hlog hJA hDreg h273' h557C h557R hone' hκ hjS hjG b
  rw [heG_coef_eq_driftCoef] at hmain
  exact hmain

/-! ### The a.e. data of T1516 at the grid endpoint -/

/-- The T1516 expansion identity (all `k ≤ K N`) and T1506's remainder bound (all `j < K N`),
at one `ω`: the inputs `hexp` and `hRstep` of T1518 (T3). -/
def GridAE (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) : Prop :=
  (∀ k : ℕ, k ≤ K N → ∀ b : LoopArg ((band d).L N) 2,
      Agrid (band d) E s u K N k ω b
        = Uker ((band d).L N) (fun _ => (1 : ℂ)) (time s u K N 0 : ℂ) (time s u K N k : ℂ)
              (Agrid (band d) E s u K N 0 ω) b
          + (∑ j ∈ Finset.range k, Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Zvec (band d) E s u K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Yvec (band d) E s u K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, step s u K N • Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Dgrid (band d) E s u K N j ω)) b
          + (∑ j ∈ Finset.range k, Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Rgrid (band d) E s u K N j ω)) b) ∧
  (∀ j < K N, ∀ b : LoopArg ((band d).L N) 2, ‖Rgrid (band d) E s u K N j ω b‖ ≤
      stepErr (band d) E N (time s u K N j) (time s u K N (j + 1)) (step s u K N))

/-- `GridAE` holds a.e. on a nondegenerate grid (`s N < u N < 1`): T1516 `grid_expansion_all'`
and `condExp_A_succ` (countably many `j`). -/
theorem ae_gridAE {E : ℝ} (hE : |E| < 2) {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N)
    (hsu : s N < u N) (hu1 : u N < 1) (hK0 : K N ≠ 0) :
    ∀ᵐ ω ∂(Pg d), GridAE d E s u K N ω := by
  have hK1 : 1 ≤ K N := Nat.one_le_iff_ne_zero.2 hK0
  have h1 := grid_expansion_all' (band d) s u K N E hE hs0 hsu hu1 hK1
  have h2 : ∀ᵐ ω ∂(Pg d), ∀ j : ℕ, j < K N → ∀ b : LoopArg ((band d).L N) 2,
      ‖Rgrid (band d) E s u K N j ω b‖ ≤
        stepErr (band d) E N (time s u K N j) (time s u K N (j + 1)) (step s u K N) := by
    refine ae_all_iff.mpr fun j => ?_
    by_cases hj : j < K N
    · have hu0 : 0 ≤ time s u K N j := hs0.trans (s_le_time s u K N hsu.le j)
      have hu1' : time s u K N (j + 1) < 1 :=
        (time_le_t s u K N hsu.le hK1 (by omega)).trans_lt hu1
      filter_upwards [condExp_A_succ (band d) s u K N j E hE hsu hj hu0 hu1'] with ω hω _ b
      exact (hω b).2
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [h1, h2] with ω h1ω h2ω
  exact ⟨h1ω, h2ω⟩

/-! ### (T1): `GridPointwise'` for the Gaussian model -/

/-- **(T1) `gridPointwise'_gauss`.** Under step2's Gaussian hypotheses (no `Hy`, no
`Step1.Hyp`), `GridPointwise' d E s t` holds.

Parameters, for given `D > 0`, `u`: `D' = max(D+4, 64)`, `δ₀ = min(c/24, 1)`; for
`δ ∈ (0, δ₀]` and `D₁ > 0`: `ζ = ζCtr = τ3 = δ/96`, `τ57 = ζ/2`, `ε = δ/4`, `τ₁ = δ/32`,
`K = gridK D' (D₁ + 2)` (depends only on `D, D₁`). On the good event
(T1519 (T6′) at `D₁ + 1`) ∩ (row form of (5.57)) ∩ (T1516 a.e. set), at `k = gridTau ω`,
T1518 (T3) gives `J_τ < thr(u_τ)` (T1519 (T5) on a degenerate grid `u N = s N`); T1520's
`min_firstHit_eq_of_at` gives `τ = K`, so `J_K < thr(u N)`; T1520's `lk_le_of_jS` converts. -/
theorem gridPointwise'_gauss {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    GridPointwise' d E s t := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 (band d) E s t := Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := band d) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  intro D hD u
  set D' : ℝ := max (D + 4) 64 with hD'def
  have hD'64 : (64 : ℝ) ≤ D' := le_max_right _ _
  have hDD : D + 4 ≤ D' := le_max_left _ _
  refine ⟨min (c / 24) 1, lt_min (by positivity) one_pos, fun δ hδ0 hδδ₀ D₁ hD₁ => ?_⟩
  have hδc : δ ≤ c / 24 := hδδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδδ₀.trans (min_le_right _ _)
  set ζ : ℝ := δ / 96 with hζdef
  set ε : ℝ := δ / 4 with hεdef
  set τ₁ : ℝ := δ / 32 with hτ₁def
  have hζ0 : 0 < ζ := by positivity
  have hε0 : 0 < ε := by positivity
  have hτ₁0 : 0 < τ₁ := by positivity
  have hεδ : 2 * ε ≤ δ := by rw [hεdef]; linarith
  have hDζ : 8 + 2 * ζ ≤ D' := by rw [hζdef]; linarith
  set uR : ℕ → ℝ := fun N => (u N : ℝ) with huRdef
  have hsu : ∀ N, s N ≤ uR N := fun N => (u N).2.1
  have hut : ∀ N, uR N ≤ t N := fun N => (u N).2.2
  have hu1 : ∀ N, uR N < 1 := fun N => (hut N).trans_lt (ht1 N)
  set K : ℕ → ℕ := gridK D' (D₁ + 1 + 1) with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D' (D₁ + 1 + 1)
  have hCK : 0 ≤ CK D' (D₁ + 1 + 1) := by unfold CK; linarith
  refine ⟨K, hK0, ⟨CK D' (D₁ + 1 + 1) + 2, by linarith, gridK_card_le hCK⟩, ?_⟩
  -- the probabilistic inputs, and the deterministic premises, eventually in `N`
  have hGood := goodEvent_grid (d := d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg hδ0 hδc
    (by linarith : (60 : ℝ) ≤ D') hτ₁0 hε0 hζ0 hζ0 (by positivity : (0 : ℝ) < ζ / 2) hsu hut
    (D₁ + 1) (by linarith)
  have hImp := goodEvent_grid_imp (d := d) hE hs0 hst ht1 hcond hc0 hreg hδ0 hδc
    (by linarith : (60 : ℝ) ≤ D') ζ ζ (ζ / 2) (le_of_eq hτ₁def) hε0.le hεδ hsu hut (D₁ + 1)
    (by linarith)
  have hRow := highProb_grid_rowSet d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' (ζ / 2)
    (by positivity) hsu hut K hK0 (by linarith : (0 : ℝ) ≤ CK D' (D₁ + 1 + 1) + 2)
    (gridK_card_le hCK)
  have hThr := grid_thr_improve (band d) (K := K) hE hs0 hsu hu1 hc0
    (hreg_endpoint d hE ht1 hreg u) hδ0 hδ1 (by linarith : 24 * δ ≤ c) hD'64 hζ0.le
  have hMgN : ∀ᶠ N : ℕ in atTop,
      65 * (N : ℝ) ^ (3 * ζ) * mgDrift (band d) ζ N ≤ (N : ℝ) ^ (δ / 8) := by
    filter_upwards [mgDrift_le (band d) (κ := δ / 32) (ζ := ζ) (by positivity) hζ0.le,
      eventually_le_rpow 178880 (by positivity : (0 : ℝ) < δ / 32), eventually_ge_atTop 1]
      with N hM hC hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have e1 : (N : ℝ) ^ (3 * ζ) * (N : ℝ) ^ (δ / 32 + 3 * ζ) = (N : ℝ) ^ (3 * δ / 32) := by
      rw [← Real.rpow_add hN0]; congr 1; rw [hζdef]; ring
    have e2 : (N : ℝ) ^ (δ / 8) = (N : ℝ) ^ (3 * δ / 32) * (N : ℝ) ^ (δ / 32) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h3 : 0 ≤ 65 * (N : ℝ) ^ (3 * ζ) := by positivity
    have h4 : 0 ≤ (N : ℝ) ^ (3 * δ / 32) := Real.rpow_nonneg hN0.le _
    calc 65 * (N : ℝ) ^ (3 * ζ) * mgDrift (band d) ζ N
        ≤ 65 * (N : ℝ) ^ (3 * ζ) * (2752 * (N : ℝ) ^ (δ / 32 + 3 * ζ)) :=
          mul_le_mul_of_nonneg_left hM h3
      _ = 178880 * (N : ℝ) ^ (3 * δ / 32) := by rw [← e1]; ring
      _ ≤ (N : ℝ) ^ (δ / 32) * (N : ℝ) ^ (3 * δ / 32) := mul_le_mul_of_nonneg_right hC h4
      _ = (N : ℝ) ^ (δ / 8) := by rw [e2]; ring
  have hScal := drift_point_le_heG_scalars (band d) hE hs0 ht1 hreg hδ0.le hδc hεδ
    (by linarith : (4 : ℝ) ≤ D')
  have hcr := SumZeroDyn.flow_crude hE hs0 hst ht1 hcond
  have hW2 := Step2.eventually_le_W_sq (band d)
  have hae : ∀ N, ∀ᵐ ω ∂(Pg d), s N < uR N → GridAE d E s uR K N ω := by
    intro N
    by_cases hlt : s N < uR N
    · filter_upwards [ae_gridAE d hE (hs0 N) hlt (hu1 N) (hK0 N)] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hlt
  filter_upwards [hGood, hImp, hRow (D₁ + 1) (by linarith), hThr, hScal, hMgN, hcr, hW2,
    eventually_ge_atTop 2] with N hGN hImpN hRowN hThrN hScalN hMgN' hcrN hW2N hN2
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1' : (1 : ℝ) ≤ N := by linarith
  obtain ⟨⟨hK1, hΔR, _hMm0, hMmle⟩, hImpω⟩ := hImpN
  obtain ⟨_, hW8, hLW, hNW, hlog, hv⟩ := hScalN
  set Gd : Set (Ωg d) :=
    goodEventGrid d E D' δ τ₁ ε ζ ζ (ζ / 2) s uR K (2 * D' + 2) (2 * D' + 2) N with hGd
  set Rw : Set (Ωg d) := {ω | ∀ k : Fin (K N + 1), H d s uR K N k ω ∈
    rowSet d E N (time s uR K N k) ((band d).ell N (s N)) (ζ / 2)} with hRw
  set Ae : Set (Ωg d) := {ω | ¬ (s N < uR N → GridAE d E s uR K N ω)} with hAe
  have hAe0 : Pg d Ae = 0 := ae_iff.1 (hae N)
  -- the pointwise core: on the good event, `J_K < thr(u N)`
  have hcore : ∀ ω, ω ∈ Gd → ω ∈ Rw → (s N < uR N → GridAE d E s uR K N ω) →
      jSMat d E D' N (uR N) (H d s uR K N (K N) ω) < Step2.thr E s δ N (uR N) := by
    intro ω hGω hRω hAω
    obtain ⟨hinit, hZ, hY, hbefore, hgoodAll, hJ0⟩ := hImpω ω hGω
    set τω := gridTau d E D' δ τ₁ ε ζ ζ (ζ / 2) s uR K N ω with hτω
    have hτK : τω ≤ K N := gridTau_le E D' δ τ₁ ε ζ ζ (ζ / 2) s uR K N ω
    have hat : jSMat d E D' N (time s uR K N τω) (H d s uR K N τω ω)
        < Step2.thr E s δ N (time s uR K N τω) := by
      rcases lt_or_eq_of_le (hsu N) with hlt' | heq
      · obtain ⟨hexp, hRst⟩ := hAω hlt'
        have hdrift : ∀ j < τω, ∀ b : LoopArg ((band d).L N) 2,
            ‖Dgrid (band d) E s uR K N j ω b‖ ≤
              driftCoef (band d) E s δ D' ζ (mgDrift (band d) ζ N) N (time s uR K N j) *
                Step2.tT (band d) E N D' (time s uR K N j) (zdist ((band d).L N) (b 0 - b 1)) := by
          intro j hj
          obtain ⟨hjS, hjG⟩ := hbefore j hj
          have hjK : j ≤ K N := (le_of_lt hj).trans hτK
          have hmem := mem_Icc_time s uR K N j (hs0 N) (hsu N) hjK
          obtain ⟨hJA, hDreg⟩ := hv (time s uR K N j) hmem.1 (hmem.2.trans (hut N))
          exact drift_of_goodSet d hE hN1' (hs0 N) hmem.1 (hmem.2.trans_lt (hu1 N)) hδ0.le
            hε0.le hεδ hζ0.le hDζ hW8 hLW hNW hlog hJA hDreg hjG
            (hRω ⟨j, Nat.lt_succ_of_le hjK⟩) hjS.le
        have h := hThrN ((N : ℝ) ^ (δ / 16)) (mgDrift (band d) ζ N) (azumaMm d E δ τ₁ N)
          (Real.rpow_nonneg hN0.le _) (mgDrift_nonneg d ζ N)
          (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)) hMgN' hMmle hK1 hΔR τω hτK ω
          (hexp τω hτK) hinit hdrift hZ hY (fun j hj b => hRst j (lt_of_lt_of_le hj hτK) b)
        exact lt_of_le_of_lt h.1 h.2
      · rw [H_eq_H_zero_of_eq d heq, time_eq_time_zero_of_eq heq]
        exact hJ0
    have hτeq : τω = K N :=
      min_firstHit_eq_of_at
        (fun j (ω : Ωg d) => jSMat d E D' N (time s uR K N j) (H d s uR K N j ω))
        (fun j (ω : Ωg d) => (goodSet d E N (time s uR K N j) ((band d).ell N (s N)) τ₁ ε ζ ζ
          (ζ / 2) D')ᶜ.indicator (fun _ => (1 : ℝ)) (H d s uR K N j ω))
        (fun j => Step2.thr E s δ N (time s uR K N j)) (1 / 2) (K N)
        (fun j hj => by
          rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hgoodAll j hj))]
          norm_num)
        hat
    rw [hτeq, time_last s uR K N (hK0 N)] at hat
    exact hat
  -- the event inclusion
  have hsub : {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
      (N : ℝ) ^ δ * ((etaT E (s N) / etaT E (uR N)) ^ 4 *
        ((band d).scale E N (uR N))⁻¹ ^ 2 * (band d).decayProf N (uR N) D p.1 p.2)
      < lkErrMat d E N (uR N) (H d s uR K N (K N) ω) (pmLoop p.1 p.2)} ⊆ (Gdᶜ ∪ Rwᶜ) ∪ Ae := by
    intro ω hω
    by_contra hcon
    have hGω : ω ∈ Gd := by by_contra h; exact hcon (Or.inl (Or.inl h))
    have hRω : ω ∈ Rw := by by_contra h; exact hcon (Or.inl (Or.inr h))
    have hAω : s N < uR N → GridAE d E s uR K N ω := by by_contra h; exact hcon (Or.inr h)
    obtain ⟨p, hp⟩ := hω
    have hJK := hcore ω hGω hRω hAω
    have hlk := lk_le_of_jS d (H_isHermitian d s uR K N (K N) ω) hDD (hcrN.2.2.2 (u N)).1
      ((hcrN.2.2.2 (u N)).2.1.trans hW2N) hJK.le p.1 p.2
    have e : Step2.thr E s δ N (uR N) * ((band d).scale E N (uR N))⁻¹ ^ 2 *
          (band d).decayProf N (uR N) D p.1 p.2
        = (N : ℝ) ^ δ * ((etaT E (s N) / etaT E (uR N)) ^ 4 *
          ((band d).scale E N (uR N))⁻¹ ^ 2 * (band d).decayProf N (uR N) D p.1 p.2) := by
      unfold Step2.thr; ring
    linarith
  refine le_trans (measure_mono hsub) ?_
  have hp0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D₁ + 1)) := Real.rpow_nonneg hN0.le _
  calc Pg d ((Gdᶜ ∪ Rwᶜ) ∪ Ae) ≤ Pg d (Gdᶜ ∪ Rwᶜ) + Pg d Ae := measure_union_le _ _
    _ ≤ (Pg d Gdᶜ + Pg d Rwᶜ) + 0 := by
        rw [hAe0]; exact add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D₁ + 1)))) + 0 :=
        add_le_add (add_le_add hGN hRowN) le_rfl
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D₁ + 1))) := by
        rw [add_zero, ← ENNReal.ofReal_add hp0 hp0]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show -(D₁ + 1) = -D₁ + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        have h0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
        have : 2 * (N : ℝ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hN0]; exact hN2'
        nlinarith

end RBM.Gauss.Grid

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### (T2): `step2_gauss` -/

/-- **(T2) `step2_gauss`**: `Step2.step2`'s full conclusion, (2.75) and (2.76), for the Gaussian
model `sample d`, under step2's hypotheses **without `Hy`** (and without `Step1.Hyp`, which is
discharged internally). T1520's `step2_gauss_of_gridPointwise'` applied to (T1). -/
theorem step2_gauss {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  Grid.step2_gauss_of_gridPointwise' d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg
    (Grid.gridPointwise'_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg)

/-! ### (T3): `steps12_gauss` -/

/-- **(T3) `steps12_gauss`**: `Steps12 (sample d) E s t` with no `Hy`: `localLaw`/`aprioriDecay`
from (T2), `apriori`/`weakLaw` from `Step1.apriori`/`Step1.weakLaw` with `Step1.Hyp` discharged by
`step1Hyp_gauss_of_scale''` (the route of T1521's `steps12_gauss_of_grid`). -/
theorem steps12_gauss {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    Steps12 (sample d) E s t := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 (band d) E s t := Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := band d) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have h1 : Step1.Hyp (sample d) E s t :=
    step1Hyp_gauss_of_scale'' d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg'
  obtain ⟨hlocal, hdecay⟩ := step2_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg
  exact
    { apriori := Step1.apriori (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' h1
      weakLaw := Step1.weakLaw (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' h1
      localLaw := hlocal
      aprioriDecay := hdecay }

/-! ### (T4): audit checks -/

/-- **(T4)(a)** From `Step2.step2`'s hypothesis list for `X := sample d` **minus `Hy`** (the
`Step1.Hyp` binder `h1` is kept but unused), `step2_gauss` proves `Step2.step2`'s conclusion,
written out verbatim at `B := band d`, `X := sample d`. -/
example {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (_h1 : Step1.Hyp (sample d) E s t) (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  step2_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg

/-- **(T4)(b)** The conclusion type is *literally* `Step2.step2`'s: for any `Hy` (used only to
name the type `type_of% Step2.step2 …`; the proof term `step2_gauss …` does not mention `Hy`
or `h1`). -/
example {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (Hy : Step2.Hyp (sample d) E s t) (h1 : Step1.Hyp (sample d) E s t)
    (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    type_of% (Step2.step2 (sample d) hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg) :=
  step2_gauss d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg

end RBM.Gauss

end

#print axioms RBM.Gauss.Grid.hreg_endpoint
#print axioms RBM.Gauss.Grid.time_eq_time_zero_of_eq
#print axioms RBM.Gauss.Grid.H_eq_H_zero_of_eq
#print axioms RBM.Gauss.Grid.rowSet
#print axioms RBM.Gauss.Grid.measurableSet_rowSet
#print axioms RBM.Gauss.Grid.highProb_grid_rowSet
#print axioms RBM.Gauss.Grid.heG_coef_eq_driftCoef
#print axioms RBM.Gauss.Grid.mgDrift_nonneg
#print axioms RBM.Gauss.Grid.drift_of_goodSet
#print axioms RBM.Gauss.Grid.GridAE
#print axioms RBM.Gauss.Grid.ae_gridAE
#print axioms RBM.Gauss.Grid.gridPointwise'_gauss
#print axioms RBM.Gauss.step2_gauss
#print axioms RBM.Gauss.steps12_gauss
