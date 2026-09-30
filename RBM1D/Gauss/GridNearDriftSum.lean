/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridDriftPoint
import RBM1D.Gauss.GridStepBound
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Hierarchy.Step3

/-!
# The joint near-drift grid sum

The grid analogue of the integral bound for the near-drift integrand
`RBM.Step2Near47.driftNearInt` (`Step2Near47.lean`): a left Riemann sum of the near-drift integrand,
taken **jointly** (the ratio `(ℓ_u/ℓ_s)³` and the propagator weight `(η_u/η_v)²` combined *before*
summing), stays at `R²` instead of the `R^{7/2}` that a `sup × length` bound would give.

## Main result

* `RBM.Gauss.Grid.nearDrift_grid_sum_le` — the joint near-drift grid sum.

## Route

1. `(ℓ_u/ℓ_s)³ ≤ (η_s/η_u)^{3/2}` (as `√(η_s/η_u) ^ 3`) from `Step3.ellHat_le_sqrt_mul`
   (the same cap-robust ratio bound that `DriftPt.ell_mul_sqrt_le` (`GridDriftPoint.lean`)
   expresses in product form).
2. `1 - u_{j+1} ≤ 1 - u_j` from `time_mono'` (`GridStepBound.lean`).
3. The two combine, pointwise, to exactly `RBM.Step2Near47.driftNearInt E s v u`, whose closed
   form `RBM.Step2Near47.driftNearInt_eq` is `C / √(1 - u)` for a `j`-independent constant `C`.
4. `DriftPt.sum_step_div_sqrt_le` (`GridDriftPoint.lean`) telescopes
   `∑_{j<k} Δ / √(1 - u_j) ≤ 2 √(1 - u_0)`; no `sup × length` step is used anywhere.
5. The final identity `C · 2 √(1 - s) = 2 (Im m)^{-1} (η_s/η_v)²` closes the bound; this is the
   same algebraic identity as in the continuous analogue, the integral of the near-drift
   integrand.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Real Finset RBM

/-- **The joint near-drift grid sum**: the grid analogue of the integral of
`RBM.Step2Near47.driftNearInt`. -/
theorem nearDrift_grid_sum_le {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ}
    (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N) (hst : s N ≤ t N)
    (ht1 : t N < 1) (hK1 : 1 ≤ K N) {k : ℕ} (hk : k ≤ K N) :
    ∑ j ∈ Finset.range k, step s t K N * (etaT E (time s t K N j))⁻¹ *
        ((1 - time s t K N (j + 1)) / (1 - time s t K N k)) ^ 2 *
        (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3
      ≤ 2 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (time s t K N k)) ^ 2 := by
  have hm := mE_im_pos hE
  have hs1 : s N < 1 := hst.trans_lt ht1
  set v := time s t K N k with hvdef
  have hv_le_t : v ≤ t N := time_le_t s t K N hst hK1 hk
  have hv1 : v < 1 := hv_le_t.trans_lt ht1
  have ha : 0 < etaT E (s N) := Step2.etaT_pos' hE hs1
  have hc : 0 < etaT E v := Step2.etaT_pos' hE hv1
  set C : ℝ := √(etaT E (s N)) ^ 3 * (etaT E v ^ 2 * √((mE E).im))⁻¹ with hCdef
  have hC0 : 0 < C := by
    have h1 : 0 < √(etaT E (s N)) := Real.sqrt_pos.2 ha
    have h2 : 0 < √((mE E).im) := Real.sqrt_pos.2 hm
    rw [hCdef]; positivity
  -- Pointwise bound: each summand is `≤ Δ · C / √(1 - u_j)`.
  have hterm2 : ∀ j ∈ Finset.range k,
      step s t K N * (etaT E (time s t K N j))⁻¹ *
          ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 *
          (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3
        ≤ step s t K N * (C / √(1 - time s t K N j)) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set u := time s t K N j with hudef
    have hu_le_v : u ≤ v := time_mono' s t K N hst hjk.le
    have hu1 : u < 1 := hu_le_v.trans_lt hv1
    have hs_le_u : s N ≤ u := s_le_time s t K N hst j
    have hb : 0 < etaT E u := Step2.etaT_pos' hE hu1
    have hL1 : 1 ≤ B.L N := B.one_le_L N
    have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
    have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL1 hu1
    -- Step 2: `1 - u_{j+1} ≤ 1 - u_j`.
    have h_j1_le_v : time s t K N (j + 1) ≤ v := time_mono' s t K N hst (by omega)
    have h_j1_lt1 : time s t K N (j + 1) < 1 := h_j1_le_v.trans_lt hv1
    have h_u_le_j1 : u ≤ time s t K N (j + 1) := time_mono' s t K N hst (Nat.le_succ j)
    have hRatio_frac_le : (1 - time s t K N (j + 1)) / (1 - v) ≤ (1 - u) / (1 - v) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hfrac_nonneg : (0 : ℝ) ≤ (1 - time s t K N (j + 1)) / (1 - v) := by
      apply div_nonneg <;> linarith
    have hsq_le : ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 ≤ ((1 - u) / (1 - v)) ^ 2 :=
      pow_le_pow_left₀ hfrac_nonneg hRatio_frac_le 2
    have hEtaRatio : (1 - u) / (1 - v) = etaT E u / etaT E v := (Step2.etaT_ratio hE u v).symm
    rw [hEtaRatio] at hsq_le
    -- Step 1: `(ℓ_u/ℓ_s)³ ≤ (η_s/η_u)^{3/2}`.
    have hy0 : (0 : ℝ) ≤ B.ell N u / B.ell N (s N) := div_nonneg hℓu.le hℓs.le
    have hRe : etaT E (s N) / etaT E u = (1 - s N) / (1 - u) := Step2.etaT_ratio hE _ _
    have hyR : B.ell N u / B.ell N (s N) ≤ √(etaT E (s N) / etaT E u) := by
      rw [hRe, div_le_iff₀ hℓs]
      exact Step3.ellHat_le_sqrt_mul (L := B.L N) hs_le_u hu1
    have hy3 : (B.ell N u / B.ell N (s N)) ^ 3 ≤ √(etaT E (s N) / etaT E u) ^ 3 :=
      pow_le_pow_left₀ hy0 hyR 3
    have hmid : (etaT E u)⁻¹ * ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2
        ≤ (etaT E u)⁻¹ * (etaT E u / etaT E v) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_le (by positivity)
    -- Step 3: the summand is `≤ Δ · driftNearInt E s v u = Δ · η_s^{3/2} η_u^{-1/2} η_v^{-2}`.
    have h1 : (etaT E u)⁻¹ * ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 *
          (B.ell N u / B.ell N (s N)) ^ 3
        ≤ Step2Near47.driftNearInt E (s N) v u := by
      unfold Step2Near47.driftNearInt
      calc (etaT E u)⁻¹ * ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 *
              (B.ell N u / B.ell N (s N)) ^ 3
          ≤ (etaT E u)⁻¹ * (etaT E u / etaT E v) ^ 2 * (B.ell N u / B.ell N (s N)) ^ 3 :=
            mul_le_mul_of_nonneg_right hmid (by positivity)
        _ ≤ (etaT E u)⁻¹ * (etaT E u / etaT E v) ^ 2 * √(etaT E (s N) / etaT E u) ^ 3 :=
            mul_le_mul_of_nonneg_left hy3 (by positivity)
    have hstep_nonneg : (0 : ℝ) ≤ step s t K N := step_nonneg' s t K N hst
    have hdEq : Step2Near47.driftNearInt E (s N) v u = C / √(1 - u) := by
      rw [Step2Near47.driftNearInt_eq hE hs1 hu1 hv1, hCdef]; ring
    calc step s t K N * (etaT E u)⁻¹ *
          ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 * (B.ell N u / B.ell N (s N)) ^ 3
        = step s t K N * ((etaT E u)⁻¹ *
            ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 * (B.ell N u / B.ell N (s N)) ^ 3) := by
          ring
      _ ≤ step s t K N * Step2Near47.driftNearInt E (s N) v u :=
          mul_le_mul_of_nonneg_left h1 hstep_nonneg
      _ = step s t K N * (C / √(1 - u)) := by rw [hdEq]
  have hsum1 :
      ∑ j ∈ Finset.range k, step s t K N * (etaT E (time s t K N j))⁻¹ *
          ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 *
          (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3
        ≤ ∑ j ∈ Finset.range k, step s t K N * (C / √(1 - time s t K N j)) :=
    Finset.sum_le_sum hterm2
  have hfact : ∑ j ∈ Finset.range k, step s t K N * (C / √(1 - time s t K N j))
      = C * ∑ j ∈ Finset.range k, step s t K N / √(1 - time s t K N j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- Step 4: the telescoping sum.
  have htelescope : ∑ j ∈ Finset.range k, step s t K N / √(1 - time s t K N j)
      ≤ 2 * √(1 - s N) := by
    have hu_step : ∀ j, time s t K N (j + 1) = time s t K N j + step s t K N :=
      fun j => time_succ' s t K N j
    have hΔ0 : (0 : ℝ) ≤ step s t K N := step_nonneg' s t K N hst
    have huk1 : time s t K N k < 1 := hv1
    have hres := DriftPt.sum_step_div_sqrt_le (time s t K N) (step s t K N) hΔ0 hu_step huk1
    rwa [time_zero] at hres
  -- Step 5: the closing algebraic identity.
  have hfinal : C * (2 * √(1 - s N)) = 2 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 := by
    obtain ⟨p, hp0, hp⟩ : ∃ p : ℝ, 0 < p ∧ p ^ 2 = 1 - s N :=
      ⟨√(1 - s N), Real.sqrt_pos.2 (by linarith), Real.sq_sqrt (by linarith)⟩
    obtain ⟨q, hq0, hq⟩ : ∃ q : ℝ, 0 < q ∧ q ^ 2 = (mE E).im :=
      ⟨√((mE E).im), Real.sqrt_pos.2 hm, Real.sq_sqrt hm.le⟩
    have hps : √(1 - s N) = p := by rw [← hp, Real.sqrt_sq hp0.le]
    have hqs : √((mE E).im) = q := by rw [← hq, Real.sqrt_sq hq0.le]
    have hsa : √(etaT E (s N)) = p * q := by
      rw [Step2.etaT_eq, ← hp, ← hq, ← mul_pow, Real.sqrt_sq (by positivity)]
    have hes : etaT E (s N) = p ^ 2 * q ^ 2 := by rw [Step2.etaT_eq, hp, hq]
    have hne3 : etaT E v ≠ 0 := hc.ne'
    rw [hCdef, hsa, hps, hqs, hes, ← hq]
    field_simp
  calc ∑ j ∈ Finset.range k, step s t K N * (etaT E (time s t K N j))⁻¹ *
        ((1 - time s t K N (j + 1)) / (1 - v)) ^ 2 *
        (B.ell N (time s t K N j) / B.ell N (s N)) ^ 3
      ≤ ∑ j ∈ Finset.range k, step s t K N * (C / √(1 - time s t K N j)) := hsum1
    _ = C * ∑ j ∈ Finset.range k, step s t K N / √(1 - time s t K N j) := hfact
    _ ≤ C * (2 * √(1 - s N)) := mul_le_mul_of_nonneg_left htelescope hC0.le
    _ = 2 * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 := hfinal

end RBM.Gauss.Grid

end
