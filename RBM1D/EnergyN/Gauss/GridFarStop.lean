/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarStop
import RBM1D.EnergyN.Gauss.Step2Plain

/-!
# The Chebyshev bound for the grid drift sum at a stopping index, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: the probability that the propagated
sum of the drift terms `Yvec` up to a stopping index `τ ≤ gridK` reaches `Step2.tT` at some pair
is at most `N^{-D₁}`, eventually (`RBM.Gauss.Grid.cheb_grid_at_stop_plainN`), and its instance at
`τ = gridTauFar` (`RBM.Gauss.Grid.cheb_grid_at_tauFar_plainN`).

## The external `κ`

Neither fixes an energy-dependent constant. The only energy-regularity input of
`cheb_grid_at_stop_plainN` is `etaT_inv_le_of_plainN` (`EnergyN/Gauss/Step2Plain.lean`); every
other `E`-use (`thrFar`, `gridTauFar`, `mE_im_pos`, `mE_im_le_one`, `Φgrid*`, the
Duhamel/Chebyshev machinery) is energy-free, deterministic at a single fixed energy, and used at
`E N`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {d : Dims}

/-- **Chebyshev bound at a stopping index `τ ≤ gridK`**: eventually, the probability that the
propagated drift sum `Σ_{j < τ} U_{u_{j+1}, u_τ} Y_{j+1}` reaches `Step2.tT` at some pair is at
most `N^{-D₁}`. The only energy-regularity input is `etaT_inv_le_of_plainN`. -/
theorem cheb_grid_at_stop_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {D : ℝ} (hD0 : 0 ≤ D) (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (D₁ : ℝ)
    (τ : ℕ → Ωg d → ℕ) (hτle : ∀ N ω, τ N ω ≤ gridK D D₁ N)
    (hτm : ∀ N j, MeasurableSet[filt d j] {ω | j < τ N ω}) :
    ∀ᶠ N : ℕ in atTop,
      (Pg d) {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D (time s u (gridK D D₁) N (τ N ω)) (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (τ N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D D₁) N (j + 1) : ℂ)
                (time s u (gridK D D₁) N (τ N ω) : ℂ)
                (Yvec (band d) (E N) s u (gridK D D₁) N (j + 1) ω)) a‖}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  filter_upwards [etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc, d.dim, eventually_ge_atTop 2]
    with N hηt hdim hN2
  set K : ℕ → ℕ := gridK D D₁ with hKdef
  have hK0 : ∀ N, K N ≠ 0 := gridK_ne_zero D D₁
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 := mE_im_pos (hE N)
  have hm1 := mE_im_le_one (E := E N) (hE N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have huN1 : u N < 1 := (hut N).trans_lt (ht1 N)
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith [hsu N]) (Nat.cast_nonneg _)
  have hus : u N - s N ≤ 1 := by linarith [hs0 N]
  have hΔCK : step s u K N ≤ (N : ℝ) ^ (-CK D D₁) := step_gridK_le (by omega) hus
  have hKΔ : (K N : ℝ) * step s u K N ≤ 1 := by
    have hKne : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK0 N)
    have : (K N : ℝ) * step s u K N = u N - s N := by unfold step; field_simp
    rw [this]; exact hus
  set τN : Ωg d → ℕ := fun ω => τ N ω with hτN
  have hτK : ∀ ω, τN ω ≤ K N := fun ω => hτle N ω
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τN ω} := fun j => hτm N j
  have hY : ∀ i, StronglyMeasurable[filt d i] (YvecCut (d := d) (E N) s u K N i) := fun i =>
    stronglyMeasurable_YvecCut (hE N) hsu hut ht1 hK0 N i
  have hu0 : 0 ≤ time s u K N 0 := by rw [time_zero]; exact hs0 N
  have hu_succ : ∀ j, time s u K N j ≤ time s u K N (j + 1) := fun j =>
    time_mono_of_le (hsu N) (Nat.le_succ j)
  have hutK : time s u K N (K N) = u N := time_last s u K N (hK0 N)
  have hηt0 : 0 < etaT (E N) (t N) := Step2.etaT_pos' (hE N) (ht1 N)
  have hcard := card_idx_le hdim.1
  set eb : ℝ := 2 ^ 22 * (N : ℝ) ^ 19 * step s u K N ^ 2 with heb
  -- per-step inputs
  have hstep : ∀ b : LoopArg (d.L N) 2, ∀ j < K N,
      let S : Set (Ωg d) := {ω | j < τN ω}
      let Φ := Φgrid (band d) (E N) N (time s u K N (j + 1))
      let U := ukerMat (d.L N) (time s u K N (j + 1)) (u N)
      (fun ω => S.indicator (fun ω' => Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (u N : ℂ) (YvecCut (d := d) (E N) s u K N (j + 1) ω') b) ω)
        =ᵐ[Pg d] S.indicator (stepY d s u K N j Φ U b) ∧
      (∀ a A, A.IsHermitian → (Φ a A).im = 0) ∧ (∀ a, TestFun d N (Φ a)) ∧
      (∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ (Fintype.card (d.Idx N) : ℝ) *
          ((2 : ℝ) ^ 2 * (2 * (1 + (etaT (E N) (t N))⁻¹) ^ 3) ^ 2)) ∧
      ∑ a : LoopArg (d.L N) 2, |U b a| ≤ (N : ℝ) ^ 2 := by
    intro b j hj S Φ U
    have hv0 : 0 ≤ time s u K N (j + 1) := hu0.trans
      (by have := time_mono_of_le (K := K) (hsu N) (Nat.zero_le (j + 1)); rwa [time_zero] at this ⊢)
    have hvw : time s u K N (j + 1) ≤ u N := by
      rw [← hutK]; exact time_mono_of_le (hsu N) hj
    have hv1 : time s u K N (j + 1) < 1 := hvw.trans_lt huN1
    have hΦ : ∀ a, TestFun d N (Φ a) := fun a => Φgrid_testFun (band d) (hE N) N hv1 a
    have hae := stepY_ukerMat_eq_Uker_ae d s u K N j hΦ hv0 hvw huN1
    refine ⟨?_, fun a A hA => Φgrid_im_eq_zero (band d) (hE N).le N hv0 hv1 a hA, hΦ, ?_, ?_⟩
    · filter_upwards [hae] with ω hω
      by_cases hωS : ω ∈ S
      · rw [Set.indicator_of_mem hωS, Set.indicator_of_mem hωS, YvecCut_succ hj, hω b]
        rfl
      · rw [Set.indicator_of_notMem hωS, Set.indicator_of_notMem hωS]
    · intro a A
      have hzη : etaT (E N) (t N) ≤ |(zt (E N) (time s u K N (j + 1))).im| := by
        rw [zt_im]
        refine le_trans ?_ (le_abs_self _)
        simp only [Step2.etaT_eq]
        exact mul_le_mul_of_nonneg_right (by linarith [hut N]) hm0.le
      exact Φgrid_bdd2 (band d) (hE N) N hv1 hηt0 hzη a A
    · refine (sum_abs_ukerMat_le (d.L N) (d.three_le_L N) hv0 hvw huN1 b).trans ?_
      have h1 : (1 - time s u K N (j + 1)) / (1 - u N) ≤ N := by
        have h1u : 0 < 1 - u N := by linarith
        have h1t : 0 < 1 - t N := by linarith [ht1 N]
        calc (1 - time s u K N (j + 1)) / (1 - u N) ≤ 1 / (1 - t N) := by
              rw [div_le_div_iff₀ h1u h1t]; nlinarith [hut N]
          _ ≤ (etaT (E N) (t N))⁻¹ := by
              rw [Step2.etaT_eq, one_div, mul_inv]
              have : 1 ≤ ((mE (E N)).im)⁻¹ := (one_le_inv₀ hm0).2 hm1
              have h0 : 0 < (1 - t N)⁻¹ := inv_pos.2 h1t
              nlinarith
          _ ≤ N := hηt
      have h0 : 0 ≤ (1 - time s u K N (j + 1)) / (1 - u N) :=
        div_nonneg (by linarith) (by linarith)
      exact pow_le_pow_left₀ h0 h1 2
  have hηi0 : 0 ≤ (etaT (E N) (t N))⁻¹ := inv_nonneg.2 hηt0.le
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
          ((2 : ℝ) ^ 2 * (2 * (1 + (etaT (E N) (t N))⁻¹) ^ 3) ^ 2) := by positivity
      refine (integral_sq_indicator_stepY_le s u K N j hΦ hR hC₂ hΔ0 _ b hS hrow hC₂0).trans ?_
      exact cheb_e_le hN1' (by positivity) le_rfl (Nat.cast_nonneg _) hcard hηi0 hηt
        (hM40 j) (hM4 j))
    (x := ((d.W N : ℝ) ^ (-D)) / 4)
    (div_pos (Real.rpow_pos_of_pos (by exact_mod_cast d.W_pos N) _) (by norm_num))
  -- the event inclusion
  set Sbad : Set (Ωg d) := {ω | ∃ a, 2 ^ 2 * (((d.W N : ℝ) ^ (-D)) / 4) ≤
      ‖(∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
        (time s u K N (τN ω) : ℂ) (YvecCut (d := d) (E N) s u K N (j + 1) ω)) a‖} with hSbad
  have hsub : {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D (time s u K N (τN ω)) (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
            (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
              (Yvec (band d) (E N) s u K N (j + 1) ω)) a‖} ⊆ Sbad := by
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    refine ⟨a, ?_⟩
    have hsum : (∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
        (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
          (YvecCut (d := d) (E N) s u K N (j + 1) ω))
        = ∑ j ∈ Finset.range (τN ω), Uker (d.L N) (fun _ => (1 : ℂ))
          (time s u K N (j + 1) : ℂ) (time s u K N (τN ω) : ℂ)
            (Yvec (band d) (E N) s u K N (j + 1) ω) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j < K N := lt_of_lt_of_le (Finset.mem_range.1 hj) (hτK ω)
      rw [YvecCut_succ this]
    rw [hsum]
    have hT : (d.W N : ℝ) ^ (-D) ≤
        Step2.tT (band d) (E N) N D (time s u K N (τN ω)) (zdist (d.L N) (a 0 - a 1)) :=
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

/-- **The same bound at the stopping index `gridTauFar`.** -/
theorem cheb_grid_at_tauFar_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t u : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    {D : ℝ} (hD0 : 0 ≤ D) (δ' τ₁ ε ζCtr τ3 τ57 : ℝ) (hsu : ∀ N, s N ≤ u N)
    (hut : ∀ N, u N ≤ t N) :
    ∀ D₁ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (Pg d) {ω | ∃ a : LoopArg (d.L N) 2,
        Step2.tT (band d) (E N) N D
            (time s u (gridK D D₁) N
              (gridTauFar d (E N) D δ' τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω))
            (zdist (d.L N) (a 0 - a 1)) ≤
          ‖(∑ j ∈ Finset.range (gridTauFar d (E N) D δ' τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω),
              Uker (d.L N) (fun _ => (1 : ℂ)) (time s u (gridK D D₁) N (j + 1) : ℂ)
                (time s u (gridK D D₁) N
                  (gridTauFar d (E N) D δ' τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω) : ℂ)
                (Yvec (band d) (E N) s u (gridK D D₁) N (j + 1) ω)) a‖}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
  intro D₁ _
  exact cheb_grid_at_stop_plainN hE hs0 hst ht1 hc0 hAc hD0 hsu hut D₁
    (fun N ω => gridTauFar d (E N) D δ' τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω)
    (fun N ω => gridTauFar_le (E N) D δ' τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N ω)
    (fun N j => lt_gridTauFar_measurableSet (hE N) D δ' τ₁ ε ζCtr τ3 τ57 s u (gridK D D₁) N j)

end RBM.Gauss.Grid

end
