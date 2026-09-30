/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarLift
import RBM1D.Gauss.Step4Base
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Gauss.SigmaExhaust
import RBM1D.Gauss.GridFarClosure
import RBM1D.EnergyN.Gauss.Step4Closed
import RBM1D.EnergyN.Gauss.GridFarLift
import RBM1D.EnergyN.Gauss.GridFarClosure
import RBM1D.EnergyN.Hierarchy.Step2MomentStep
import RBM1D.EnergyN.Hierarchy.Step45

/-!
# Step 5 for the Gaussian flow at an `N`-dependent energy

Four statements at an `N`-dependent energy `E : ℕ → ℝ`: the near half of (5.48)
(`hnear_of_step4_far_ofN`), (5.48) for the flow (`flowEq548_gauss_ofN`), and Step 5, (2.79), from
the far-field pointwise bound (`step5_gauss_ofN`) and under the plain pair
(`step5_gauss_plainN`).

The hypotheses are `hEκ : ∀ N, |E N| ≤ 2 - κ`, `hB : BoundsCoreN`,
`hG : Grid.FarGridPointwiseN`. No energy-dependent constant is fixed in this file. The proofs
call `Grid.hfar_of_farGridPointwiseN` with `hκ0 hκ1 hEκ`, which every theorem here binds.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace Gauss

variable (d : Dims)

/-- **The near half of (5.48), at all distances**, at an `N`-dependent energy: `|L - K|` for
`σ = (+,-)` is `≺ (η_s/η_u)^2 tailT`, uniformly in `u ∈ [s, t]`. The proof uses
`step4_gauss_plainN`, `Grid.hfar_of_farGridPointwiseN` and `Step2.etaT_ratio`; the only eventual
filter (`W → ∞`, `W ≤ N`, `N ≥ 1`) involves no energy. -/
theorem hnear_of_step4_far_ofN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hG : Grid.FarGridPointwiseN d E s t) :
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 2 *
        tailT ((band d).W N : ℝ) ((band d).ell N p.1) (etaT (E N) p.1) D
          (zdist ((band d).L N) (p.2.1 - p.2.2))) := by
  intro D hD0
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  -- Step 4's sharp bound at `n = 2`, reindexed from `LoopData` to `pmLoop`.
  have h4 : StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ 2) :=
    (step4_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc 2
      (by norm_num)).precomp_param
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) =>
        (p.1, Step45.pmData p.2.1 p.2.2))
  -- The far bound supplied by `hG`.
  have hfar := Grid.hfar_of_farGridPointwiseN d hκ0 hκ1 hEκ hs0 hst ht1 hc0 hAc hG D hD0
  -- `(η_s/η_u)² ≥ 1` on `[s N, t N] ⊆ [0,1)`.
  have hpref1 : ∀ N (u : TimeIcc s t N),
      (1 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) (u : ℝ)) ^ 2 := by
    intro N u
    have hsu : s N ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    rw [Step2.etaT_ratio (hE N)]
    have h1 : (0 : ℝ) < 1 - (u : ℝ) := by linarith
    have h2 : 1 - (u : ℝ) ≤ 1 - s N := by linarith
    have hge1 : (1 : ℝ) ≤ (1 - s N) / (1 - (u : ℝ)) := by
      rw [le_div_iff₀ h1]; linarith
    nlinarith [hge1]
  -- The eventual polynomial bound absorbing `exp(√6 (log W)^{3/4})`.
  refine StochDom.of_subset_union h4 hfar fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hWtendsto : Tendsto (fun N : ℕ => ((band d).W N : ℝ)) atTop atTop :=
    tendsto_atTop.2 fun W₀ => (band d).eventually_le_W W₀
  filter_upwards [hWtendsto.eventually (eventually_exp_mul_log_rpow_le (√6) (half_pos hτ)),
    Step45.eventually_W_le (band d), eventually_ge_atTop 1] with N hexp hWleN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hWpos : (1 : ℝ) ≤ ((band d).W N : ℝ) := by
    have := (band d).W_pos N; exact_mod_cast this
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  dsimp only at hp
  have hu1 : ((p.1 : TimeIcc s t N) : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hℓpos : 0 < (band d).ell N ((p.1 : TimeIcc s t N) : ℝ) :=
    Step3.ellHat_pos_of_lt_one ((band d).one_le_L N) hu1
  have hT0 : (0 : ℝ) ≤ tailT ((band d).W N : ℝ) ((band d).ell N ((p.1 : TimeIcc s t N) : ℝ))
      (etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) D (zdist ((band d).L N) (p.2.1 - p.2.2)) :=
    tailT_nonneg (Nat.cast_nonneg _) _
  have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hpow0' : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hpref1' : (1 : ℝ) ≤ (etaT (E N) (s N) / etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) ^ 2 :=
    hpref1 N p.1
  by_cases hnear : (zdist ((band d).L N) (p.2.1 - p.2.2) : ℝ) ≤
      6 * ellStar ((band d).W N : ℝ) ((band d).ell N ((p.1 : TimeIcc s t N) : ℝ))
  · -- Near case: use Step 4's sharp bound.
    left
    refine ⟨p, ?_⟩
    dsimp only
    simp only [Band.scale]
    rw [inv_pow]
    have hinvsq := Step45.inv_sq_le_tailT (η := etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) (D := D)
      hWpos hℓpos hnear
    have hc1 : Real.exp (√6 * Real.log ((band d).W N : ℝ) ^ ((3 : ℝ) / 4)) ≤ (N : ℝ) ^ (τ / 2) :=
      hexp.trans (Real.rpow_le_rpow (by linarith) hWleN (half_pos hτ).le)
    set T := tailT ((band d).W N : ℝ) ((band d).ell N ((p.1 : TimeIcc s t N) : ℝ))
      (etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) D (zdist ((band d).L N) (p.2.1 - p.2.2))
      with hTdef
    set pref := (etaT (E N) (s N) / etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) ^ 2 with hprefdef
    calc (N : ℝ) ^ (τ / 2) *
          ((((band d).W N : ℝ) * (band d).ell N ((p.1 : TimeIcc s t N) : ℝ) *
              etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) ^ 2)⁻¹
        ≤ (N : ℝ) ^ (τ / 2) *
            (Real.exp (√6 * Real.log ((band d).W N : ℝ) ^ ((3 : ℝ) / 4)) * T) :=
          mul_le_mul_of_nonneg_left hinvsq hpow0'
      _ = (N : ℝ) ^ (τ / 2) * Real.exp (√6 * Real.log ((band d).W N : ℝ) ^ ((3 : ℝ) / 4)) * T :=
          by ring
      _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hpow0') hT0
      _ = (N : ℝ) ^ τ * T := by
          rw [← Real.rpow_add (by linarith : (0 : ℝ) < (N : ℝ))]
          congr 2
          ring
      _ ≤ (N : ℝ) ^ τ * (pref * T) := by
          have := mul_le_mul_of_nonneg_left hpref1' hT0
          nlinarith [hpow0]
      _ < (sample d).lkErr (E N) N ((p.1 : TimeIcc s t N) : ℝ) ω (pmLoop p.2.1 p.2.2) := hp
  · -- Far case: use `hG`'s far bound directly.
    right
    refine ⟨p, ?_⟩
    dsimp only
    rw [if_neg hnear]
    set T := tailT ((band d).W N : ℝ) ((band d).ell N ((p.1 : TimeIcc s t N) : ℝ))
      (etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) D (zdist ((band d).L N) (p.2.1 - p.2.2))
      with hTdef
    set pref := (etaT (E N) (s N) / etaT (E N) ((p.1 : TimeIcc s t N) : ℝ)) ^ 2 with hprefdef
    have h3a : (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    calc (N : ℝ) ^ (τ / 2) * T ≤ (N : ℝ) ^ τ * T := mul_le_mul_of_nonneg_right h3a hT0
      _ ≤ (N : ℝ) ^ τ * (pref * T) := by
          have := mul_le_mul_of_nonneg_left hpref1' hT0
          nlinarith [hpow0]
      _ < (sample d).lkErr (E N) N ((p.1 : TimeIcc s t N) : ℝ) ω (pmLoop p.2.1 p.2.2) := hp

/-- **(5.48) for the flow** at an `N`-dependent energy: `Step2MomentStep.flowEq548_of_near_farN` fed
`hnear_of_step4_far_ofN` and `Grid.hfar_of_farGridPointwiseN`. -/
theorem flowEq548_gauss_ofN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hG : Grid.FarGridPointwiseN d E s t) :
    Step45.FlowEq548N (sample d) E s t :=
  Step2MomentStep.flowEq548_of_near_farN (sample d)
    (hnear_of_step4_far_ofN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hG)
    (Grid.hfar_of_farGridPointwiseN d hκ0 hκ1 hEκ hs0 hst ht1 hc0 hAc hG)

/-- **(2.79)** at an `N`-dependent energy, from the far-field pointwise bound `hG`:
`Step45.flow_sharpDecayN` fed `step4_gauss_plainN … 2` and `flowEq548_gauss_ofN`. -/
theorem step5_gauss_ofN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hG : Grid.FarGridPointwiseN d E s t) :
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  exact Step45.flow_sharpDecayN (sample d) hE hs0 ht1
    (step4_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc 2 (by norm_num))
    (flowEq548_gauss_ofN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hG)

/-- **(2.79)** at an `N`-dependent energy, on the plain pair alone: `step5_gauss_ofN` with `hG`
discharged by `Grid.farGridPointwise_gauss_plainN` (whose binders are identical). -/
theorem step5_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  step5_gauss_ofN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    (Grid.farGridPointwise_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc)

end Gauss

end RBM

end

