/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Plain
import RBM1D.Gauss.Step4Base
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Gauss.SigmaExhaust
import RBM1D.Gauss.GridFarLift
import RBM1D.Gauss.GridFarClosure
import RBM1D.EnergyN.Gauss.Thm221Gauss
import RBM1D.EnergyN.Gauss.Step6PairInputs
import RBM1D.EnergyN.Gauss.LoopDecayFixed
import RBM1D.EnergyN.Gauss.Step4Closed
import RBM1D.EnergyN.Hierarchy.StepGlue
import RBM1D.EnergyN.Flow.Thm221RegN
import RBM1D.Flow.FlowRandomLayer
import RBM1D.Flow.Theorem26Assembly

/-!
# Theorem 2.21 with (2.71) and Lemmas 2.18–2.20 including (2.62), energy-uniform, Gaussian model

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.21 (with (2.71)) and Lemmas 2.18–2.20 including (2.62) (§2.7, §5.8), at an
`N`-dependent energy `E : ℕ → ℝ` with `∀ N, |E N| ≤ 2 - κ` (the paper's uniformity in `E`).

Three window statements for the Gaussian model under the plain pair: Lemma 5.9 for `L` and
`L - K` (`step6LoopDecayPair_gauss_plainN`), `Ξ^{(L-K)} ≺ 1` (`xiLK_le_one_gauss_plainN`) and
`η_u ≥ N^{-1}` on the window (`eta_rpow_neg_one_le_windowN`, which takes
`hE : ∀ N, |E N| < 2`); and the terminal results `thm221RegN_gauss` and `boundsNInput_gauss`.
The energy-dependent callees are `Grid.highProb_flow_decaySet_plainN`, `step4_gauss_plainN`,
`plain_of_cond272N`, `thm221NoELNReg_gauss`, `StepGlue.stochDom_flowXiLKN`,
`bounds_step_gauss_window_pairN`, `BoundsN_of_Thm221NReg`.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter

variable (d : Dims)

/-! ### (T1) `step6LoopDecayPair_gauss_plainN` -/

/-- **Lemma 5.9 for `L` and `L - K`, uniformly on the window**, Gaussian model, plain pair, at an
`N`-dependent energy, from `Grid.highProb_flow_decaySet_plainN`. -/
theorem step6LoopDecayPair_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    Step6LoopDecayPairN (sample d) E s t := by
  intro m _hm τ D hτ hD
  have hpair := Grid.highProb_flow_decaySet_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    m hτ (show (0 : ℝ) < 2 * D by linarith)
  intro D' hD'
  filter_upwards [hpair D' hD', (band d).dim, (band d).bandwidth, eventually_ge_atTop 1] with
    N hPN hdimN hbwN hN1
  refine le_trans (measure_mono ?_) hPN
  refine Set.compl_subset_compl.2 fun ω hω u => ?_
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast d.W_pos N
  have hWN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
    have h1 : d.W N ≤ d.W N * d.L N :=
      Nat.le_mul_of_pos_right _ (by have := d.three_le_L N; omega)
    exact_mod_cast h1.trans hdimN.1
  have hWτ : ((band d).W N : ℝ) ^ τ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow hWpos.le hWN hτ.le
  have hellu0 : (0 : ℝ) ≤ (band d).ell N (u : ℝ) :=
    le_trans zero_le_one (one_le_ellHat (d.L N) (d.three_le_L N)
      ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N)))
  have hrad : (band d).ell N (u : ℝ) * ((band d).W N : ℝ) ^ τ
      ≤ (band d).ell N (u : ℝ) * (N : ℝ) ^ τ := mul_le_mul_of_nonneg_left hWτ hellu0
  have hexp : (N : ℝ) ^ D ≤ ((band d).W N : ℝ) ^ (2 * D) := by
    have hcpos := (band d).c_pos
    have h1 : (N : ℝ) ^ ((1 / 2 + (band d).c) * (2 * D)) ≤ ((band d).W N : ℝ) ^ (2 * D) := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbwN (by linarith)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_) h1
    nlinarith
  have hWD : ((band d).W N : ℝ) ^ (-(2 * D)) ≤ (N : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hWpos.le, Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 D) hexp
  have hgloop : Decay.LoopDecay (d.L N) m
      ((band d).ell N (u : ℝ) * ((band d).W N : ℝ) ^ τ) (((band d).W N : ℝ) ^ (-(2 * D)))
      (fun I => gloop (d.L N) (d.W N) (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) I) := (hω u).1
  have hlk : Decay.LoopDecay (d.L N) m
      ((band d).ell N (u : ℝ) * ((band d).W N : ℝ) ^ τ) (((band d).W N : ℝ) ^ (-(2 * D)))
      (fun I => gloop (d.L N) (d.W N) (Hflow d N (u : ℝ) ω) (zt (E N) (u : ℝ)) I
        - (band d).Kval (E N) N (u : ℝ) I) := (hω u).2
  exact ⟨hlk.mono (d.L N) le_rfl hrad hWD, hgloop.mono (d.L N) le_rfl hrad hWD⟩

/-! ### (T2) `xiLK_le_one_gauss_plainN` -/

/-- **`Ξ^{(L-K)}_{u,m} ≺ 1`** at an `N`-dependent energy,
from `step4_gauss_plainN` at `f N u := scale (E N) N u⁻¹ ^ m` fed through
`StepGlue.stochDom_flowXiLKN`. -/
theorem xiLK_le_one_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) {m : ℕ}
    (hm : 1 ≤ m) :
    StochDom (band d).P (fun N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      fun _ _ _ => (1 : ℝ) := by
  have h4 := step4_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc m hm
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hpos : ∀ N (u : TimeIcc s t N), 0 < (band d).scale (E N) N u := fun N u =>
    (band d).scale_pos' (hE2 N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hA : ∀ N (u : TimeIcc s t N), 0 ≤ (band d).scale (E N) N u := fun N u => (hpos N u).le
  have hdom := StepGlue.stochDom_flowXiLKN (sample d)
    (f := fun N u => ((band d).scale (E N) N u)⁻¹ ^ m) hA h4
  have heq : (fun N (u : TimeIcc s t N) (_ : Ω d) =>
        ((band d).scale (E N) N u)⁻¹ ^ m * (band d).scale (E N) N u ^ m)
      = fun _ _ _ => (1 : ℝ) := by
    funext N u _
    rw [← mul_pow, inv_mul_cancel₀ (hpos N u).ne', one_pow]
  rwa [heq] at hdom

/-! ### (T3) `eta_rpow_neg_one_le_windowN` -/

/-- **`η_u ≥ N^{-1}` on the whole window**, eventually, at an `N`-dependent energy. -/
theorem eta_rpow_neg_one_le_windowN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E N) u := by
  filter_upwards [hAc, (band d).dim, eventually_ge_atTop 1] with N hAcN hdimN hN1
  intro u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have ht0 : 0 ≤ t N := (hs0 N).trans (hst N)
  have httN : t N < 1 := ht1 N
  have hηt_pos : 0 < etaT (E N) (t N) := etaT_pos (hE N) httN
  have hellL : (band d).ell N (t N) ≤ ((band d).L N : ℝ) := SumZeroDyn.ellHat_real_le_L httN
  have hWL : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdimN.1
  have hWpos : (0 : ℝ) ≤ ((band d).W N : ℝ) := by positivity
  have hscale_le : (band d).scale (E N) N (t N) ≤ etaT (E N) (t N) * (N : ℝ) := by
    have h1 : (band d).scale (E N) N (t N)
        = etaT (E N) (t N) * (((band d).W N : ℝ) * (band d).ell N (t N)) := by
      change ((band d).W N : ℝ) * (band d).ell N (t N) * etaT (E N) (t N) = _
      ring
    rw [h1]
    have hstep : ((band d).W N : ℝ) * (band d).ell N (t N) ≤ (N : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hellL hWpos) hWL
    exact mul_le_mul_of_nonneg_left hstep hηt_pos.le
  have h1Nc : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  have h1Net : (1 : ℝ) ≤ etaT (E N) (t N) * (N : ℝ) := h1Nc.trans (hAcN.trans hscale_le)
  have hetat_ge : (N : ℝ)⁻¹ ≤ etaT (E N) (t N) := by
    rw [inv_eq_one_div, div_le_iff₀ hN0]
    exact h1Net
  have hmono : etaT (E N) (t N) ≤ etaT (E N) (u : ℝ) := etaT_le_of_le_window (hE N) u.2.2
  have hcast : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := by
    rw [show (-(1 : ℝ)) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  rw [hcast]
  exact hetat_ge.trans hmono

end RBM.Gauss

/-! ### Terminal results -/

namespace RBM.Gauss

open MeasureTheory Filter

/-- Theorem 2.21 with (2.71), (2.72) = `Cond272NReg`, `N`-dependent energy, Gaussian model. -/
theorem thm221RegN_gauss (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) : Thm221NReg (sample d) κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB := by
    have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
    set κ' : ℝ := min κ 1 with hκ'def
    have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
    have hκ'1 : κ' ≤ 1 := min_le_right _ _
    have hle : (2 : ℝ) - κ ≤ 2 - κ' := by have := min_le_left κ 1; linarith
    have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans hle
    have hBcore : BoundsCoreN (sample d) E s := hB.toBoundsCoreN
    have hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
        (band d).scale (E N) N (t N) := plain_of_cond272N d hE2 hst ht1 hreg.1
    have hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N) := hreg.2
    have hBC : BoundsCoreN (sample d) E t :=
      (thm221NoELNReg_gauss d hκ0).step E hE c hc0 s t hs0 hst ht1 hreg hBcore
    have hLD : Step6LoopDecayPairN (sample d) E s t :=
      step6LoopDecayPair_gauss_plainN d hκ'0 hκ'1 hEκ' hBcore hs0 hst ht1 hc0 hreg0 hAc
    have hxi1 := xiLK_le_one_gauss_plainN d hκ'0 hκ'1 hEκ' hBcore hs0 hst ht1 hc0 hreg0 hAc
      (m := 1) (by norm_num)
    have hxi2 := xiLK_le_one_gauss_plainN d hκ'0 hκ'1 hEκ' hBcore hs0 hst ht1 hc0 hreg0 hAc
      (m := 2) (by norm_num)
    have hxi3 := xiLK_le_one_gauss_plainN d hκ'0 hκ'1 hEκ' hBcore hs0 hst ht1 hc0 hreg0 hAc
      (m := 3) (by norm_num)
    have hlmk : SharpLmKFlowN (sample d) E s t :=
      step4_gauss_plainN d hκ'0 hκ'1 hEκ' hBcore hs0 hst ht1 hc0 hreg0 hAc
    have hη := eta_rpow_neg_one_le_windowN d hE2 hs0 hst ht1 hc0 hAc
    exact bounds_step_gauss_window_pairN d hκ'0 hκ'1 hEκ' hs0 hst ht1 hreg.1 zero_le_one hη
      hLD hxi1 hxi2 hxi3 hlmk hBC hB
/-- The input `BoundsNInput d κ` of `RBM1D/Flow/FlowRandomLayer.lean`. -/
theorem boundsNInput_gauss (d : Dims) {κ : ℝ} (hκ : 0 < κ) : BoundsNInput d κ :=
  fun _E hE _τ hτ _t ht0 ht => BoundsN_of_Thm221NReg hκ (thm221RegN_gauss d hκ) hE hτ ht0 ht

end RBM.Gauss

namespace RBM.Gauss

open MeasureTheory Filter

section CompatN

variable (d : Dims)

end CompatN

end RBM.Gauss

