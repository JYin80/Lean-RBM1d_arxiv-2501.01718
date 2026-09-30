/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.BlockGreen
import RBM1D.Gauss.MinorDiffCond
import RBM1D.EnergyN.Gauss.BlockGreen
import RBM1D.EnergyN.Gauss.GoodSetFlowProb
import RBM1D.EnergyN.Gauss.EntryBoundTime

/-!
# `jG ≤ N^{2ε} jS` along the flow, at an `N`-dependent energy

`RBM.Gauss.Step2.highProb_jG_le_jSN`: with high probability `jG ≤ N^{2ε} jS` at all
`u ∈ [s, t]`, at an `N`-dependent energy `E : ℕ → ℝ`. No energy-dependent constant is fixed in
this file: `κ` is explicit (`hE : ∀ N, |E N| ≤ 2 - κ`), and the proof uses
`highProb_jG_le_of_entryBoundFlowN` (`BlockGreen.lean`) and `highProb_goodSetFlowN`
(`GoodSetFlowProb.lean`), plus
`entryBoundFlow_floorN`/`rpow_neg_one_le_etaT_of_scale_geN`/`flowDelta_le_rpow_negN`
(`EntryBoundTime.lean`).
-/

namespace RBM.Gauss.Step2

open Filter MeasureTheory Set RBM RBM.Gauss

/-- **With high probability `jG ≤ N^{2ε} jS` for all `u ∈ [s, t]`**, from (2.68)–(2.70) at `s`,
(2.72) and `N^c ≤ W ℓ_t η_t`. No energy-dependent constant is fixed here: `κ` is explicit. -/
theorem highProb_jG_le_jSN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t)
    {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      BlockGreen.jG (sample d) (E N) N (u : ℝ) ω ((band d).ell N (u : ℝ))
        (etaT (E N) (u : ℝ)) D ≤
      (N : ℝ) ^ (2 * ε) * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω}) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hCond272Reg : Cond272NReg (band d) E s t c := ⟨hcond, hreg⟩
  have hGoodHP : HighProb (P d) (fun N => goodSetFlow d (E N) s t
      (fun N => flowDelta d (E N) t N) N) :=
    GoodSetFlowProb.highProb_goodSetFlowN d hκ hE hs0 hst ht1 hc0 hCond272Reg hB
  have hEntry : EntryBoundFlow'N d E s t (fun N => 2 * (N : ℝ) ^ (-D)) :=
    entryBoundFlow_floorN d hE2 hs0 hst ht1 (K := 1) zero_le_one
      (rpow_neg_one_le_etaT_of_scale_geN d hE2 ht1 hc0 hreg) (c₀ := c / 6) (by linarith)
      (flowDelta_le_rpow_negN d hreg) (B := D) hD
  have hHP := BlockGreen.highProb_jG_le_of_entryBoundFlowN d hE2 hs0 hst ht1 hcond D hD
    hEntry hGoodHP hε
  refine hHP.mono ?_
  filter_upwards [eventually_le_rpow (3 + 9 * Real.exp (Real.sqrt 3)) hε,
    Filter.eventually_ge_atTop (1 : ℕ)] with N hAle hN1 ω hω u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNε1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1' hε.le
  have hNε0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := by linarith
  have hJ : (1 : ℝ) ≤ RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω :=
    Step2Moment.one_le_jS (sample d) (E := E N) (D := D) N (u : ℝ) ω
  have hJ0 : (0 : ℝ) ≤ RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := le_trans zero_le_one hJ
  have hj := hω u
  have hstepA : (3 : ℝ) * (N : ℝ) ^ ε ≤
      (3 : ℝ) * (N : ℝ) ^ ε * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := by
    have h := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ) ^ ε)
    simpa using h
  have hstepC : (1 : ℝ) + 2 * (N : ℝ) ^ ε ≤
      (3 : ℝ) * (N : ℝ) ^ ε * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω :=
    (show (1 : ℝ) + 2 * (N : ℝ) ^ ε ≤ 3 * (N : ℝ) ^ ε by linarith).trans hstepA
  have hstepD : (1 : ℝ) + (N : ℝ) ^ ε *
      (9 * Real.exp (Real.sqrt 3) * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω + 2) ≤
      (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
        RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω) := by
    have hexpand1 : (N : ℝ) ^ ε *
        (9 * Real.exp (Real.sqrt 3) * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω + 2)
        = (N : ℝ) ^ ε * (9 * Real.exp (Real.sqrt 3) *
            RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω) + 2 * (N : ℝ) ^ ε := by ring
    have hexpand2 : (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
        RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω)
        = (N : ℝ) ^ ε * (9 * Real.exp (Real.sqrt 3) *
            RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω)
          + 3 * (N : ℝ) ^ ε * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := by ring
    rw [hexpand1, hexpand2]
    linarith [hstepC]
  have hstepE :
      (N : ℝ) ^ ε * (3 + 9 * Real.exp (Real.sqrt 3)) ≤ (N : ℝ) ^ ε * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_left hAle hNε0
  have hstepF : (N : ℝ) ^ ε * (N : ℝ) ^ ε = (N : ℝ) ^ (2 * ε) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hstepG : (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
      RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω) ≤
      (N : ℝ) ^ (2 * ε) * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := by
    have h := mul_le_mul_of_nonneg_right hstepE hJ0
    calc (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
          RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω)
        = ((N : ℝ) ^ ε * (3 + 9 * Real.exp (Real.sqrt 3))) *
          RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := by ring
      _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ ε) * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := h
      _ = (N : ℝ) ^ (2 * ε) * RBM.Step2.jS (sample d) (E N) D N (u : ℝ) ω := by rw [hstepF]
  exact hj.trans (hstepD.trans hstepG)

end RBM.Gauss.Step2
