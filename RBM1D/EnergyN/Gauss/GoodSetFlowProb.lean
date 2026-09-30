/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp
import Mathlib.Analysis.Calculus.Deriv.Abs
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.TestFunHerm
import RBM1D.Gauss.WeightedSumSqrt
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Gauss.Lemma514Moment
import RBM1D.Gauss.QVEndpoint
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.MinorDiffCond
import RBM1D.EnergyN.Gauss.Step1Hyp
import RBM1D.EnergyN.Gauss.EntryBoundTime
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.Flow.EnergyUniformReg

/-!
# The good set along the flow with high probability, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: the good set
`goodSetFlow` with `δ = flowDelta` holds with high probability, given the hypotheses of Step 1
(`RBM.GoodSetFlowProb.highProb_goodSetFlow_of_step1N`) or with those hypotheses built inside the
proof (`RBM.GoodSetFlowProb.highProb_goodSetFlowN`).

## The external `κ`

Both take an external `κ` with `hE : ∀ N, |E N| ≤ 2 - κ` and pass it directly into
`Step1.eq58N`/`step1Hyp_gauss_of_scale''N` (both accept an arbitrary external `κ` in this exact
shape); no `κ` is derived from `2 - |E N|`.
-/

namespace RBM.GoodSetFlowProb

open Filter MeasureTheory Set Gauss

noncomputable section

/-- **The good set `goodSetFlow` with `δ = flowDelta` holds with high probability**, from
(2.68)–(2.70) at `s`, the regime condition `Cond272NReg` and the hypotheses of Step 1. The margin
is the external `κ` of `hE`. -/
theorem highProb_goodSetFlow_of_step1N (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    HighProb (P d) (fun N => goodSetFlow d (E N) s t
      (fun N => flowDelta d (E N) t N) N) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have h58 := Step1.eq58N (sample d) hκ0 hE hB hs0 hst ht1 hreg.1
    hStep.scaling (by norm_num) (hStep.lift 2 (by norm_num))
  have hweak := Step1.weakLaw_highProbN (sample d) hE2 hB hs0 hst ht1
    hreg.1 hc hreg.2 h58 hStep.lemma41 hStep.cont
  have hgood : HighProb (P d) (fun N =>
      {ω | ∀ u : TimeIcc s t N,
        ω ∈ Step1.goodEv (sample d) (E N) N (u : ℝ)}) := by
    refine hweak.mono ?_
    filter_upwards [Step1.eventually_scale_factsN (B := band d)
      hE2 hst ht1 hreg.1 hreg.2, eventually_ge_atTop 1]
      with N hf hN ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA : 0 < (band d).scale (E N) N (u : ℝ) :=
      (band d).scale_pos' (hE2 N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hA1 : 1 ≤ (band d).scale (E N) N (u : ℝ) :=
      (Real.one_le_rpow hN1 hc.le).trans (hf u).1
    have hpow : ((band d).scale (E N) N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 4) ≤
        ((band d).scale (E N) N (u : ℝ))⁻¹ ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr hA)
        (inv_le_one_of_one_le₀ hA1) (by norm_num)
    exact (hω u).le.trans hpow
  refine hgood.mono ?_
  filter_upwards with N ω hω
  intro u hu
  let uu : TimeIcc s t N := ⟨u, hu⟩
  exact goodEv_subset_goodSet_flow (hE2 N) hs0 ht1 N uu (hω uu)

/-- **The same conclusion without the hypotheses of Step 1**: `Step1.HypN` is built from the same
`BoundsCoreN` and `Cond272NReg` assumptions, with the external `κ` of `hE`. -/
theorem highProb_goodSetFlowN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s) :
    HighProb (P d) (fun N => goodSetFlow d (E N) s t
      (fun N => flowDelta d (E N) t N) N) := by
  have hStep : Step1.HypN (sample d) E s t :=
    step1Hyp_gauss_of_scale''N d hκ0 hE hB hs0 hst ht1 hreg.1 hc hreg.2
  exact highProb_goodSetFlow_of_step1N d hκ0 hE hs0 hst ht1 hc hreg hB hStep

section Compat

end Compat

end
end RBM.GoodSetFlowProb
