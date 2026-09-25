/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.APrimeGoodSetFlowGeneralDims
import RBM1D.Hierarchy.Step2Moment

/-!
# T1502: `jG ≤ N^{2ε} jS` on one high-probability event

Formalization of the chain named in `docs/reports/T1499-prove.md` §"Target (T2)", paragraph
"Satisfiability of `h560'`": for every `d : Gauss.Dims` under the Step-1 hypotheses (the
hypothesis list of `RBM.Gauss.step1Hyp_gauss_of_scale''`), the block-resolved witness
`RBM.APrimeJG.jG` is at most `N^{2ε} · RBM.Step2.jS` with high probability, for every `ε > 0`.

## Route

`RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow` already proves, for every `τ > 0`, on one
high-probability event,

  `jG ≤ 1 + N^τ (9 e^{√3} jS + 2)`,

by exactly the chain the ticket names: `gsqBlk ≤ max_{x'∼x} gmBlk(x',y)²`
(`RBM.APrimeJG.jG_le_of_neighbor_green_sq`); (4.2) for the Gaussian flow
(`RBM.Gauss.entry_bound_gauss`, assembled along the flow with a floor by
`RBM.Gauss.entryBoundFlow_floor`); the neighbour `K ≤ W^{-D}` absorbed into that same floor
(`RBM.Gauss.stochDom_ldeRow_flow_floor`/`stochDom_ldeCol_flow_floor`, the (5.30) route); and the
nine shifted terms costing only a factor `9 e^{√3}` via `tailT_sub_le`
(`RBM.APrimeJG.tailT_shift_three`).

What remains here is real analysis: absorb the additive `1` and the fixed constant
`9 e^{√3} + 3` into a single `N^ε` factor, using `1 ≤ jS` (`RBM.Step2Moment.one_le_jS`) and
`N^ε → ∞`. This uses no new probabilistic input and no hypothesis beyond the Step-1 list, `D`,
and `ε`; `jStar` does not appear.

## Main result

* `RBM.Gauss.Step2.highProb_jG_le_jS` — (T1).
-/

namespace RBM.Gauss.Step2

open Filter MeasureTheory Set RBM RBM.Gauss

/-- **(T1): the block-resolved `jG` is at most `N^{2ε} · jS` with high probability.**

For every `d : Gauss.Dims` under the Step-1 hypotheses (the hypothesis list of
`RBM.Gauss.step1Hyp_gauss_of_scale''`), for every `D ≥ 0` and every `ε > 0`: with high
probability, for every `u ∈ [s_N, t_N]`, `RBM.APrimeJG.jG ≤ N^{2ε} · RBM.Step2.jS`.

This composes `RBM.APrimeJG.highProb_jG_le_of_entryBoundFlow` (`jG ≤ 1 + N^ε (9 e^{√3} jS + 2)`
on one high-probability event) with `1 ≤ jS` (`RBM.Step2Moment.one_le_jS`) to absorb the
additive `1` and the fixed constant `9 e^{√3} + 3` into a single `N^ε` factor, so that the
overall loss is `N^ε · N^ε = N^{2ε}`. -/
theorem highProb_jG_le_jS (d : Dims) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      APrimeJG.jG (sample d) E N (u : ℝ) ω ((band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D ≤
      (N : ℝ) ^ (2 * ε) * RBM.Step2.jS (sample d) E D N (u : ℝ) ω}) := by
  have hE2 : |E| < 2 := by linarith
  have hCond272Reg : Cond272Reg (band d) E s t c := ⟨hcond, hreg⟩
  have hGoodHP : HighProb (P d) (goodSetFlow d E s t (flowDelta d E t)) :=
    APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow d hE2 hs0 hst ht1 hc0 hCond272Reg hB
  have hEntry : EntryBoundFlow' d E s t (fun N => 2 * (N : ℝ) ^ (-D)) :=
    entryBoundFlow_floor d hE2 hs0 hst ht1 (K := 1) zero_le_one
      (rpow_neg_one_le_etaT_of_scale_ge d hE2 ht1 hc0 hreg) (c₀ := c / 6) (by linarith)
      (flowDelta_le_rpow_neg d hreg) (B := D) hD
  have hHP := APrimeJG.highProb_jG_le_of_entryBoundFlow d hE2 hs0 hst ht1 hcond D hD
    hEntry hGoodHP hε
  refine hHP.mono ?_
  filter_upwards [eventually_le_rpow (3 + 9 * Real.exp (Real.sqrt 3)) hε,
    Filter.eventually_ge_atTop (1 : ℕ)] with N hAle hN1 ω hω u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNε1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1' hε.le
  have hNε0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := by linarith
  have hJ : (1 : ℝ) ≤ RBM.Step2.jS (sample d) E D N (u : ℝ) ω :=
    Step2Moment.one_le_jS (sample d) (E := E) (D := D) N (u : ℝ) ω
  have hJ0 : (0 : ℝ) ≤ RBM.Step2.jS (sample d) E D N (u : ℝ) ω := le_trans zero_le_one hJ
  have hj := hω u
  have hstepA : (3 : ℝ) * (N : ℝ) ^ ε ≤
      (3 : ℝ) * (N : ℝ) ^ ε * RBM.Step2.jS (sample d) E D N (u : ℝ) ω := by
    have h := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ) ^ ε)
    simpa using h
  have hstepC : (1 : ℝ) + 2 * (N : ℝ) ^ ε ≤
      (3 : ℝ) * (N : ℝ) ^ ε * RBM.Step2.jS (sample d) E D N (u : ℝ) ω :=
    (show (1 : ℝ) + 2 * (N : ℝ) ^ ε ≤ 3 * (N : ℝ) ^ ε by linarith).trans hstepA
  have hstepD : (1 : ℝ) + (N : ℝ) ^ ε *
      (9 * Real.exp (Real.sqrt 3) * RBM.Step2.jS (sample d) E D N (u : ℝ) ω + 2) ≤
      (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
        RBM.Step2.jS (sample d) E D N (u : ℝ) ω) := by
    have hexpand1 : (N : ℝ) ^ ε *
        (9 * Real.exp (Real.sqrt 3) * RBM.Step2.jS (sample d) E D N (u : ℝ) ω + 2)
        = (N : ℝ) ^ ε * (9 * Real.exp (Real.sqrt 3) *
            RBM.Step2.jS (sample d) E D N (u : ℝ) ω) + 2 * (N : ℝ) ^ ε := by ring
    have hexpand2 : (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
        RBM.Step2.jS (sample d) E D N (u : ℝ) ω)
        = (N : ℝ) ^ ε * (9 * Real.exp (Real.sqrt 3) *
            RBM.Step2.jS (sample d) E D N (u : ℝ) ω)
          + 3 * (N : ℝ) ^ ε * RBM.Step2.jS (sample d) E D N (u : ℝ) ω := by ring
    rw [hexpand1, hexpand2]
    linarith [hstepC]
  have hstepE : (N : ℝ) ^ ε * (3 + 9 * Real.exp (Real.sqrt 3)) ≤ (N : ℝ) ^ ε * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_left hAle hNε0
  have hstepF : (N : ℝ) ^ ε * (N : ℝ) ^ ε = (N : ℝ) ^ (2 * ε) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hstepG : (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
      RBM.Step2.jS (sample d) E D N (u : ℝ) ω) ≤
      (N : ℝ) ^ (2 * ε) * RBM.Step2.jS (sample d) E D N (u : ℝ) ω := by
    have h := mul_le_mul_of_nonneg_right hstepE hJ0
    calc (N : ℝ) ^ ε * ((3 + 9 * Real.exp (Real.sqrt 3)) *
          RBM.Step2.jS (sample d) E D N (u : ℝ) ω)
        = ((N : ℝ) ^ ε * (3 + 9 * Real.exp (Real.sqrt 3))) *
          RBM.Step2.jS (sample d) E D N (u : ℝ) ω := by ring
      _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ ε) * RBM.Step2.jS (sample d) E D N (u : ℝ) ω := h
      _ = (N : ℝ) ^ (2 * ε) * RBM.Step2.jS (sample d) E D N (u : ℝ) ω := by rw [hstepF]
  exact hj.trans (hstepD.trans hstepG)

end RBM.Gauss.Step2
