/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PPGoodEvent
import RBM1D.EnergyN.Gauss.OneLoopSharpGridAll
import RBM1D.EnergyN.Gauss.LoopDecayFixed
import RBM1D.EnergyN.Gauss.GridJStar
import RBM1D.Flow.EnergyUniform

/-!
# The good event of the `(+,+)` route with high probability, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: `Grid.highProb_grid_goodSetPP_plainN`
(the grid process lies in `goodSetPP` at all grid times) and `Grid.highProb_init_ppN` (the
initial bound). Neither fixes an `(mE E).im`/`2−|E|`-shaped constant of its own before `∀ᶠ N`:
each only passes `κ`/`hEκ`/`Cond272N`/`BoundsCoreN` (or, for `highProb_init_ppN`, the plain
`hE : ∀ N, |E N| < 2`) to its callees (`highProb_grid_xiLK_one_plainN`,
`highProb_grid_decaySet_plainN`; `highProb_grid_eq273N`) or to a `BoundsCoreN.LmK` structure
field.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

theorem highProb_grid_goodSetPP_plainN {κ : ℝ} {E : ℕ → ℝ} {c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s t K N k ω ∈ goodSetPP d (E N) N (time s t K N k) ε ((band d).ell N (s N)) D}) := by
  have h1 := highProb_grid_xiLK_one_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    K hK0 hC0 hKcard hε
  have h2 := highProb_grid_eq273N d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc K hK0 hC0 hKcard
    3 (by norm_num) ε hε
  have h3 := highProb_grid_eq273N d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc K hK0 hC0 hKcard
    6 (by norm_num) ε hε
  have h4 := highProb_grid_decaySet_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    6 hε hD K hK0 hC0 hKcard
  have hcomb := ((h1.inter h2).inter h3).inter h4
  refine hcomb.mono ?_
  filter_upwards with N ω hω k
  obtain ⟨⟨⟨hω1, hω2⟩, hω3⟩, hω4⟩ := hω
  exact ⟨⟨⟨⟨hω1 k, hω2 k⟩, hω3 k⟩, (hω4 k).1⟩, (hω4 k).2⟩

theorem highProb_init_ppN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    HighProb (Pg d) (fun N => {ω |
      JPP d (E N) N (time s t K N 0) (H d s t K N 0 ω) ≤ (N : ℝ) ^ ε}) := by
  have hLmK := hB.LmK 2 (by norm_num)
  have hHP := hLmK.highProb hε
  have hscale : ∀ᶠ N : ℕ in atTop, 0 < (band d).scale (E N) N (s N) := by
    filter_upwards with N
    exact (band d).scale_pos' (hE N) N (hs0 N) ((hst N).trans_lt (ht1 N))
  have Gflow : HighProb (P d)
      (fun N => {ω | JPP d (E N) N (s N) (Hflow d N (s N) ω) ≤ (N : ℝ) ^ ε}) := by
    refine hHP.mono ?_
    filter_upwards [hscale] with N hNscale ω hω
    have hle : Finset.univ.sup' Finset.univ_nonempty
        (fun a : LoopArg (d.L N) 2 => lkErrMat d (E N) N (s N) (Hflow d N (s N) ω)
          (LoopData.idx (sigPP, a))) ≤ (N : ℝ) ^ ε * ((band d).scale (E N) N (s N))⁻¹ ^ 2 := by
      refine Finset.sup'_le _ _ fun a _ => ?_
      have hlk : lkErrMat d (E N) N (s N) (Hflow d N (s N) ω) (LoopData.idx (sigPP, a)) ≤
          (N : ℝ) ^ ε * ((band d).scale (E N) N (s N))⁻¹ ^ 2 :=
        hω (sigPP, a)
      exact hlk
    have hstep : (band d).scale (E N) N (s N) ^ 2 * Finset.univ.sup' Finset.univ_nonempty
          (fun a : LoopArg (d.L N) 2 => lkErrMat d (E N) N (s N) (Hflow d N (s N) ω)
            (LoopData.idx (sigPP, a)))
        ≤ (band d).scale (E N) N (s N) ^ 2 *
          ((N : ℝ) ^ ε * ((band d).scale (E N) N (s N))⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have heq2 : (band d).scale (E N) N (s N) ^ 2 *
        ((N : ℝ) ^ ε * ((band d).scale (E N) N (s N))⁻¹ ^ 2) = (N : ℝ) ^ ε := by
      have hne : (band d).scale (E N) N (s N) ≠ 0 := hNscale.ne'
      field_simp
    unfold JPP
    rw [heq2] at hstep
    exact hstep
  intro D' hD'
  filter_upwards [Gflow D' hD'] with N hN
  have hHmeas : Measurable (H d s t K N 0) :=
    (H_measurable_filt d s t K N 0).mono ((filt d).le 0) le_rfl
  have hHflowmeas : Measurable (Hflow d N (s N)) := RBM.measurable_H (sample d) N (s N)
  have hSmeas :
      MeasurableSet {M : Matrix (d.Idx N) (d.Idx N) ℂ | JPP d (E N) N (s N) M ≤ (N : ℝ) ^ ε} :=
    measurableSet_le (measurable_JPP d (E N) N (s N)) measurable_const
  have heq : (Pg d) {ω | JPP d (E N) N (time s t K N 0) (H d s t K N 0 ω) ≤ (N : ℝ) ^ ε}ᶜ
      = (P d) {ω' | JPP d (E N) N (s N) (Hflow d N (s N) ω') ≤ (N : ℝ) ^ ε}ᶜ := by
    rw [time_zero]
    change (Pg d) ((H d s t K N 0) ⁻¹'
        {M | JPP d (E N) N (s N) M ≤ (N : ℝ) ^ ε})ᶜ
      = (P d) ((Hflow d N (s N)) ⁻¹' {M | JPP d (E N) N (s N) M ≤ (N : ℝ) ^ ε})ᶜ
    rw [← Set.preimage_compl, ← Set.preimage_compl,
      ← Measure.map_apply hHmeas hSmeas.compl, ← Measure.map_apply hHflowmeas hSmeas.compl,
      map_H_eq s t K N 0 (hs0 N) (hst N) (hK0 N), time_zero]
  rw [heq]
  exact hN

end RBM.Gauss.Grid

end
