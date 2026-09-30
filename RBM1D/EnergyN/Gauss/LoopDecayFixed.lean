/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LoopDecayFixed
import RBM1D.EnergyN.Hierarchy.LKDecayQuant
import RBM1D.EnergyN.Gauss.Step2Gauss
import RBM1D.Flow.EnergyUniform

/-!
# The decay sets of the loops with high probability, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: with high probability the flow lies in
`decaySet` and `lkDecaySet` at all times `v ∈ [s, t]`
(`RBM.Gauss.Grid.highProb_flow_decaySet_plainN`), and the grid process lies in them at all grid
times (`RBM.Gauss.Grid.highProb_grid_decaySet_plainN`).

## The external `κ`

The proof of `highProb_flow_decaySet_plainN` needs `2 * (max 1 (mE (E N)).im⁻¹) ^ m₀ ≤ N` for
large `N`, via `tendsto_natCast_atTop_atTop.eventually_ge_atTop`. The theorem takes the pair
`κ`/`hEκ : ∀ N, |E N| ≤ 2 - κ`, derives the `N`-independent bound
`mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N` (`κ' := min κ 1`, `mE_im_ge`,
`Flow/Scales.lean`), applies the same helper to the fixed constant `2 * (max 1 mκ⁻¹) ^ m₀`, and
transfers the bound to `2 * (max 1 (mE (E N)).im⁻¹) ^ m₀` by antitonicity.
`mem_decaySets_of_lre` (energy-free) is applied at `E N`.

`highProb_grid_decaySet_plainN` fixes no energy-dependent constant of its own: it is a one-line
corollary of `highProb_flow_decaySet_plainN` via the generic (`E`-free) transfer lemma
`Grid.highProb_grid_of_flow`, and its deterministic ingredients (`decaySet`, `lkDecaySet`,
`measurableSet_decaySet`, `measurableSet_lkDecaySet`, `time`, `H`) are energy-free.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

section HighProbT5N

open LKDecayQuant

/-- **With high probability `Hflow v ∈ decaySet ∩ lkDecaySet` for all `v ∈ [s, t]`.** The
constant `2 * (max 1 (mE (E N)).im⁻¹) ^ m₀` is bounded by the uniform `2 * (max 1 mκ⁻¹) ^ m₀`
(`κ' := min κ 1`, `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N`, by `mE_im_ge`). -/
theorem highProb_flow_decaySet_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (m₀ : ℕ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) :
    HighProb (P d) (fun N => {ω | ∀ v : TimeIcc s t N,
      Hflow d N (v : ℝ) ω ∈ decaySet d (E N) N m₀ (v : ℝ) τ D ∧
        Hflow d N (v : ℝ) ω ∈ lkDecaySet d (E N) N m₀ (v : ℝ) τ D}) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have h12 : Steps12N (sample d) E s t :=
    steps12_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hFD := highProb_flowDec_of_aprioriDecayN (B := band d) (X := sample d) hκ0 hEκ hs0 ht1
    (τ := τ / 2) (by linarith) (c := 2 * (D + 2 * (m₀ : ℝ) + 1) + 2) (by positivity)
    h12.aprioriDecay
  refine hFD.mono ?_
  have hWN : ∀ᶠ N : ℕ in atTop, (d.W N : ℝ) ≤ N := by
    filter_upwards [(band d).dim] with N hN
    have h : d.W N ≤ d.W N * d.L N :=
      Nat.le_mul_of_pos_right _ (by have := d.three_le_L N; omega)
    exact_mod_cast h.trans hN.1
  have hWlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N := by
    filter_upwards [(band d).bandwidth, eventually_ge_atTop 1] with N hN hN1
    refine le_trans ?_ hN
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
      (by linarith [(band d).c_pos])
  have h2m : ∀ᶠ N : ℕ in atTop, 2 * (m₀ : ℝ) ≤ (N : ℝ) ^ (τ / 2 / 2) := by
    filter_upwards [SumZeroDyn.eventually_const_mul_rpow_le (2 * (m₀ : ℝ))
      (show (0 : ℝ) < τ / 2 / 2 by linarith)] with N hN
    simpa using hN
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (τ / 2 / 2) := by
    filter_upwards [SumZeroDyn.eventually_const_mul_rpow_le 2
      (show (0 : ℝ) < τ / 2 / 2 by linarith)] with N hN
    simpa using hN
  -- The fixed constant `2 * (max 1 (mE E).im⁻¹) ^ m₀` becomes the uniform `κ`-bound.
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'2 : κ' ≤ 2 := (min_le_right κ 1).trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hEκ N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκ0 : 0 < mκ := by rw [hmκdef]; positivity
  have hm : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hCκ : ∀ N, 2 * (max 1 ((mE (E N)).im)⁻¹) ^ m₀ ≤ 2 * (max 1 mκ⁻¹) ^ m₀ := fun N =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (max_le_max le_rfl (inv_anti₀ hmκ0 (hm N))) m₀)
      (by norm_num)
  have hCE' : ∀ᶠ N : ℕ in atTop, 2 * (max 1 mκ⁻¹) ^ m₀ ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hCE : ∀ᶠ N : ℕ in atTop, 2 * (max 1 ((mE (E N)).im)⁻¹) ^ m₀ ≤ (N : ℝ) := by
    filter_upwards [hCE'] with N hN using (hCκ N).trans hN
  have hexp := SumZeroDyn.eventually_exp_small (2 * cKbound m₀)
    (((2 * cKexp m₀ : ℕ) : ℝ) + D) (cZero / 2) (by have := cZero_pos; linarith)
    (show (0 : ℝ) < τ / 2 / 2 by linarith)
  filter_upwards [eventually_ge_atTop 1, eventually_L_le (B := band d), hWN, hWlow, h2m, h2,
    hCE, hexp] with N hN1 hLN hWNN hWlowN h2mN h2N hCEN hexpN
  intro ω hω v
  have hv0 : 0 ≤ (v : ℝ) := le_trans (hs0 N) v.2.1
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (ht1 N)
  exact mem_decaySets_of_lre d (hE2 N) m₀ hτ hD hv0 hv1 (Hflow d N (v : ℝ) ω)
    ((sample d).hermitian N (v : ℝ) ω) hN1 hLN hWNN hWlowN h2mN h2N hCEN hexpN
    (fun a b hab => hω v a b hab)

/-- **The grid form of `highProb_flow_decaySet_plainN`.** No energy-dependent constant is fixed
here: a one-line corollary of `highProb_flow_decaySet_plainN` via the generic (`E`-free)
transfer lemma `highProb_grid_of_flow`. -/
theorem highProb_grid_decaySet_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (m₀ : ℕ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
      H d s t K N k ω ∈ decaySet d (E N) N m₀ (time s t K N k) τ D ∧
        H d s t K N k ω ∈ lkDecaySet d (E N) N m₀ (time s t K N k) τ D}) :=
  highProb_grid_of_flow d s t K hs0 hst hK0 hC0 hKcard
    (fun N v => decaySet d (E N) N m₀ v τ D ∩ lkDecaySet d (E N) N m₀ v τ D)
    (fun N v => (measurableSet_decaySet d (E N) N m₀ v τ D).inter
      (measurableSet_lkDecaySet d (E N) N m₀ v τ D))
    (highProb_flow_decaySet_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc m₀ hτ hD)

end HighProbT5N

end RBM.Gauss.Grid

end
