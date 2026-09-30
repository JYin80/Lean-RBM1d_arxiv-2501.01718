/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma510Fixed
import RBM1D.EnergyN.Gauss.OneLoopSharpGridAll
import RBM1D.EnergyN.Gauss.LoopDecayFixed
import RBM1D.EnergyN.Gauss.GridJStar
import RBM1D.Flow.EnergyUniform

/-!
# The grid good set of Lemma 5.14 with high probability, at an `N`-dependent energy

`Grid.highProb_grid_goodSet514_plainN`: given stochastic bounds on `xiLM` and `xiLKM` along the
grid, with high probability the grid process lies in `goodSet514` at all grid times, at an
`N`-dependent energy `E : ℕ → ℝ`. It fixes no `(mE E).im`/`2−|E|`-shaped constant of its own
before `∀ᶠ N`: it only passes `κ`/`hEκ`/`Cond272N`/`BoundsCoreN` to its callees
(`highProb_grid_xiLK_one_plainN`, `highProb_grid_decaySet_plainN`, `highProb_grid_eq557N`,
`highProb_grid_eq273N`) and to the energy-free defs `xiLM`, `xiLKM`, `goodSet514` (applied at the
concrete real `E N`).
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

theorem highProb_grid_goodSet514_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {E : ℕ → ℝ} (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272N (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (K : ℕ → ℕ) (hK0 : ∀ N, K N ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    (n : ℕ) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) (Λ Φ : ℕ → ℝ)
    (hYΛ : StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
        xiLM d (E N) N (time s t K N k) (H d s t K N k ω) (2 * n + 2)) (fun N _ _ => Λ N))
    (hXΦlt : ∀ m, 1 ≤ m → m < n → StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
        xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) m) (fun N _ _ => Φ N))
    (hXΦprod : ∀ m, 2 ≤ m → m ≤ n → StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
        xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) m
          * xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) (n - m + 2)
          / (band d).scale (E N) N (time s t K N k)) (fun N _ _ => Φ N))
    (hYΦ : StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
        xiLM d (E N) N (time s t K N k) (H d s t K N k ω) (n + 1)) (fun N _ _ => Φ N)) :
    HighProb (Pg d) (fun N => {ω | ∀ k : Fin (K N + 1),
        H d s t K N k ω ∈ goodSet514 d (E N) N (time s t K N k) n ε (Λ N) (Φ N) τ D
          ((band d).ell N (s N))}) := by
  have h1 := hYΛ.highProb hε
  have h4 := hYΦ.highProb hε
  have h5 := highProb_grid_xiLK_one_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    K hK0 hC0 hKcard hε
  have h6 := highProb_grid_decaySet_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
    (2 * n + 2) hτ hD K hK0 hC0 hKcard
  have h7 := highProb_grid_eq557N d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc K hK0 hC0 hKcard τ hτ
  have h8 := highProb_grid_eq273N d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hAc K hK0 hC0 hKcard
    (2 * n + 2) (by omega) τ hτ
  have h2 := highProb_biInter_finset (P := Pg d) (Finset.Ico 1 n)
    (fun m N => {ω : Ωg d | ∀ k : Fin (K N + 1),
      xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) m ≤ (N : ℝ) ^ ε * Φ N})
    (fun m hm => by
      rw [Finset.mem_Ico] at hm
      exact (hXΦlt m hm.1 hm.2).highProb hε)
  have h3 := highProb_biInter_finset (P := Pg d) (Finset.Icc 2 n)
    (fun m N => {ω : Ωg d | ∀ k : Fin (K N + 1),
      xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) m
          * xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) (n - m + 2)
          / (band d).scale (E N) N (time s t K N k)
        ≤ (N : ℝ) ^ ε * Φ N})
    (fun m hm => by
      rw [Finset.mem_Icc] at hm
      exact (hXΦprod m hm.1 hm.2).highProb hε)
  have hcomb := ((((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7).inter h8
  refine hcomb.mono (Filter.Eventually.of_forall fun N ω hω k => ?_)
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hω
  obtain ⟨⟨⟨⟨⟨⟨⟨hω1, hω2⟩, hω3⟩, hω4⟩, hω5⟩, hω6⟩, hω7⟩, hω8⟩ := hω
  have hk1 : time s t K N k ≤ 1 :=
    ((mem_Icc_time s t K N k (hs0 N) (hst N) (Nat.lt_succ_iff.mp k.isLt)).2.trans
      (ht1 N).le)
  have hXi : xiLKM d (E N) N (time s t K N k) (H d s t K N k ω) 1 ≤ (N : ℝ) ^ ε :=
    xiLKM_one_le_of_forall d hk1 _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hω5 k)
  simp only [goodSet514, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hω1 k, fun m hm1 hm2 => hω2 m (Finset.mem_Ico.2 ⟨hm1, hm2⟩) k⟩,
    fun m hm1 hm2 => hω3 m (Finset.mem_Icc.2 ⟨hm1, hm2⟩) k⟩, hω4 k⟩,
    hXi⟩, (hω6 k).1⟩, (hω6 k).2⟩, hω7 k⟩, hω8 k⟩

end RBM.Gauss.Grid

end
