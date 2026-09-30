/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Two
import RBM1D.EnergyN.Gauss.Lemma514Assemble

/-!
# Lemma 5.14 for loops of length two, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`:

* `lemma514_of_endpoint_twoN` — Lemma 5.14 at `n = 2` from its endpoint estimate, the `n = 2`
  analogue of `RBM.Gauss.lemma514_of_endpointN` (`RBM1D/EnergyN/Gauss/Lemma514Assemble.lean`),
  with the same κ-bound (via `hKb_flowN`) and without `hn : 3 ≤ n`.
* `hend_of_split_twoN` — the length-two endpoint estimate from its non-alternating and
  alternating parts; no bound on `E` is needed (as for `fixedTimeFAStatement_provedN`,
  `RBM1D/EnergyN/Gauss/DetFlucAvgComplete.lean`).

`RBM.Gauss.Grid.sigma_split_two` (the pure `Fin 2 → Bool` combinatorics helper) carries no energy
binder at all.
-/

open MeasureTheory Filter

namespace RBM.Gauss

theorem lemma514_of_endpoint_twoN (d : Dims) (h : TraceMomentBound d) {E : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc1 : 1 ≤ c)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ c)
    (hend : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) 2) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹)) :
    Step3.Lemma514 (band d).P (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) 2 := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by have := hE N; linarith
  have hκ0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ1 : min κ 1 ≤ 1 := min_le_right _ _
  have hEκ : ∀ N, |E N| ≤ 2 - min κ 1 := fun N => by
    have hmin : min κ 1 ≤ κ := min_le_left _ _
    have := hE N
    linarith
  have hn1 : 1 ≤ 2 := by norm_num
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hcn1 : c ≤ c * (2 : ℝ) + 1 := by nlinarith
  have hcn2 : (1 : ℝ) ≤ c * (2 : ℝ) + 1 := by nlinarith
  have hcn3 : (2 : ℝ) ≤ c * (2 : ℝ) + 1 := by nlinarith
  obtain ⟨Ξ, hΞ, hXΞ0⟩ := exists_highProb_normX d h (le_refl (2 : ℝ))
  refine lemma514_of_seqN (sample d) hE2 hs0 hst ht1 (card_loopData_le 2)
    (show (0 : ℝ) ≤ (c * (2 : ℝ) + 1) * (3 * (2 : ℝ) + 4) + 1 by nlinarith)
    (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num) hΞ
    (hHol_flowN d hE2 hs0 ht1 hcn2 hn1 (eventually_le_rpow_mono hcn1 hreg) ?_
      (hKb_flowN (band d) hκ0 hκ1 hEκ ht1 hc0 2 hreg))
    hend
  filter_upwards [hXΞ0, eventually_ge_atTop 1] with N hN hN1 ω hω
  exact (hN ω hω).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hcn3)

theorem hend_of_split_twoN (d : Dims) (E : ℕ → ℝ) (s t : ℕ → ℝ)
    (hEndNonAlt : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : {q : LoopData ((band d).L N) 2 // q.1 0 = q.1 1}) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹))
    (hEndAlt : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : {q : LoopData ((band d).L N) 2 //
              q.1 = Grid.sigmaAltGen 2 ∨ q.1 = Grid.sigmaAltGen' 2}) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹)) :
    ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) 2) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹) := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hPrem v hv
  have h1 := hEndNonAlt Λ Φ hΛ0 hΦ0 hΛ1 hPrem v hv
  have h2 := hEndAlt Λ Φ hΛ0 hΦ0 hΛ1 hPrem v hv
  refine StochDom.of_subset_union h1 h2 (fun τ hτ => ⟨τ, hτ, ?_⟩)
  filter_upwards with N
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  rcases Grid.sigma_split_two q.1 with hs | hs | hs
  · exact Or.inl ⟨⟨q, hs⟩, hq⟩
  · exact Or.inr ⟨⟨q, Or.inl hs⟩, hq⟩
  · exact Or.inr ⟨⟨q, Or.inr hs⟩, hq⟩

end RBM.Gauss

section CompatN

open RBM RBM.Gauss

end CompatN
