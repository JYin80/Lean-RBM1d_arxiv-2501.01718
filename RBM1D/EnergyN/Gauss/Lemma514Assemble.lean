/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.EnergyN.Gauss.Lemma514Holder
import RBM1D.EnergyN.Gauss.Lemma514Moment

/-!
# Lemma 5.14 from its endpoint estimate, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: Lemma 5.14, (5.92), for the flow, for one
loop length `n ≥ 3` (`RBM.Gauss.lemma514_of_endpointN`) and for all `n ≥ 3`
(`RBM.Gauss.lemma514_of_endpoint_allN`), from the endpoint estimate `hend` at every time.

## The external `κ`

The proofs use `RBM.Gauss.hKb_flowN` (`RBM1D/EnergyN/Gauss/Lemma514Holder.lean`), which takes the
spectral gap `κ` externally (`∀ N, |E N| ≤ 2 - κ`): the constant of the kernel bound depends on
the gap and must be fixed before `∀ᶠ N`. So both theorems take
`{κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)`. `κ` is capped at `1` internally, which only
weakens the hypothesis, so no `κ ≤ 1` is assumed.
-/

open MeasureTheory Filter

namespace RBM.Gauss

/-- **Lemma 5.14, (5.92), for the flow, at one loop length `n ≥ 3`**: the endpoint estimate
`hend` (`‖lkT‖ ≺ (Λ^{1/2} + Φ) (W ℓ_v η_v)^{-n}` at every `v ∈ [s, t]` under the premises
`Lemma514PremisesN`) gives the family `Step3.Lemma514` at `n`, when `η_t⁻¹ ≤ N^c` eventually. The
margin is the external `κ` (see the module docstring). -/
theorem lemma514_of_endpointN (d : Dims) (h : TraceMomentBound d) {E : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {n : ℕ} (hn : 3 ≤ n) {c : ℝ} (hc1 : 1 ≤ c)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ c)
    (hend : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514PremisesN (sample d) E s t n Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) n) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖)
          (fun N _ _ =>
            (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ n)⁻¹)) :
    Step3.Lemma514 (band d).P (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) n := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by have := hE N; linarith
  have hκ0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ1 : min κ 1 ≤ 1 := min_le_right _ _
  have hEκ : ∀ N, |E N| ≤ 2 - min κ 1 := fun N => by
    have hmin : min κ 1 ≤ κ := min_le_left _ _
    have := hE N
    linarith
  have hn1 : 1 ≤ n := by omega
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hcn1 : c ≤ c * (n : ℝ) + 1 := by
    nlinarith [mul_nonneg hc0 (show (0 : ℝ) ≤ (n : ℝ) - 1 by linarith)]
  have hcn2 : (1 : ℝ) ≤ c * (n : ℝ) + 1 := by
    nlinarith [mul_nonneg hc0 (show (0 : ℝ) ≤ (n : ℝ) by linarith)]
  have hcn3 : (2 : ℝ) ≤ c * (n : ℝ) + 1 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ c - 1 by linarith)
      (show (0 : ℝ) ≤ (n : ℝ) - 3 by linarith)]
  obtain ⟨Ξ, hΞ, hXΞ0⟩ := exists_highProb_normX d h (le_refl (2 : ℝ))
  refine lemma514_of_seqN (sample d) hE2 hs0 hst ht1 (card_loopData_le n)
    (show (0 : ℝ) ≤ (c * (n : ℝ) + 1) * (3 * (n : ℝ) + 4) + 1 by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ c * (n : ℝ) + 1 by linarith)
        (show (0 : ℝ) ≤ 3 * (n : ℝ) + 4 by linarith)])
    (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num) hΞ
    (hHol_flowN d hE2 hs0 ht1 hcn2 hn1 (eventually_le_rpow_mono hcn1 hreg) ?_
      (hKb_flowN (band d) hκ0 hκ1 hEκ ht1 hc0 n hreg))
    hend
  filter_upwards [hXΞ0, eventually_ge_atTop 1] with N hN hN1 ω hω
  exact (hN ω hω).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hcn3)

/-- **The same for every `n ≥ 3`**, from the endpoint estimate at every `n ≥ 3`. Same κ-bound. -/
theorem lemma514_of_endpoint_allN (d : Dims) (h : TraceMomentBound d) {E : ℕ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc1 : 1 ≤ c)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ c)
    (hend : ∀ n : ℕ, 3 ≤ n → ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t n Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) n) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖)
          (fun N _ _ =>
            (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ n)⁻¹)) :
    ∀ n : ℕ, 3 ≤ n → Step3.Lemma514 (band d).P
      (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) n := by
  intro n hn
  exact lemma514_of_endpointN d h hκ hE hs0 hst ht1 hn hc1 hreg (hend n hn)

end RBM.Gauss

section Compat

open RBM RBM.Gauss

end Compat
