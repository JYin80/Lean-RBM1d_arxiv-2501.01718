/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step4Base
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.EnergyN.Gauss.Step4Base
import RBM1D.EnergyN.Gauss.Lemma514NonAltTwo
import RBM1D.EnergyN.Gauss.Lemma514Two
import RBM1D.EnergyN.Gauss.OneLoopTimeIcc
import RBM1D.EnergyN.Hierarchy.Step45

/-!
# Step 4 for the Gaussian flow from Lemma 5.14, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: Lemma 5.14 at `n = 2`
(`RBM.Gauss.lemma514_two_of_plainN`) and (2.78) for every `n ≥ 1` from the alternating endpoint
estimate at `n = 2` and Lemma 5.14 for `n ≥ 3` (`RBM.Gauss.step4_gauss_of_plainN`).

No energy-dependent constant is fixed in this file: both take the full
`hEκ : ∀ N, |E N| ≤ 2 - κ` of their callees, so no κ-bound needs inserting here.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace Gauss

variable (d : Dims)

/-! ### `N`-form of Lemma 5.14 at `n = 2`, from the two endpoint halves -/

/-- **`Step3.Lemma514 … 2` at an `N`-dependent energy**, from `hendAlt2` (the endpoint estimate at
`n = 2` for the alternating charges) combined with the unconditional non-alternating half
`Grid.endpoint_nonAlt_two_plainN`, via `hend_of_split_twoN` / `lemma514_of_endpoint_twoN`.
`lemma514_of_endpoint_twoN` needs the full κ-bound `hEκ` directly; the weaker `|E N| < 2` is used
only for `Grid.etaT_inv_le_of_plainN`. -/
theorem lemma514_two_of_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hendAlt2 : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : {q : LoopData ((band d).L N) 2 //
              q.1 = Grid.sigmaAltGen 2 ∨ q.1 = Grid.sigmaAltGen' 2}) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹)) :
    Step3.Lemma514 (band d).P (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) 2 := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hreg1 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [Grid.etaT_inv_le_of_plainN (band d) hE2 ht1 hc0 hAc] with N hN
    rwa [Real.rpow_one]
  exact lemma514_of_endpoint_twoN d (traceMomentBound_gauss d) hκ0 hEκ hs0 hst ht1 le_rfl hreg1
    (hend_of_split_twoN d E s t
      (Grid.endpoint_nonAlt_two_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc) hendAlt2)

/-! ### `N`-form of the Step 4 assembly, conditional -/

/-- **(2.78), the conclusion of `Step45.flow_sharpLmKN`, for every `n ≥ 1`**, at an `N`-dependent
energy, from `hendAlt2` and `h514_ge3`. It supplies the inputs of `Step45.flow_sharpLmKN`; the
case `n = 2` of `h514` comes from `lemma514_two_of_plainN` above. -/
theorem step4_gauss_of_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hendAlt2 : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : {q : LoopData ((band d).L N) 2 //
              q.1 = Grid.sigmaAltGen 2 ∨ q.1 = Grid.sigmaAltGen' 2}) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹))
    (h514_ge3 : ∀ n, 3 ≤ n → Step3.Lemma514 (band d).P
      (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) n) :
    ∀ n : ℕ, 1 ≤ n → StochDom (band d).P
      (fun N (p : TimeIcc s t N × LoopData ((band d).L N) n) ω =>
        (sample d).lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => ((band d).scale (E N) N p.1)⁻¹ ^ n) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have h514 : ∀ n, 2 ≤ n → Step3.Lemma514 (band d).P
      (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) n := by
    intro n hn
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact lemma514_two_of_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc hendAlt2
    · exact h514_ge3 n hn3
  have h0 : ∀ m, 1 ≤ m → Step3.S (band d).P
      (fun n N u ω => Step3.flowXiLK (sample d) (E N) s t n N u ω)
      (fun N => Step3.flowAs (band d) (E N) s N) (Step3.flowR (band d) s t)
      (fun N u => Step3.flowA (band d) (E N) s t N u) m 0 :=
    flow_S_zero_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S (band d).P
      (fun n N u ω => Step3.flowXiLK (sample d) (E N) s t n N u ω)
      (fun N => Step3.flowAs (band d) (E N) s N) (Step3.flowR (band d) s t)
      (fun N u => Step3.flowA (band d) (E N) s t N u) m l := by
    intro m l hm1 hm2
    interval_cases m
    · exact flow_S_oneN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc l
    · exact flow_S_two_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc l
  have h1 : StochDom (band d).P (fun N u ω => Step3.flowXiLK (sample d) (E N) s t 1 N u ω)
      fun _ _ _ => 1 :=
    flow_xiLK_one_le_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have h2 : StochDom (band d).P (fun N u ω => Step3.flowXiLK (sample d) (E N) s t 2 N u ω)
      (fun N u _ => Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4)) :=
    flowXiLK_two_le_quarter_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hc : Cond272N (band d) E s t := Step2.cond272_of_plainN hE2 hst ht1 hreg0
  exact Step45.flow_sharpLmKN (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hc h514 h0 h12 h1 h2

end Gauss

end RBM

end

