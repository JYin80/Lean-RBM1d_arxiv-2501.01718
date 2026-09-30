/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Gauss.SigmaExhaust
import RBM1D.Gauss.Step3Charges
import RBM1D.Gauss.TraceMoment
import RBM1D.Flow.EnergyUniform
import RBM1D.EnergyN.Gauss.Lemma514NonAlt
import RBM1D.EnergyN.Gauss.Lemma514AltEnd
import RBM1D.EnergyN.Gauss.Lemma514Assemble
import RBM1D.EnergyN.Gauss.Lemma514Moment
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.Step4Gauss

/-!
# Lemma 5.14 for all loop lengths `n ≥ 3`, at an `N`-dependent energy

Two statements of Lemma 5.14, (5.92), at an `N`-dependent energy `E : ℕ → ℝ`, with
`hEκ : ∀ N, |E N| ≤ 2 - κ`:

* `RBM.Gauss.Grid.hend_all_plainN` — the endpoint estimate for all `σ`; it calls
  `endpoint_nonAlt_all_plainN` and `endpoint_alt_all_plainN`, and the combination
  (`sigma_exhaustive_nonAlt`, `StochDom.max`) is energy-free.
* `RBM.Gauss.h514_all_plainN` — Lemma 5.14 for the flow; it calls
  `Grid.etaT_inv_le_of_plainN` and `lemma514_of_endpoint_allN` (whose κ-bound is met by this
  theorem's own `hκ0`, `hEκ`).
-/

open MeasureTheory Filter

namespace RBM.Gauss.Grid

variable (d : Dims)

/-- **The endpoint estimate of Lemma 5.14 for all `σ`**: for `n ≥ 3`, under the premises
`Lemma514PremisesN` with `Λ ≥ 1` eventually, `‖lkT‖ ≺ (Λ^{1/2} + Φ) (W ℓ_v η_v)^{-n}` at every
time `v ∈ [s, t]`. -/
theorem hend_all_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ n : ℕ, 3 ≤ n → ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t n Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) n) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ n)⁻¹) := by
  intro n hn Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have h1 := endpoint_nonAlt_all_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc m hm1 Λ Φ hΛ0 hΦ0
    hΛ1 hprem v hv
  have h2 := endpoint_alt_all_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc m Λ Φ hΛ0 hΦ0 hΛ1
    hprem v hv
  have hcomb := h1.max h2
  have heq : (fun N (q : LoopData ((band d).L N) (m + 2)) ω =>
      max (if SumZeroDyn.NonAlt q.1 then
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0)
          (if q.1 = sigmaAltGen (m + 2) ∨ q.1 = sigmaAltGen' (m + 2)
            then ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0))
      = fun N (q : LoopData ((band d).L N) (m + 2)) ω =>
        ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ := by
    funext N q ω
    set x := ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ with hxdef
    have hx0 : (0 : ℝ) ≤ x := norm_nonneg _
    rcases sigma_exhaustive_nonAlt hm1 q.1 with hna | ⟨-, halt⟩
    · rw [if_pos hna]
      by_cases hc2 : q.1 = sigmaAltGen (m + 2) ∨ q.1 = sigmaAltGen' (m + 2)
      · rw [if_pos hc2, max_self]
      · rw [if_neg hc2, max_eq_left hx0]
    · rw [if_pos halt]
      by_cases hc1 : SumZeroDyn.NonAlt q.1
      · rw [if_pos hc1, max_self]
      · rw [if_neg hc1, max_eq_right hx0]
  rw [heq] at hcomb
  exact hcomb

end RBM.Gauss.Grid

namespace RBM.Gauss

variable (d : Dims)

/-- **Lemma 5.14, (5.92), for the flow, for every `n ≥ 3`**: the conclusion is the eta-expanded
`Step3.Lemma514` family of `lemma514_of_endpoint_allN`, which is the `h514_ge3` argument of
`step4_gauss_of_plainN`. -/
theorem h514_all_plainN (h : TraceMomentBound d) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {E : ℕ → ℝ} (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ n, 3 ≤ n → Step3.Lemma514 (band d).P
      (fun m N u ω => Step3.flowXiLK (sample d) (E N) s t m N u ω)
      (fun m N u ω => Step3.flowXiL (sample d) (E N) s t m N u ω)
      (fun N u => Step3.flowA (band d) (E N) s t N u) n := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hreg1 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [Grid.etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc] with N hN
    rwa [Real.rpow_one]
  exact lemma514_of_endpoint_allN d h hκ0 hEκ hs0 hst ht1 le_rfl hreg1
    (Grid.hend_all_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc)

end RBM.Gauss

section CompatN

open RBM RBM.Gauss

end CompatN

section ConsumerN

open RBM RBM.Gauss

end ConsumerN

