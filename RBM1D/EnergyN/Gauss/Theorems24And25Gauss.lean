/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.EnergyN.Flow.Thm221Gain
import RBM1D.EnergyN.Gauss.Thm221RegGauss
import RBM1D.Gauss.Theorem22Gauss

/-!
# Energy-uniform Theorems 2.4 and 2.5 for the Gaussian model

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.4 ((2.6)–(2.9)) and Theorem 2.5 ((2.12)/(2.13)) for the true-path Gaussian
model `RBM.Gauss.sample d`, along arbitrary sequences of spectral parameters / energies.

The statements use `SpecSeqN` at an energy `E : ℕ → ℝ`, and the proofs apply the consumers
`…_of_Thm221N'` to `(thm221RegN_gauss d hκ).toThm221N' hκ`. The energy-uniform Theorem 2.21
producer `thm221RegN_gauss` is discharged internally; no statement has a
`Thm221NReg`/`Thm221N'` hypothesis.

## Main results

* `quantumDiffusion_gaussN` — **Theorem 2.4** for any `SpecSeqN κ τ E z` data.
* `quantumDiffusion_gaussN_of_z` — **Theorem 2.4** for any sequence `z` in the domain
  (`0 < Im z ≤ 1`, `|Re z| ≤ 2 − κ`, eventually `N^{-1+τ} ≤ Im z`); no energy binder.
* `theorem2_5_gaussN` — **Theorem 2.5, paper form**: hypotheses `κ > 0`, `0 < τ < c/2` (2.11),
  and `|E N| ≤ 2 − κ` for every `N`.

The per-sequence form is equivalent to the uniform one by
`RBM.eventually_forall_of_forall_sequences` (`docs/PAPER-VS-LEAN.md` §2.8).
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix

/-! ### Theorem 2.4 -/

/-- **Theorem 2.4 (quantum diffusion) for the Gaussian model, along an energy sequence.**
The four conclusions are (2.6)–(2.9); the proof is `RBM.quantumDiffusion_of_Thm221N'` at
`(thm221RegN_gauss d hκ).toThm221N' hκ`. -/
theorem quantumDiffusion_gaussN (d : Dims) {κ τ : ℝ} {E : ℕ → ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hτ : 0 < τ) (hz : SpecSeqN κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) :=
  quantumDiffusion_of_Thm221N' (transfer_gauss d) hκ ((thm221RegN_gauss d hκ).toThm221N' hκ)
    hτ hz hτ' hD

/-- **Theorem 2.4 for the Gaussian model, for an arbitrary sequence of spectral parameters** in
the domain of Theorem 2.3 (no energy binder). The conclusions are those of
`quantumDiffusion_gaussN`. -/
theorem quantumDiffusion_gaussN_of_z (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 2 <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.1 *
            green ((transfer_gauss d).Hband N ω) (z N) *
              Eblk ((band d).L N) ((band d).W N) ab.2).trace -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              (green ((transfer_gauss d).Hband N ω) (z N))ᴴ *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta ((band d).L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) ∧
    (∀ᶠ N : ℕ in atTop, ∀ ab : ZMod ((band d).L N) × ZMod ((band d).L N),
      ‖(∫ ω, (green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.1 *
              green ((transfer_gauss d).Hband N ω) (z N) *
                Eblk ((band d).L N) ((band d).W N) ab.2).trace ∂(band d).P) -
          ((band d).W N : ℂ)⁻¹ * msc (z N) ^ 2 *
            Theta ((band d).L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ 3) :=
  quantumDiffusion_gaussN d hκ hτ (SpecSeqN.of_z him_pos him_le_one habs_re him_ge) hτ' hD

/-! ### Theorem 2.5 -/

/-- **Theorem 2.5 (QUE) for the Gaussian model, paper form** ((2.11)–(2.13)): for every `κ > 0`,
every `0 < τ < c/2` and every bulk energy sequence `|E N| ≤ 2 − κ`. No `SpecSeqN` hypothesis.
The conclusions are the bounds (2.12) and (2.13) on the events `queEvent212`, `queEvent213`. -/
theorem theorem2_5_gaussN (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ0 : 0 < τ)
    (hτ : τ < (band d).c / 2) (E : ℕ → ℝ) (hE : ∀ N, |E N| ≤ 2 - κ) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod ((band d).L N),
      (band d).P (queEvent212 ((transfer_gauss d).hermitian N) a (E N)
          ((band d).queEtaN τ N) (((band d).size N : ℝ) ^ (-(τ / 6)))) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod ((band d).L N)), A.Nonempty →
      (band d).P (queEvent213 ((transfer_gauss d).hermitian N) A (E N)
          ((band d).queEtaN τ N) τ) ≤
        ENNReal.ofReal ((((band d).size N : ℝ)) ^ (-(τ / 6)))) :=
  theorem2_5_of_Thm221N'_of_E (transfer_gauss d) hκ ((thm221RegN_gauss d hκ).toThm221N' hκ)
    hτ0 hτ E hE (int_pp_thm25_gauss d τ E) (int_pm_thm25_gauss d τ E)

end RBM.Gauss

/-! ### Nondegenerate instances, unconditional -/

namespace RBM.Gauss.NonVacuity

open MeasureTheory Filter RBM RBM.Gauss
open scoped Matrix

/-- The Theorem 2.5 energy sequence `E N = (−1)^N/4`. -/
noncomputable def energy (N : ℕ) : ℝ := (-1 : ℝ) ^ N / 4

theorem abs_energy_le (N : ℕ) : |energy N| ≤ 2 - (1 / 2 : ℝ) := by
  rw [energy, abs_div, abs_pow, abs_neg, abs_one, one_pow]
  norm_num

theorem tau_pos : (0 : ℝ) < 1 / 32 := by norm_num

/-- (2.11) at the instance: `τ = 1/32 < c/2 = 1/16` for `Dims.exampleGrow` (`c = 1/8`). -/
theorem tau_lt_half_c : (1 / 32 : ℝ) < (band Dims.exampleGrow).c / 2 := by
  have hc : (band Dims.exampleGrow).c = 1 / 8 := Dims.exampleGrow_c
  rw [hc]; norm_num

end RBM.Gauss.NonVacuity

namespace RBM.Gauss

end RBM.Gauss
