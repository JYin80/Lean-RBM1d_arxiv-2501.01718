/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Plain
import RBM1D.Gauss.Step4Base
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Gauss.OneLoopTimeIcc
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Gauss.SigmaExhaust
import RBM1D.Gauss.GridFarLift
import RBM1D.Gauss.GridFarClosure
import RBM1D.Gauss.Theorem22Gauss
import RBM1D.Flow.EnergyUniformReg
import RBM1D.Flow.BandLocalLawReg
import RBM1D.EnergyN.Flow.Thm221NoEL
import RBM1D.EnergyN.Gauss.Step2Gauss
import RBM1D.EnergyN.Gauss.Step4Closed
import RBM1D.EnergyN.Gauss.Step5Gauss

/-!
# Energy-uniform Theorem 2.21, Theorem 2.2 and Theorem 2.3 for the Gaussian model

Two statements of the step of Theorem 2.21 at an `N`-dependent energy `E : ℕ → ℝ`: the plain
pair from (2.72) (`plain_of_cond272N`, which takes `hE : ∀ N, |E N| < 2`) and (2.68)–(2.70) at
`t` (`boundsCore_step_gauss_plainN`); and the three terminal results below. The private helper
`scale_pos_of_lt_one` is proved in this file.

## Terminals

* `RBM.Gauss.thm221NoELNReg_gauss d hκ : Thm221NoELNReg (sample d) κ` — Theorem 2.21 without
  (2.71), energy-uniform, `Reg` step condition, for the Gaussian model, **unconditional**.
* `RBM.Gauss.delocalization_gauss` — **Theorem 2.2** for `sample d`, every `d : Dims`,
  unconditional: `delocalization_gauss_of_reg d hκ (thm221NoELNReg_gauss d hκ)`.
* `RBM.Gauss.localSemicircleLaw_gaussN_of_z` — **Theorem 2.3** in energy-uniform (paper) form:
  (2.3), (2.4) and the tracial law along any sequence `z` with `|Re z| ≤ 2 - κ`,
  `N^{-1+τ} ≤ Im z ≤ 1`; no energy slice.
-/

noncomputable section

namespace RBM

namespace Gauss

open MeasureTheory Filter

section CoreN

variable (d : Dims)

/-- `(band d).scale E N t > 0` for `|E| < 2` and `t < 1`, with **no** hypothesis `0 ≤ t`: `ell`
is positive for any `t < 1` (`RBM.Step3.ellHat_pos_of_lt_one`, using only `1 ≤ L N`), and `etaT`
is positive for any `t < 1` (`RBM.etaT_pos`). This is the form `RBM.Band.scale_pos'` does not
give (it demands `0 ≤ t`), and is what `plain_of_cond272N` needs, since its hypotheses are
`|E| < 2`, `s ≤ t < 1` only. -/
private theorem scale_pos_of_lt_one {E : ℝ} (hE : |E| < 2) (N : ℕ) {t : ℝ} (ht1 : t < 1) :
    0 < (band d).scale E N t := by
  have hW : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
  have hL1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
  have hℓ : 0 < (band d).ell N t := RBM.Step3.ellHat_pos_of_lt_one hL1 ht1
  have hη : 0 < etaT E t := RBM.etaT_pos hE ht1
  have hscale : (band d).scale E N t = ((band d).W N : ℝ) * (band d).ell N t * etaT E t := rfl
  rw [hscale]
  exact mul_pos (mul_pos hW hℓ) hη

/-- **The plain pair from (2.72)**: `Cond272N` gives `(η_s/η_t)^30 ≤ W ℓ_t η_t` eventually, the
converse of `RBM.Step2.cond272_of_plainN`, at an `N`-dependent energy with
`hE : ∀ N, |E N| < 2`. -/
theorem plain_of_cond272N {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272N (band d) E s t) :
    ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N) := by
  filter_upwards [hcond] with N hN
  have ht := ht1 N
  have hpos : 0 < (band d).scale (E N) N (t N) := scale_pos_of_lt_one d (hE N) N ht
  have hinvpos : 0 < ((band d).scale (E N) N (t N))⁻¹ := inv_pos.mpr hpos
  have hstep := inv_anti₀ hinvpos hN
  rw [inv_inv, ← inv_pow, inv_div] at hstep
  rwa [Step2.etaT_ratio (hE N)]

/-- **(2.68)–(2.70) at `t` from (2.75), (2.78), (2.79)** at an `N`-dependent energy:
`BoundsCore_of_flowN` fed the local-law half of `step2_gauss_plainN`, `step4_gauss_plainN` and
`step5_gauss_plainN`. -/
theorem boundsCore_step_gauss_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    BoundsCoreN (sample d) E t :=
  BoundsCore_of_flowN hst (step2_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc).1
    (step4_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc)
    (step5_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc)

end CoreN

/-! ### Terminal 1: `Thm221NoELNReg (sample d) κ` -/

/-- **Theorem 2.21 without (2.71), energy-uniform, for the Gaussian model** (`Reg` step
condition). For the step data `E hE c hc0 s t hs0 hst ht1 hreg hB` of `Thm221NoELNReg`, apply
`boundsCore_step_gauss_plainN` at `κ' := min κ 1` (so `|E N| ≤ 2 - κ ≤ 2 - κ'` and
`0 < κ' ≤ 1`), with `hreg0 := plain_of_cond272N … hreg.1` and `hAc := hreg.2`. -/
theorem thm221NoELNReg_gauss (d : Dims) {κ : ℝ} (hκ : 0 < κ) : Thm221NoELNReg (sample d) κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB := by
    have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
    set κ' : ℝ := min κ 1 with hκ'def
    have hκ'0 : 0 < κ' := lt_min hκ one_pos
    have hκ'1 : κ' ≤ 1 := min_le_right _ _
    have hle : (2 : ℝ) - κ ≤ 2 - κ' := by have := min_le_left κ 1; linarith
    have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans hle
    exact boundsCore_step_gauss_plainN d hκ'0 hκ'1 hEκ' hB hs0 hst ht1 hc0
      (plain_of_cond272N d hE2 hst ht1 hreg.1) hreg.2

/-! ### Terminal 2: Theorem 2.2, unconditional -/

/-- **Theorem 2.2 (delocalization) for the Gaussian model, unconditional, every `d : Dims`.**
The conclusion of `delocalization_gauss_of_reg` (`Gauss/Theorem22Gauss.lean`), verbatim, with
its only hypothesis `hT` discharged by `thm221NoELNReg_gauss`. -/
theorem delocalization_gauss (d : Dims) {κ : ℝ} (hκ : 0 < κ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      (band d).P {ω | ∃ p : (band d).Idx N × (band d).Idx N, (N : ℝ) ^ (-1 + τ) <
        ‖((transfer_gauss d).hermitian N ω).eigenvectorBasis p.1 p.2‖ ^ 2 *
          Set.indicator (Set.Icc (-2 + κ) (2 - κ)) (fun _ => (1 : ℝ))
            (((transfer_gauss d).hermitian N ω).eigenvalues p.1)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  delocalization_gauss_of_reg d hκ (thm221NoELNReg_gauss d hκ) hτ hD

/-! ### Terminal 3: Theorem 2.3 in energy-uniform form -/

/-- **Theorem 2.3 (local semicircle law) for the Gaussian model, energy-uniform (paper) form.**
The three conjuncts ((2.3), (2.4), tracial law) of `localSemicircleLaw_of_boundsCoreN_of_z`
(`Flow/EnergyUniform.lean`) at `B := band d`, `X := sample d`, `T := transfer_gauss d`,
along any sequence `z` with `0 < Im z ≤ 1`, `|Re z| ≤ 2 - κ`, eventually `N^{-1+τ} ≤ Im z`. No
energy slice: `SpecSeqN.of_z` sets `E N := lemE (z N)`. -/
theorem localSemicircleLaw_gaussN_of_z (d : Dims) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    {z : ℕ → ℂ} (him_pos : ∀ N, 0 < (z N).im) (him_le_one : ∀ N, (z N).im ≤ 1)
    (habs_re : ∀ N, |(z N).re| ≤ 2 - κ)
    (him_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (z N).im) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ ij : (band d).Idx N × (band d).Idx N,
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green ((transfer_gauss d).Hband N ω) (z N) -
            msc (z N) • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ a : ZMod ((band d).L N),
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ <
        ‖((band d).W N : ℂ)⁻¹ * ∑ x : Fin ((band d).W N),
            green ((transfer_gauss d).Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, (band d).P {ω | ∃ _u : Unit,
      ((band d).W N : ℝ) ^ τ' * ((band d).zScale N (z N))⁻¹ <
        ‖(((band d).L N * (band d).W N : ℕ) : ℂ)⁻¹ *
            (green ((transfer_gauss d).Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  localSemicircleLaw_of_boundsCoreN_of_z (transfer_gauss d) (transferLoop1_gauss d) hκ him_pos
    him_le_one habs_re him_ge
    ((SpecSeqN.of_z him_pos him_le_one habs_re him_ge).boundsCoreN' (sample d) hκ
      ((thm221NoELNReg_gauss d hκ).toThm221NoELN' hκ) hτ) hτ' hD

end Gauss

end RBM

end


