/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step3Charges
import RBM1D.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.Step2Gauss
import RBM1D.EnergyN.Gauss.Step3Charges
import RBM1D.EnergyN.Gauss.Step3Plain
import RBM1D.EnergyN.Hierarchy.StepGlue

/-!
# The estimates `S(m, 0)`, `S(1, l)` and the `(+,-)` 2-loop, for the Gaussian flow

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: the estimates `S(m, 0)`
(`RBM.Gauss.flow_S_zero_plainN`) and `S(1, l)` (`RBM.Gauss.flow_S_oneN`) of Step 3 for the
flow, and `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` for the charges `(+,-)`, `(-,+)`
(`RBM.Gauss.flowXiLK_two_pm_le_quarterN`). No energy-dependent constant is fixed in this file.

`Step3.flowXiLK`/`.flowAs`/`.flowA`/`.flowXiLKTwoPM`/`.flowXiLKSigma` are plain
`E : ℝ`-parametrised `def`s; they are used at `E N` through the eta-expansion
`fun n N u ω => Step3.flowXiLK X (E N) s t n N u ω` etc., as in
`RBM1D/EnergyN/Hierarchy/StepGlue.lean` and `RBM1D/EnergyN/Gauss/Step3Charges.lean`.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace Gauss

variable (d : Dims)

/-! ### (T1) `flow_S_zero_plainN` -/

/-- **The estimate `S(m, 0)` of Step 3 for the flow**: the hypothesis `h0` of
`RBM.Step45.flow_sharpLmKN`, at an `N`-dependent energy. No energy-dependent constant is fixed
here. -/
theorem flow_S_zero_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ m, 1 ≤ m → Step3.S (band d).P (fun n N u ω => Step3.flowXiLK (sample d) (E N) s t n N u ω)
      (fun N => Step3.flowAs (band d) (E N) s N) (Step3.flowR (band d) s t)
      (fun N u => Step3.flowA (band d) (E N) s t N u) m 0 := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE hst ht1 hreg0
  have h12 := steps12_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  exact fun m hm =>
    StepGlue.flow_S_zero'N (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hcond h12.apriori m hm

/-! ### (T3) `flowXiLK_two_pm_le_quarterN` -/

/-- **`Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` for `σ ∈ {(+,-),(-,+)}`**, pointwise in `u`, at an
`N`-dependent energy. No energy-dependent constant is fixed here. -/
theorem flowXiLK_two_pm_le_quarterN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    StochDom (band d).P (fun N => Step3.flowXiLKTwoPM (sample d) (E N) s t N)
      (fun N u _ => Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4)) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hE2 : ∀ N, |E N| ≤ 2 := fun N => by linarith [hEκ N]
  have h12 := steps12_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hA : ∀ N (u : TimeIcc s t N), (0 : ℝ) < (band d).scale (E N) N u := fun N u =>
    (band d).scale_pos' (hE N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hR4 : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT (E N) (s N) / etaT (E N) u) ^ 4 ≤ (band d).scale (E N) N u ^ ((1 : ℝ) / 4) :=
    StepGlue.eventually_R4_le_rpow_quarter_plainN hE hst ht1 hreg0
  have hpm0 := StepGlue.aprioriDecay_pm'N (sample d) ht1 h12.aprioriDecay
  have hpm_raw : StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω ⟨[true, false], [p.2.1, p.2.2]⟩)
      (fun N p _ => (band d).scale (E N) N p.1 ^ ((1 : ℝ) / 4) *
        ((band d).scale (E N) N p.1)⁻¹ ^ 2) := by
    refine Step3.stochDom_mono (fun N p _ => mul_nonneg
      (Real.rpow_nonneg (hA N p.1).le _) (sq_nonneg _)) 1 ?_ hpm0
    filter_upwards [hR4] with N hR4N p _
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right (hR4N p.1) (sq_nonneg _)
  have hmp_raw : StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω ⟨[false, true], [p.2.1, p.2.2]⟩)
      (fun N p _ => (band d).scale (E N) N p.1 ^ ((1 : ℝ) / 4) *
        ((band d).scale (E N) N p.1)⁻¹ ^ 2) := by
    have hswap := hpm_raw.precomp_param (fun N (p : TimeIcc s t N ×
      (ZMod ((band d).L N) × ZMod ((band d).L N))) => (p.1, (p.2.2, p.2.1)))
    have heq : (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω ⟨[true, false], [p.2.2, p.2.1]⟩) =
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr (E N) N p.1 ω ⟨[false, true], [p.2.1, p.2.2]⟩) := by
      funext N p ω
      exact ChargeReduce.lkErr_two_flip (sample d) (hE2 N) N ((hs0 N).trans p.1.2.1)
        (p.1.2.2.trans_lt (ht1 N)) ω true false p.2.2 p.2.1
    rwa [heq] at hswap
  have hpm2 : StochDom (band d).P
      (fun N => Step3.flowXiLKSigma (sample d) (E N) s t true false N)
      (fun N u _ => (band d).scale (E N) N u ^ ((1 : ℝ) / 4)) := by
    have hbr := stochDom_flowXiLKSigmaN (σ₁ := true) (σ₂ := false)
      (f := fun N u => (band d).scale (E N) N u ^ ((1 : ℝ) / 4) *
        ((band d).scale (E N) N u)⁻¹ ^ 2) (sample d) (fun N u => (hA N u).le) hpm_raw
    refine Step3.stochDom_mono (fun N u _ => Real.rpow_nonneg (hA N u).le _) 1 ?_ hbr
    filter_upwards with N u _
    have hne : ((band d).scale (E N) N u) ≠ 0 := (hA N u).ne'
    have heq : (band d).scale (E N) N u ^ ((1 : ℝ) / 4) * ((band d).scale (E N) N u)⁻¹ ^ 2 *
        (band d).scale (E N) N u ^ 2 = (band d).scale (E N) N u ^ ((1 : ℝ) / 4) := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hne), mul_one]
    rw [one_mul, heq]
  have hmp2 : StochDom (band d).P
      (fun N => Step3.flowXiLKSigma (sample d) (E N) s t false true N)
      (fun N u _ => (band d).scale (E N) N u ^ ((1 : ℝ) / 4)) := by
    have hbr := stochDom_flowXiLKSigmaN (σ₁ := false) (σ₂ := true)
      (f := fun N u => (band d).scale (E N) N u ^ ((1 : ℝ) / 4) *
        ((band d).scale (E N) N u)⁻¹ ^ 2) (sample d) (fun N u => (hA N u).le) hmp_raw
    refine Step3.stochDom_mono (fun N u _ => Real.rpow_nonneg (hA N u).le _) 1 ?_ hbr
    filter_upwards with N u _
    have hne : ((band d).scale (E N) N u) ≠ 0 := (hA N u).ne'
    have heq : (band d).scale (E N) N u ^ ((1 : ℝ) / 4) * ((band d).scale (E N) N u)⁻¹ ^ 2 *
        (band d).scale (E N) N u ^ 2 = (band d).scale (E N) N u ^ ((1 : ℝ) / 4) := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hne), mul_one]
    rw [one_mul, heq]
  exact hpm2.max hmp2

/-! ### (T4) `flow_S_oneN` -/

/-- **The estimate `S(1, l)` of Step 3 for the flow**: the case `m = 1` of the hypothesis `h12` of
`RBM.Step45.flow_sharpLmKN`, at an `N`-dependent energy. No energy-dependent constant is fixed
here. -/
theorem flow_S_oneN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ} (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) (l : ℕ) :
    Step3.S (band d).P (fun n N u ω => Step3.flowXiLK (sample d) (E N) s t n N u ω)
      (fun N => Step3.flowAs (band d) (E N) s N) (Step3.flowR (band d) s t)
      (fun N u => Step3.flowA (band d) (E N) s t N u) 1 l := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE hst ht1 hreg0
  have h12 := steps12_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  exact StepGlue.flow_S_one'N (sample d) hE hs0 hst ht1 hcond h12.localLaw l

section CompatN

end CompatN

end Gauss

end RBM

end
