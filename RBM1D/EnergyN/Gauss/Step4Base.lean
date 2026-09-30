/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step4Base
import RBM1D.EnergyN.Gauss.Step4BasePM
import RBM1D.EnergyN.Gauss.PPUniform
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Hierarchy.Step3

/-!
# The base cases `n = 2` of Step 4 for the Gaussian flow, at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: `thetaPP ≤ (W ℓ_u η_u)^{1/4}`
(`thetaPP_le_flowA_quarter_plainN`), `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` for all charges
(`flowXiLK_two_le_quarter_plainN`), and the estimate `S(2, l)` of Step 3
(`flow_S_two_plainN`). No energy-dependent constant is fixed in this file.

Energy-dependent dependencies: `flowXiLK_two_pm_le_quarterN` (`Gauss/Step4BasePM.lean`),
`hpp_gauss_plainN` (`Gauss/PPUniform.lean`), `Step2.cond272_of_plainN`
(`Gauss/Step2Plain.lean`), `Step3.scales_flowN` (`Hierarchy/Step3.lean`). The energy-free callee
`Step3.flowXiLK_two_eq_max_pp_twoPM` (`Gauss/Step3Charges.lean`, plain `E`) is called at `E N`.
`Step3.stochDom_mono`, `StochDom.max`, `Step3.flowA_pos`, `Step3.psi_nonneg`,
`quarter_le_psi_two`, `Step3.ellHat_le_sqrt_mul`, `Grid.RPP_nonneg`, `Step2.etaT_ratio`,
`flowScale_antitoneOn` are energy-free/generic, used at `E N`.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

namespace Gauss

variable (d : Dims)

/-! ### `N`-form of the pointwise scale fact `Θ_{pp} ≤ A_u^{1/4}` -/

/-- **`thetaPP ≤ (W ℓ_u η_u)^{1/4}` eventually**, for all `u ∈ [s, t]`, under the plain pair: a
purely deterministic per-`N` real-number chain, with no hidden `E`-dependent constant. -/
theorem thetaPP_le_flowA_quarter_plainN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      thetaPP d s t N ≤ Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4) := by
  have hc524 : 0 < 5 * c / 24 := by positivity
  have ev3 : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ (N : ℝ) ^ (5 * c / 24) :=
    ((tendsto_rpow_atTop hc524).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  filter_upwards [hreg0, hAc, ev3] with N hreg0N hAcN h3N u
  set At := (band d).scale (E N) N (t N) with hAtdef
  have hL1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have ht0 : (0 : ℝ) ≤ t N := (hs0 N).trans (hst N)
  have hAt0 : 0 < At := (band d).scale_pos' (hE N) N ht0 (ht1 N)
  have h1t : (0 : ℝ) < 1 - t N := by linarith [ht1 N]
  have h1s : (0 : ℝ) < 1 - s N := by linarith [hs1]
  set r : ℝ := (1 - s N) / (1 - t N) with hrdef
  have hr1 : (1 : ℝ) ≤ r := by rw [hrdef, le_div_iff₀ h1t]; linarith [hst N]
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hRsqrt : Grid.RPP d s t N ≤ Real.sqrt r := by
    have hℓs : (0 : ℝ) < (band d).ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
    change (band d).ell N (t N) / (band d).ell N (s N) ≤ Real.sqrt r
    rw [div_le_iff₀ hℓs, hrdef]
    exact Step3.ellHat_le_sqrt_mul (L := (band d).L N) (s := s N) (t := t N) (hst N) (ht1 N)
  have hR0 : (0 : ℝ) ≤ Grid.RPP d s t N := Grid.RPP_nonneg d s t N
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
  have hR2 : Grid.RPP d s t N ^ 2 ≤ r := by
    calc Grid.RPP d s t N ^ 2 ≤ Real.sqrt r ^ 2 := pow_le_pow_left₀ hR0 hRsqrt 2
      _ = r := hsr
  have hR52 : Grid.RPP d s t N ^ (5 / 2 : ℝ) ≤ r ^ ((5 : ℝ) / 4) := by
    have e1 : Grid.RPP d s t N ^ (5 / 2 : ℝ) = (Grid.RPP d s t N ^ 2) ^ ((5 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (Grid.RPP d s t N) 2, ← Real.rpow_mul hR0]; norm_num
    rw [e1]
    exact Real.rpow_le_rpow (sq_nonneg _) hR2 (by norm_num)
  have hrAt : r ^ (30 : ℕ) ≤ At := by
    have heq : etaT (E N) (s N) / etaT (E N) (t N) = r := by
      rw [hrdef]; exact Step2.etaT_ratio (hE N) (s N) (t N)
    rw [← heq]; exact hreg0N
  have hr524 : r ^ ((5 : ℝ) / 4) ≤ At ^ ((1 : ℝ) / 24) := by
    have h1 := Real.rpow_le_rpow (show (0 : ℝ) ≤ r ^ (30 : ℕ) by positivity) hrAt
      (show (0 : ℝ) ≤ (1 : ℝ) / 24 by norm_num)
    have heq2 : (r ^ (30 : ℕ) : ℝ) ^ ((1 : ℝ) / 24) = r ^ ((5 : ℝ) / 4) := by
      rw [← Real.rpow_natCast r 30, ← Real.rpow_mul hr0]; norm_num
    rwa [heq2] at h1
  have hr54_1 : (1 : ℝ) ≤ r ^ ((5 : ℝ) / 4) := Real.one_le_rpow hr1 (by norm_num)
  have hr_le_r54 : r ≤ r ^ ((5 : ℝ) / 4) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ ((5 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  have hthetaPP : thetaPP d s t N ≤ 3 * At ^ ((1 : ℝ) / 24) := by
    unfold thetaPP
    linarith [hR2, hR52, hr524, hr54_1, hr_le_r54]
  have h324 : (3 : ℝ) ≤ At ^ ((5 : ℝ) / 24) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have e : (N : ℝ) ^ (5 * c / 24) = ((N : ℝ) ^ c) ^ ((5 : ℝ) / 24) := by
      rw [← Real.rpow_mul hN0]; ring_nf
    calc (3 : ℝ) ≤ (N : ℝ) ^ (5 * c / 24) := h3N
      _ = ((N : ℝ) ^ c) ^ ((5 : ℝ) / 24) := e
      _ ≤ At ^ ((5 : ℝ) / 24) := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hAcN (by norm_num)
  have hfinal : 3 * At ^ ((1 : ℝ) / 24) ≤ At ^ ((1 : ℝ) / 4) := by
    have hsplit : At ^ ((1 : ℝ) / 4) = At ^ ((5 : ℝ) / 24) * At ^ ((1 : ℝ) / 24) := by
      rw [← Real.rpow_add hAt0]; norm_num
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right h324 (Real.rpow_nonneg hAt0.le _)
  have hAtAu : At ≤ Step3.flowA (band d) (E N) s t N u := by
    have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
    change At ≤ (band d).scale (E N) N (u : ℝ)
    exact flowScale_antitoneOn (Nat.cast_nonneg _) ((band d).L N) (E N)
      (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have hAuAt14 : At ^ ((1 : ℝ) / 4) ≤ Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hAt0.le hAtAu (by norm_num)
  calc thetaPP d s t N ≤ 3 * At ^ ((1 : ℝ) / 24) := hthetaPP
    _ ≤ At ^ ((1 : ℝ) / 4) := hfinal
    _ ≤ Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4) := hAuAt14

/-! ### `Ξ^{(L-K)}_{u,2}` for all charges -/

/-- **`Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` for all charges**: the hypothesis `h2` of
`RBM.Step45.flow_sharpLmKN`, at an `N`-dependent energy. `κ`/`hEκ`/`hB` are those of the two
callees. Route: `flowXiLK_two_pm_le_quarterN` for `(+,-)`/`(-,+)`; `hpp_gauss_plainN` +
`thetaPP_le_flowA_quarter_plainN` for `(+,+)`; `Step3.flowXiLK_two_eq_max_pp_twoPM`
(energy-free, called at `E N`) folds in `(-,-)`. -/
theorem flowXiLK_two_le_quarter_plainN {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    StochDom (band d).P (fun N => Step3.flowXiLK (sample d) (E N) s t 2 N)
      (fun N u _ => Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4)) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hE2 : ∀ N, |E N| ≤ 2 := fun N => by linarith [hEκ N]
  have hpm := flowXiLK_two_pm_le_quarterN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hpp0 := hpp_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hA : ∀ N (u : TimeIcc s t N), (0 : ℝ) ≤ Step3.flowA (band d) (E N) s t N u := fun N u =>
    (Step3.flowA_pos (hE N) hs0 ht1 N u).le
  have hleAt := thetaPP_le_flowA_quarter_plainN d hE hs0 hst ht1 hc0 hreg0 hAc
  have hpp : StochDom (band d).P (fun N => Step3.flowXiLKSigma (sample d) (E N) s t true true N)
      (fun N u _ => Step3.flowA (band d) (E N) s t N u ^ ((1 : ℝ) / 4)) := by
    refine Step3.stochDom_mono (fun N u _ => Real.rpow_nonneg (hA N u) _) 1 ?_ hpp0
    filter_upwards [hleAt] with N hN u _
    rw [one_mul]
    exact hN u
  have hmax := hpp.max hpm
  have heq : (fun N => Step3.flowXiLK (sample d) (E N) s t 2 N) =
      fun N u ω => max (Step3.flowXiLKSigma (sample d) (E N) s t true true N u ω)
        (Step3.flowXiLKTwoPM (sample d) (E N) s t N u ω) := by
    funext N u ω
    exact congrFun (congrFun
      (congrFun (Step3.flowXiLK_two_eq_max_pp_twoPM (sample d) (hE2 N) hs0 ht1) N) u) ω
  rw [heq]
  exact hmax

/-! ### `flow_S_two_plainN`, the `m = 2` case -/

/-- **The estimate `S(2, l)` of Step 3 for the flow**: the hypothesis `h12` of
`RBM.Step45.flow_sharpLmKN` at `m = 2`, at an `N`-dependent energy. `κ`/`hEκ`/`hB` as for
`flowXiLK_two_le_quarter_plainN`; the `Cond272N`/`Scales` callees are taken at `E N`;
`quarter_le_psi_two` is energy-free. -/
theorem flow_S_two_plainN {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤ (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) (l : ℕ) :
    Step3.S (band d).P (fun n N u ω => Step3.flowXiLK (sample d) (E N) s t n N u ω)
      (fun N => Step3.flowAs (band d) (E N) s N) (Step3.flowR (band d) s t)
      (fun N u => Step3.flowA (band d) (E N) s t N u) 2 l := by
  unfold Step3.S
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE hst ht1 hreg0
  have sc := Step3.scales_flowN hE hs0 hst ht1 hcond
  have h2 := flowXiLK_two_le_quarter_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (n := 2) (k := l)
    (sc.As_pos N).le (sc.R_nonneg N) (sc.A_pos N u).le) 1 ?_ h2
  filter_upwards [sc.one_le_As, sc.A_le_As] with N hAs1 hAle u _
  rw [one_mul]
  exact quarter_le_psi_two hAs1 (sc.R_nonneg N) (sc.A_pos N u).le (hAle u) l

end Gauss

end RBM

end

