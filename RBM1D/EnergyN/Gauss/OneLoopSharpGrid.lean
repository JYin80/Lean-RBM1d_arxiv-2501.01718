/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OneLoopSharpGrid
import RBM1D.EnergyN.Gauss.DetAvgIBPFlow
import RBM1D.EnergyN.Gauss.GoodSetFlow
import RBM1D.EnergyN.Flow.Hypotheses
import RBM1D.EnergyN.Gauss.Step2Gauss

/-!
# The sharp one-loop bound at a single time, at an `N`-dependent energy

Four statements at an `N`-dependent energy `E : ℕ → ℝ`: the regime at an intermediate time
(`RBM.Gauss.eventually_regime_of_hreg_plainN`), the bound `(W ℓ_u η_u) lkMax_1 ≺ 1` from the
local law (`RBM.Gauss.stochDom_lkMax_one_of_localLawN`) and from Steps 1–2
(`RBM.Gauss.stochDom_lkMax_one_of_steps12_plainN`), and the restriction of (2.75) to a single
time (`RBM.Gauss.localLawFlow_singleton_of_localLawFlowN`).

## The external `κ`

None of the four fixes an energy-dependent constant, and none of the four proofs calls an
energy-dependent constant producer: `stochDom_lkMax_one_of_localLawN` calls
`detAvgIBP_stochDom_of_localLaw_completeN` (`EnergyN/Gauss/DetAvgIBPFlow.lean`), which takes its
own `κ`, and the two energy-free helpers
`W_rpow_neg_half_le_scale_inv_rpow_half`/`scale_mul_inv_rpow_half_sq` (this file, deterministic,
fixed `E`) are applied at `E N`. `stochDom_lkMax_one_of_steps12_plainN` calls
`steps12_gauss_plainN` (`EnergyN/Gauss/Step2Gauss.lean`) and
`localLawUnifIcc_of_localLawFlowN`/`LocalLawUnifIccN` (`EnergyN/Gauss/GoodSetFlow.lean`).
-/

namespace RBM.Gauss

open MeasureTheory Filter

section OneLoopSharpGridN

variable (d : Dims)

/-- **The regime at an intermediate time**: under the plain pair, eventually
`N^c ≤ W ℓ_u η_u` and `N^{-1} ≤ η_u` at `u N ∈ [s N, t N]`. -/
theorem eventually_regime_of_hreg_plainN {E : ℕ → ℝ} {c : ℝ} {s t u : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ c ≤ (band d).scale (E N) N (u N) ∧ (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E N) (u N) := by
  filter_upwards [hAc, (band d).dim, eventually_ge_atTop 1] with N hAcN hdim hN1
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hm : 0 < (mE (E N)).im := mE_im_pos (hE N)
  have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
  have hct : (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N) := hAcN
  have hut : (band d).scale (E N) N (t N) ≤ (band d).scale (E N) N (u N) :=
    band_scale_antitone d (hu N).2 (ht1 N).le
  refine ⟨hct.trans hut, ?_⟩
  have hNc1 : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow hn1 hc0.le
  have hℓ : (band d).ell N (t N) ≤ (band d).L N := by
    rw [Band.ell, ellHat_ofReal _ (ht1 N)]
    exact min_le_right _ _
  have hWL : ((band d).W N : ℝ) * (band d).L N ≤ (N : ℝ) := by exact_mod_cast hdim.1
  have hsc : (band d).scale (E N) N (t N) ≤ (N : ℝ) * etaT (E N) (t N) := by
    calc
      (band d).scale (E N) N (t N) =
          ((band d).W N : ℝ) * (band d).ell N (t N) * etaT (E N) (t N) := rfl
      _ ≤ ((band d).W N : ℝ) * (band d).L N * etaT (E N) (t N) := by gcongr
      _ ≤ (N : ℝ) * etaT (E N) (t N) := by gcongr
  have h1 : 1 ≤ (N : ℝ) * etaT (E N) (t N) := hNc1.trans (hct.trans hsc)
  have hηu : etaT (E N) (t N) ≤ etaT (E N) (u N) := by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [(hu N).2]) hm.le
  rw [Real.rpow_neg_one]
  refine le_trans ?_ hηu
  rw [inv_eq_one_div, div_le_iff₀ hn0]
  linarith

/-- **`(W ℓ_u η_u) lkMax_1 ≺ 1` at the time `u`**, from the uniform local law on `[u, u]` with the
control `(W ℓ_u η_u)^{-1/2} ≤ N^{-a}`. It uses `detAvgIBP_stochDom_of_localLaw_completeN`. -/
theorem stochDom_lkMax_one_of_localLawN {E : ℕ → ℝ} {κ : ℝ} {u : ℕ → ℝ} {a K : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨhi : ∀ᶠ N : ℕ in atTop,
      ((band d).scale (E N) N (u N))⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIccN d E u u (fun N => ((band d).scale (E N) N (u N))⁻¹ ^ (1 / 2 : ℝ))) :
    StochDom (P d)
      (fun N (_ : Unit) ω =>
        (band d).scale (E N) N (u N) * Sample.lkMax (sample d) (E N) N (u N) ω 1)
      (fun _ _ _ => (1 : ℝ)) := by
  have hE' : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ ((band d).scale (E N) N (u N))⁻¹ ^ ((1 : ℝ) / 2) :=
    Eventually.of_forall fun N => W_rpow_neg_half_le_scale_inv_rpow_half d (hE' N) (hu0 N) (hu1 N)
  set Ψ : ℕ → ℝ := fun N => ((band d).scale (E N) N (u N))⁻¹ ^ ((1 : ℝ) / 2) with hΨdef
  have hbase := detAvgIBP_stochDom_of_localLaw_completeN d hκ0 hκ1 hE hu0 hu1 ha hK hη hΨlo hΨhi
    hll
  have heq : (fun N (v : LoopData (d.L N) 1) ω => (sample d).lkErr (E N) N (u N) ω v.idx)
      = fun N (v : LoopData (d.L N) 1) ω =>
          ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt (E N) (u N))
            - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) (v.2 0))‖ := by
    funext N v ω
    exact lkErr_one_eq_norm_trace (sample d) v
  have hloop : StochDom (P d)
      (fun N (v : LoopData (d.L N) 1) ω => (sample d).lkErr (E N) N (u N) ω v.idx)
      (fun N (_ : LoopData (d.L N) 1) _ => Ψ N * Ψ N) := by
    rw [heq]
    exact hbase.precomp_param (fun N (v : LoopData (d.L N) 1) => v.2 0)
  have hΨΨ1 : ∀ N, (band d).scale (E N) N (u N) * (Ψ N * Ψ N) = 1 := fun N =>
    scale_mul_inv_rpow_half_sq d (hE' N) (hu0 N) (hu1 N)
  intro τ hτ D hD
  filter_upwards [hloop τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  rintro ω ⟨_, hω⟩
  rw [mul_one] at hω
  have hxpos : 0 < (band d).scale (E N) N (u N) := (band d).scale_pos' (hE' N) N (hu0 N) (hu1 N)
  have hΨpos : 0 < Ψ N := Real.rpow_pos_of_pos (inv_pos.mpr hxpos) _
  have hpos : 0 < Ψ N * Ψ N := mul_pos hΨpos hΨpos
  have hω2 : (N : ℝ) ^ τ * (Ψ N * Ψ N)
      < (band d).scale (E N) N (u N) * Sample.lkMax (sample d) (E N) N (u N) ω 1 * (Ψ N * Ψ N) :=
    mul_lt_mul_of_pos_right hω hpos
  have heq2 : (band d).scale (E N) N (u N) * Sample.lkMax (sample d) (E N) N (u N) ω 1
      * (Ψ N * Ψ N) = Sample.lkMax (sample d) (E N) N (u N) ω 1 := by
    have hcomm : (band d).scale (E N) N (u N) * Sample.lkMax (sample d) (E N) N (u N) ω 1
        * (Ψ N * Ψ N) = ((band d).scale (E N) N (u N) * (Ψ N * Ψ N))
          * Sample.lkMax (sample d) (E N) N (u N) ω 1 := by
      ring
    rw [hcomm, hΨΨ1 N, one_mul]
  rw [heq2] at hω2
  have hω3 : (N : ℝ) ^ τ * (Ψ N * Ψ N)
      < ⨆ v : LoopData (d.L N) 1, (sample d).lkErr (E N) N (u N) ω v.idx := hω2
  obtain ⟨v, hv⟩ := exists_lt_of_lt_ciSup hω3
  exact ⟨v, hv⟩

/-- **(2.75) on `[s, t]` gives (2.75) on the single time `[u, u]`**, for `u N ∈ [s N, t N]`
(`LocalLawFlowN`, `EnergyN/Flow/Hypotheses.lean`). -/
theorem localLawFlow_singleton_of_localLawFlowN {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
    {X : Sample B} {E : ℕ → ℝ} {s t u : ℕ → ℝ}
    (h : RBM.LocalLawFlowN X E s t) (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    RBM.LocalLawFlowN X E u u := by
  have hprc := h.precomp_param (fun N (q : TimeIcc u u N × (B.Idx N × B.Idx N)) =>
    ((⟨q.1.1, by
        have hv : (q.1 : ℝ) = u N := le_antisymm q.1.2.2 q.1.2.1
        rw [hv]; exact hu N⟩ : TimeIcc s t N), q.2))
  exact hprc

/-- **`(W ℓ_u η_u) lkMax_1 ≺ 1` at the time `u`**, from (2.68)–(2.70) at `s` and the plain pair,
through Steps 1–2. It uses `steps12_gauss_plainN` and `localLawUnifIcc_of_localLawFlowN`. -/
theorem stochDom_lkMax_one_of_steps12_plainN {κ c : ℝ} {E : ℕ → ℝ} {s t u : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)
    (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hu : ∀ N, u N ∈ Set.Icc (s N) (t N)) :
    StochDom (P d)
      (fun N (_ : Unit) ω =>
        (band d).scale (E N) N (u N) * Sample.lkMax (sample d) (E N) N (u N) ω 1)
      (fun _ _ _ => (1 : ℝ)) := by
  have hE' : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hu0 : ∀ N, 0 ≤ u N := fun N => (hs0 N).trans (hu N).1
  have hu1 : ∀ N, u N < 1 := fun N => lt_of_le_of_lt (hu N).2 (ht1 N)
  have hrg := eventually_regime_of_hreg_plainN d hE' hst ht1 hc0 hreg0 hAc hu
  have hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT (E N) (u N) := hrg.mono fun _ h => h.2
  have hΨhi : ∀ᶠ N : ℕ in atTop,
      ((band d).scale (E N) N (u N))⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(c / 2)) := by
    filter_upwards [hrg, eventually_ge_atTop 1] with N h hN1
    exact scale_inv_rpow_half_le_of_rpow_le d hN1 h.1
  have hS := steps12_gauss_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hLLu : RBM.LocalLawFlowN (sample d) E u u :=
    localLawFlow_singleton_of_localLawFlowN hS.localLaw hu
  have hll : LocalLawUnifIccN d E u u (fun N => ((band d).scale (E N) N (u N))⁻¹ ^ (1 / 2 : ℝ)) :=
    localLawUnifIcc_of_localLawFlowN hLLu
      (Eventually.of_forall fun N v hv => by
        rw [le_antisymm hv.2 hv.1])
  exact stochDom_lkMax_one_of_localLawN d hκ0 hκ1 hEκ hu0 hu1 (half_pos hc0) zero_le_one hη hΨhi
    hll

end OneLoopSharpGridN

end RBM.Gauss
