/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.EnergyN.Gauss.DetIBPWeighted
import RBM1D.EnergyN.Gauss.DetFlucAvgComplete
import RBM1D.EnergyN.Gauss.DetFlucThreshold

/-!
# The block trace `tr((G_u - m) E_b)` by integration by parts, at an `N`-dependent energy

Bounds `|tr((G_u - m) E_b)| ≺ Ψ²` at a single time `u` and an `N`-dependent energy
`E : ℕ → ℝ`: from the integration-by-parts and fluctuation-average inputs
(`RBM.Gauss.detAvgIBP_stochDom_of_inputsN`), from the uniform local law with the envelope and
good-set hypotheses (`RBM.Gauss.detAvgIBP_stochDom_of_localLawN`), and from the uniform local law
alone (`RBM.Gauss.detAvgIBP_stochDom_of_localLaw'N`,
`RBM.Gauss.detAvgIBP_stochDom_of_localLaw_completeN`); and the envelope bound
`RBM.Gauss.eventually_etaEnv_sq_leN`. No energy-dependent constant is fixed in them.

`detAvgIBP_stochDom_of_inputsN` and `detAvgIBP_stochDom_of_localLawN` carry an external `κ`
(`{κ} (hκ0) (hκ1) (hE : ∀ N, |E N| ≤ 2 - κ)`). `stochDom_of_unifDomIcc_singleton` (no `E`
binder), `norm_detAvgIBP_le` (deterministic, per fixed `N`/`ω`),
`eventually_rpow_neg_one_le_psi_sq` and `eventually_psi_sq_le_one` (no `E`) are used at `E N`.
`detAvgIBP_stochDom_of_localLawN` uses `unifDomIcc_condExpDiag_weightedN`
(`RBM1D/EnergyN/Gauss/DetIBPWeighted.lean`) and `fixedTimeFAStatement_provedN`
(`RBM1D/EnergyN/Gauss/DetFlucAvgComplete.lean`). `eventually_etaEnv_sq_leN` uses
`etaInv_le_rpow_of_lowerN` (`RBM1D/EnergyN/Gauss/DetFlucThreshold.lean`).
`detAvgIBP_stochDom_of_localLaw'N` uses `highProb_detFlucDelta_of_localLawN` (same file as the
latter),
`detAvgIBP_stochDom_of_localLawN` and `eventually_etaEnv_sq_leN`.
`detAvgIBP_stochDom_of_localLaw_completeN` uses the generic `UnifDomIcc.mono_control` (on
`LocalLawUnifIccN`, an abbreviation of `UnifDomIcc`) and `detAvgIBP_stochDom_of_localLaw'N`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- **`|tr((G_u - m) E_a)| ≺ Ψ²` at the time `u`**, from the integration-by-parts bound `hIBP` and
the fluctuation averages `hFArow`, `hFAblk`. `stochDom_of_unifDomIcc_singleton` and
`norm_detAvgIBP_le` (deterministic per fixed `N`/`ω`) are applied at `E N`. -/
theorem detAvgIBP_stochDom_of_inputsN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} {u Ψ : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hIBP : UnifDomIcc (P d) u u
      (fun N v (i : d.Idx N) ω =>
        ‖condExpDiag d N v (zt (E N) v) (mE (E N)) i ω
          - (v : ℂ) * mE (E N) ^ 2 * ∑ k,
            (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt (E N) v) k k - mE (E N))‖)
      (fun N _ _ _ => Ψ N * Ψ N))
    (hFArow : UnifDomIcc (P d) u u
      (fun N v (i : d.Idx N) ω =>
        ‖flucAvg d N v (zt (E N) v) (mE (E N))
          (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N))
    (hFAblk : UnifDomIcc (P d) u u
      (fun N v (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N v (zt (E N) v) (mE (E N))
          (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N)) :
    StochDom (P d)
      (fun N (a : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt (E N) (u N))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) a)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  have hI := stochDom_of_unifDomIcc_singleton (card_Idx_le d) hIBP
  have hR := stochDom_of_unifDomIcc_singleton (card_Idx_le d) hFArow
  have hB := stochDom_of_unifDomIcc_singleton (card_ZMod_L_le d) hFAblk
  have hjoint := (hI.sumElim hR).sumElim hB
  refine StochDom.of_det hjoint (fun N a ω => mul_nonneg (hΨ0 N) (hΨ0 N))
    (δ := fun _ => 0) (fun _ => le_rfl) one_pos
    (Eventually.of_forall fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    one_pos (1 + 2 * Kstab κ) 1 ?_
  intro N ω Φ hΦ1 _ _ hAB a
  have h := norm_detAvgIBP_le d hκ0 hκ1 (hE N) (hu0 N) (hu1 N) ω a
    (A := Φ) (Φ := Ψ N * Ψ N)
    (fun i => hAB (Sum.inl (Sum.inl i)))
    (fun i => hAB (Sum.inl (Sum.inr i)))
    (hAB (Sum.inr a))
  calc
    _ ≤ (1 + 2 * Kstab κ) * Φ * (Ψ N * Ψ N) := h
    _ = (1 + 2 * Kstab κ) * Φ ^ 1 * (Ψ N * Ψ N) := by ring

/-- **`|tr((G_u - m) E_b)| ≺ Ψ²` at the time `u`**, from the uniform local law on `[u, u]`, the
good set and the envelope bounds. It uses `unifDomIcc_condExpDiag_weightedN` and
`fixedTimeFAStatement_provedN`. -/
theorem detAvgIBP_stochDom_of_localLawN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} {u Ψ δ : ℕ → ℝ}
    {a K Kenv B : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop,
      ((etaT (E N) (u N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) u u δ N))
    (hll : LocalLawUnifIccN d E u u Ψ) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt (E N) (u N))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  have hE' : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hIBP := unifDomIcc_condExpDiag_weightedN (d := d) (E := E)
    (s := u) (t := u) (Ψ := Ψ) (δ := δ) (Kenv := Kenv) (B := B)
    hE' hu0 hu1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hWΨ hδ1 hΩ hll
  have hFA := fixedTimeFAStatement_provedN d E u Ψ a K ha hK hE'
    (fun N => ⟨hu0 N, hu1 N⟩) hη (hΨlo.and hΨhi) hll
  exact detAvgIBP_stochDom_of_inputsN d hκ0 hκ1 hE hu0 hu1 hΨ0 hIBP
    (by simpa only [pow_two] using hFA.1)
    (by simpa only [pow_two] using hFA.2)

/-- **`(η_u⁻¹ + 1)^2 ≤ N^{2K+1}` eventually**, from `N^{-K} ≤ η_u`. It uses
`etaInv_le_rpow_of_lowerN`. -/
theorem eventually_etaEnv_sq_leN {E : ℕ → ℝ} {K : ℝ} {u : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N)) :
    ∀ᶠ N : ℕ in atTop,
      ((etaT (E N) (u N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ (2 * K + 1) := by
  filter_upwards [etaInv_le_rpow_of_lowerN hE hu1 hK hη,
    eventually_ge_atTop 1, eventually_le_rpow 4 one_pos]
      with N hInv hN1 h4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 1 ≤ (N : ℝ) ^ K := Real.one_le_rpow hn hK
  have hbase : (etaT (E N) (u N))⁻¹ + 1 ≤ 2 * (N : ℝ) ^ K := by linarith
  have henv0 : 0 ≤ (etaT (E N) (u N))⁻¹ + 1 := by
    have hηpos := etaT_pos_of_lt_one (hE N) (hu1 N)
    positivity
  have hsq := pow_le_pow_left₀ henv0 hbase 2
  have hpow2 : ((N : ℝ) ^ K) ^ 2 = (N : ℝ) ^ (2 * K) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  calc
    ((etaT (E N) (u N))⁻¹ + 1) ^ 2 ≤ (2 * (N : ℝ) ^ K) ^ 2 := hsq
    _ = 4 * (N : ℝ) ^ (2 * K) := by
      rw [mul_pow, hpow2]
      ring
    _ ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (2 * K) := by gcongr
    _ = (N : ℝ) ^ (2 * K + 1) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring

/-- **`|tr((G_u - m) E_b)| ≺ Ψ²` at the time `u`**, from the uniform local law on `[u, u]` with
`W^{-1/2} ≤ Ψ ≤ N^{-a}` and `W⁻¹ ≤ Ψ²`. It uses `highProb_detFlucDelta_of_localLawN`,
`detAvgIBP_stochDom_of_localLawN` and `eventually_etaEnv_sq_leN`;
`eventually_rpow_neg_one_le_psi_sq`/`eventually_psi_sq_le_one` carry no `E`-binder. -/
theorem detAvgIBP_stochDom_of_localLaw'N (d : Dims) {E : ℕ → ℝ} {κ : ℝ} {u Ψ : ℕ → ℝ}
    {a K : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hll : LocalLawUnifIccN d E u u Ψ) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt (E N) (u N))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  have hE' : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  let θ := detFlucTheta a 1
  obtain ⟨hθ0, hθa, _, hθ1⟩ := detFlucTheta_specs ha one_pos
  have hΩ := highProb_detFlucDelta_of_localLawN d hE' hu0 hu1 ha hK
    hθ0 hθa.le hθ1 hη hΨhi hll
  have hδ1 : ∀ᶠ N : ℕ in atTop,
      detFlucDelta Ψ θ N ≤ 1 / 2 :=
    Eventually.of_forall fun N => by linarith [detFlucDelta_le_quarter Ψ θ N]
  exact detAvgIBP_stochDom_of_localLawN d hκ0 hκ1 hE hu0 hu1 ha hK
    hη hΨlo hΨhi hΨ0 hWΨ (by linarith : 0 ≤ 2 * K + 1)
    (by norm_num : 0 ≤ (1 : ℝ))
    (eventually_etaEnv_sq_leN hE' hu1 hK hη)
    (eventually_rpow_neg_one_le_psi_sq d hΨlo)
    (eventually_psi_sq_le_one ha hΨ0 hΨhi) hδ1 hΩ hll

/-- **The same bound without the hypotheses `0 ≤ Ψ` and `W⁻¹ ≤ Ψ²`.** It uses the generic
`UnifDomIcc.mono_control` (on `LocalLawUnifIccN`, an abbreviation of `UnifDomIcc`) and
`detAvgIBP_stochDom_of_localLaw'N`. -/
theorem detAvgIBP_stochDom_of_localLaw_completeN (d : Dims) {E : ℕ → ℝ} {κ : ℝ}
    {u Ψ : ℕ → ℝ} {a K : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : ∀ N, |E N| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIccN d E u u Ψ) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt (E N) (u N))
          - mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  let Ψ' := detAvgSafePsi d Ψ
  have hEq := eventually_detAvgSafePsi_eq d hΨlo
  have hEq' : ∀ᶠ N : ℕ in atTop, Ψ' N = Ψ N := hEq
  have hΨhi' : ∀ᶠ N : ℕ in atTop, Ψ' N ≤ (N : ℝ) ^ (-a) := by
    filter_upwards [hEq', hΨhi] with N hEqN hN
    rw [hEqN]
    exact hN
  have hll' : LocalLawUnifIccN d E u u Ψ' :=
    hll.mono_control (fun N _ _ _ => le_max_left _ _)
  have h := detAvgIBP_stochDom_of_localLaw'N d hκ0 hκ1 hE hu0 hu1
    ha hK hη (Eventually.of_forall fun N => le_max_right _ _) hΨhi'
    (detAvgSafePsi_nonneg d Ψ) (W_inv_le_detAvgSafePsi_sq d Ψ) hll'
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hEq'] with N hN hEqN
  have hEqN' : max (Ψ N) (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2)) = Ψ N := hEqN
  simpa [badSet, detAvgSafePsi, hEqN'] using hN

section Compat

end Compat

end RBM.Gauss
