/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetIBPWeighted
import RBM1D.Gauss.DetFlucAvgComplete

/-!
# Averaged one-loop closure at one deterministic Gaussian-flow time
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- A singleton `UnifDomIcc` estimate supplies stochastic domination of a
deterministic-time sequence once the index family has polynomial cardinality. -/
theorem stochDom_of_unifDomIcc_singleton {d : Dims} {V : ℕ → Type*}
    [∀ N, Fintype (V N)] {C : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ C)
    {u : ℕ → ℝ} {ξ ζ : ∀ N, ℝ → V N → Ω d → ℝ}
    (h : UnifDomIcc (P d) u u ξ ζ) :
    StochDom (P d) (fun N b ω => ξ N (u N) b ω)
      (fun N b ω => ζ N (u N) b ω) := by
  refine StochDom.of_forall_le hcard fun τ hτ D hD => ?_
  filter_upwards [h τ hτ D hD] with N hN b
  exact hN (u N) ⟨le_rfl, le_rfl⟩ b

/-- Actual-model one-loop algebra and short-edge row stability, with the three
error bounds at the same deterministic scale. -/
theorem norm_detAvgIBP_le (d : Dims) {N : ℕ} {E κ v : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (ω : Ω d) (a : ZMod (d.L N))
    {A Φ : ℝ} (hIBP : ∀ i : d.Idx N,
      ‖condExpDiag d N v (zt E v) (mE E) i ω
        - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N v ω) (zt E v) k k - mE E)‖ ≤ A * Φ)
    (hFArow : ∀ i : d.Idx N,
      ‖flucAvg d N v (zt E v) (mE E)
        (fun j => Sblk (d.L N) (d.W N) i j) ω‖ ≤ A * Φ)
    (hFAblk : ‖flucAvg d N v (zt E v) (mE E)
      (blkCoef (d.L N) (d.W N) a) ω‖ ≤ A * Φ) :
    ‖Matrix.trace ((green (Hflow d N v ω) (zt E v)
      - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) a)‖ ≤
      (1 + 2 * Kstab κ) * A * Φ := by
  have h := norm_trace_green_sub_mul_Eblk_le_flucAvg hκ0 hκ1 hE hv0 hv1 v ω
    (A := A * Φ) (B := A * Φ) (B' := A * Φ) hIBP hFArow a hFAblk
  calc
    _ ≤ A * Φ + Kstab κ * (A * Φ + A * Φ) := h
    _ = (1 + 2 * Kstab κ) * A * Φ := by ring

/-- The fixed-time stochastic assembler.  T336 provides `hIBP`, and T345
provides the row and block fluctuation bounds. -/
theorem detAvgIBP_stochDom_of_inputs (d : Dims) {E κ : ℝ} {u Ψ : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hIBP : UnifDomIcc (P d) u u
      (fun N v (i : d.Idx N) ω =>
        ‖condExpDiag d N v (zt E v) (mE E) i ω
          - (v : ℂ) * mE E ^ 2 * ∑ k,
            (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖)
      (fun N _ _ _ => Ψ N * Ψ N))
    (hFArow : UnifDomIcc (P d) u u
      (fun N v (i : d.Idx N) ω =>
        ‖flucAvg d N v (zt E v) (mE E)
          (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N))
    (hFAblk : UnifDomIcc (P d) u u
      (fun N v (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N v (zt E v) (mE E)
          (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N)) :
    StochDom (P d)
      (fun N (a : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt E (u N))
          - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
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
  have h := norm_detAvgIBP_le d hκ0 hκ1 hE (hu0 N) (hu1 N) ω a
    (A := Φ) (Φ := Ψ N * Ψ N)
    (fun i => hAB (Sum.inl (Sum.inl i)))
    (fun i => hAB (Sum.inl (Sum.inr i)))
    (hAB (Sum.inr a))
  calc
    _ ≤ (1 + 2 * Kstab κ) * Φ * (Ψ N * Ψ N) := h
    _ = (1 + 2 * Kstab κ) * Φ ^ 1 * (Ψ N * Ψ N) := by ring

/-- The actual Gaussian IBP remainder (T336) and fixed-time row/block fluctuation
averages (T345) close the deterministic-scale one-loop equation.  Every numerical
premise of the IBP source remains visible. -/
theorem detAvgIBP_stochDom_of_localLaw (d : Dims) {E κ : ℝ} {u Ψ δ : ℕ → ℝ}
    {a K Kenv B : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop,
      ((etaT E (u N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E u u δ))
    (hll : LocalLawUnifIcc d E u u Ψ) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt E (u N))
          - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  have hE' : |E| < 2 := by linarith
  have hIBP := unifDomIcc_condExpDiag_weighted (d := d) (E := E)
    (s := u) (t := u) (Ψ := Ψ) (δ := δ) (Kenv := Kenv) (B := B)
    hE' hu0 hu1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hWΨ hδ1 hΩ hll
  have hFA := fixedTimeFAStatement_proved d E u Ψ a K ha hK hE'
    (fun N => ⟨hu0 N, hu1 N⟩) hη (hΨlo.and hΨhi) hll
  exact detAvgIBP_stochDom_of_inputs d hκ0 hκ1 hE hu0 hu1 hΨ0 hIBP
    (by simpa only [pow_two] using hFA.1)
    (by simpa only [pow_two] using hFA.2)

/-- The polynomial spectral floor supplies the squared resolvent envelope needed
only on exceptional IBP samples. -/
theorem eventually_etaEnv_sq_le {E K : ℝ} {u : ℕ → ℝ}
    (hE : |E| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N)) :
    ∀ᶠ N : ℕ in atTop,
      ((etaT E (u N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ (2 * K + 1) := by
  filter_upwards [etaInv_le_rpow_of_lower hE hu1 hK hη,
    eventually_ge_atTop 1, eventually_le_rpow 4 one_pos]
      with N hInv hN1 h4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 1 ≤ (N : ℝ) ^ K := Real.one_le_rpow hn hK
  have hbase : (etaT E (u N))⁻¹ + 1 ≤ 2 * (N : ℝ) ^ K := by linarith
  have henv0 : 0 ≤ (etaT E (u N))⁻¹ + 1 := by
    have hηpos := etaT_pos_of_lt_one hE (hu1 N)
    positivity
  have hsq := pow_le_pow_left₀ henv0 hbase 2
  have hpow2 : ((N : ℝ) ^ K) ^ 2 = (N : ℝ) ^ (2 * K) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  calc
    ((etaT E (u N))⁻¹ + 1) ^ 2 ≤ (2 * (N : ℝ) ^ K) ^ 2 := hsq
    _ = 4 * (N : ℝ) ^ (2 * K) := by
      rw [mul_pow, hpow2]
      ring
    _ ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (2 * K) := by gcongr
    _ = (N : ℝ) ^ (2 * K + 1) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring

/-- The bandwidth lower control implies the IBP producer's polynomial lower bound
on its squared deterministic scale. -/
theorem eventually_rpow_neg_one_le_psi_sq (d : Dims) {Ψ : ℕ → ℝ}
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ Ψ N * Ψ N := by
  filter_upwards [hΨlo, W_le_self d, eventually_ge_atTop 1]
    with N hΨN hWN hN1
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hwr : (d.W N : ℝ) ≤ N := by exact_mod_cast hWN
  have hInv : (N : ℝ) ^ (-(1 : ℝ)) ≤ ((d.W N : ℝ))⁻¹ := by
    rw [Real.rpow_neg_one]
    exact inv_anti₀ hw hwr
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hw.le _) hΨN 2
  have hr : (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2)) ^ 2 = ((d.W N : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num [Real.rpow_neg_one]
  rw [hr] at hsq
  rw [← pow_two]
  exact hInv.trans hsq

/-- Polynomial decay of `Ψ` makes the squared IBP control eventually at most one. -/
theorem eventually_psi_sq_le_one {Ψ : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) :
    ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1 := by
  filter_upwards [hΨhi, eventually_ge_atTop 1] with N hΨN hN1
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpow : (N : ℝ) ^ (-a) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith : -a ≤ (0 : ℝ)))
  have hΨ1 : Ψ N ≤ 1 := hΨN.trans hpow
  nlinarith [mul_nonneg (hΨ0 N) (sub_nonneg.mpr hΨ1)]

/-- One-loop averaging from the actual singleton entry local law.  The only
all-size normalization is the deterministic `W⁻¹≤Ψ²` required by T336's
weighted IBP interface; all probabilistic inputs are constructed here. -/
theorem detAvgIBP_stochDom_of_localLaw' (d : Dims) {E κ : ℝ} {u Ψ : ℕ → ℝ}
    {a K : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hll : LocalLawUnifIcc d E u u Ψ) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt E (u N))
          - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  have hE' : |E| < 2 := by linarith
  let θ := detFlucTheta a 1
  obtain ⟨hθ0, hθa, _, hθ1⟩ := detFlucTheta_specs ha one_pos
  have hΩ := highProb_detFlucDelta_of_localLaw d hE' hu0 hu1 ha hK
    hθ0 hθa.le hθ1 hη hΨhi hll
  have hδ1 : ∀ᶠ N : ℕ in atTop,
      detFlucDelta Ψ θ N ≤ 1 / 2 :=
    Eventually.of_forall fun N => by linarith [detFlucDelta_le_quarter Ψ θ N]
  exact detAvgIBP_stochDom_of_localLaw d hκ0 hκ1 hE hu0 hu1 ha hK
    hη hΨlo hΨhi hΨ0 hWΨ (by linarith : 0 ≤ 2 * K + 1)
    (by norm_num : 0 ≤ (1 : ℝ))
    (eventually_etaEnv_sq_le hE' hu1 hK hη)
    (eventually_rpow_neg_one_le_psi_sq d hΨlo)
    (eventually_psi_sq_le_one ha hΨ0 hΨhi) hδ1 hΩ hll

/-- A harmless finite-prefix regularization of the entry scale.  It lets the
all-size normalization in T336 coexist with T345's eventual bandwidth hypothesis. -/
noncomputable def detAvgSafePsi (d : Dims) (Ψ : ℕ → ℝ) (N : ℕ) : ℝ :=
  max (Ψ N) (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2))

theorem detAvgSafePsi_nonneg (d : Dims) (Ψ : ℕ → ℝ) (N : ℕ) :
    0 ≤ detAvgSafePsi d Ψ N := by
  unfold detAvgSafePsi
  exact (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (le_max_right _ _)

theorem W_inv_le_detAvgSafePsi_sq (d : Dims) (Ψ : ℕ → ℝ) (N : ℕ) :
    ((d.W N : ℝ))⁻¹ ≤ detAvgSafePsi d Ψ N * detAvgSafePsi d Ψ N := by
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hlo : ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ detAvgSafePsi d Ψ N :=
    le_max_right _ _
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hw.le _) hlo 2
  have hr : (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2)) ^ 2 = ((d.W N : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num [Real.rpow_neg_one]
  rw [hr] at hsq
  simpa only [pow_two] using hsq

/-- The regularization vanishes on the eventual bandwidth regime. -/
theorem eventually_detAvgSafePsi_eq (d : Dims) {Ψ : ℕ → ℝ}
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop, detAvgSafePsi d Ψ N = Ψ N := by
  filter_upwards [hΨlo] with N hN
  exact max_eq_left hN

/-- Deterministic-scale one-loop averaging at any prescribed singleton time,
with exactly the fixed-time local-law and bandwidth hypotheses. -/
theorem detAvgIBP_stochDom_of_localLaw_complete (d : Dims) {E κ : ℝ}
    {u Ψ : ℕ → ℝ} {a K : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hu0 : ∀ N, 0 ≤ u N) (hu1 : ∀ N, u N < 1)
    (ha : 0 < a) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIcc d E u u Ψ) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt E (u N))
          - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ => Ψ N * Ψ N) := by
  let Ψ' := detAvgSafePsi d Ψ
  have hEq := eventually_detAvgSafePsi_eq d hΨlo
  have hEq' : ∀ᶠ N : ℕ in atTop, Ψ' N = Ψ N := hEq
  have hΨhi' : ∀ᶠ N : ℕ in atTop, Ψ' N ≤ (N : ℝ) ^ (-a) := by
    filter_upwards [hEq', hΨhi] with N hEqN hN
    rw [hEqN]
    exact hN
  have hll' : LocalLawUnifIcc d E u u Ψ' :=
    hll.mono_control (fun N _ _ _ => le_max_left _ _)
  have h := detAvgIBP_stochDom_of_localLaw' d hκ0 hκ1 hE hu0 hu1
    ha hK hη (Eventually.of_forall fun N => le_max_right _ _) hΨhi'
    (detAvgSafePsi_nonneg d Ψ) (W_inv_le_detAvgSafePsi_sq d Ψ) hll'
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hEq'] with N hN hEqN
  have hEqN' : max (Ψ N) (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2)) = Ψ N := hEqN
  simpa [badSet, detAvgSafePsi, hEqN'] using hN

/-- The initial-time one-loop error vanishes identically for every sample. -/
theorem detAvgIBP_at_zero (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| ≤ 2)
    (ω : Ω d) (a : ZMod (d.L N)) :
    Matrix.trace ((green (Hflow d N 0 ω) (zt E 0)
      - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) a) = 0 := by
  rw [Hflow_zero, zt_zero, green_zero_eq_smul (mE_mul hE)]
  simp

/-- The Step 1 first-cell law simultaneously supports T336's weighted IBP,
T345's two fluctuation averages, and the resulting one-loop estimate at the
same positive deterministic time. -/
theorem detAvgIBP_firstCell_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, 0 < firstCellT τ' N) ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellT τ') (firstCellT τ')
        firstCellPsiWeighted ∧
      UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (i : Dims.exampleGrow.Idx N) ω =>
          ‖condExpDiag Dims.exampleGrow N v (zt 0 v) (mE 0) i ω
            - (v : ℂ) * mE 0 ^ 2 * ∑ k,
              (Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i k : ℂ)
                * (green (Hflow Dims.exampleGrow N v ω) (zt 0 v) k k - mE 0)‖)
        (fun N _ _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N) ∧
      UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (i : Dims.exampleGrow.Idx N) ω =>
          ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
            (fun j => Sblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) i j) ω‖)
        (fun N _ _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N) ∧
      UnifDomIcc (P Dims.exampleGrow) (firstCellT τ') (firstCellT τ')
        (fun N v (b : ZMod (Dims.exampleGrow.L N)) ω =>
          ‖flucAvg Dims.exampleGrow N v (zt 0 v) (mE 0)
            (blkCoef (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b) ω‖)
        (fun N _ _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N) ∧
      StochDom (P Dims.exampleGrow)
        (fun N (b : ZMod (Dims.exampleGrow.L N)) ω =>
          ‖Matrix.trace ((green (Hflow Dims.exampleGrow N (firstCellT τ' N) ω)
            (zt 0 (firstCellT τ' N))
            - mE 0 • (1 : Matrix (Dims.exampleGrow.Idx N)
              (Dims.exampleGrow.Idx N) ℂ)) *
              Eblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b)‖)
        (fun N _ _ => firstCellPsiWeighted N * firstCellPsiWeighted N) := by
  obtain ⟨τ', hτ', hpos, hu, hη, hΨpair, hll, ⟨hFArow, hFAblk⟩⟩ :=
    fixedTimeFA_gaussian_witness_pos
  let d := Dims.exampleGrow
  let Ψ := firstCellPsiWeighted
  have hu0 : ∀ N, 0 ≤ firstCellT τ' N := fun N => (hu N).1
  have hu1 : ∀ N, firstCellT τ' N < 1 := fun N => (hu N).2
  have hΨ0 : ∀ N, 0 ≤ Ψ N := by
    intro N
    exact mul_nonneg (by norm_num) (firstCellPsi_pos N).le
  obtain ⟨_, _, hWinv, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  have hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N := by
    intro N
    have h := hWinv N
    change ((d.W N : ℝ))⁻¹ ≤ 4 * firstCellPsi N ^ 2 at h
    dsimp [Ψ, firstCellPsiWeighted]
    nlinarith
  have hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N :=
    hΨpair.mono (fun N hN => hN.1)
  have hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8) :=
    hΨpair.mono (fun N hN => hN.2)
  have hΨhi' : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-( (1 : ℝ) / 8)) := by
    filter_upwards [hΨhi] with N hN
    convert hN using 1 <;> ring
  let θ := detFlucTheta (1 / 8) 1
  obtain ⟨hθ0, hθa, _, hθ1⟩ :=
    detFlucTheta_specs (by norm_num : (0 : ℝ) < 1 / 8) one_pos
  have hΩ := highProb_detFlucDelta_of_localLaw d (E := 0)
    (u := firstCellT τ') (Ψ := Ψ) (a := 1 / 8) (K := 1) (θ := θ)
    (by norm_num) hu0 hu1 (by norm_num) (by norm_num)
    hθ0 hθa.le hθ1 hη hΨhi' hll
  have hδ1 : ∀ᶠ N : ℕ in atTop, detFlucDelta Ψ θ N ≤ 1 / 2 :=
    Eventually.of_forall fun N => by linarith [detFlucDelta_le_quarter Ψ θ N]
  have hEnv : ∀ᶠ N : ℕ in atTop,
      ((etaT 0 (firstCellT τ' N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ (3 : ℝ) := by
    convert eventually_etaEnv_sq_le (by norm_num : |(0 : ℝ)| < 2)
      hu1 (by norm_num : (0 : ℝ) ≤ 1) hη using 1 <;> norm_num
  have hIBP := unifDomIcc_condExpDiag_weighted (d := d) (E := 0)
    (s := firstCellT τ') (t := firstCellT τ') (Ψ := Ψ)
    (δ := detFlucDelta Ψ θ) (Kenv := 3) (B := 1)
    (by norm_num) hu0 hu1 hΨ0 (by norm_num) (by norm_num)
    hEnv
    (eventually_rpow_neg_one_le_psi_sq d hΨlo)
    (eventually_psi_sq_le_one (by norm_num) hΨ0 hΨhi')
    hWΨ hδ1 hΩ hll
  have hFArow' : UnifDomIcc (P d) (firstCellT τ') (firstCellT τ')
      (fun N v (i : d.Idx N) ω =>
        ‖flucAvg d N v (zt 0 v) (mE 0)
          (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
    simpa only [Ψ, firstCellPsiWeighted, pow_two] using hFArow
  have hFAblk' : UnifDomIcc (P d) (firstCellT τ') (firstCellT τ')
      (fun N v (b : ZMod (d.L N)) ω =>
        ‖flucAvg d N v (zt 0 v) (mE 0) (blkCoef (d.L N) (d.W N) b) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
    simpa only [Ψ, firstCellPsiWeighted, pow_two] using hFAblk
  have hAvg := detAvgIBP_stochDom_of_inputs d (E := 0) (κ := 1)
    (u := firstCellT τ') (Ψ := Ψ) (by norm_num) (by norm_num)
    (by norm_num) hu0 hu1 hΨ0 hIBP hFArow' hFAblk'
  exact ⟨τ', hτ', hpos, hll, hIBP, hFArow', hFAblk', hAvg⟩

#print axioms stochDom_of_unifDomIcc_singleton
#print axioms norm_detAvgIBP_le
#print axioms detAvgIBP_stochDom_of_inputs
#print axioms detAvgIBP_stochDom_of_localLaw
#print axioms eventually_etaEnv_sq_le
#print axioms eventually_rpow_neg_one_le_psi_sq
#print axioms eventually_psi_sq_le_one
#print axioms detAvgIBP_stochDom_of_localLaw'
#print axioms detAvgIBP_stochDom_of_localLaw_complete
#print axioms detAvgIBP_at_zero
#print axioms detAvgIBP_firstCell_witness

end RBM.Gauss
