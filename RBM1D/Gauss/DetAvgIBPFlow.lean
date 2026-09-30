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

/-- A harmless finite-prefix regularization of the entry scale.  It lets an
all-size normalization coexist with an eventual bandwidth hypothesis. -/
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

end RBM.Gauss
