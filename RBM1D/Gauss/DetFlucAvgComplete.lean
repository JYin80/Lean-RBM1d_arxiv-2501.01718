/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetFlucThreshold

/-!
# Fixed-time fluctuation averaging at the deterministic entry scale

The moment consumer below takes the bandwidth comparison only eventually.  This is
essential: its all-size version fails at `N = 0` for the movable threshold.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- Once the bandwidth scale is reached, the floor in the threshold is below `Ψ`.
The remaining loss is at most `N^(2θ)`. -/
theorem detFlucDelta_le_rpow_mul_psi (d : Dims) {Ψ : ℕ → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop,
      detFlucDelta Ψ θ N ≤ (N : ℝ) ^ (2 * θ) * Ψ N := by
  filter_upwards [hΨlo, W_le_self d, eventually_ge_atTop 4]
    with N hΨN hWN hN4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : (0 : ℝ) < N := by linarith
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hwr : (d.W N : ℝ) ≤ N := by exact_mod_cast hWN
  have hfloorN : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num)
  have hNhalf : (N : ℝ) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hWhalf : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hw hwr (by norm_num)
  have hfloor : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ Ψ N :=
    (hfloorN.trans hNhalf).trans (hWhalf.trans hΨN)
  have hmax : max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) = Ψ N :=
    max_eq_left hfloor
  have hΨ0 : 0 ≤ Ψ N := le_trans (Real.rpow_nonneg hw.le _) hΨN
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN2 : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hpow : ((N : ℝ) + 4) ^ θ ≤ (N : ℝ) ^ (2 * θ) := by
    calc
      ((N : ℝ) + 4) ^ θ ≤ ((N : ℝ) ^ (2 : ℕ)) ^ θ :=
        Real.rpow_le_rpow (by positivity) hN2 hθ
      _ = (N : ℝ) ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        ring
  calc
    detFlucDelta Ψ θ N ≤ ((N : ℝ) + 4) ^ θ *
        max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ = ((N : ℝ) + 4) ^ θ * Ψ N := by rw [hmax]
    _ ≤ (N : ℝ) ^ (2 * θ) * Ψ N :=
      mul_le_mul_of_nonneg_right hpow hΨ0

/-- Absorb the movable threshold's polynomial loss with half of the requested
stochastic-domination tolerance. -/
theorem detFlucDelta_scale_absorb (d : Dims) {Ψ : ℕ → ℝ} {τ θ : ℝ}
    (hτ : 0 < τ) (hθ0 : 0 ≤ θ) (hθτ : θ ≤ τ / 16)
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (τ / 2) * (4 * detFlucDelta Ψ θ N ^ 2) ≤
        (N : ℝ) ^ τ * Ψ N ^ 2 := by
  filter_upwards [detFlucDelta_le_rpow_mul_psi d hθ0 hΨlo,
    eventually_ge_atTop 1, eventually_le_rpow 4 (by linarith : 0 < τ / 4)]
      with N hδ hN1 h4
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hδ0 : 0 ≤ detFlucDelta Ψ θ N := (detFlucDelta_pos Ψ θ N).le
  have hsq : detFlucDelta Ψ θ N ^ 2 ≤
      ((N : ℝ) ^ (2 * θ) * Ψ N) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have hPowExp : (N : ℝ) ^ (4 * θ) ≤ (N : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hpow2 : ((N : ℝ) ^ (2 * θ)) ^ 2 = (N : ℝ) ^ (4 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring
  have hΨsq : 0 ≤ Ψ N ^ 2 := sq_nonneg _
  calc
    (N : ℝ) ^ (τ / 2) * (4 * detFlucDelta Ψ θ N ^ 2)
      = 4 * (N : ℝ) ^ (τ / 2) * detFlucDelta Ψ θ N ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ (τ / 2) *
        (((N : ℝ) ^ (2 * θ) * Ψ N) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (4 * θ) * Ψ N ^ 2 := by
      rw [mul_pow, hpow2]; ring
    _ ≤ 4 * (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 4) * Ψ N ^ 2 := by
      gcongr
    _ ≤ (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (τ / 2) *
        (N : ℝ) ^ (τ / 4) * Ψ N ^ 2 := by
      gcongr
    _ = (N : ℝ) ^ τ * Ψ N ^ 2 := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring

/-- A family of positive thresholds gives domination at the original squared entry
control, because the threshold exponent can be chosen after the requested tolerance. -/
theorem fixedMoment_budgetFamily_absorb (d : Dims) {u Ψ : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    {V : ℕ → Type*} {ξ : ∀ N, ℝ → V N → Ω d → ℝ}
    (hfamily : ∀ θ : ℝ, 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
      UnifDomIcc (P d) u u ξ
        (fun N _ _ _ => 4 * detFlucDelta Ψ θ N ^ 2)) :
    UnifDomIcc (P d) u u ξ (fun N _ _ _ => Ψ N ^ 2) := by
  intro τ hτ D hD
  let θ := detFlucTheta a τ
  obtain ⟨hθ0, hθa, hθτ, hθ1⟩ := detFlucTheta_specs ha hτ
  have hsource := hfamily θ hθ0 hθa.le hθ1 (τ / 2) (by linarith) D hD
  filter_upwards [hsource, detFlucDelta_scale_absorb d hτ hθ0.le hθτ.le hΨlo]
    with N hN hscale v hv b
  refine (measure_mono ?_).trans (hN v hv b)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt hscale hω

end RBM.Gauss
