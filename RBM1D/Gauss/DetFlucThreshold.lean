/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.MinorDiffCond
import RBM1D.Flow.Thm221Bare
import RBM1D.Flow.EnergyUniform
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.CutoffBounds
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Flow.Eq548Producer
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.Eq45Small
import RBM1D.Gauss.Step6Sample

/-!
# A movable deterministic threshold for fixed-time fluctuation averaging

The threshold is chosen after the requested stochastic-domination exponent.  A positive
floor makes its finite initial segment harmless without imposing a global sign condition
on the deterministic entry control.
-/

namespace RBM.Gauss

open Filter MeasureTheory Topology

/-- Positive, capped threshold with a polynomial floor. -/
noncomputable def detFlucDelta (Ψ : ℕ → ℝ) (θ : ℝ) (N : ℕ) : ℝ :=
  min (1 / 4 : ℝ)
    (((N : ℝ) + 4) ^ θ * max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))))

/-- The regularized entry control used in the all-`N` net theorem. -/
noncomputable def detFlucControl (Ψ : ℕ → ℝ) (N : ℕ) : ℝ :=
  max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ)))

/-- A threshold exponent chosen after the desired domination tolerance. -/
noncomputable def detFlucTheta (a τ : ℝ) : ℝ :=
  min (a / 8) (min (τ / 32) (1 / 8))

theorem detFlucTheta_specs {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    0 < detFlucTheta a τ ∧ detFlucTheta a τ < a / 4 ∧
      detFlucTheta a τ < τ / 16 ∧ detFlucTheta a τ ≤ 1 / 4 := by
  unfold detFlucTheta
  have hpos : 0 < min (a / 8) (min (τ / 32) (1 / 8)) :=
    lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have ha8 := min_le_left (a / 8) (min (τ / 32) (1 / 8))
  have hτ32 := (min_le_right (a / 8) (min (τ / 32) (1 / 8))).trans
    (min_le_left (τ / 32) (1 / 8))
  have h8 := (min_le_right (a / 8) (min (τ / 32) (1 / 8))).trans
    (min_le_right (τ / 32) (1 / 8))
  refine ⟨hpos, ?_, ?_, ?_⟩ <;> linarith

theorem detFlucControl_pos (Ψ : ℕ → ℝ) (N : ℕ) :
    0 < detFlucControl Ψ N := by
  unfold detFlucControl
  have hn : (0 : ℝ) < (N : ℝ) + 4 := by positivity
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hn _) (le_max_right _ _)

theorem detFlucControl_ge_psi (Ψ : ℕ → ℝ) (N : ℕ) :
    Ψ N ≤ detFlucControl Ψ N := le_max_left _ _

theorem detFlucControl_floor (Ψ : ℕ → ℝ) (N : ℕ) :
    ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ detFlucControl Ψ N := le_max_right _ _

/-- The positive floor does not change the eventual polynomial upper scale. -/
theorem detFlucControl_le_rpow {Ψ : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hΨ : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) :
    ∀ᶠ N : ℕ in atTop,
      detFlucControl Ψ N ≤ (N : ℝ) ^ (-(min a 1)) := by
  let β : ℝ := min a 1
  have hβa : β ≤ a := min_le_left _ _
  have hβ1 : β ≤ 1 := min_le_right _ _
  filter_upwards [hΨ, eventually_ge_atTop 1] with N hΨN hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hx : (N : ℝ) ≤ (N : ℝ) + 4 := by linarith
  have hfloor : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnp hx (by norm_num)
  unfold detFlucControl
  apply max_le
  · exact hΨN.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  · exact hfloor.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))

theorem detFlucControl_rpow_neg_four_le (Ψ : ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(4 : ℝ)) ≤ detFlucControl Ψ N := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hsq : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hlow := Real.rpow_le_rpow_of_nonpos
    (by positivity : (0 : ℝ) < (N : ℝ) + 4) hsq
    (by norm_num : -(2 : ℝ) ≤ 0)
  have hr : ((N : ℝ) ^ (2 : ℕ)) ^ (-(2 : ℝ)) = (N : ℝ) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    norm_num
  rw [hr] at hlow
  exact hlow.trans (detFlucControl_floor Ψ N)

theorem detFlucDelta_pos (Ψ : ℕ → ℝ) (θ : ℝ) (N : ℕ) :
    0 < detFlucDelta Ψ θ N := by
  unfold detFlucDelta
  have hn : (0 : ℝ) < (N : ℝ) + 4 := by positivity
  exact lt_min (by norm_num) (mul_pos (Real.rpow_pos_of_pos hn θ)
    (lt_of_lt_of_le (Real.rpow_pos_of_pos hn _) (le_max_right _ _)))

theorem detFlucDelta_le_quarter (Ψ : ℕ → ℝ) (θ : ℝ) (N : ℕ) :
    detFlucDelta Ψ θ N ≤ 1 / 4 := min_le_left _ _

theorem detFlucDelta_floor_le {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ detFlucDelta Ψ θ N := by
  have hx4 : (4 : ℝ) ≤ (N : ℝ) + 4 := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hfloor : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ 1 / 4 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) hx4
      (by norm_num : -(2 : ℝ) ≤ 0)
    norm_num at h ⊢
    linarith
  have hpow : 1 ≤ ((N : ℝ) + 4) ^ θ :=
    Real.one_le_rpow (by linarith : (1 : ℝ) ≤ (N : ℝ) + 4) hθ
  unfold detFlucDelta
  apply le_min
  · exact hfloor
  · have hmax : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤
        max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) := le_max_right _ _
    have hpos : 0 ≤ ((N : ℝ) + 4) ^ (-(2 : ℝ)) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hpos,
      mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) + 4) θ)
        (sub_nonneg.mpr hmax)]

theorem detFlucDelta_polyLo {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) :
    PolyLo (detFlucDelta Ψ θ) := by
  refine ⟨1, one_pos, 4, ?_⟩
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hsq : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hlow := Real.rpow_le_rpow_of_nonpos
    (by positivity : (0 : ℝ) < (N : ℝ) + 4) hsq
    (by norm_num : -(2 : ℝ) ≤ 0)
  have hr : ((N : ℝ) ^ (2 : ℕ)) ^ (-(2 : ℝ)) = (N : ℝ) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  rw [hr] at hlow
  simpa only [one_mul] using hlow.trans (detFlucDelta_floor_le hθ N)

/-- Both the entry-control branch and the positive floor decay at a common power. -/
theorem detFlucDelta_le_rpow {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) :
    ∀ᶠ N : ℕ in atTop,
      detFlucDelta Ψ θ N ≤ (N : ℝ) ^ (-(min (a / 2) 1)) := by
  let β : ℝ := min (a / 2) 1
  have hβa : β ≤ a / 2 := min_le_left _ _
  have hβ1 : β ≤ 1 := min_le_right _ _
  filter_upwards [hΨ, eventually_ge_atTop 4] with N hΨN hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hnpos : (0 : ℝ) < N := by linarith
  have hx0 : (0 : ℝ) ≤ (N : ℝ) + 4 := by positivity
  have hxN : (N : ℝ) ≤ (N : ℝ) + 4 := by linarith
  have hxN2 : (N : ℝ) + 4 ≤ (N : ℝ) ^ (2 : ℕ) := by
    have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hpow : ((N : ℝ) + 4) ^ θ ≤ (N : ℝ) ^ (2 * θ) := by
    calc
      ((N : ℝ) + 4) ^ θ ≤ ((N : ℝ) ^ (2 : ℕ)) ^ θ :=
        Real.rpow_le_rpow hx0 hxN2 hθ0
      _ = (N : ℝ) ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        ring
  have hfloor : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤ (N : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnpos hxN (by norm_num)
  have hΨcap : Ψ N ≤ (N : ℝ) ^ (-(β + 2 * θ)) := by
    calc
      Ψ N ≤ (N : ℝ) ^ (-a) := hΨN
      _ ≤ (N : ℝ) ^ (-(β + 2 * θ)) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hfloorcap : ((N : ℝ) + 4) ^ (-(2 : ℝ)) ≤
      (N : ℝ) ^ (-(β + 2 * θ)) := by
    exact hfloor.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hmax : max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) ≤
      (N : ℝ) ^ (-(β + 2 * θ)) := max_le hΨcap hfloorcap
  have hraw : ((N : ℝ) + 4) ^ θ *
      max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) ≤
      (N : ℝ) ^ (2 * θ) * (N : ℝ) ^ (-(β + 2 * θ)) := by
    calc
      _ ≤ (N : ℝ) ^ (2 * θ) *
          max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hpow (detFlucControl_pos Ψ N).le
      _ ≤ (N : ℝ) ^ (2 * θ) * (N : ℝ) ^ (-(β + 2 * θ)) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
  calc
    detFlucDelta Ψ θ N ≤ ((N : ℝ) + 4) ^ θ *
        max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) := min_le_right _ _
    _ ≤ (N : ℝ) ^ (2 * θ) * (N : ℝ) ^ (-(β + 2 * θ)) := hraw
    _ = (N : ℝ) ^ (-β) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

/-- The required Good-event margin, including the global positive control floor. -/
theorem detFlucDelta_margin {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (θ / 2) * detFlucControl Ψ N ≤ detFlucDelta Ψ θ N := by
  let β : ℝ := min a 1
  have hβa : β ≤ a := min_le_left _ _
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hβθ : 0 < β - θ / 2 := by
    have hβpos : 0 < β := lt_min ha (by norm_num)
    rcases le_total a 1 with ha1 | ha1
    · have : β = a := min_eq_left ha1
      rw [this]
      linarith
    · have : β = 1 := min_eq_right ha1
      rw [this]
      linarith
  filter_upwards [detFlucControl_le_rpow ha hΨ,
    eventually_le_rpow 4 hβθ, eventually_ge_atTop 1] with N hctrl hpow hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hpowp : (0 : ℝ) < (N : ℝ) ^ (β - θ / 2) := Real.rpow_pos_of_pos hnp _
  have hcap : (N : ℝ) ^ (θ / 2) * detFlucControl Ψ N ≤ 1 / 4 := by
    have hh : (N : ℝ) ^ (θ / 2) * detFlucControl Ψ N ≤
        (N : ℝ) ^ (-(β - θ / 2)) := by
      calc
        _ ≤ (N : ℝ) ^ (θ / 2) * (N : ℝ) ^ (-β) :=
          mul_le_mul_of_nonneg_left hctrl (by positivity)
        _ = (N : ℝ) ^ (-(β - θ / 2)) := by
          rw [← Real.rpow_add hnp]
          congr 1
          ring
    have hquarter : (N : ℝ) ^ (-(β - θ / 2)) ≤ 1 / 4 := by
      rw [Real.rpow_neg hnp.le]
      rw [inv_le_iff_one_le_mul₀ hpowp]
      linarith
    exact hh.trans hquarter
  have hraw : (N : ℝ) ^ (θ / 2) * detFlucControl Ψ N ≤
      ((N : ℝ) + 4) ^ θ * detFlucControl Ψ N := by
    have hbase : (N : ℝ) ^ (θ / 2) ≤ ((N : ℝ) + 4) ^ θ := by
      calc
        (N : ℝ) ^ (θ / 2) ≤ (N : ℝ) ^ θ :=
          Real.rpow_le_rpow_of_exponent_le hn (by linarith)
        _ ≤ ((N : ℝ) + 4) ^ θ :=
          Real.rpow_le_rpow hnp.le (by linarith) hθ0.le
    exact mul_le_mul_of_nonneg_right hbase (detFlucControl_pos Ψ N).le
  unfold detFlucDelta
  exact le_min hcap hraw

/-- For each fixed coefficient, the threshold is eventually small. -/
theorem detFlucDelta_eventually_mul_le_one {Ψ : ℕ → ℝ} {a θ C : ℝ}
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, C * detFlucDelta Ψ θ N ≤ 1 := by
  have hβ : 0 < min (a / 2) 1 := lt_min (by linarith) (by norm_num)
  filter_upwards [detFlucDelta_le_rpow ha hθ0 hθa hθ1 hΨ,
    eventually_le_rpow C hβ, eventually_ge_atTop 1] with N hδ hCN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (0 : ℝ) < (N : ℝ) ^ (min (a / 2) 1) := Real.rpow_pos_of_pos hn _
  have hbound : C * (N : ℝ) ^ (-(min (a / 2) 1)) ≤ 1 := by
    rw [Real.rpow_neg hn.le]
    rw [mul_inv_le_iff₀ hp]
    simpa using hCN
  exact (mul_le_mul_of_nonneg_left hδ hC).trans hbound

theorem detFlucDelta_moment_small {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) (p : ℕ) :
    (∀ᶠ N : ℕ in atTop, 8 * (2 * p : ℝ) * detFlucDelta Ψ θ N ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      2 * minorDiffC (2 * p) * (2 * detFlucDelta Ψ θ N)
        + 2 * detFlucDelta Ψ θ N ≤ 1) := by
  have hC : 0 ≤ 4 * minorDiffC (2 * p) + 2 := by
    have := minorDiffC_nonneg (2 * p)
    linarith
  constructor
  · filter_upwards [detFlucDelta_eventually_mul_le_one ha hθ0 hθa hθ1 hΨ
      (C := 16 * (p : ℝ)) (by positivity)] with N hN
    nlinarith
  · filter_upwards [detFlucDelta_eventually_mul_le_one ha hθ0 hθa hθ1 hΨ
      (C := 4 * minorDiffC (2 * p) + 2) hC] with N hN
    nlinarith

/-- The cap never reduces the threshold below a quarter of a small entry control. -/
theorem detFlucDelta_quarter_psi_le {Ψ : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    {N : ℕ} (hΨ0 : 0 ≤ Ψ N) (hΨ1 : Ψ N ≤ 1) :
    Ψ N / 4 ≤ detFlucDelta Ψ θ N := by
  unfold detFlucDelta
  apply le_min
  · linarith
  · have hn : (1 : ℝ) ≤ (N : ℝ) + 4 := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    have hp : 1 ≤ ((N : ℝ) + 4) ^ θ := Real.one_le_rpow hn hθ
    have hmax : Ψ N ≤ max (Ψ N) (((N : ℝ) + 4) ^ (-(2 : ℝ))) :=
      le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hΨ0,
      mul_nonneg (Real.rpow_nonneg (by positivity) θ) (sub_nonneg.mpr hmax)]

/-- The bandwidth normalization is an eventual consequence of the entry-scale floor.
The all-`N` version is false at `N=0`; this is the precise quantifier needed downstream. -/
theorem eventually_W_inv_le_detFlucDelta_sq (d : Dims) {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ : 0 ≤ θ)
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) :
    ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ))⁻¹ ≤ (4 * detFlucDelta Ψ θ N) ^ 2 := by
  filter_upwards [hΨlo, hΨhi, eventually_ge_atTop 1] with N hlow hhigh hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hΨ0 : 0 ≤ Ψ N :=
    le_trans (Real.rpow_nonneg hw.le _) hlow
  have hΨ1 : Ψ N ≤ 1 :=
    hhigh.trans (by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith : -a ≤ (0 : ℝ))))
  have hquarter := detFlucDelta_quarter_psi_le hθ hΨ0 hΨ1
  have hΨδ : Ψ N ≤ 4 * detFlucDelta Ψ θ N := by linarith
  have hsq1 := pow_le_pow_left₀ (Real.rpow_nonneg hw.le _) hlow 2
  have hsq2 := pow_le_pow_left₀ hΨ0 hΨδ 2
  have hr : (((d.W N : ℝ)) ^ (-(1 : ℝ) / 2)) ^ 2 = ((d.W N : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num [Real.rpow_neg_one]
  rw [hr] at hsq1
  exact hsq1.trans hsq2

end RBM.Gauss
