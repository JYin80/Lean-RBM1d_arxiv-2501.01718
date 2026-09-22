/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetFlucAvg
import RBM1D.Gauss.Step6Sample

/-!
# A movable deterministic threshold for fixed-time fluctuation averaging

The threshold is chosen after the requested stochastic-domination exponent.  A positive
floor makes its finite initial segment harmless without imposing a global sign condition
on the deterministic entry control.
-/

namespace RBM.Gauss

open Filter MeasureTheory Topology

#check highProb_goodSetFlow_of_localLaw
#check fixedMoment_gain_of_goodSetFlow
#check firstCellFlucAvg_psiSq_of_localLaw
#check polyHi_of_sq_le
#check Dims.exampleGrow
#check Dims.dim_grow
#check UnifDomIcc.mono_control

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

theorem localLaw_detFlucControl {d : Dims} {E : ℝ} {u Ψ : ℕ → ℝ}
    (hll : LocalLawUnifIcc d E u u Ψ) :
    LocalLawUnifIcc d E u u (detFlucControl Ψ) :=
  UnifDomIcc.mono_control hll (fun N _ _ _ => detFlucControl_ge_psi Ψ N)

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

theorem detFlucControl_polyLo (Ψ : ℕ → ℝ) : PolyLo (detFlucControl Ψ) :=
  ⟨1, one_pos, 4, by simpa only [one_mul] using detFlucControl_rpow_neg_four_le Ψ⟩

theorem etaInv_le_rpow_of_lower {E K : ℝ} {u : ℕ → ℝ}
    (hE : |E| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N)) :
    ∀ᶠ N : ℕ in atTop, (etaT E (u N))⁻¹ ≤ (N : ℝ) ^ K := by
  filter_upwards [hη, eventually_ge_atTop 1] with N hηN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hηpos : 0 < etaT E (u N) := etaT_pos_of_lt_one hE (hu1 N)
  have hpow : 0 < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hn _
  have h := inv_anti₀ hpow hηN
  rw [Real.rpow_neg hn.le, inv_inv] at h
  exact h

theorem etaPolyHi_of_lower {E K : ℝ} {u : ℕ → ℝ}
    (hE : |E| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N)) :
    PolyHi (fun N => (etaT E (u N))⁻¹ + 1) := by
  refine ⟨2, by norm_num, K, ?_⟩
  filter_upwards [etaInv_le_rpow_of_lower hE hu1 hK hη,
    eventually_ge_atTop 1] with N hInv hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hOne : (1 : ℝ) ≤ (N : ℝ) ^ K := Real.one_le_rpow hn hK
  linarith

theorem etaNet_bound_of_lower {E K : ℝ} {u : ℕ → ℝ}
    (hE : |E| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N)) :
    ∀ᶠ N : ℕ in atTop,
      (etaT E (u N))⁻¹ * (etaT E (u N))⁻¹ * ((N : ℝ) + 1)
        ≤ (N : ℝ) ^ (2 * K + 2) := by
  filter_upwards [etaInv_le_rpow_of_lower hE hu1 hK hη,
    eventually_ge_atTop 2] with N hInv hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (N : ℝ) + 1 ≤ (N : ℝ) ^ (2 : ℕ) := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hInv0 : 0 ≤ (etaT E (u N))⁻¹ := inv_nonneg.mpr
    (etaT_pos_of_lt_one hE (hu1 N)).le
  have hPow0 : 0 ≤ (N : ℝ) ^ K := by positivity
  have hsq : (etaT E (u N))⁻¹ * (etaT E (u N))⁻¹ ≤
      (N : ℝ) ^ K * (N : ℝ) ^ K := by nlinarith
  calc
    (etaT E (u N))⁻¹ * (etaT E (u N))⁻¹ * ((N : ℝ) + 1)
        ≤ ((N : ℝ) ^ K * (N : ℝ) ^ K) * ((N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ ((N : ℝ) ^ K * (N : ℝ) ^ K) * (N : ℝ) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hN2 (by positivity)
    _ = (N : ℝ) ^ (2 * K + 2) := by
          rw [← Real.rpow_add hn, ← Real.rpow_natCast, ← Real.rpow_add hn]
          congr 1
          ring

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

theorem detFlucDelta_tendsto_zero {Ψ : ℕ → ℝ} {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hΨ : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a)) :
    Tendsto (detFlucDelta Ψ θ) atTop (𝓝 0) := by
  have hβ : 0 < min (a / 2) 1 := lt_min (by linarith) (by norm_num)
  exact squeeze_zero' (Eventually.of_forall fun N => (detFlucDelta_pos Ψ θ N).le)
    (detFlucDelta_le_rpow ha hθ0 hθa hθ1 hΨ)
    ((tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop)

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

/-- The fixed-time entry law supplies the *same* global Good event for the threshold. -/
theorem highProb_detFlucDelta_of_localLaw (d : Dims) {E : ℝ} {u Ψ : ℕ → ℝ}
    {a K θ : ℝ} (hE : |E| < 2) (hu0 : ∀ N, 0 ≤ u N)
    (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIcc d E u u Ψ) :
    HighProb (P d) (goodSetFlow d E u u (detFlucDelta Ψ θ)) := by
  exact highProb_goodSetFlow_of_localLaw d (half_pos hθ0) hE hu0 hu1
    (fun _ => le_rfl) (by linarith : 0 ≤ 2 * K + 2) (by norm_num : 0 ≤ (4 : ℝ))
    (etaNet_bound_of_lower hE hu1 hK hη)
    (fun N => (detFlucControl_pos Ψ N).le)
    (detFlucControl_rpow_neg_four_le Ψ)
    (localLaw_detFlucControl hll)
    (detFlucDelta_margin ha hθ0 hθa hθ1 hΨhi)

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

/-- The discarded all-size normalization is already false at `N=0`. -/
theorem not_allN_W_inv_le_detFlucDelta_sq :
    ¬ ∀ (Ψ : ℕ → ℝ) (θ : ℝ) (N : ℕ),
      ((Dims.exampleGrow.W N : ℝ))⁻¹ ≤ (4 * detFlucDelta Ψ θ N) ^ 2 := by
  intro h
  have h0 := h (fun _ => 0) 0 0
  norm_num [detFlucDelta, Dims.exampleGrow_W, Dims.growW, Dims.growL] at h0

/-- All threshold inputs for the fixed-`2p` resampling gain, with the bandwidth bound
in its correct eventual form.  The only stochastic premise is the entry local law. -/
theorem fixedMoment_gain_of_localLaw (d : Dims) {E : ℝ} {u Ψ : ℕ → ℝ}
    {a K θ : ℝ} (hE : |E| < 2) (hu0 : ∀ N, 0 ≤ u N)
    (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIcc d E u u Ψ) (p : ℕ) :
    (∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (u N) (u N),
      FlucGainUpTo' d N v (zt E v) (mE E)
        (2 * (2 * minorDiffC (2 * p) * (2 * detFlucDelta Ψ θ N)
          + 2 * detFlucDelta Ψ θ N))
        (4 * detFlucDelta Ψ θ N) (2 * p) (2 * p)) ∧
    (∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ))⁻¹ ≤ (4 * detFlucDelta Ψ θ N) ^ 2) := by
  have hΩ := highProb_detFlucDelta_of_localLaw d hE hu0 hu1 ha hK
    hθ0 hθa hθ1 hη hΨhi hll
  obtain ⟨hMδ, hδC⟩ :=
    detFlucDelta_moment_small ha hθ0.le hθa hθ1 hΨhi p
  constructor
  · exact fixedMoment_gain_of_goodSetFlow d hE hu1
      (detFlucDelta_pos Ψ θ) (detFlucDelta_le_quarter Ψ θ)
      (detFlucDelta_polyLo hθ0.le)
      (etaPolyHi_of_lower hE hu1 hK hη) hΩ p hMδ hδC
  · exact eventually_W_inv_le_detFlucDelta_sq d ha hθ0.le hΨlo hΨhi

theorem firstCellS_eq_zero (τ' : ℝ) (N : ℕ) : firstCellS τ' N = 0 := by
  unfold firstCellS
  exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The established first-cell entry law restricts to its deterministic left endpoint. -/
theorem firstCell_localLaw_at_left {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellS τ')
      firstCellPsi := by
  intro ε hε D hD
  filter_upwards [hll ε hε D hD] with N hN v hv ij
  have hst : firstCellS τ' N ≤ firstCellT τ' N := by
    change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 ≤
      gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1
    exact gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
      hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  exact hN v ⟨hv.1, hv.2.trans hst⟩ ij

theorem firstCell_localLaw_at_right {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      firstCellPsi) :
    LocalLawUnifIcc Dims.exampleGrow 0 (firstCellT τ') (firstCellT τ')
      firstCellPsi := by
  intro ε hε D hD
  filter_upwards [hll ε hε D hD] with N hN v hv ij
  have hst : firstCellS τ' N ≤ firstCellT τ' N := by
    change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 ≤
      gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1
    exact gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
      hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
  exact hN v ⟨hst.trans hv.1, hv.2⟩ ij

/-- Positive-time first-cell model, avoiding the deterministic `u=0` fluctuation. -/
theorem detFlucThreshold_gaussian_witness_pos :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, 0 < firstCellT τ' N) ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellT τ') (firstCellT τ')
        (fun N => 2 * firstCellPsi N) ∧
      (∀ᶠ N : ℕ in atTop,
        ((Dims.exampleGrow.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ 2 * firstCellPsi N) ∧
      (∀ᶠ N : ℕ in atTop,
        2 * firstCellPsi N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8)) ∧
      (∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT 0 (firstCellT τ' N)) := by
  obtain ⟨τ', hτ', hll⟩ := firstCell_localLawUnifIcc_of_step1
  have hwin := first_cell_window_nondegenerate Dims.exampleGrow hτ'
  refine ⟨τ', hτ', ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hwin] with N hN
    change firstCellS τ' N < firstCellT τ' N at hN
    rw [firstCellS_eq_zero] at hN
    exact hN
  · exact UnifDomIcc.mono_control (firstCell_localLaw_at_right hτ' hll)
      (fun N _ _ _ => by
        have hp : 0 ≤ firstCellPsi N := (firstCellPsi_pos N).le
        linarith)
  · exact Eventually.of_forall fun N => by
      unfold firstCellPsi
      convert (le_refl (((Dims.exampleGrow.W N : ℝ)) ^ (-(1 : ℝ) / 2))) using 1 <;> ring
  · have hpow : ∀ᶠ N : ℕ in atTop,
        2 * (N : ℝ) ^ (-(1 : ℝ) / 4) ≤
          (N : ℝ) ^ (-(1 : ℝ) / 8) :=
      eventually_const_mul_rpow_le_rpow 2 (by norm_num)
    filter_upwards [firstCellPsi_le_rpow_neg_quarter, hpow] with N hΨ hN
    nlinarith
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hT : firstCellT τ' N ≤ 1 / 2 := by
      change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
      exact gridT_le (1 / 2 : ℝ) 1
    have hη : (1 / 2 : ℝ) ≤ etaT 0 (firstCellT τ' N) := by
      rw [Step2.etaT_eq, mE_zero]
      norm_num
      linarith
    have hInv : (N : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_iff_one_le_mul₀ hNpos]
      nlinarith
    rw [Real.rpow_neg_one]
    exact hInv.trans hη

/-- Joint nondegenerate Gaussian witness for every model premise of the threshold route.
Here `2·firstCellPsi=W⁻¹/²`, `a=1/8`, `K=0`, and the fixed time is `u=0`. -/
theorem detFlucThreshold_gaussian_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, firstCellS τ' N < firstCellT τ' N) ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellS τ')
        (fun N => 2 * firstCellPsi N) ∧
      (∀ᶠ N : ℕ in atTop,
        ((Dims.exampleGrow.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ 2 * firstCellPsi N) ∧
      (∀ᶠ N : ℕ in atTop,
        2 * firstCellPsi N ≤ (N : ℝ) ^ (-(1 : ℝ) / 8)) ∧
      (∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (-(0 : ℝ)) ≤ etaT 0 (firstCellS τ' N)) := by
  obtain ⟨τ', hτ', hll⟩ := firstCell_localLawUnifIcc_of_step1
  refine ⟨τ', hτ', first_cell_window_nondegenerate Dims.exampleGrow hτ', ?_, ?_, ?_, ?_⟩
  · exact UnifDomIcc.mono_control (firstCell_localLaw_at_left hτ' hll)
      (fun N _ _ _ => by
        have hp : 0 ≤ firstCellPsi N := (firstCellPsi_pos N).le
        linarith)
  · exact Eventually.of_forall fun N => by
      unfold firstCellPsi
      convert (le_refl (((Dims.exampleGrow.W N : ℝ)) ^ (-(1 : ℝ) / 2))) using 1 <;> ring
  · have hpow : ∀ᶠ N : ℕ in atTop,
        2 * (N : ℝ) ^ (-(1 : ℝ) / 4) ≤
          (N : ℝ) ^ (-(1 : ℝ) / 8) :=
      eventually_const_mul_rpow_le_rpow 2 (by norm_num)
    filter_upwards [firstCellPsi_le_rpow_neg_quarter, hpow] with N hΨ hN
    nlinarith
  · exact Eventually.of_forall fun N => by
      rw [firstCellS_eq_zero, Step2.etaT_eq, mE_zero]
      norm_num

/-- The numerical and stochastic premises meet in one positive Gaussian example.
The moment order is fixed before the eventual threshold. -/
theorem detFlucThreshold_gain_witness (p : ℕ) :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, firstCellS τ' N < firstCellT τ' N) ∧
      (∀ᶠ N : ℕ in atTop,
        ∀ v ∈ Set.Icc (firstCellS τ' N) (firstCellS τ' N),
          FlucGainUpTo' Dims.exampleGrow N v (zt 0 v) (mE 0)
            (2 * (2 * minorDiffC (2 * p) *
              (2 * detFlucDelta (fun N => 2 * firstCellPsi N) (1 / 64) N)
                + 2 * detFlucDelta (fun N => 2 * firstCellPsi N) (1 / 64) N))
            (4 * detFlucDelta (fun N => 2 * firstCellPsi N) (1 / 64) N)
            (2 * p) (2 * p)) := by
  obtain ⟨τ', hτ', hwin, hll, hlo, hhi, hη⟩ := detFlucThreshold_gaussian_witness
  have hu0 : ∀ N, 0 ≤ firstCellS τ' N := fun N => by rw [firstCellS_eq_zero]
  have hu1 : ∀ N, firstCellS τ' N < 1 := fun N => by rw [firstCellS_eq_zero]; norm_num
  have hhi' : ∀ᶠ N : ℕ in atTop,
      2 * firstCellPsi N ≤ (N : ℝ) ^ (-( (1 : ℝ) / 8)) := by
    filter_upwards [hhi] with N hN
    convert hN using 1 <;> ring
  have hgain := fixedMoment_gain_of_localLaw Dims.exampleGrow
    (E := 0) (u := firstCellS τ')
    (Ψ := fun N => 2 * firstCellPsi N)
    (a := 1 / 8) (K := 0) (θ := 1 / 64)
    (by norm_num) hu0 hu1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hη hlo hhi' hll p
  exact ⟨τ', hτ', hwin, hgain.1⟩

theorem detFlucThreshold_gain_witness_pos (p : ℕ) :
    ∃ τ' : ℝ, 0 < τ' ∧
      (∀ᶠ N : ℕ in atTop, 0 < firstCellT τ' N) ∧
      (∀ᶠ N : ℕ in atTop,
        ∀ v ∈ Set.Icc (firstCellT τ' N) (firstCellT τ' N),
          FlucGainUpTo' Dims.exampleGrow N v (zt 0 v) (mE 0)
            (2 * (2 * minorDiffC (2 * p) *
              (2 * detFlucDelta (fun N => 2 * firstCellPsi N) (1 / 64) N)
                + 2 * detFlucDelta (fun N => 2 * firstCellPsi N) (1 / 64) N))
            (4 * detFlucDelta (fun N => 2 * firstCellPsi N) (1 / 64) N)
            (2 * p) (2 * p)) := by
  obtain ⟨τ', hτ', hpos, hll, hlo, hhi, hη⟩ := detFlucThreshold_gaussian_witness_pos
  have hu0 : ∀ N, 0 ≤ firstCellT τ' N := by
    intro N
    have hst : firstCellS τ' N ≤ firstCellT τ' N := by
      change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 0 ≤
        gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1
      exact gridT_mono (by exact_mod_cast (band Dims.exampleGrow).one_le_W N)
        hτ'.le (1 / 2 : ℝ) (Nat.zero_le 1)
    simpa only [firstCellS_eq_zero] using hst
  have hu1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    have hT : firstCellT τ' N ≤ 1 / 2 := by
      change gridT ((band Dims.exampleGrow).W N : ℝ) τ' (1 / 2 : ℝ) 1 ≤ 1 / 2
      exact gridT_le (1 / 2 : ℝ) 1
    linarith
  have hhi' : ∀ᶠ N : ℕ in atTop,
      2 * firstCellPsi N ≤ (N : ℝ) ^ (-( (1 : ℝ) / 8)) := by
    filter_upwards [hhi] with N hN
    convert hN using 1 <;> ring
  have hgain := fixedMoment_gain_of_localLaw Dims.exampleGrow
    (E := 0) (u := firstCellT τ')
    (Ψ := fun N => 2 * firstCellPsi N)
    (a := 1 / 8) (K := 1) (θ := 1 / 64)
    (by norm_num) hu0 hu1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hη hlo hhi' hll p
  exact ⟨τ', hτ', hpos, hgain.1⟩

#print axioms detFlucDelta_pos
#print axioms detFlucTheta_specs
#print axioms detFlucDelta_polyLo
#print axioms detFlucDelta_le_rpow
#print axioms detFlucDelta_tendsto_zero
#print axioms detFlucDelta_margin
#print axioms detFlucDelta_moment_small
#print axioms highProb_detFlucDelta_of_localLaw
#print axioms detFlucControl_polyLo
#print axioms etaPolyHi_of_lower
#print axioms etaNet_bound_of_lower
#print axioms detFlucDelta_quarter_psi_le
#print axioms eventually_W_inv_le_detFlucDelta_sq
#print axioms not_allN_W_inv_le_detFlucDelta_sq
#print axioms fixedMoment_gain_of_localLaw
#print axioms detFlucThreshold_gaussian_witness
#print axioms detFlucThreshold_gaussian_witness_pos
#print axioms detFlucThreshold_gain_witness
#print axioms detFlucThreshold_gain_witness_pos

end RBM.Gauss
