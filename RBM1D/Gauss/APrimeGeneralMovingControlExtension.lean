/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingWindowFloor
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore

/-!
# T504: global extension of the moving one-loop control

The control `(ell_u / ell_s) / scale_u` is positive on each admissible
moving window. Clamping time to that window gives a globally positive
extension. The original control and its extension have symmetric factor-two
comparison at distances at most `N^(-16)` under the original `Cond272Reg`.
This module is deterministic and does not assert a time-net theorem.
-/

namespace RBM.APrimeGeneralMovingControlExtension

open Filter Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d




theorem clampTime_mem {s t : ℕ → ℝ} {N : ℕ}
    (hst : s N ≤ t N) (u : ℝ) :
    clampTime s t N u ∈ Icc (s N) (t N) := by
  exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩

theorem clampTime_eq {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) : clampTime s t N u = u := by
  simp only [clampTime, min_eq_right hu.2, max_eq_right hu.1]

theorem qExt_eq_q {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) : qExt E s t N u = q E s N u := by
  rw [qExt, clampTime_eq hu]

/-- The moving block length cancels exactly from the one-loop control. -/
theorem q_eq_inv {E : ℝ} {s : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hs1 : s N < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    q E s N u = 1 / ((B.W N : ℝ) * B.ell N (s N) * etaT E u) := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hls : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hs0 hs1
    change 0 < ellHat (B.L N) ((s N : ℝ) : ℂ)
    linarith
  have hlu : 0 < B.ell N u := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    change 0 < ellHat (B.L N) (u : ℂ)
    linarith
  have hη : 0 < etaT E u := etaT_pos hE hu1
  unfold q Band.scale
  field_simp

theorem q_pos {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N)
    (ht1 : t N < 1) (hu : u ∈ Icc (s N) (t N)) :
    0 < q E s N u := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hls : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hs0 (hst.trans_lt ht1)
    change 0 < ellHat (B.L N) ((s N : ℝ) : ℂ)
    linarith
  have hη : 0 < etaT E u := etaT_pos hE (hu.2.trans_lt ht1)
  rw [q_eq_inv hE hs0 (hst.trans_lt ht1) (hs0.trans hu.1) (hu.2.trans_lt ht1)]
  positivity

/-- Positivity holds at every real time for the clamped extension. -/
theorem qExt_pos {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : ℝ) : 0 < qExt E s t N u := by
  exact q_pos hE (hs0 N) (hst N) (ht1 N) (clampTime_mem (hst N) u)

theorem qExt_nonneg {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : ℝ) : 0 ≤ qExt E s t N u :=
  (qExt_pos hE hs0 hst ht1 N u).le

/-- The endpoint floor bounds the relative change by `N^(-15)`. -/
theorem eventually_relative_time_change {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      |u - v| / (1 - u) ≤ (N : ℝ) ^ (-15 : ℝ) := by
  filter_upwards [APrimeGeneralMovingWindowFloor.eventually_endpoint_floor
    hE hs0 hst ht1 hc hreg, eventually_ge_atTop (1 : ℕ)]
    with N hfloor hN u hu v _hv hdist
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hupos : 0 < 1 - u := by linarith [hu.2, ht1 N]
  have hinv : (1 - u)⁻¹ ≤ (N : ℝ) := by
    apply (inv_le_comm₀ hupos hNpos).2
    linarith [hfloor.1, hu.2]
  calc
    |u - v| / (1 - u) = |u - v| * (1 - u)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (N : ℝ) ^ (-16 : ℝ) * (N : ℝ) :=
      mul_le_mul hdist hinv (inv_nonneg.mpr hupos.le) (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (-15 : ℝ) := by
      simpa only [show (-16 : ℝ) + 1 = -15 by norm_num, Real.rpow_one] using
        (Real.rpow_add hNpos (-16 : ℝ) 1).symm

/-- A deterministic comparison whenever the time separation fits within
the terminal distance from one. -/
theorem q_le_two_mul_of_abs_sub_le {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hu : u ∈ Icc (s N) (t N)) (hv : v ∈ Icc (s N) (t N))
    (hdist : |u - v| ≤ 1 - t N) : q E s N u ≤ 2 * q E s N v := by
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hv1 : v < 1 := hv.2.trans_lt ht1
  have hbase : 1 - v ≤ 2 * (1 - u) := by
    have habs := le_abs_self (u - v)
    linarith [hu.2]
  have hη : etaT E v ≤ 2 * etaT E u := by
    have hmul := mul_le_mul_of_nonneg_right hbase (mE_im_pos hE).le
    dsimp only [etaT]
    nlinarith
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hls : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hs0 (hst.trans_lt ht1)
    change 0 < ellHat (B.L N) ((s N : ℝ) : ℂ)
    linarith
  have hK : 0 < (B.W N : ℝ) * B.ell N (s N) := mul_pos hW hls
  rw [q_eq_inv hE hs0 (hst.trans_lt ht1) (hs0.trans hu.1) hu1,
    q_eq_inv hE hs0 (hst.trans_lt ht1) (hs0.trans hv.1) hv1, mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hK (etaT_pos hE hu1))
    (mul_pos hK (etaT_pos hE hv1))).2
  nlinarith [mul_le_mul_of_nonneg_left hη hK.le]

/-- Symmetric comparison is simultaneous in both real times after a single
eventual threshold. -/
theorem eventually_q_short_time_comparable {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      q E s N u ≤ 2 * q E s N v ∧ q E s N v ≤ 2 * q E s N u := by
  filter_upwards [APrimeGeneralMovingWindowFloor.eventually_endpoint_floor
    hE hs0 hst ht1 hc hreg, eventually_ge_atTop (1 : ℕ)]
    with N hfloor hN u hu v hv hdist
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmesh : (N : ℝ) ^ (-16 : ℝ) ≤ (N : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (-16 : ℝ) ≤ -1))
  have hclose : |u - v| ≤ 1 - t N := hdist.trans (hmesh.trans hfloor.1)
  exact ⟨q_le_two_mul_of_abs_sub_le hE (hs0 N) (hst N) (ht1 N) hu hv hclose,
    q_le_two_mul_of_abs_sub_le hE (hs0 N) (hst N) (ht1 N) hv hu
      (by simpa only [abs_sub_comm] using hclose)⟩

/-- The globally nonnegative extension has the same symmetric comparison
on the moving window. -/
theorem eventually_qExt_short_time_comparable {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      qExt E s t N u ≤ 2 * qExt E s t N v ∧
        qExt E s t N v ≤ 2 * qExt E s t N u := by
  filter_upwards [eventually_q_short_time_comparable hE hs0 hst ht1 hc hreg]
    with N hN u hu v hv hdist
  simpa only [qExt_eq_q hu, qExt_eq_q hv] using hN u hu v hv hdist

/-- The same positive-length T473 grid window supports every conclusion
above; no independently chosen admissible window is substituted. -/
theorem positive_length_grid_window_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      (∀ N u, 0 < qExt 0 s t N u) ∧
      (∀ N u, u ∈ Icc (s N) (t N) → qExt 0 s t N u = q 0 s N u) ∧
      ∀ᶠ N : ℕ in atTop, s N < t N ∧
        ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
          |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
          qExt 0 s t N u ≤ 2 * qExt 0 s t N v ∧
            qExt 0 s t N v ≤ 2 * qExt 0 s t N u := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hlength⟩ :=
    APrimeGeneralMovingWindowFloor.positive_length_grid_window_witness
  refine ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg,
    qExt_pos (by norm_num) hs0 hst ht1, fun _ _ hu => qExt_eq_q hu, ?_⟩
  filter_upwards [hlength,
    eventually_qExt_short_time_comparable (by norm_num) hs0 hst ht1 hc hreg]
    with N hlengthN hcomparison
  exact ⟨hlengthN, hcomparison⟩

#print axioms clampTime_mem
#print axioms clampTime_eq
#print axioms qExt_eq_q
#print axioms q_eq_inv
#print axioms q_pos
#print axioms qExt_pos
#print axioms qExt_nonneg
#print axioms eventually_relative_time_change
#print axioms q_le_two_mul_of_abs_sub_le
#print axioms eventually_q_short_time_comparable
#print axioms eventually_qExt_short_time_comparable
#print axioms positive_length_grid_window_witness

end
end RBM.APrimeGeneralMovingControlExtension
