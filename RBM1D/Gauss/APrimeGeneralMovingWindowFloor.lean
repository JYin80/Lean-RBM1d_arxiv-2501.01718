/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSlotFields
import RBM1D.Flow.Thm221Assembly
import RBM1D.Flow.Step1Producer

/-!
# T473: polynomial floor for general moving windows

The original `Cond272Reg` supplies a polynomial distance from the terminal
time to one.  This removes the fixed-terminal-time hypothesis from the
elementary modulus of the normalized fourth-power scale.
-/

namespace RBM.APrimeGeneralMovingWindowFloor

open Filter Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- An admissible moving window has the endpoint floor
`N⁻¹ ≤ 1 - t_N ≤ 1 - s_N`. -/
theorem eventually_endpoint_floor {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (_hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ ≤ 1 - t N ∧ 1 - t N ≤ 1 - s N := by
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_ge
    B hE ht1 hc hreg.2
  filter_upwards [hfloor] with N hfloorN
  constructor
  · simpa only [Real.rpow_neg_one] using hfloorN
  · linarith [hst N]

/-- On every admissible moving interval, the normalization
`((1-u)/(1-s_N))⁴` is eventually `4N`-Lipschitz. -/
theorem eventually_abs_rhoS_sub_le {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
      |APrimeSlotFields.rhoS s N v - APrimeSlotFields.rhoS s N w| ≤
        4 * (N : ℝ) * |v - w| := by
  filter_upwards [eventually_endpoint_floor hE hs0 hst ht1 hc hreg,
    eventually_ge_atTop (1 : ℕ)] with N hfloor hN v hv w hw
  have htpos : 0 < 1 - t N := by linarith [ht1 N]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hinv : (1 - t N)⁻¹ ≤ (N : ℝ) := by
    exact (inv_le_comm₀ htpos hNpos).2 hfloor.1
  have hbase := APrimeSlotFields.abs_rhoS_sub_le
    (s := s) (N := N) (t₀ := t N) (v := v) (w := w)
    (ht1 N) (hst N) hv.1 hw.1 hv.2 hw.2
  calc
    |APrimeSlotFields.rhoS s N v - APrimeSlotFields.rhoS s N w|
        ≤ 4 * (1 - t N)⁻¹ * |v - w| := hbase
    _ ≤ 4 * (N : ℝ) * |v - w| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (by norm_num)) (abs_nonneg _)

/-- The paper grid supplies an admissible window of positive length at
`E = 0` and terminal time `1/2`; the resident window and its
`Cond272Reg` proof come from one application of the grid-domain theorem. -/
theorem positive_length_grid_window_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ ∀ᶠ N : ℕ in atTop, s N < t N := by
  obtain ⟨τ', hτ', c, hc, _n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain B (hκ := (by norm_num : (0 : ℝ) < 1))
      (hτ := (by norm_num : (0 : ℝ) < 1 / 2))
  let terminal : ℕ → ℝ := fun _ => 1 / 2
  have hterminal0 : ∀ N, 0 ≤ terminal N := fun _ => by norm_num [terminal]
  have hpow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 / 2 : ℝ)) ≤ 1 - terminal N := by
    have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    filter_upwards [htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
      with N hN
    norm_num [terminal] at ⊢
    exact hN.le
  obtain ⟨_hlast, hstep⟩ := hgrid 0 (by norm_num) terminal hterminal0 hpow
  let s : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (terminal N) 0
  let t : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (terminal N) 1
  have hdomain := hstep 0
  have hpos : ∀ᶠ N : ℕ in atTop, s N < t N := by
    simpa only [s, t] using
      (Gauss.eventually_gridT_zero_lt_gridT_one B hτ'
        (Eventually.of_forall fun N => by norm_num [terminal]))
  exact ⟨τ', hτ', c, hc, s, t,
    hdomain.1, hdomain.2.1, hdomain.2.2.1,
    hdomain.2.2.2, hpos⟩

#print axioms eventually_endpoint_floor
#print axioms eventually_abs_rhoS_sub_le
#print axioms positive_length_grid_window_witness

end
end RBM.APrimeGeneralMovingWindowFloor
