/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.SingletonLocalLaw
import RBM1D.Gauss.DetAvgIBPFlow
import RBM1D.Gauss.CenteredTraceModulus
import RBM1D.Gauss.Eq45FlowInputs

/-!
# Arbitrary-dimension actual all-time centered source

The actual Gaussian centered block trace in both charges is stochastically
dominated over the full moving time window.  The proof derives its selector
control from the generic band, and its fixed-time field and same-norm-event time
modulus from the fixed-time results, before applying the generic time-net
theorem.
-/

namespace RBM.CenteredOneLoopAllTime

open Filter MeasureTheory Set Gauss

noncomputable section

def clampTime (s t : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  max (s N) (min (t N) u)

theorem clampTime_mem {s t : ℕ → ℝ} {N : ℕ} (hst : s N ≤ t N) (u : ℝ) :
    clampTime s t N u ∈ Icc (s N) (t N) := by
  exact ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩

theorem clampTime_eq {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) : clampTime s t N u = u := by
  simp only [clampTime, min_eq_right hu.2, max_eq_right hu.1]

/-- The generic band control before the globally defined time clamp. -/
noncomputable def q (d : Dims) (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (band d).ell N u / (band d).ell N (s N) * ((band d).scale E N u)⁻¹

/-- A globally defined positive extension of `q` on the original window. -/
noncomputable def qExt (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  q d E s N (clampTime s t N u)

theorem q_eq_selectorQ (d : Dims) (E : ℝ) (s u : ℕ → ℝ) (N : ℕ) :
    q d E s N (u N) = SingletonLocalLaw.selectorQ d E s u N := rfl

theorem qExt_eq_q {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) : qExt d E s t N u = q d E s N u := by
  rw [qExt, clampTime_eq hu]

theorem qExt_eq_selectorQ {d : Dims} {E : ℝ} {s t u : ℕ → ℝ}
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    qExt d E s t N (u N) =
      SingletonLocalLaw.selectorQ d E s u N := by
  rw [qExt_eq_q (hu N)]
  exact q_eq_selectorQ d E s u N

theorem q_eq_inv (d : Dims) {E : ℝ} {s : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hs1 : s N < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    q d E s N u = 1 / ((band d).W N * (band d).ell N (s N) * etaT E u) := by
  have hW : (0 : ℝ) < (band d).W N := by exact_mod_cast (band d).W_pos N
  have hls : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hs0 hs1
    change 0 < ellHat ((band d).L N) ((s N : ℝ) : ℂ)
    linarith
  have hlu : 0 < (band d).ell N u := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
    change 0 < ellHat ((band d).L N) (u : ℂ)
    linarith
  have hη : 0 < etaT E u := etaT_pos hE hu1
  unfold q Band.scale
  field_simp

theorem q_pos {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N)
    (ht1 : t N < 1) (hu : u ∈ Icc (s N) (t N)) : 0 < q d E s N u := by
  have hu0 : 0 ≤ u := hs0.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hW : (0 : ℝ) < (band d).W N := by exact_mod_cast (band d).W_pos N
  have hls : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N)
      (hs0) (hst.trans_lt ht1)
    change 0 < ellHat ((band d).L N) ((s N : ℝ) : ℂ)
    linarith
  have hη : 0 < etaT E u := etaT_pos hE hu1
  rw [q_eq_inv d hE hs0 (hst.trans_lt ht1) hu0 hu1]
  exact one_div_pos.mpr (mul_pos (mul_pos hW hls) hη)

theorem qExt_pos {d : Dims} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : ℝ) : 0 < qExt d E s t N u :=
  q_pos hE (hs0 N) (hst N) (ht1 N) (clampTime_mem (hst N) u)

theorem qExt_nonneg {d : Dims} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : ℝ) : 0 ≤ qExt d E s t N u :=
  (qExt_pos hE hs0 hst ht1 N u).le

theorem W_inv_le_q {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (ht1 : t N < 1)
    (hu : u ∈ Icc (s N) (t N)) :
    (d.W N : ℝ)⁻¹ ≤ q d E s N u := by
  have hu0 : 0 ≤ u := hs0.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hbase := Step1.inv_W_le_inv_scale (B := band d) hE N hu0 hu1
  have hr : 1 ≤ (band d).ell N u / (band d).ell N (s N) :=
    Step1.one_le_ell_div (B := band d) hu.1 hu1
  have hAi : 0 ≤ ((band d).scale E N u)⁻¹ :=
    inv_nonneg.mpr ((band d).scale_pos' hE N hu0 hu1).le
  calc
    (d.W N : ℝ)⁻¹ ≤ ((band d).scale E N u)⁻¹ := hbase
    _ ≤ ((band d).ell N u / (band d).ell N (s N)) *
        ((band d).scale E N u)⁻¹ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hAi
    _ = q d E s N u := by rfl

theorem q_le_two_mul_of_abs_sub_le {d : Dims} {E : ℝ} {s t : ℕ → ℝ}
    {N : ℕ} {u v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hu : u ∈ Icc (s N) (t N)) (hv : v ∈ Icc (s N) (t N))
    (hdist : |u - v| ≤ 1 - t N) : q d E s N u ≤ 2 * q d E s N v := by
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hv1 : v < 1 := hv.2.trans_lt ht1
  have hbase : 1 - v ≤ 2 * (1 - u) := by
    have habs := le_abs_self (u - v)
    linarith [hu.2]
  have hη : etaT E v ≤ 2 * etaT E u := by
    have hmul := mul_le_mul_of_nonneg_right hbase (mE_im_pos hE).le
    dsimp only [etaT]
    nlinarith
  have hW : (0 : ℝ) < (band d).W N := by exact_mod_cast (band d).W_pos N
  have hls : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N)
      (hs0) (hst.trans_lt ht1)
    change 0 < ellHat ((band d).L N) ((s N : ℝ) : ℂ)
    linarith
  have hK : 0 < (band d).W N * (band d).ell N (s N) := mul_pos hW hls
  rw [q_eq_inv d hE hs0 (hst.trans_lt ht1) (hs0.trans hu.1) hu1,
    q_eq_inv d hE hs0 (hst.trans_lt ht1) (hs0.trans hv.1) hv1, mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hK (etaT_pos hE hu1))
    (mul_pos hK (etaT_pos hE hv1))).2
  nlinarith [mul_le_mul_of_nonneg_left hη hK.le]

def control (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (u : ℝ)
    (_b : ZMod (d.L N)) (_ω : Ω d) : ℝ :=
  2 * qExt d E s t N u

def meshSpacing (N : ℕ) : ℝ := (N : ℝ) ^ (-16 : ℝ)

theorem net_exponent_eq : ((6 : ℝ) + 1 + 1) / (1 / 2) = 16 := by norm_num

theorem eventually_net_spacing_le :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) / (N : ℝ) ^ (((6 : ℝ) + 1 + 1) / (1 / 2)) ≤ meshSpacing N := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (show 0 ≤ N by omega)
  rw [net_exponent_eq, meshSpacing, Real.rpow_neg hN0, one_div]

structure NetNumerics (d : Dims) (s t : ℕ → ℝ) : Prop where
  hcard : ∀ᶠ N : ℕ in atTop,
    (Fintype.card (ZMod (d.L N)) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ)
  hst : ∀ N, s N ≤ t N
  hT : (0 : ℝ) < 1
  hlen : ∀ N, t N - s N ≤ 1
  hK : (0 : ℝ) ≤ 6
  hB : (0 : ℝ) ≤ 1
  hγ : (0 : ℝ) < 1 / 2
  hδ : ∀ᶠ N : ℕ in atTop,
    (1 : ℝ) / (N : ℝ) ^ (((6 : ℝ) + 1 + 1) / (1 / 2)) ≤ meshSpacing N

theorem netNumerics (d : Dims) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) : NetNumerics d s t := by
  refine ⟨Gauss.card_ZMod_L_le d, hst, by norm_num, ?_, by norm_num,
    by norm_num, by norm_num, eventually_net_spacing_le⟩
  intro N
  linarith [hs0 N, ht1 N]

/-- The joint event for both charge traces, with arbitrary positive loss. -/
def centeredEvent (d : Dims) (E ζ : ℝ) (s t : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc s t N × ZMod (d.L N), ∀ σ : Bool,
    ‖CenteredTraceModulus.centeredTrace d E N
      (p.1 : ℝ) ω σ p.2‖ ≤
        (N : ℝ) ^ ζ * (2 * qExt d E s t N (p.1 : ℝ))}

end
end RBM.CenteredOneLoopAllTime
