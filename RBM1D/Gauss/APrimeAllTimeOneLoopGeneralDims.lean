/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFixedOneLoopGeneralDims
import RBM1D.Gauss.APrimeCenteredModulusGeneralDims
import RBM1D.Gauss.Eq45FlowInputs

/-!
# T1377: arbitrary-dimension actual all-time centered source

The actual Gaussian centered block trace in both charges is stochastically
dominated over the full moving time window.  The proof derives its selector
control from the generic band, its fixed-time field from T1373, and its
same-norm-event time modulus from T1375 before applying the generic time-net
theorem.
-/

namespace RBM.APrimeAllTimeOneLoopGeneralDims

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
    q d E s N (u N) = APrimeSingletonLocalLawGeneralDims.selectorQ d E s u N := rfl

theorem qExt_eq_q {d : Dims} {E : ℝ} {s t : ℕ → ℝ} {N : ℕ} {u : ℝ}
    (hu : u ∈ Icc (s N) (t N)) : qExt d E s t N u = q d E s N u := by
  rw [qExt, clampTime_eq hu]

theorem qExt_eq_selectorQ {d : Dims} {E : ℝ} {s t u : ℕ → ℝ}
    (hu : ∀ N, u N ∈ Icc (s N) (t N)) (N : ℕ) :
    qExt d E s t N (u N) =
      APrimeSingletonLocalLawGeneralDims.selectorQ d E s u N := by
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

theorem eventually_qExt_short_time_comparable {d : Dims} {E c : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
      |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
      qExt d E s t N u ≤ 2 * qExt d E s t N v ∧
        qExt d E s t N v ≤ 2 * qExt d E s t N u := by
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_ge
    (band d) hE ht1 hc hreg.2
  filter_upwards [hfloor, eventually_ge_atTop (1 : ℕ)] with N hfloorN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloorN' : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloorN
  have hmesh : (N : ℝ) ^ (-16 : ℝ) ≤ (N : ℝ)⁻¹ := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hN1
      (by norm_num : (-16 : ℝ) ≤ -1)
    simpa only [Real.rpow_neg_one] using hpow
  intro u hu v hv hdist
  have hclose : |u - v| ≤ 1 - t N := hdist.trans (hmesh.trans hfloorN')
  have hforward := q_le_two_mul_of_abs_sub_le (d := d) hE (hs0 N) (hst N) (ht1 N)
    hu hv hclose
  have hback := q_le_two_mul_of_abs_sub_le (d := d) hE (hs0 N) (hst N) (ht1 N)
    hv hu (by simpa only [abs_sub_comm] using hclose)
  simpa only [qExt_eq_q hu, qExt_eq_q hv] using ⟨hforward, hback⟩
def control (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (u : ℝ)
    (_b : ZMod (d.L N)) (_ω : Ω d) : ℝ :=
  2 * qExt d E s t N u

theorem control_nonneg {d : Dims} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : ℝ)
    (b : ZMod (d.L N)) (ω : Ω d) : 0 ≤ control d E s t N u b ω := by
  exact mul_nonneg (by norm_num) (qExt_nonneg hE hs0 hst ht1 N u)

theorem eventually_inv_le_q {d : Dims} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Icc (s N) (t N),
      (N : ℝ)⁻¹ ≤ q d E s N u := by
  filter_upwards [Gauss.W_le_self d] with N hWN u hu
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (d.W_pos N) hWN)
  have hinv : (N : ℝ)⁻¹ ≤ (d.W N : ℝ)⁻¹ :=
    inv_anti₀ hW (by exact_mod_cast hWN)
  exact hinv.trans (W_inv_le_q hE (hs0 N) (ht1 N) hu)

theorem eventually_control_lower {d : Dims} {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d, ∀ b : ZMod (d.L N),
      ∀ u ∈ Icc (s N) (t N),
        (N : ℝ) ^ (-1 : ℝ) ≤ control d E s t N u b ω := by
  filter_upwards [eventually_inv_le_q hE hs0 ht1] with N hfloor ω b u hu
  rw [Real.rpow_neg_one, control, qExt_eq_q hu]
  have hq0 : 0 ≤ q d E s N u :=
    (q_pos hE (hs0 N) (hst N) (ht1 N) hu).le
  exact (hfloor u hu).trans (by nlinarith)

theorem control_slow {d : Dims} {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ω : Ω d, ∀ b : ZMod (d.L N),
        ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
          |u - v| ≤ (N : ℝ) ^ (-16 : ℝ) →
            control d E s t N v b ω ≤ (N : ℝ) ^ ε * control d E s t N u b ω := by
  intro ε hε
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [eventually_qExt_short_time_comparable hE hs0 hst ht1 hc hreg,
    hlarge] with N hcomparison hlargeN ω b u hu v hv hdist
  have hq := (hcomparison u hu v hv hdist).2
  have htwo : control d E s t N v b ω ≤ 2 * control d E s t N u b ω := by
    exact mul_le_mul_of_nonneg_left hq (by norm_num)
  exact htwo.trans
    (mul_le_mul_of_nonneg_right hlargeN (control_nonneg hE hs0 hst ht1 N u b ω))

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

theorem centeredTrace_unifDomIcc (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    UnifDomIcc (P d) s t
      (fun N u (b : ZMod (d.L N)) ω =>
        ‖APrimeCenteredModulusGeneralDims.centeredTrace d E N u ω true b‖)
      (fun N u (_b : ZMod (d.L N)) (_ω : Ω d) =>
        2 * qExt d E s t N u) := by
  refine Gauss.unifDomIcc_of_forall_stochDom hst ?_
  intro u hu
  have hfixed := APrimeFixedOneLoopGeneralDims.centered_block_trace_stochDom d
    hE hs0 hst ht1 hu hc hreg hB hStep
  have hcontrol : ∀ N,
      2 * APrimeSingletonLocalLawGeneralDims.selectorQ d E s u N =
        2 * qExt d E s t N (u N) := by
    intro N
    rw [qExt_eq_selectorQ hu N]
  simpa only [APrimeCenteredModulusGeneralDims.centeredTrace,
    Gsig_true, mSigma_true, hcontrol] using hfixed

theorem centeredTrace_false_stochDom_of_true (d : Dims) {E : ℝ}
    {s t : ℕ → ℝ}
    {control : ∀ N, (TimeIcc s t N × ZMod (d.L N)) → Ω d → ℝ}
    (hplus : StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖APrimeCenteredModulusGeneralDims.centeredTrace
          d E N (p.1 : ℝ) ω true p.2‖)
      control) :
    StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖APrimeCenteredModulusGeneralDims.centeredTrace
          d E N (p.1 : ℝ) ω false p.2‖)
      control := by
  exact StochDom.of_le_left
    (fun N p ω => by
      rw [APrimeCenteredModulusGeneralDims.centeredTrace_false_eq_conj_true]
      simp)
    hplus

set_option maxHeartbeats 1000000 in
-- The generic fixed-selector, event, and net compositions exceed the default elaboration budget.
/-- Both charges are dominated simultaneously over all times and blocks by
the same generic band control. All fixed-time, norm-event, and numerical
fields are derived from the actual Gaussian assumptions in this theorem. -/
theorem centeredTrace_twoCharge_stochDom_timeIcc (d : Dims) {E c : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    ∀ σ : Bool,
      StochDom (P d) (U := fun N => TimeIcc s t N × ZMod (d.L N))
        (fun N p ω =>
          ‖APrimeCenteredModulusGeneralDims.centeredTrace
            d E N (p.1 : ℝ) ω σ p.2‖)
        (fun N p _ω => 2 * qExt d E s t N (p.1 : ℝ)) := by
  let ξ : ∀ N, ℝ → ZMod (d.L N) → Ω d → ℝ := fun N u b ω =>
    ‖APrimeCenteredModulusGeneralDims.centeredTrace d E N u ω true b‖
  let ζ : ∀ N, ℝ → ZMod (d.L N) → Ω d → ℝ := fun N u _b _ω =>
    2 * qExt d E s t N u
  have hζ0 : ∀ N u b ω, 0 ≤ ζ N u b ω := by
    intro N u b ω
    exact mul_nonneg (by norm_num) (qExt_nonneg hE hs0 hst ht1 N u)
  have hfix : UnifDomIcc (P d) s t ξ ζ := by
    simpa only [ξ, ζ] using
      centeredTrace_unifDomIcc d hE hs0 hst ht1 hc hreg hB hStep
  have hmod := APrimeCenteredModulusGeneralDims.eventually_centeredTrace_sub_le
    d hE hs0 hst ht1 hc hreg
  have hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      APrimeCenteredModulusGeneralDims.normGood d N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          ∀ v ∈ Icc (s N) (t N),
            |ξ N u b ω - ξ N v b ω| ≤
              (N : ℝ) ^ (6 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
    filter_upwards [hmod, eventually_ge_atTop (2 : ℕ)] with N hNmod hN
    intro ω hω b u hu v hv
    have hcomplex := hNmod ω hω u hu v hv true b
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hcoef : 2 * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 6 := by
      calc
        2 * (N : ℝ) ^ 5 ≤ (N : ℝ) * (N : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hNr (by positivity)
        _ = (N : ℝ) ^ 6 := by ring
    calc
      |ξ N u b ω - ξ N v b ω| ≤
          ‖APrimeCenteredModulusGeneralDims.centeredTrace d E N u ω true b -
            APrimeCenteredModulusGeneralDims.centeredTrace d E N v ω true b‖ :=
              abs_norm_sub_norm_le _ _
      _ ≤ 2 * (N : ℝ) ^ 5 * Real.sqrt |u - v| := hcomplex
      _ ≤ (N : ℝ) ^ 6 * Real.sqrt |u - v| :=
        mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
      _ = (N : ℝ) ^ (6 : ℝ) * |u - v| ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        congr 1
        exact (Real.rpow_natCast (N : ℝ) 6).symm
  have hlow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      APrimeCenteredModulusGeneralDims.normGood d N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          (N : ℝ) ^ (-1 : ℝ) ≤ ζ N u b ω := by
    filter_upwards [eventually_control_lower hE hs0 hst ht1] with N hN
    intro ω hω b u hu
    simpa only [ζ, control] using hN ω b u hu
  have hslow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      APrimeCenteredModulusGeneralDims.normGood d N,
        ∀ b : ZMod (d.L N), ∀ u ∈ Icc (s N) (t N),
          ∀ v ∈ Icc (s N) (t N),
            |u - v| ≤ meshSpacing N →
              ζ N v b ω ≤ (N : ℝ) ^ ε * ζ N u b ω := by
    intro ε hε
    have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ε :=
      ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
    filter_upwards [eventually_qExt_short_time_comparable hE hs0 hst ht1 hc hreg,
      hlarge] with N hcomparison hlargeN ω hω b u hu v hv hdist
    have hq := (hcomparison u hu v hv (by simpa only [meshSpacing] using hdist)).2
    have htwo : ζ N v b ω ≤ 2 * ζ N u b ω := by
      dsimp [ζ]
      exact mul_le_mul_of_nonneg_left hq (by norm_num)
    exact htwo.trans
      (mul_le_mul_of_nonneg_right hlargeN (by
        exact mul_nonneg (by norm_num) (qExt_nonneg hE hs0 hst ht1 N u)))
  have hnum := netNumerics d hs0 hst ht1
  have hall := Gauss.stochDom_timeIcc_of_unifDom
    (P := P d) (Cv := (1 : ℝ)) (T := (1 : ℝ))
    (K := (6 : ℝ)) (B := (1 : ℝ)) (γ := (1 : ℝ) / 2)
    (ξ := ξ) (ζ := ζ) (δ := meshSpacing)
    hnum.hcard hnum.hst hnum.hT hnum.hlen hnum.hK hnum.hB hnum.hγ hζ0
    (by simpa only [meshSpacing] using hnum.hδ)
    (APrimeCenteredModulusGeneralDims.highProb_normGood d)
    hHol hlow hslow hfix
  have hplus : StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N p ω =>
        ‖APrimeCenteredModulusGeneralDims.centeredTrace d E N
            (p.1 : ℝ) ω true p.2‖)
      (fun N p _ω => 2 * qExt d E s t N (p.1 : ℝ)) := by
    simpa only [ξ, ζ] using hall
  intro σ
  cases σ with
  | false => exact centeredTrace_false_stochDom_of_true d hplus
  | true => exact hplus

/-- The joint event for both charge traces, with arbitrary positive loss. -/
def centeredEvent (d : Dims) (E ζ : ℝ) (s t : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc s t N × ZMod (d.L N), ∀ σ : Bool,
    ‖APrimeCenteredModulusGeneralDims.centeredTrace d E N
      (p.1 : ℝ) ω σ p.2‖ ≤
        (N : ℝ) ^ ζ * (2 * qExt d E s t N (p.1 : ℝ))}

theorem highProb_centeredEvent (d : Dims) {E c ζ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c) (hζ : 0 < ζ)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    HighProb (P d) (centeredEvent d E ζ s t) := by
  have htwo := centeredTrace_twoCharge_stochDom_timeIcc d
    hE hs0 hst ht1 hc hreg hB hStep
  have hfalse := (htwo false).highProb hζ
  have htrue := (htwo true).highProb hζ
  refine (hfalse.inter htrue).mono ?_
  filter_upwards with N ω homega
  intro p σ
  cases σ with
  | false => exact homega.1 p
  | true => exact homega.2 p

/-- The accepted `exampleGrow` first-cell tuple supplies a nondegenerate
instance of the generic theorem, and the same actual norm event remains
measurable, high-probability, nonempty, and valid for the T1375 modulus. -/
theorem positive_length_exampleGrow_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
      BoundsCore (sample Dims.exampleGrow) 0 s ∧
      Step1.Hyp (sample Dims.exampleGrow) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ N, MeasurableSet
        (APrimeCenteredModulusGeneralDims.normGood Dims.exampleGrow N)) ∧
      HighProb (P Dims.exampleGrow)
        (APrimeCenteredModulusGeneralDims.normGood Dims.exampleGrow) ∧
      (∀ N, (APrimeCenteredModulusGeneralDims.normGood Dims.exampleGrow N).Nonempty) ∧
      (∀ᶠ N : ℕ in atTop, ∀ ω ∈
        APrimeCenteredModulusGeneralDims.normGood Dims.exampleGrow N,
          ∀ u ∈ Icc (s N) (t N), ∀ v ∈ Icc (s N) (t N),
            ∀ σ b, ‖APrimeCenteredModulusGeneralDims.centeredTrace
                Dims.exampleGrow 0 N u ω σ b -
              APrimeCenteredModulusGeneralDims.centeredTrace
                Dims.exampleGrow 0 N v ω σ b‖ ≤
              2 * (N : ℝ) ^ 5 * Real.sqrt |u - v|) ∧
      ∀ σ : Bool,
        StochDom (P Dims.exampleGrow)
          (U := fun N => TimeIcc s t N × ZMod (Dims.exampleGrow.L N))
          (fun N p ω =>
            ‖APrimeCenteredModulusGeneralDims.centeredTrace
              Dims.exampleGrow 0 N (p.1 : ℝ) ω σ p.2‖)
          (fun N p _ω =>
            2 * qExt Dims.exampleGrow 0 s t N (p.1 : ℝ)) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, _hfixed⟩ :=
    APrimeFixedOneLoopGeneralDims.positive_length_same_parameter_witness
  have hmeas := APrimeCenteredModulusGeneralDims.measurableSet_normGood
    Dims.exampleGrow
  have hhigh := APrimeCenteredModulusGeneralDims.highProb_normGood Dims.exampleGrow
  have hnonempty := APrimeCenteredModulusGeneralDims.normGood_nonempty Dims.exampleGrow
  have hmod := APrimeCenteredModulusGeneralDims.eventually_centeredTrace_sub_le
    Dims.exampleGrow (by norm_num) hs0 hst ht1 hc hreg
  have htwo := centeredTrace_twoCharge_stochDom_timeIcc Dims.exampleGrow
    (E := 0) (s := s) (t := t) (by norm_num) hs0 hst ht1 hc hreg hB hStep
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
    hStep, hpos, hmeas, hhigh, hnonempty, hmod, htwo⟩

#print axioms q_eq_inv
#print axioms qExt_pos
#print axioms W_inv_le_q
#print axioms eventually_qExt_short_time_comparable
#print axioms eventually_control_lower
#print axioms control_slow
#print axioms netNumerics
#print axioms centeredTrace_unifDomIcc
#print axioms centeredTrace_false_stochDom_of_true
#print axioms centeredTrace_twoCharge_stochDom_timeIcc
#print axioms highProb_centeredEvent
#print axioms positive_length_exampleGrow_witness

end
end RBM.APrimeAllTimeOneLoopGeneralDims
