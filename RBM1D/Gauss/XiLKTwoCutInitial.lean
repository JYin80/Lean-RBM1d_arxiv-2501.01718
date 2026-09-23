/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.XiLKTwoCutMoment
import RBM1D.Gauss.MomentDuhamelRhs
import RBM1D.Gauss.MomentDuhamelQInt
import RBM1D.Gauss.Lemma514XiPoly
import RBM1D.Flow.Thm221NoEL

/-!
# The arbitrary-charge transported initial row for the two-loop cutoff argument (T608)

This file proves only the transported-initial row isolated by T602.  The source is
`BoundsCore.LmK 2`; the stochastic-domination bound is converted to a Gaussian moment bound,
then propagated with the arbitrary-charge moment form of Lemma 7.1.  The conclusion is uniform
over the exact `meshK 21 (1/2)` net, includes the endpoint `v = s_N`, and keeps the literal
normalization

`scale(v)^2 * ((1-s_N)/(1-v))^2 * scale(s_N)^(-2)`.

No positive-time Duhamel theorem, Step-3 all-charge conclusion, A-prime package, or first-cell
moment producer is used.
-/

namespace RBM.Gauss.XiLKTwoCutInitial

open Filter MeasureTheory Real Set
open RBM.MomentDuhamel RBM.MomentDuhamelCut

noncomputable section

/-- The raw two-loop initial coordinate has the moment bound supplied by
`BoundsCore.LmK 2`, uniformly in every charge and every label. -/
theorem twoCoord_initial_source_momNorm_le
    (d : Dims) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (_hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ (q : LoopData (d.L N) 2) (b : LoopArg (d.L N) 2),
          momNorm (band d).P (2 * P) (fun ω =>
              ‖SumZeroDyn.lkT (sample d) E N (s N) ω q.1 b‖)
            ≤ C * ((N : ℝ) ^ (ε / 4) * ((band d).scale E N (s N))⁻¹ ^ 2) := by
  letI := (band d).isProbabilityMeasure
  obtain ⟨CK, hCK0, hK⟩ := exists_norm_Kval_le_upto_one (band d) hE 2
  have hK' : ∀ (N : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
      ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 1 ≤ J.length → J.length ≤ 2 →
        ‖(band d).Kval E N u J‖ ≤
          CK * ((band d).scale E N u)⁻¹ ^ (J.length - 1) := by
    simpa only [band_L] using hK
  let Env : ℕ → ℝ := fun N =>
    (etaT E (s N))⁻¹ ^ 2 * (((band d).W N : ℝ))⁻¹ +
      CK * ((band d).scale E N (s N))⁻¹
  have hmom : MomNormDom (band d).P
      (fun N (i : LoopData (d.L N) 2 × LoopArg (d.L N) 2) ω =>
        ‖SumZeroDyn.lkT (sample d) E N (s N) ω i.1.1 i.2‖)
      (fun N _ => ((band d).scale E N (s N))⁻¹ ^ 2) := by
    refine momNormDom_of_stochDom (P := (band d).P)
      (Y := fun N (i : LoopData (d.L N) 2 × LoopArg (d.L N) 2) ω =>
        ‖SumZeroDyn.lkT (sample d) E N (s N) ω i.1.1 i.2‖)
      (Φ := fun N (_ : LoopData (d.L N) 2 × LoopArg (d.L N) 2) =>
        ((band d).scale E N (s N))⁻¹ ^ 2)
      (Env := Env) (Kenv := 5) (Blow := 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro N i
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      have hz : (zt E (s N)).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hs1
      have hm : ∀ x y : Bool,
          ‖((s N : ℝ) : ℂ) * (mSigma E x * mSigma E y)‖ < 1 := by
        intro x y
        exact window_norm_mul_lt hE.le (hs0 N) (ht1 N) (s N)
          ⟨le_rfl, hst N⟩ x y
      exact (continuous_lkT_omega (d := d) E N hz hm i.1.1 i.2).norm.measurable
    · intro r N i
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      have hz : (zt E (s N)).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hs1
      exact integrable_lkT_pow d E N hz (2 * r) (by norm_num) i.1.1 i.2
    · intro N i
      exact pow_pos (inv_pos.mpr
        ((band d).scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N)))) 2
    · norm_num
    · filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 hreg.toCond272]
        with N hN i
      have hA0 : 0 < (band d).scale E N (s N) :=
        (band d).scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hinv : (N : ℝ)⁻¹ ≤ ((band d).scale E N (s N))⁻¹ := by
        exact inv_anti₀ hA0 (hN.2.2.2 ⟨s N, le_rfl, hst N⟩).2.1
      have hsq := pow_le_pow_left₀ (inv_nonneg.mpr hN0.le) hinv 2
      rw [show (N : ℝ) ^ (-(2 : ℝ)) = (N : ℝ)⁻¹ ^ 2 by
        rw [Real.rpow_neg hN0.le, Real.rpow_two, inv_pow]]
      exact hsq
    · intro N
      dsimp [Env]
      exact add_nonneg
        (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (by positivity)))
        (mul_nonneg hCK0 (inv_nonneg.mpr
          ((band d).scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))).le))
    · norm_num
    · intro N i ω
      have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
      let I : LoopIdx (ZMod (d.L N)) := LoopData.idx ((i.1.1, i.2) : LoopData (d.L N) 2)
      have hIwf : I.WF := LoopData.idx_wf _
      have hIlen : I.length = 2 := by simp [I]
      have hIalen : I.a.length = 2 := by change I.length = 2; exact hIlen
      have hg := norm_gloop_le_det (Hflow_isHermitian d N (s N) ω) hE hs1 I
        hIwf (by rw [hIalen]; norm_num)
      have hk := hK' N (s N) (hs0 N) hs1 I hIwf (by rw [hIlen]; norm_num)
        (by rw [hIlen])
      change |‖gloop (d.L N) (d.W N) (Hflow d N (s N) ω) (zt E (s N)) I -
        (band d).Kval E N (s N) I‖| ≤ Env N
      rw [abs_norm]
      refine (norm_sub_le _ _).trans ?_
      dsimp [Env]
      rw [hIalen] at hg
      rw [hIlen] at hk
      norm_num at hg hk ⊢
      exact add_le_add hg hk
    · filter_upwards [eventually_etaT_inv_le_sq_window (band d) hE hs0 hst ht1 hreg.toCond272,
        SumZeroDyn.flow_crude hE hs0 hst ht1 hreg.toCond272,
        eventually_le_rpow (CK + 1) (by norm_num : (0 : ℝ) < 1),
        eventually_ge_atTop 2] with N hη hcr hCKN hN2
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hWinv : ((((band d).W N : ℝ))⁻¹) ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (by exact_mod_cast (band d).W_pos N)
      have hAinv : ((band d).scale E N (s N))⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (hcr.2.2.2 ⟨s N, le_rfl, hst N⟩).1
      have hCK : CK ≤ (N : ℝ) := by
        have h : CK + 1 ≤ (N : ℝ) := by simpa only [Real.rpow_one] using hCKN
        exact (le_add_of_nonneg_right zero_le_one).trans h
      have heta : (etaT E (s N))⁻¹ ≤ (N : ℝ) ^ 2 := hη ⟨s N, le_rfl, hst N⟩
      have heta0 : 0 ≤ (etaT E (s N))⁻¹ :=
        inv_nonneg.mpr (etaT_pos hE ((hst N).trans_lt (ht1 N))).le
      have hAinv0 : 0 ≤ ((band d).scale E N (s N))⁻¹ :=
        inv_nonneg.mpr ((band d).scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))).le
      have hNleN4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
        simpa only [pow_one] using pow_le_pow_right₀ hN1 (by norm_num : (1 : ℕ) ≤ 4)
      have hpoly : Env N ≤ (N : ℝ) ^ (5 : ℕ) := by
        dsimp [Env]
        calc
          (etaT E (s N))⁻¹ ^ 2 * (((band d).W N : ℝ))⁻¹ +
                CK * ((band d).scale E N (s N))⁻¹
              ≤ ((N : ℝ) ^ 2) ^ 2 * 1 + (N : ℝ) * 1 := by gcongr
          _ = (N : ℝ) ^ 4 + (N : ℝ) := by ring
          _ ≤ (N : ℝ) ^ 4 + (N : ℝ) ^ 4 := by linarith
          _ = 2 * (N : ℝ) ^ 4 := by ring
          _ ≤ (N : ℝ) * (N : ℝ) ^ 4 := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN2) (by positivity)
          _ = (N : ℝ) ^ 5 := by ring
      rw [← Real.rpow_natCast] at hpoly
      norm_num at hpoly ⊢
      exact hpoly
    · have hLmK : StochDom (band d).P
          (fun N (q : LoopData (d.L N) 2) ω =>
            (sample d).lkErr E N (s N) ω q.idx)
          (fun N _ _ => ((band d).scale E N (s N))⁻¹ ^ 2) := by
        simpa only [band_L] using hB.LmK 2 (by norm_num)
      refine StochDom.of_le_left (fun N i ω => le_of_eq ?_)
        (hLmK.precomp_param fun N
          (i : LoopData (d.L N) 2 × LoopArg (d.L N) 2) =>
            ((i.1.1, i.2) : LoopData (d.L N) 2))
      rw [abs_norm]
      exact SumZeroDyn.norm_lkT (sample d) E N (s N) ω i.1.1 i.2
  intro ε hε P hP
  obtain ⟨C, hC, hN⟩ := hmom (ε / 2) (half_pos hε) P hP
  refine ⟨C, hC, hN.mono fun N hN q b => ?_⟩
  simpa [show (ε / 2) / 2 = ε / 4 by ring] using hN (q, b)

/-- **Arbitrary-charge transported-initial row.**  The endpoint ranges over the exact target
net, with no strict inequality, so the same statement includes `v = s_N`.  The parenthesized
factor on the right is the literal scale/time-ratio ledger and is not hidden in an asymptotic
abbreviation. -/
theorem twoCoord_initial_momNorm_le_ratio
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ v ∈ netFinset s t (meshK 21 (1 / 2)) N,
          ∀ q : LoopData (d.L N) 2,
            (band d).scale E N v ^ 2 *
                momNorm (band d).P (2 * P) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) q.1)
                    ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT (sample d) E N (s N) ω q.1) q.2‖)
              ≤ C * ((N : ℝ) ^ (ε / 4) *
                ((band d).scale E N v ^ 2 *
                  ((1 - s N) / (1 - v)) ^ 2 *
                  ((band d).scale E N (s N))⁻¹ ^ 2)) := by
  intro ε hε P hP
  obtain ⟨C, hC, hsrc⟩ :=
    twoCoord_initial_source_momNorm_le d hE hs0 hst ht1 hc hreg hB ε hε P hP
  refine ⟨C, hC, hsrc.mono fun N hN v hv q => ?_⟩
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hst N) (meshK_pos 21 ((1 : ℝ) / 2) N) v hv
  have hv0 : 0 ≤ v := (hs0 N).trans hvIcc.1
  have hv1 : v < 1 := hvIcc.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := hvIcc.1.trans_lt hv1
  have hξ : ∀ i : Fin 2, ‖xiOf (mSigma E) q.1 i‖ = 1 :=
    fun i => norm_xiOf_mSigma hE.le q.1 i
  have ht : ∀ i : Fin 2,
      ‖((v : ℝ) : ℂ) * xiOf (mSigma E) q.1 i‖ < 1 := by
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv0, hξ i, mul_one]
    exact hv1
  have hCker : ∀ i : Fin 2,
      1 + ‖(((s N : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * xiOf (mSigma E) q.1 i‖ *
          (1 - ‖((v : ℝ) : ℂ) * xiOf (mSigma E) q.1 i‖)⁻¹
        ≤ (1 - s N) / (1 - v) := by
    intro i
    calc
      1 + ‖(((s N : ℝ) : ℂ) - ((v : ℝ) : ℂ)) * xiOf (mSigma E) q.1 i‖ *
            (1 - ‖((v : ℝ) : ℂ) * xiOf (mSigma E) q.1 i‖)⁻¹
          = 1 + (v - s N) * (1 - v)⁻¹ := by
              rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonpos (sub_nonpos.mpr hvIcc.1), hξ i, mul_one, norm_mul,
                Complex.norm_real, Real.norm_of_nonneg hv0, hξ i, mul_one]
              ring
      _ ≤ (1 - s N) / (1 - v) := (one_add_row_eq hv1).le
  have hz : (zt E (s N)).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hs1
  have hint : ∀ b : LoopArg (d.L N) 2,
      Integrable (fun ω =>
        ‖SumZeroDyn.lkT (sample d) E N (s N) ω q.1 b‖ ^ (2 * P)) (band d).P := by
    intro b
    simpa only [abs_norm] using
      integrable_lkT_pow d E N hz (2 * P) (by norm_num) q.1 b
  let M : ℝ := C * ((N : ℝ) ^ (ε / 4) * ((band d).scale E N (s N))⁻¹ ^ 2)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hU := momNorm_Uker_apply_le (P := (band d).P) (d.L N) (d.three_le_L N)
    (q := 2 * P) (by omega) ht hCker hint hM0 (fun b => hN q b) q.2
  have hA2 : 0 ≤ (band d).scale E N v ^ 2 := sq_nonneg _
  calc
    (band d).scale E N v ^ 2 *
          momNorm (band d).P (2 * P) (fun ω =>
            ‖Uker (d.L N) (xiOf (mSigma E) q.1)
              ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (SumZeroDyn.lkT (sample d) E N (s N) ω q.1) q.2‖)
        ≤ (band d).scale E N v ^ 2 * (((1 - s N) / (1 - v)) ^ 2 * M) :=
          mul_le_mul_of_nonneg_left hU hA2
    _ = C * ((N : ℝ) ^ (ε / 4) *
          ((band d).scale E N v ^ 2 * ((1 - s N) / (1 - v)) ^ 2 *
            ((band d).scale E N (s N))⁻¹ ^ 2)) := by
          dsimp [M]
          ring

/-- Checked specialization of the transported-initial row to the independent constant charge
`(+,+)`. -/
theorem ppCoord_initial_momNorm_le_ratio
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ v ∈ netFinset s t (meshK 21 (1 / 2)) N,
          ∀ a : LoopArg (d.L N) 2,
            (band d).scale E N v ^ 2 *
                momNorm (band d).P (2 * P) (fun ω =>
                  ‖Uker (d.L N) (xiOf (mSigma E) XiLKTwoCutMoment.ppCharge)
                    ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
                    (SumZeroDyn.lkT (sample d) E N (s N) ω
                      XiLKTwoCutMoment.ppCharge) a‖)
              ≤ C * ((N : ℝ) ^ (ε / 4) *
                ((band d).scale E N v ^ 2 *
                  ((1 - s N) / (1 - v)) ^ 2 *
                  ((band d).scale E N (s N))⁻¹ ^ 2)) := by
  intro ε hε P hP
  obtain ⟨C, hC, hN⟩ :=
    twoCoord_initial_momNorm_le_ratio d hE hs0 hst ht1 hc hreg hB ε hε P hP
  refine ⟨C, hC, hN.mono fun N hN v hv a => ?_⟩
  exact hN v hv (XiLKTwoCutMoment.ppCharge, a)

/-- The left boundary is part of the theorem directly.  This corollary uses the zeroth net
point, not T596's theorem for strictly positive Duhamel intervals. -/
theorem twoCoord_initial_momNorm_le_ratio_at_left
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ ε > (0 : ℝ), ∀ P : ℕ, 1 ≤ P →
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ q : LoopData (d.L N) 2,
          (band d).scale E N (s N) ^ 2 *
              momNorm (band d).P (2 * P) (fun ω =>
                ‖Uker (d.L N) (xiOf (mSigma E) q.1)
                  ((s N : ℝ) : ℂ) ((s N : ℝ) : ℂ)
                  (SumZeroDyn.lkT (sample d) E N (s N) ω q.1) q.2‖)
            ≤ C * ((N : ℝ) ^ (ε / 4) *
              ((band d).scale E N (s N) ^ 2 *
                ((1 - s N) / (1 - s N)) ^ 2 *
                ((band d).scale E N (s N))⁻¹ ^ 2)) := by
  intro ε hε P hP
  obtain ⟨C, hC, hN⟩ :=
    twoCoord_initial_momNorm_le_ratio d hE hs0 hst ht1 hc hreg hB ε hε P hP
  refine ⟨C, hC, hN.mono fun N hN q => ?_⟩
  have hs_mem : s N ∈ netFinset s t (meshK 21 (1 / 2)) N := by
    simpa [CutHypTheta.cutNetPt_zero] using
      (CutHypTheta.cutNetPt_mem_netFinset (s := s) (t := t) (mesh := meshK 21 (1 / 2))
        (N := N) (k := 0) (Nat.zero_le _))
  exact hN (s N) hs_mem q

private theorem eventual_half_cap :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 / 2 : ℝ) := by
  filter_upwards [eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with N hNpow hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hEq : (N : ℝ) ^ (-1 + (1 : ℝ) / 2) =
      ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [show -1 + (1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hN0]
  rw [hEq]
  have hInv : ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNpow)
  norm_num at hInv ⊢
  exact hInv

/-- **Nondegenerate satisfiability witness from the general grid-domain theorem.**

The first paper-grid cell has positive length eventually, carries `Cond272Reg` and
`BoundsCore` for the same Gaussian sample and left endpoint, and has a genuine `(+,+)`
two-loop coordinate at every size.  The construction calls `cond272Reg_grid_step_domain`
directly; it does not use a first-cell moment producer. -/
theorem positive_grid_boundsCore_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      let d := Dims.exampleGrow
      let B := band d
      let s : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
      let t : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (sample d) 0 s ∧
      (∀ᶠ N : ℕ in atTop, s N < t N ∧
        ∃ q : LoopData (d.L N) 2, q.1 = XiLKTwoCutMoment.ppCharge) := by
  let d := Dims.exampleGrow
  let B := band d
  obtain ⟨τ', hτ', c, hc, _n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain B (κ := 1) (τ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
  obtain ⟨_, hsteps⟩ := hgrid 0 (by norm_num)
    (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) eventual_half_cap
  obtain ⟨hs0, hst, ht1, hreg⟩ := hsteps 0
  let s : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
  let t : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  have hsEq : ∀ N, s N = 0 := by
    intro N
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hB : BoundsCore (sample d) 0 s :=
    (BoundsCore_zero (sample d) (by norm_num : |(0 : ℝ)| ≤ 2)).congr
      (sample d) (Eventually.of_forall fun N => (hsEq N).symm)
  have hpos : ∀ᶠ N : ℕ in atTop,
      gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0 <
        gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1 := by
    filter_upwards [(Step2.tendsto_W B).eventually_ge_atTop 2] with N hWN
    have hW1 : (1 : ℝ) < (B.W N : ℝ) := by linarith
    have hlt : ((B.W N : ℝ)) ^ (-(((1 : ℕ) : ℝ) * τ')) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hW1 (by push_cast; linarith)
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2), gridT]
    refine lt_min ?_ (by norm_num)
    rw [gridS]
    linarith
  change ∀ᶠ N : ℕ in atTop, s N < t N at hpos
  refine ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1, hreg, hB, ?_⟩
  filter_upwards [hpos] with N hN
  refine ⟨hN, ⟨(XiLKTwoCutMoment.ppCharge, fun _ => 0), rfl⟩⟩

#print axioms twoCoord_initial_source_momNorm_le
#print axioms twoCoord_initial_momNorm_le_ratio
#print axioms ppCoord_initial_momNorm_le_ratio
#print axioms twoCoord_initial_momNorm_le_ratio_at_left
#print axioms positive_grid_boundsCore_witness

end

end RBM.Gauss.XiLKTwoCutInitial
