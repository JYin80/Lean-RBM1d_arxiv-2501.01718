/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelQInt
import RBM1D.Gauss.TestFunQGeneral

/-!
# The actual Gaussian `Q_t` moment inequality

This closes the `MomentIneqQ` field of `gaussHypOfMoments` on the actual Gaussian sample,
with the paper's `C_{n,p} = (n+2)(2p-1)` and arbitrary initial windows `0 ≤ s_N ≤ t_N < 1`.
The proof assembles the derivative estimate for (5.91), the quadratic-variation bridge
(5.103)–(5.105), and the interval side conditions on each closed subwindow `[s_N,v]`.
-/

namespace RBM

open MeasureTheory Filter Real Set
open scoped Matrix.Norms.L2Operator NNReal

namespace Gauss

/-- **The actual Gaussian `Q_t` moment inequality with the paper constant.** The sample is
`Gauss.sample d`, the window is arbitrary, and the coefficient is the original
`C_{n,p} = (n+2)(2p-1)`. -/
theorem momentIneqQ_gauss_cMDval'_closed (d : Dims) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    MomentDuhamel.MomentIneqQ (sample d) E s t n
      (fun p => MomentDuhamel.cMDval' p n) := by
  refine MomentDuhamel.momentIneqQ_of_derivBound' hE.le hs0 ht1 ?_
  intro p hp N σ v hsv hvt a
  have hsN : 0 ≤ s N := hs0 N
  have hv1 : v < 1 := lt_of_le_of_lt hvt (ht1 N)
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    exists_bdd_Kval_Kprim (d := d) E N hE.le hsN hv1 (v := v) σ
  obtain ⟨Cψ, hCψ⟩ :=
    exists_bdd_psiQ_gauss E N hE hsN hv1 σ a ((v : ℝ) : ℂ) p hcK hKb
  have hcont :=
    continuousOn_integral_psiQ_gauss E N hE hsN hv1 σ a ((v : ℝ) : ℂ) p hcK hKb
  obtain ⟨cF, hcF0, hFb⟩ := exists_driftF_bdd_window (d := d) E N hE hsN hv1 σ
  obtain ⟨CF, hCF0, hCF⟩ :=
    exists_bdd_uker_Qop_driftF E N hsN hv1 σ a ((v : ℝ) : ℂ) hFb
  obtain ⟨Ccomm, hCcomm0, hCcomm⟩ :=
    exists_bdd_uker_commS_lkT E N hE hsN hv1 σ a ((v : ℝ) : ℂ) hcK hKb
  obtain ⟨Cdot, hCdot0, hCdot⟩ :=
    exists_bdd_uker_PsumVarthetaDot_lkT E N hE hsN hv1 σ a ((v : ℝ) : ℂ) hcK hKb
  obtain ⟨Cqq, hCqq0, hCqq⟩ :=
    exists_bdd_uker_QQ_eeFun E N hE hsN hv1 σ a ((v : ℝ) : ℂ)
  let CG : ℝ := max (max CF Ccomm) (max Cdot Cqq)
  have hCFle : CF ≤ CG := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCcommle : Ccomm ≤ CG := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCdotle : Cdot ≤ CG := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCqqle : Cqq ≤ CG := le_trans (le_max_right _ _) (le_max_right _ _)
  have hpoint : ∀ u ∈ Set.Ioo (s N) v,
      (∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (d.L N) ((u : ℝ) : ℂ)
            (DriftDef.driftF (band d) E N u ((sample d).H N u ω) σ)) a‖ ≤ CG)
      ∧ (∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (SumZeroDyn.commS (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
            (SumZeroDyn.lkT (sample d) E N u ω σ)) a‖ ≤ CG)
      ∧ (∀ ω : Ω d, ‖Uker (d.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (fun b => Psum (d.L N) (SumZeroDyn.lkT (sample d) E N u ω σ) (b 0)
            * SumZeroDyn.varthetaDot (d.L N) u b) a‖ ≤ CG)
      ∧ (∀ ω : Ω d, ‖Uker (d.L N) (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (SumZeroDyn.QQ (d.L N) ((u : ℝ) : ℂ)
            (MomentDuhamel.eeFun (band d) E N u ((sample d).H N u ω) σ))
            (Fin.append a a)‖ ≤ CG) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (s N) v := ⟨hu.1.le, hu.2.le⟩
    exact ⟨fun ω => (hCF u huIcc ω).trans hCFle,
      fun ω => (hCcomm u huIcc ω).trans hCcommle,
      fun ω => (hCdot u huIcc ω).trans hCdotle,
      fun ω => (hCqq u huIcc ω).trans hCqqle⟩
  obtain ⟨φ', hderiv, hbound⟩ :=
    derivAndBound_qMomentObsT_gauss' E N hE hsN hv1 σ a hp (CG := CG)
      (fun u hu => by
        have hu0 : 0 ≤ u := le_trans hsN hu.1.le
        have hu1 : u < 1 := lt_trans hu.2 hv1
        have huIcc : u ∈ Set.Icc (s N) v := ⟨hu.1.le, hu.2.le⟩
        exact (continuous_uker_Qop_driftF_omega E N hu0 hu1
          (window_im_ne_zero hE hv1 u huIcc)
          (window_norm_mul_lt hE.le hsN hv1 u huIcc) σ a ((v : ℝ) : ℂ)).norm)
      (fun u hu ω => (hpoint u hu).1 ω)
      (fun u hu => by
        have hu0 : 0 ≤ u := le_trans hsN hu.1.le
        have hu1 : u < 1 := lt_trans hu.2 hv1
        have huIcc : u ∈ Set.Icc (s N) v := ⟨hu.1.le, hu.2.le⟩
        exact (continuous_uker_commS_lkT_omega E N hE.le hu0 hu1
          (window_im_ne_zero hE hv1 u huIcc)
          (window_norm_mul_lt hE.le hsN hv1 u huIcc) σ a ((v : ℝ) : ℂ)).norm)
      (fun u hu ω => (hpoint u hu).2.1 ω)
      (fun u hu => by
        have hu0 : 0 ≤ u := le_trans hsN hu.1.le
        have hu1 : u < 1 := lt_trans hu.2 hv1
        have huIcc : u ∈ Set.Icc (s N) v := ⟨hu.1.le, hu.2.le⟩
        exact (continuous_uker_PsumVarthetaDot_lkT_omega E N hu0 hu1
          (window_im_ne_zero hE hv1 u huIcc)
          (window_norm_mul_lt hE.le hsN hv1 u huIcc) σ a ((v : ℝ) : ℂ)).norm)
      (fun u hu ω => (hpoint u hu).2.2.1 ω)
      (fun u hu => by
        have hu0 : 0 ≤ u := le_trans hsN hu.1.le
        have hu1 : u < 1 := lt_trans hu.2 hv1
        have huIcc : u ∈ Set.Icc (s N) v := ⟨hu.1.le, hu.2.le⟩
        exact (continuous_uker_QQ_eeFun_omega E N hu0 hu1
          (window_im_ne_zero hE hv1 u huIcc) σ a ((v : ℝ) : ℂ)).norm)
      (fun u hu ω => (hpoint u hu).2.2.2 ω)
      (fun u hu ω => by
        have hu0 : 0 ≤ u := le_trans hsN hu.1.le
        have hu1 : u < 1 := lt_trans hu.2 hv1
        have hv0 : 0 ≤ v := le_trans hsN hsv
        exact EEUker.quadVar_qUkerObsT_le_norm_QQ_eeFun' (B := band d) hE hu0 hu1 hv0 hv1
          σ (hM := Hflow_isHermitian d N u ω) a
          (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))))
  let Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    qMomentObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b))) a p
  let φ : ℝ → ℝ := fun r =>
    ∫ ω, |‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop (d.L N) ((r : ℝ) : ℂ) (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖|
        ^ (2 * p) ∂(band d).P
  have hT₁ : TestFunT₁ d N (Set.Icc (s N) v) Ψ :=
    testFunT₁_qMomentObsT E (m := n + 1) List.length_ofFn
      (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun r b => (band d).Kval E N r (LoopData.idx (σ, b)))
      (Kprim (band d) E N σ) a p (window_eta_pos hE hv1) hcK hsN hv1
      (window_le_abs_im hE hv1)
      (fun r hr b => hasDerivAt_Kval_Kprim (band d) E N
        (window_norm_mul_lt hE.le hsN hv1 r hr) σ b) hKb hK'b
  have hΦφ : (fun r : ℝ => ∫ ω, Ψ r (Hflow d N r ω) ∂(P d)) =
      fun r : ℝ => ((φ r : ℝ) : ℂ) := by
    funext r
    have hpt : ∀ ω : Ω d, Ψ r (Hflow d N r ω) =
        ((|‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (Qop (d.L N) ((r : ℝ) : ℂ)
              (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖| ^ (2 * p) : ℝ) : ℂ) :=
      fun ω => qMomentObsT_flow (band d) (sample d) E N σ a ((v : ℝ) : ℂ)
        (fun _ _ => rfl) p r ω
    rw [show (fun ω : Ω d => Ψ r (Hflow d N r ω)) =
      fun ω : Ω d => ((|‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (d.L N) ((r : ℝ) : ℂ)
            (SumZeroDyn.lkT (sample d) E N r ω σ)) a‖| ^ (2 * p) : ℝ) : ℂ)
        from funext hpt]
    exact integral_complex_ofReal
  have hphiInt : IntervalIntegrable φ' volume (s N) v :=
    intervalIntegrable_phi'_of_testFunT₁ hsN hsv hT₁ hΦφ hderiv
  have hFint := intervalIntegrable_momNorm_Qop_driftF_gauss_env E N hE hsN hsv hv1 σ a
    ((v : ℝ) : ℂ) (2 * p)
  have hcommInt := intervalIntegrable_momNorm_commS_gauss E N hE hsN hsv hv1 σ a
    ((v : ℝ) : ℂ) (2 * p) hcK hKb
  have hdotInt := intervalIntegrable_momNorm_PsumVarthetaDot_gauss E N hE hsN hsv hv1 σ a
    ((v : ℝ) : ℂ) (2 * p) hcK hKb
  have hqqInt := intervalIntegrable_momNorm_QQ_eeFun_gauss E N hE hsN hsv hv1 σ a
    ((v : ℝ) : ℂ) p
  have hprod := intervalIntegrable_psiQ_mul_driftQ_gauss_env E N hE hsN hv1 σ a
    ((v : ℝ) : ℂ) (2 * p)
  exact ⟨φ', Cψ, hCψ, hcont, hderiv, hphiInt, hFint, hcommInt, hdotInt, hqqInt,
    hprod, hbound⟩

/-- A concrete noncollapsed actual-model window, including size `N = 0`, so the universal
size quantifier in the source theorem is witnessed at its endpoint as well. -/
theorem momentIneqQ_exampleGrow_window (n : ℕ) :
    MomentDuhamel.MomentIneqQ (sample Dims.exampleGrow) 0 (fun _ => 0) (fun _ => 1 / 2) n
      (fun p => MomentDuhamel.cMDval' p n) := by
  apply momentIneqQ_gauss_cMDval'_closed Dims.exampleGrow
  · norm_num
  · intro N; norm_num
  · intro N; norm_num

theorem exampleGrow_window_at_zero_is_noncollapsed :
    0 < (fun _ : ℕ => (1 / 2 : ℝ)) 0 ∧
      (fun _ : ℕ => (0 : ℝ)) 0 < (fun _ : ℕ => (1 / 2 : ℝ)) 0 := by
  norm_num

/-- The actual growing model has one sample point on the same noncollapsed window: at `N=0`,
`ω=0` gives `H₀=0`, while the selected endpoint is `v=1/4`. -/
theorem exampleGrow_actual_window_same_sample :
    ∃ ω : Ω Dims.exampleGrow,
      Hflow Dims.exampleGrow 0 0 ω = 0 ∧ 0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 := by
  refine ⟨0, Hflow_zero Dims.exampleGrow 0 0, ?_⟩
  norm_num

#print axioms RBM.Gauss.momentIneqQ_gauss_cMDval'_closed
#print axioms RBM.Gauss.momentIneqQ_exampleGrow_window
#print axioms RBM.Gauss.exampleGrow_actual_window_same_sample

end Gauss
end RBM
