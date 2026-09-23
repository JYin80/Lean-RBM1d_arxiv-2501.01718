/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftTimeFamilyCore
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # Clean finite-window regularity for the Gaussian A-prime QV rate -/

namespace RBM.APrimeQVRateTime

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

private theorem window_eta_pos {E v : ℝ} (hE : |E| < 2) (hv1 : v < 1) :
    0 < (1 - v) * (mE E).im := mul_pos (by linarith) (mE_im_pos hE)

private theorem window_le_abs_im {E : ℝ} (hE : |E| < 2) {s v : ℝ} (hv1 : v < 1) :
    ∀ u ∈ Set.Icc s v, (1 - v) * (mE E).im ≤ |(zt E u).im| :=
  fun _ hu => Gauss.le_abs_im_zt_of_le hE hv1 hu.2

private theorem window_im_ne_zero {E : ℝ} (hE : |E| < 2) {s v : ℝ} (hv1 : v < 1) :
    ∀ u ∈ Set.Icc s v, (zt E u).im ≠ 0 :=
  fun u hu => Gauss.im_zt_ne_zero_of_le (window_eta_pos hE hv1)
    (window_le_abs_im hE hv1 u hu)

private theorem window_norm_mul_lt {E : ℝ} (hE : |E| ≤ 2) {s v : ℝ}
    (hs0 : 0 ≤ s) (hv1 : v < 1) :
    ∀ u ∈ Set.Icc s v, ∀ x y : Bool,
      ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1 := by
  intro u hu x y
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hs0.trans hu.1), norm_mSigma hE, norm_mSigma hE, mul_one, mul_one]
  exact lt_of_le_of_lt hu.2 hv1

private theorem hasDerivAt_Kval_pair (d : Gauss.Dims) (E : ℝ) (N : ℕ)
    {u : ℝ} (hm : ∀ x y : Bool, ‖(u : ℂ) * (mSigma E x * mSigma E y)‖ < 1)
    (σ : Fin 2 → Bool) (b : LoopArg (d.L N) 2) :
    ∃ z : ℂ, HasDerivAt
      (fun r : ℝ => (Gauss.band d).Kval E N r (LoopData.idx (σ, b))) z u := by
  refine ⟨primRhs (d.L N) (d.W N)
      (Kgen (d.L N) (d.W N) (mSigma E) u) (LoopData.idx (σ, b)), ?_⟩
  simpa only [Band.Kval, Gauss.band_L, Gauss.band_W] using
    (hasDerivAt_Kgen_all (d.W N) (mSigma E) (d.three_le_L N) hm
      (LoopData.idx (σ, b)) (LoopData.idx_wf _)
      (by simpa using (show 2 ≤ 2 by omega)))

private theorem continuous_subtype_time {ι : Type*} [TopologicalSpace ι]
    {s v : ℝ} {F : ℝ × ι → ℂ}
    (hF : ContinuousOn F ((Icc s v) ×ˢ (Set.univ : Set ι))) :
    Continuous (fun q : (Icc s v) × ι => F (q.1.1, q.2)) := by
  have hg : Continuous (fun q : (Icc s v) × ι => ((q.1.1, q.2) : ℝ × ι)) := by
    fun_prop
  exact hF.comp_continuous hg (by intro q; exact ⟨q.1.2, Set.mem_univ _⟩)

/-- Joint continuity of the actual normalized coordinate, restricted only
in its time parameter. -/
theorem continuous_coordAt_on_window (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (_hsv : s ≤ v) (hv1 : v < 1) :
    Continuous (fun q : (Icc s v) × Matrix (d.Idx N) (d.Idx N) ℂ =>
      APrimeDriftTimeFamily.coordAt d E D N σ a s v q.1.1 q.2) := by
  let F : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ → ℂ := fun q =>
    Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
      (fun x b => (Gauss.band d).Kval E N x (LoopData.idx (σ, b))) a q.1 q.2
  have hrawOn : ContinuousOn F
      ((Icc s v) ×ˢ (Set.univ : Set (Matrix (d.Idx N) (d.Idx N) ℂ))) := by
    rintro ⟨r, M⟩ ⟨hr, -⟩
    have hz : (zt E r).im ≠ 0 := window_im_ne_zero hE hv1 r hr
    have hK : ∀ b, DifferentiableAt ℝ
        (fun x : ℝ => (Gauss.band d).Kval E N x (LoopData.idx (σ, b))) r := by
      intro b
      obtain ⟨z, hz⟩ := hasDerivAt_Kval_pair d E N
        (window_norm_mul_lt hE.le hs0 hv1 r hr) σ b
      exact hz.differentiableAt
    exact (Gauss.differentiableAt_ukerObsT_pair E (xiOf (mSigma E) σ)
      ((v : ℝ) : ℂ)
      (fun x b => (Gauss.band d).Kval E N x (LoopData.idx (σ, b))) a hz hK M)
      |>.continuousAt.continuousWithinAt
  have hsub := continuous_subtype_time hrawOn
  change Continuous (fun q : (Icc s v) × Matrix (d.Idx N) (d.Idx N) ℂ =>
    F (q.1.1, q.2) /
      ((APrimeDriftTimeFamily.driftScale d E D N a s v : ℝ) : ℂ))
  exact hsub.div_const _

/-- Joint Borel measurability of the actual, uncut evolved QV on the
closed time window and Gaussian sample space. -/
theorem measurable_qvAt_on_window (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    Measurable (fun q : (Icc s v) × Gauss.Ω d =>
      APrimeDriftTimeFamily.qvAt d E D N σ a s v q.1.1 q.2) := by
  let f : (Icc s v) → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    fun r M => APrimeDriftTimeFamily.coordAt d E D N σ a s v r.1 M
  have hf : Continuous f.uncurry :=
    continuous_coordAt_on_window d E D N σ a hE hs0 hsv hv1
  have hfd : Measurable (fun q : (Icc s v) × Matrix (d.Idx N) (d.Idx N) ℂ =>
      fderiv ℝ (f q.1) q.2) := measurable_fderiv_with_param ℝ hf
  have hflow : Continuous (fun q : (Icc s v) × Gauss.Ω d =>
      Gauss.Hflow d N q.1.1 q.2) := by
    unfold Gauss.Hflow
    exact ((Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst))).smul
      ((Gauss.continuous_Xmat d N).comp continuous_snd))
  have hpair : Measurable (fun q : (Icc s v) × Gauss.Ω d =>
      ((q.1, Gauss.Hflow d N q.1.1 q.2) :
        (Icc s v) × Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    measurable_fst.prodMk hflow.measurable
  have hderivComp : Measurable
      ((fun z : (Icc s v) × Matrix (d.Idx N) (d.Idx N) ℂ =>
        fderiv ℝ (f z.1) z.2) ∘
        (fun q : (Icc s v) × Gauss.Ω d =>
          ((q.1, Gauss.Hflow d N q.1.1 q.2) :
            (Icc s v) × Matrix (d.Idx N) (d.Idx N) ℂ))) :=
    hfd.comp hpair
  have hderiv : Measurable (fun q : (Icc s v) × Gauss.Ω d =>
      fderiv ℝ (f q.1) (Gauss.Hflow d N q.1.1 q.2)) := by
    simpa only [Function.comp_def] using hderivComp
  change Measurable (fun q : (Icc s v) × Gauss.Ω d =>
    ∑ z ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N z) : ℝ) *
      ‖fderiv ℝ (f q.1)
        (Gauss.Hflow d N q.1.1 q.2)
        (Gauss.Bmat d N z.1 z.2.1 z.2.2)‖ ^ 2)
  exact Finset.measurable_sum _ fun z _ =>
    measurable_const.mul (((ContinuousLinearMap.measurable_apply _).comp hderiv).norm.pow_const _)

/-- A finite-size, sample-independent first derivative envelope for the
actual normalized coordinate. -/
theorem exists_bdd_fderiv_coordAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc s v, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖fderiv ℝ (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) M‖ ≤ C := by
  classical
  let η : ℝ := (1 - v) * (mE E).im
  have hη : 0 < η := window_eta_pos hE hv1
  have hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d (D := D) hE hsv hv1 N a
  let row : ℝ → ℝ := Gauss.ukerRow (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a
  obtain ⟨Cr, hCr⟩ := (isCompact_Icc (a := s) (b := v)).exists_bound_of_continuousOn
    (f := row) (Gauss.continuous_ukerRow (xiOf (mSigma E) σ) ((v : ℝ) : ℂ) a).continuousOn
  let B : ℝ := (Fintype.card (d.Idx N) : ℝ) *
    ((2 : ℝ) * (2 * (1 + η⁻¹) ^ 3) ^ 2)
  let C : ℝ := (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ * (|Cr| * B)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r hr M
  let cK : ℝ := ∑ b : LoopArg (d.L N) 2,
    ‖(Gauss.band d).Kval E N r (LoopData.idx (σ, b))‖
  have hKb : ∀ b : LoopArg (d.L N) 2,
      ‖(Gauss.band d).Kval E N r (LoopData.idx (σ, b))‖ ≤ cK := by
    intro b
    exact Finset.single_le_sum (fun b _ => norm_nonneg
      ((Gauss.band d).Kval E N r (LoopData.idx (σ, b)))) (Finset.mem_univ b)
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn σ) (m := 2) hη
    (window_im_ne_zero hE hv1 r hr)
    (window_le_abs_im hE hv1 r hr) (List.length_ofFn)
    (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a hKb
  have hraw1 : ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ,
      ‖fderiv ℝ (Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
        ((v : ℝ) : ℂ)
        (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r) M‖
        ≤ row r * B := hraw.bdd₁
  have hrow : row r ≤ |Cr| :=
    (le_abs_self (row r)).trans ((hCr r hr).trans (le_abs_self Cr))
  have hnorm :
      ‖fderiv ℝ (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) M‖ =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
          ‖fderiv ℝ (Gauss.ukerObsT d N E (List.ofFn σ)
            (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
            (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r) M‖ := by
    have heq : APrimeDriftTimeFamily.coordAt d E D N σ a s v r =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ •
          Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
            ((v : ℝ) : ℂ)
            (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r := by
      funext M
      change _ / ((APrimeDriftTimeFamily.driftScale d E D N a s v : ℝ) : ℂ) =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ • _
      simp [Complex.real_smul, div_eq_mul_inv, Complex.ofReal_inv, mul_comm]
    rw [heq, fderiv_const_smul_field]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
  rw [hnorm]
  dsimp [C]
  exact mul_le_mul_of_nonneg_left
    ((hraw1 M).trans (mul_le_mul_of_nonneg_right hrow hB))
    (inv_nonneg.mpr hc.le)

/-- The uncut evolved quadratic variation has a uniform deterministic
finite-size envelope on the entire closed window. -/
theorem exists_bdd_qvAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc s v, ∀ ω : Gauss.Ω d,
      0 ≤ APrimeDriftTimeFamily.qvAt d E D N σ a s v r ω ∧
        APrimeDriftTimeFamily.qvAt d E D N σ a s v r ω ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_bdd_fderiv_coordAt d E D N σ a hE hs0 hsv hv1
  let C : ℝ := ∑ z ∈ Gauss.usedCoord d N,
    (Gauss.gvar d (Gauss.crd d N z) : ℝ) *
      (C₁ * ‖Gauss.Bmat d N z.1 z.2.1 z.2.2‖) ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun z _ =>
    mul_nonneg (Gauss.gvar d (Gauss.crd d N z)).2 (sq_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro r hr ω
  constructor
  · exact Gauss.quadVar_nonneg _ _
  · change (∑ z ∈ Gauss.usedCoord d N,
      (Gauss.gvar d (Gauss.crd d N z) : ℝ) *
        ‖Gauss.coordD1 d N
          (APrimeDriftTimeFamily.coordAt d E D N σ a s v r)
          (Gauss.Hflow d N r ω) z‖ ^ 2) ≤ C
    dsimp [C]
    apply Finset.sum_le_sum
    intro z hz
    apply mul_le_mul_of_nonneg_left _ (Gauss.gvar d (Gauss.crd d N z)).2
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Gauss.norm_coordD1_le (hC₁ r hr) (Gauss.Hflow d N r ω) z) 2

#print axioms RBM.APrimeQVRateTime.continuous_coordAt_on_window
#print axioms RBM.APrimeQVRateTime.measurable_qvAt_on_window
#print axioms RBM.APrimeQVRateTime.exists_bdd_fderiv_coordAt
#print axioms RBM.APrimeQVRateTime.exists_bdd_qvAt

end RBM.APrimeQVRateTime
