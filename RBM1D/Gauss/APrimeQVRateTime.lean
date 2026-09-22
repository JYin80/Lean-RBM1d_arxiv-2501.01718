/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeNormalizedGenerator
import RBM1D.Gauss.APrimeWeight

/-! # T294: time integrability of the actual evolved Gaussian QV rate -/

#check @RBM.APrimeDriftTimeFamily.qvAt
#check @RBM.APrimeDriftTimeFamily.coordAt
#check @RBM.Gauss.differentiableAt_ukerObsT_pair
#check @RBM.Gauss.bddC2C_ukerObsT
#check @RBM.Gauss.continuous_ukerRow
#check @measurable_fderiv_with_param
#check @MeasureTheory.StronglyMeasurable.integral_prod_right'
#check @RBM.APrimeWeight.measurable_prefixSoftW
#check @RBM.APrimeSlotFields.measurable_jSnorm

namespace RBM.APrimeQVRateTime

open MeasureTheory Set Step2Bootstrap
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

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
    have hz : (zt E r).im ≠ 0 := Gauss.window_im_ne_zero hE hv1 r hr
    have hK : ∀ b, DifferentiableAt ℝ
        (fun x : ℝ => (Gauss.band d).Kval E N x (LoopData.idx (σ, b))) r := by
      intro b
      exact (Gauss.hasDerivAt_Kval_Kprim (Gauss.band d) E N
        (Gauss.window_norm_mul_lt hE.le hs0 hv1 r hr) σ b).differentiableAt
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
  have hη : 0 < η := Gauss.window_eta_pos hE hv1
  have hc : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d (D := D) hE hsv hv1 N a
  obtain ⟨cK, hcK, hKb, _⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) E N hE.le hs0 hv1 (v := v) σ
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
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn σ) (m := 2) hη
    (Gauss.window_im_ne_zero hE hv1 r hr)
    (Gauss.window_le_abs_im hE hv1 r hr) (List.length_ofFn)
    (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a
    (hKb r hr)
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
  · exact APrimeDuhamelModel.qvRateEvolved_nonneg d N
      (APrimeDriftTimeFamily.coordAt d E D N σ a s v) r ω
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

/-- The time rate is Borel measurable on the closed-window subtype; this
uses joint parameterized matrix-derivative measurability. -/
theorem measurable_rateNormW_qvAt_window (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (w : Gauss.Ω d → ℝ) (hw : Measurable w) :
    Measurable (fun r : Icc s v => APrimeModel.rateNormW (Gauss.P d) w p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v r.1)) := by
  have hq := measurable_qvAt_on_window d E D N σ a hE hs0 hsv hv1
  have hintg : Measurable (fun q : (Icc s v) × Gauss.Ω d =>
      w q.2 * |APrimeDriftTimeFamily.qvAt d E D N σ a s v q.1.1 q.2| ^ p) :=
    (hw.comp measurable_snd).mul ((continuous_abs.measurable.comp hq).pow_const p)
  have hint : StronglyMeasurable (fun r : Icc s v =>
      ∫ ω, w ω * |APrimeDriftTimeFamily.qvAt d E D N σ a s v r.1 ω| ^ p
        ∂(Gauss.P d)) := by
    exact hintg.stronglyMeasurable.integral_prod_right'
  exact (Real.continuous_rpow_const
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ))).measurable.comp hint.measurable

/-- The actual, uncut evolved-QV rate is time integrable for every fixed
measurable sample weight between zero and one. -/
theorem intervalIntegrable_rateNormW_qvAt (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hp : 1 ≤ p) (w : Gauss.Ω d → ℝ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1) :
    IntervalIntegrable (fun r => APrimeModel.rateNormW (Gauss.P d) w p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v r)) volume s v := by
  obtain ⟨C, hC0, hQ⟩ := exists_bdd_qvAt d E D N σ a hE hs0 hsv hv1
  let f : ℝ → ℝ := fun r => APrimeModel.rateNormW (Gauss.P d) w p
    (APrimeDriftTimeFamily.qvAt d E D N σ a s v r)
  have hmeas : Measurable (fun r : Icc s v => f r.1) :=
    measurable_rateNormW_qvAt_window d E D N p σ a hE hs0 hsv hv1 w hw
  have hbd : ∀ r : Icc s v, ‖f r.1‖ ≤ C := by
    intro ⟨r, hr⟩
    have hnonneg := APrimeModel.rateNormW_nonneg (P := Gauss.P d) hw0 p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v r)
    have hle : f r ≤ C := by
      apply APrimeModel.rateNormW_le_of_le_on (P := Gauss.P d) hw0 hw1 hp hC0
        (G := Set.univ)
      · intro ω _
        rw [abs_of_nonneg (hQ r hr ω).1]
        exact (hQ r hr ω).2
      · intro ω hω
        exact False.elim (hω (Set.mem_univ ω))
    simpa [f, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  let μ : Measure (Icc s v) := volume.comap ((↑) : Icc s v → ℝ)
  haveI hcompact : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  haveI : IsFiniteMeasure μ := inferInstance
  have hint : Integrable (fun r : Icc s v => f r.1) μ :=
    Integrable.of_bound hmeas.stronglyMeasurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbd)
  have hintOn : IntegrableOn f (Icc s v) volume :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).2 hint
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).2 hintOn

/-- Specialization to the actual prefix soft weight driven by measurable
`jSnorm`; the QV itself remains uncut. -/
theorem intervalIntegrable_rateNormW_prefixSoftW (d : Gauss.Dims) (E D : ℝ)
    (N p r k : ℕ) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2)
    (sGrid mesh : ℕ → ℝ) (θ : ℝ) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (hp : 1 ≤ p) :
    IntervalIntegrable (fun u => APrimeModel.rateNormW (Gauss.P d)
      (APrimeWeight.prefixSoftW r
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D sGrid N u ω)
        sGrid mesh N k θ) p
      (APrimeDriftTimeFamily.qvAt d E D N σ a s v u)) volume s v := by
  let J : ℕ → ℝ → Gauss.Ω d → ℝ :=
    fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D sGrid N u ω
  let w : Gauss.Ω d → ℝ := APrimeWeight.prefixSoftW r J sGrid mesh N k θ
  have hw : Measurable w :=
    APrimeWeight.measurable_prefixSoftW r J sGrid mesh N k θ
      (fun u => APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D sGrid N u)
  have hw0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact softW_nonneg _ _ _ _
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    exact softW_le_one _ _ _ _
  exact intervalIntegrable_rateNormW_qvAt d E D N p σ a hE hs0 hsv hv1 hp
    w hw hw0 hw1

/-- The empty-prefix first cell has a genuinely positive time length and
unit soft weight. -/
theorem first_cell_empty_prefix_witness (d : Gauss.Dims) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (sGrid mesh : ℕ → ℝ) :
    (∀ ω : Gauss.Ω d,
      APrimeWeight.prefixSoftW 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 0 sGrid N u ω)
        sGrid mesh N 0 1 ω = 1) ∧
    IntervalIntegrable (fun u => APrimeModel.rateNormW (Gauss.P d)
      (APrimeWeight.prefixSoftW 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 0 sGrid N u ω)
        sGrid mesh N 0 1) 1
      (APrimeDriftTimeFamily.qvAt d 0 0 N σ a 0 (1 / 2) u))
      volume 0 (1 / 2) ∧
    (0 : ℝ) < 1 / 2 := by
  constructor
  · intro ω
    simp [APrimeWeight.prefixSoftW, softW, softMax, Cutoff.cutChi_eq_one]
  constructor
  · exact intervalIntegrable_rateNormW_prefixSoftW d 0 0 N 1 1 0 σ a
      sGrid mesh 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · norm_num

#print axioms RBM.APrimeQVRateTime.measurable_qvAt_on_window
#print axioms RBM.APrimeQVRateTime.exists_bdd_qvAt
#print axioms RBM.APrimeQVRateTime.intervalIntegrable_rateNormW_qvAt
#print axioms RBM.APrimeQVRateTime.intervalIntegrable_rateNormW_prefixSoftW
#print axioms RBM.APrimeQVRateTime.first_cell_empty_prefix_witness

end RBM.APrimeQVRateTime
