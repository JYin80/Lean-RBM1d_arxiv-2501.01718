/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeRateRegularity
import RBM1D.Gauss.TestFunQGeneral

/-!
# T292: the actual Gaussian drift time family at a fixed endpoint and pair
-/

#check @RBM.APrimeDuhamelModel.momFlowDeriv_le
#check @RBM.Gauss.timeD1_add_genMomentPt_le_driftF_flow
#check @RBM.Gauss.continuousOn_uker_driftF_path
#check @RBM.Gauss.exists_bdd_uker_driftF
#check @RBM.Gauss.continuousOn_momNorm_driftF_gauss
#check @RBM.Gauss.hbound_momentObsT_gauss
#check @RBM.APrimeRateRegularity.intervalIntegrable_crossInt_qHatNear
#check @RBM.Gauss.ukerObsT_flow
#check @RBM.APrimeDuhamelModel.crossPart_le_of_S5
#check @RBM.APrimeDuhamelModel.crossBudget_le_crossInt_model
#check @RBM.APrimeDuhamelModel.EvolvedQVBound

namespace RBM.APrimeDriftTimeFamily

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Fixed sample weights preserve time continuity of finite-size bounded
moment norms.  This uses dominated convergence in time, not pointwise
moment finiteness or an integral budget. -/
theorem continuousOn_momNormW_of_envelope {S : Set ℝ}
    {f : ℝ → Ω → ℝ} {w : Ω → ℝ} {C : ℝ} (p : ℕ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1)
    (hmeas : ∀ u ∈ S,
      AEStronglyMeasurable (fun ω => w ω * |f u ω| ^ (2 * p)) P)
    (hbd : ∀ u ∈ S, ∀ ω, |f u ω| ≤ C)
    (hcont : ∀ ω, ContinuousOn (fun u => f u ω) S) :
    ContinuousOn (fun u => MomentDuhamel.momNormW P w p (f u)) S := by
  have hI : ContinuousOn
      (fun u => ∫ ω, w ω * |f u ω| ^ (2 * p) ∂P) S := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun _ : Ω => |C| ^ (2 * p)) hmeas ?_ (integrable_const _) ?_
    · intro u hu
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 ω),
        abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      calc
        w ω * |f u ω| ^ (2 * p) ≤ 1 * |f u ω| ^ (2 * p) := by
          gcongr
          exact hw1 ω
        _ = |f u ω| ^ (2 * p) := one_mul _
        _ ≤ |C| ^ (2 * p) :=
          pow_le_pow_left₀ (abs_nonneg _) ((hbd u hu ω).trans (le_abs_self C)) _
    · exact Filter.Eventually.of_forall fun ω =>
        continuousOn_const.mul ((hcont ω).abs.pow (2 * p))
  exact (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 1 / (2 * (p : ℝ))))
    |>.comp_continuousOn hI

/-- The plain evolved-coordinate drift, pinned to the Gaussian `driftF`
and the same propagator row as `ukerObsT`.  The denominator is the fixed
right-endpoint normalization of the A′ slot. -/
noncomputable def driftScale (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (s v : ℝ) : ℝ :=
  Step2.tT (Gauss.band d) E N D v (zdist (d.L N) (a 0 - a 1)) *
    (etaT E s / etaT E v) ^ 4

theorem driftScale_pos (d : Gauss.Dims) {E D s v : ℝ} (hE : |E| < 2)
    (hsv : s ≤ v) (hv1 : v < 1) (N : ℕ) (a : LoopArg (d.L N) 2) :
    0 < driftScale d E D N a s v := by
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hR : 0 < etaT E s / etaT E v :=
    div_pos (Step2.etaT_pos' hE hs1) (Step2.etaT_pos' hE hv1)
  have hW : 0 < ((Gauss.band d).W N : ℝ) := by
    exact_mod_cast (Gauss.band d).W_pos N
  have hT : 0 < Step2.tT (Gauss.band d) E N D v
      (zdist (d.L N) (a 0 - a 1)) := by
    dsimp [Step2.tT]
    exact tailT_pos hW _
  exact mul_pos hT (pow_pos hR _)

noncomputable def driftAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
    (DriftDef.driftF (Gauss.band d) E N r ((Gauss.sample d).H N r ω) σ) a‖ /
      driftScale d E D N a s v

/-- The endpoint-normalized evolved coordinate at an arbitrary matrix. -/
noncomputable def coordAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r M /
      ((driftScale d E D N a s v : ℝ) : ℂ)

/-- The actual moment test function built from the normalized coordinate. -/
noncomputable def momentAt (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ((‖coordAt d E D N σ a s v r M‖ ^ (2 * p) : ℝ) : ℂ)

theorem momentAt_isModulusPow (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v : ℝ) :
    APrimeDuhamelModel.IsModulusPow
      (momentAt d E D N p σ a s v) (coordAt d E D N σ a s v) p :=
  fun _ _ => rfl

theorem flowY_coordAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hsv : s ≤ v) (hv1 : v < 1)
    (r : ℝ) (ω : Gauss.Ω d) :
    APrimeDuhamelModel.flowY d N (coordAt d E D N σ a s v) r ω =
      ‖Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.lkT (Gauss.sample d) E N r ω σ) a‖ /
          driftScale d E D N a s v := by
  have hscale := driftScale_pos d (D := D) hE hsv hv1 N a
  have hbr := Gauss.ukerObsT_flow (Gauss.band d) (Gauss.sample d) E N σ a
    ((v : ℝ) : ℂ) (fun _ _ => rfl) r ω
  change Gauss.ukerObsT d N E (List.ofFn σ) (xiOf (mSigma E) σ)
      ((v : ℝ) : ℂ)
      (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a r
      (Gauss.Hflow d N r ω) =
    Uker (d.L N) (xiOf (mSigma E) σ) ((r : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (SumZeroDyn.lkT (Gauss.sample d) E N r ω σ) a at hbr
  simp only [APrimeDuhamelModel.flowY, coordAt, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hscale]
  rw [hbr]

/-- The model-pinned quadratic-variation rate for the same normalized
coordinate.  Its time regularity belongs to T294. -/
noncomputable def qvAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  Gauss.quadVar d N (coordAt d E D N σ a s v r) (Gauss.Hflow d N r ω)

theorem qvAt_eq_evolved (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (ω : Gauss.Ω d) :
    qvAt d E D N σ a s v r ω =
      APrimeDuhamelModel.qvRateEvolved d N (coordAt d E D N σ a s v) r ω := rfl

/-- The fixed-scale regularity obligation for T275's test-function argument.
The existing Gaussian producer treats the unnormalized `momentObsT`. -/
def NormalizedTestFunBridge (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v : ℝ) : Prop :=
  Gauss.TestFunT₁ d N (Icc s v) (momentAt d E D N p σ a s v)

/-- The exact missing generator comparison after normalization.  Both rates
are model-pinned; there is no caller-chosen stochastic drift field. -/
def NormalizedGeneratorBridge (d : Gauss.Dims) (E D : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ) : Prop :=
  ∀ ω : Gauss.Ω d,
    (Gauss.timeD1 (momentAt d E D N p σ a s v) r (Gauss.Hflow d N r ω)).re +
      APrimeDuhamelModel.genPt d N (momentAt d E D N p σ a s v r)
        (Gauss.Hflow d N r ω)
      ≤ 2 * (p : ℝ) *
          (|APrimeDuhamelModel.flowY d N (coordAt d E D N σ a s v) r ω| ^
            (2 * p - 1) * |driftAt d E D N σ a s v r ω|) +
        (p : ℝ) * (2 * (p : ℝ) - 1) *
          (|APrimeDuhamelModel.flowY d N (coordAt d E D N σ a s v) r ω| ^
            (2 * p - 2) * qvAt d E D N σ a s v r ω)

/-- The deterministic near cross rate on the fixed endpoint window. -/
noncomputable def crossAt (E s v κ : ℝ) (r : ℝ) : ℝ :=
  APrimeModel.crossInt κ (APrimeTimeInt.qHatNear E s v) r

/-- The precise still-unproved near cross comparison for this same family.
Its need for an evolved-QV envelope and a common Good event is explicit in
`crossPart_le_of_S5` and `crossBudget_le_crossInt_model`. -/
def NearCrossBridge (d : Gauss.Dims) (E D κ : ℝ) (N p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (s v r : ℝ)
    (w : Gauss.Ω d → ℝ)
    (wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ) : Prop :=
  APrimeDuhamelModel.crossPart d N (momentAt d E D N p σ a s v) wD r ≤
    2 * (p : ℝ) *
      (∫ ω, w ω *
        |APrimeDuhamelModel.flowY d N (coordAt d E D N σ a s v) r ω| ^ (2 * p)
        ∂(Gauss.P d)) ^ ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
      crossAt E s v κ r

/-- The weighted norm of the model-pinned drift is continuous in time on
every fixed closed Gaussian window. -/
theorem continuousOn_momNormW_driftAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (w : Gauss.Ω d → ℝ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1) (p : ℕ) :
    ContinuousOn (fun r => MomentDuhamel.momNormW (Gauss.P d) w p
      (driftAt d E D N σ a s v r)) (Icc s v) := by
  classical
  have hscale : 0 < driftScale d E D N a s v :=
    driftScale_pos d hE hsv hv1 N a
  obtain ⟨cK, hcK, hKb, hK'b⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) E N hE.le hs0 hv1 (v := v) σ
  obtain ⟨C, hC0, hC⟩ := Gauss.exists_bdd_uker_driftF (Gauss.band d)
    E N σ a ((v : ℝ) : ℂ) (Gauss.window_eta_pos hE hv1)
    (Gauss.window_le_abs_im hE hv1) hKb hK'b
    (Gauss.window_norm_mul_lt hE.le hs0 hv1)
    (Gauss.window_norm_xi_lt hE.le hs0 hv1 σ)
    (fun i => by
      rw [xiOf, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hs0.trans hsv),
        norm_mSigma hE.le, norm_mSigma hE.le, mul_one, mul_one]
      exact hv1)
  refine continuousOn_momNormW_of_envelope (P := Gauss.P d)
    (C := C / driftScale d E D N a s v) p hw0 hw1 ?_ ?_ ?_
  · intro r hr
    have hf : Continuous (driftAt d E D N σ a s v r) := by
      exact (Gauss.continuous_uker_driftF_omega d E N
        (Gauss.window_im_ne_zero hE hv1 r hr)
        (Gauss.window_norm_mul_lt hE.le hs0 hv1 r hr)
        σ a ((v : ℝ) : ℂ)).norm.div_const _
    exact (hw.mul (hf.abs.pow (2 * p)).measurable).aestronglyMeasurable
  · intro r hr ω
    rw [driftAt, abs_div, abs_norm, abs_of_pos hscale]
    exact div_le_div_of_nonneg_right
      (hC r hr _ (Gauss.Hflow_isHermitian d N r ω)) hscale.le
  · intro ω
    exact ((Gauss.continuousOn_uker_driftF_path (X := ℝ) d N E (τ := id)
      (Mt := fun r => Gauss.Hflow d N r ω) continuousOn_id
      (Gauss.continuous_Hflow_time d N ω).continuousOn
      (fun r => Gauss.Hflow_isHermitian d N r ω)
      (fun r hr => Gauss.window_im_ne_zero hE hv1 r hr)
      (fun r hr => Gauss.window_norm_mul_lt hE.le hs0 hv1 r hr)
      σ a ((v : ℝ) : ℂ)).norm.div_const _)

theorem intervalIntegrable_momNormW_driftAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (w : Gauss.Ω d → ℝ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1) (p : ℕ) :
    IntervalIntegrable (fun r => MomentDuhamel.momNormW (Gauss.P d) w p
      (driftAt d E D N σ a s v r)) volume s v :=
  (continuousOn_momNormW_driftAt d E D N σ a hE hs0 hsv hv1 w hw hw0 hw1 p)
    |>.intervalIntegrable_of_Icc hsv

/-- The near cross budget is time integrable on any nonnegative closed
window; the first cell is included and retains the square-root singularity. -/
theorem intervalIntegrable_crossAt {E s v κ : ℝ} (hE : |E| < 2)
    (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1) :
    IntervalIntegrable (crossAt E s v κ) volume s v := by
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hq : ContinuousOn (fun u => APrimeTimeInt.qHatNear E s v u) (Icc s v) := by
    simpa only [APrimeTimeInt.qHatNear, Set.uIcc_of_le hsv] using
      (APrimeTimeInt.nearInt_continuousOn hE hsv hv1).div_const
        ((etaT E s / etaT E v) ^ 8)
  have hsqrt : ContinuousOn
      (fun u => Real.sqrt (κ * APrimeTimeInt.qHatNear E s v u)) (Icc s v) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hq)
  have hbase : IntervalIntegrable (fun u : ℝ => Real.sqrt u⁻¹) volume s v := by
    apply (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).mono_set
    rw [Set.uIcc_of_le hsv, Set.uIcc_of_le hv0]
    intro u hu
    exact ⟨hs0.trans hu.1, hu.2⟩
  change IntervalIntegrable
    (fun u => Real.sqrt u⁻¹ * Real.sqrt (κ * APrimeTimeInt.qHatNear E s v u))
    volume s v
  exact hbase.mul_continuousOn (by simpa only [Set.uIcc_of_le hsv] using hsqrt)

/-- Both rates come from the same fixed Gaussian endpoint and coordinate;
the cross rate is the deterministic near-field choice. -/
theorem intervalIntegrable_drift_add_cross (d : Gauss.Dims) (E D κ : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsv : s ≤ v) (hv1 : v < 1)
    (w : Gauss.Ω d → ℝ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1) (p : ℕ) :
    IntervalIntegrable (fun r => MomentDuhamel.momNormW (Gauss.P d) w p
      (driftAt d E D N σ a s v r) + crossAt E s v κ r) volume s v :=
  (intervalIntegrable_momNormW_driftAt d E D N σ a hE hs0 hsv hv1 w hw hw0 hw1 p).add
    (intervalIntegrable_crossAt hE hs0 hsv hv1)

/-- A positive-length first-cell witness with a strictly positive near cross
rate and a nonzero endpoint normalization. -/
theorem first_cell_witness (d : Gauss.Dims) (N : ℕ)
    (a : LoopArg (d.L N) 2) :
    0 < driftScale d 0 0 N a 0 (1 / 2) ∧
      IntervalIntegrable (crossAt 0 0 (1 / 2) 1) volume 0 (1 / 2) ∧
      0 < crossAt 0 0 (1 / 2) 1 (1 / 4) := by
  have hcross := APrimeRateRegularity.crossInt_qHatNear_first_cell_witness
  exact ⟨driftScale_pos d (D := 0) (by norm_num) (by norm_num)
      (by norm_num) N a, hcross.1, hcross.2⟩

#print axioms RBM.APrimeDriftTimeFamily.driftAt
#print axioms RBM.APrimeDriftTimeFamily.driftScale_pos
#print axioms RBM.APrimeDriftTimeFamily.crossAt
#print axioms RBM.APrimeDriftTimeFamily.continuousOn_momNormW_of_envelope
#print axioms RBM.APrimeDriftTimeFamily.intervalIntegrable_momNormW_driftAt
#print axioms RBM.APrimeDriftTimeFamily.intervalIntegrable_drift_add_cross
#print axioms RBM.APrimeDriftTimeFamily.flowY_coordAt
#print axioms RBM.APrimeDriftTimeFamily.momentAt_isModulusPow
#print axioms RBM.APrimeDriftTimeFamily.qvAt_eq_evolved
#print axioms RBM.APrimeDriftTimeFamily.first_cell_witness

end RBM.APrimeDriftTimeFamily
