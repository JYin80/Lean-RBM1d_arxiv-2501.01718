/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1079: exact actual-weighted QV product integrability

This module supplies the literal `hm2` integrability premise consumed by
`APrimeDuhamelModel.momFlowDeriv_le`, at the T615 actual smooth weight,
moving `flowY`, and T993 fixed-charge evolved QV rate.  The exponent is kept
as `2 * p - 2`, including its zero-exponent case at `p = 1`.
-/

namespace RBM.APrimeGeneralMovingWeightedQVProductIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

private theorem contDiff_coordAt (E D : Real) (N : Nat)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v r : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hv1 : v < 1)
    (hr : r ∈ Icc s v) :
    ContDiff ℝ 1 (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) := by
  obtain ⟨cK, _, hK, _⟩ := Gauss.exists_bdd_Kval_Kprim
    (d := d) E N hE.le hs0 hv1 σ
  have hη := Gauss.window_eta_pos hE hv1
  have hz := Gauss.window_im_ne_zero hE hv1 r hr
  have hzη := Gauss.window_le_abs_im hE hv1 r hr
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn σ) (m := 2) hη hz hzη List.length_ofFn
    (xiOf (mSigma E) σ) ((v : Real) : Complex)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a
    (hK r hr)
  unfold APrimeDriftTimeFamily.coordAt
  exact (hraw.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).div_const _

private noncomputable def endpoint (s _t : Nat → Real) (D : Real)
    (N k : Nat) : Real :=
  cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k

private noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingActualSmoothQVNormBudget.weight E D s t deltaWeight p N k

private noncomputable def qv (E D : Real) (s t : Nat → Real)
    (N k : Nat) (a : LoopArg (d.L N) 2) (u : Real) : Ω d → Real :=
  APrimeGeneralMovingQVNormBudget.qv E D s t N k a u

/-- For each fixed `p ≥ 1`, the exact T615 actual-smooth weight times the
`(2p-2)`-power of the moving coordinate and the fixed T993 evolved QV rate is
integrable on the full Gaussian space, eventually uniformly over all active
target cells (including `k = 0`), outputs, and closed-cell times. -/
theorem eventually_actual_weighted_qv_product_integrable
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (p : Nat) (_hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (s N) (endpoint s t D N k),
        Integrable
          (fun ω => weight E D s t deltaWeight p N k ω *
            |APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
                (s N) (endpoint s t D N k)) r ω| ^ (2 * p - 2) *
              qv E D s t N k a r ω)
          (P d) := by
  have hqEnv := APrimeGeneralMovingQVNormBudget.eventually_abs_qv_le_envelope
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [hqEnv, eventually_ge_atTop 1] with N hqEnvN hN
  intro k hk a r hr
  let v := endpoint s t D N k
  have hv : v ∈ Icc (s N) (t N) := by
    simpa [v, endpoint] using
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hsv : s N ≤ v := hv.1
  have hcoordCont := contDiff_coordAt E D N Step2.sigPM a hE (hs0 N) hv1
    (by simpa [v, endpoint] using hr)
  have hYmeas : Measurable (fun ω : Ω d =>
      APrimeDuhamelModel.flowY d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
        r ω) := by
    rw [show (fun ω : Ω d => APrimeDuhamelModel.flowY d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
        r ω) = fun ω => ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
          (s N) v r (Gauss.Hflow d N r ω)‖ by
      funext ω
      rfl]
    exact ((hcoordCont.continuous.comp (Gauss.continuous_Hflow d N r)).norm).measurable
  have hqMeas : Measurable (qv E D s t N k a r) := by
    let ur : Icc (s N) v := ⟨r, by simpa [v, endpoint] using hr⟩
    have hembed : Measurable (fun ω : Ω d => (ur, ω)) :=
      measurable_const.prodMk measurable_id
    have hjoint := APrimeQVRateTime.measurable_qvAt_on_window
      d E D N Step2.sigPM a hE (hs0 N) hsv hv1
    have hcomp := hjoint.comp hembed
    simpa [qv, APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingQVNormBudget.endpoint, ur, v, endpoint,
      Function.comp_def] using hcomp
  have hwMeas : Measurable (weight E D s t deltaWeight p N k) :=
    APrimeGeneralMovingActualSmoothQVNormBudget.measurable_weight
      hE hst ht1 (by omega) hk
  have hmeas : Measurable (fun ω =>
      weight E D s t deltaWeight p N k ω *
        |APrimeDuhamelModel.flowY d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
          r ω| ^ (2 * p - 2) * qv E D s t N k a r ω) :=
    (hwMeas.mul ((continuous_abs.measurable.comp hYmeas).pow_const (2 * p - 2))).mul hqMeas
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d E D N a (s N) v :=
    APrimeDriftTimeFamily.driftScale_pos d hE hsv hv1 N a
  obtain ⟨cK, hcK, hK, _⟩ :=
    Gauss.exists_bdd_Kval_Kprim (d := d) E N hE.le (hs0 N) hv1 Step2.sigPM
  have hKwindow : ∀ u ∈ Icc (s N) v, ∀ b : LoopArg (d.L N) 2,
      ‖(Gauss.band d).Kval E N u (LoopData.idx (Step2.sigPM, b))‖ ≤ cK :=
    fun u hu b => hK u hu b
  obtain ⟨cRaw, hcRaw, hRaw⟩ :=
    Gauss.exists_bdd₀_ukerObsT (d := d) (N := N) E
      (σ := List.ofFn Step2.sigPM) (m := 2) List.length_ofFn
      (by norm_num : 1 ≤ 2)
      (xiOf (mSigma E) Step2.sigPM) ((v : Real) : Complex)
      (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (Step2.sigPM, b))) a
      (u₀ := s N) (u₁ := v)
      (Gauss.window_eta_pos hE hv1) hcK
      (Gauss.window_le_abs_im hE hv1) hKwindow
  have hcoordBound : ∀ ω : Ω d,
      ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v r
        (Gauss.Hflow d N r ω)‖ ≤ cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v := by
    intro ω
    rw [APrimeDriftTimeFamily.coordAt, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hscale]
    exact div_le_div_of_nonneg_right (hRaw r (by simpa [v, endpoint] using hr)
      (Gauss.Hflow d N r ω)) hscale.le
  have hqBound (ω : Ω d) :
      |qv E D s t N k a r ω| ≤ APrimeGeneralMovingQVNormBudget.qvEnvelope D N := by
    exact hqEnvN k hk r (by simpa [endpoint, APrimeGeneralMovingQVNormBudget.endpoint] using hr) a ω
  have hq0 (ω : Ω d) : 0 ≤ qv E D s t N k a r ω := by
    change 0 ≤ APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N)
      (APrimeGeneralMovingQVNormBudget.endpoint s t D N k) r ω
    rw [APrimeDriftTimeFamily.qvAt_eq_evolved]
    exact APrimeDuhamelModel.qvRateEvolved_nonneg d N
      (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v) r ω
  have hC0 : 0 ≤ cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v :=
    div_nonneg hcRaw hscale.le
  let C : Real :=
    (cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v) ^ (2 * p - 2) *
      APrimeGeneralMovingQVNormBudget.qvEnvelope D N
  have hC0' : 0 ≤ C := by
    dsimp [C]
    unfold APrimeGeneralMovingQVNormBudget.qvEnvelope
    positivity
  apply Integrable.of_bound hmeas.aestronglyMeasurable C
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  have hprod0 : 0 ≤ weight E D s t deltaWeight p N k ω *
      |APrimeDuhamelModel.flowY d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
        r ω| ^ (2 * p - 2) * qv E D s t N k a r ω :=
    mul_nonneg (mul_nonneg
      (APrimeGeneralMovingActualSmoothQVNormBudget.weight_nonneg
        E D s t deltaWeight p N k ω)
      (pow_nonneg (abs_nonneg _) _)) (hq0 ω)
  rw [abs_of_nonneg hprod0]
  dsimp [C]
  have hqle : qv E D s t N k a r ω ≤
      APrimeGeneralMovingQVNormBudget.qvEnvelope D N := by
    have hh := hqBound ω
    rw [abs_of_nonneg (hq0 ω)] at hh
    exact hh
  have hflowBound : |APrimeDuhamelModel.flowY d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
        r ω| ≤ cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v := by
    rw [APrimeDuhamelModel.flowY]
    simpa using hcoordBound ω
  have hEnv0 : 0 ≤ APrimeGeneralMovingQVNormBudget.qvEnvelope D N := by
    unfold APrimeGeneralMovingQVNormBudget.qvEnvelope
    positivity
  calc
    _ ≤ weight E D s t deltaWeight p N k ω *
        |APrimeDuhamelModel.flowY d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
          r ω| ^ (2 * p - 2) * APrimeGeneralMovingQVNormBudget.qvEnvelope D N :=
      mul_le_mul_of_nonneg_left hqle
        (mul_nonneg
          (APrimeGeneralMovingActualSmoothQVNormBudget.weight_nonneg
            E D s t deltaWeight p N k ω)
          (pow_nonneg (abs_nonneg _) _))
    _ ≤ 1 * |APrimeDuhamelModel.flowY d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
        r ω| ^ (2 * p - 2) * APrimeGeneralMovingQVNormBudget.qvEnvelope D N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (APrimeGeneralMovingActualSmoothQVNormBudget.weight_le_one
            E D s t deltaWeight p N k ω)
          (pow_nonneg (abs_nonneg _) _)) hEnv0
    _ ≤ (cRaw / APrimeDriftTimeFamily.driftScale d E D N a (s N) v) ^
          (2 * p - 2) * APrimeGeneralMovingQVNormBudget.qvEnvelope D N := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hflowBound _) hEnv0

/-- T995's accepted nondegenerate same-resident positive-cell witness. -/
noncomputable abbrev t995_nondegenerate_positive_weight_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_weighted_qv_product_integrable
#print axioms t995_nondegenerate_positive_weight_witness

end
end RBM.APrimeGeneralMovingWeightedQVProductIntegrable
