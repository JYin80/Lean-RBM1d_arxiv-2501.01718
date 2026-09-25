/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingWeightedCoordinateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingWeightedDriftIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCrossYRegularity
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1077: exact actual-weighted moving drift-product integrability

The literal mixed product consumed as `hm1` by `momFlowDeriv_le` is
integrable by weighted Hölder from the accepted actual-weighted `hYi` and
`hGi` estimates. The same moving coordinate, smooth cutoff, normalized drift,
endpoint, time, and probability space are used throughout.
-/

namespace RBM.APrimeGeneralMovingWeightedDriftProductIntegrable

open Filter MeasureTheory Set Gauss CutHypTheta Real

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

private noncomputable def mesh (D : Real) : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh D

private noncomputable def endpoint (s t : Nat → Real) (D : Real)
    (N k : Nat) : Real := cutNetPt s (mesh D) N k

private noncomputable def weight (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.weight E D s t deltaWeight p N k

private noncomputable def drift (E D : Real) (s t : Nat → Real)
    (N k : Nat) (a : LoopArg (d.L N) 2) (u : Real) : Ω d → Real :=
  APrimeGeneralMovingSmoothDriftNormBudget.drift E D s t N k a u

private noncomputable def cutoff (E D deltaWeight : Real) (s t : Nat → Real)
    (N k : Nat) (omega : Ω d) : Real :=
  APrimeSmoothWeightActual.cutoff d E D deltaWeight s (mesh D) N k
    (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N) omega

private noncomputable def actualY (E D deltaWeight : Real) (s t : Nat → Real)
    (N k : Nat) (sigma : Fin 2 → Bool) (a : LoopArg (d.L N) 2)
    (r : Real) : Ω d → Real :=
  APrimeGeneralMovingCrossYRegularity.actualY d E D deltaWeight s t N k sigma a r

private noncomputable def actualG (E D deltaWeight : Real) (s t : Nat → Real)
    (N k : Nat) (a : LoopArg (d.L N) 2) (r : Real) : Ω d → Real :=
  fun omega => cutoff E D deltaWeight s t N k omega *
    |drift E D s t N k a r omega|

/-- For fixed `p ≥ 1`, the exact T615-weighted `hm1` product for the moving
`Step2.sigPM` coordinate and normalized drift is integrable on the full
Gaussian space, eventually uniformly over every active target cell (including
`k = 0`) and every time in its closed cell. -/
theorem eventually_actual_weighted_drift_product_integrable
    {E D c deltaWeight : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (p : Nat) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (s N) (endpoint s t D N k),
      Integrable
        (fun omega => weight E D s t deltaWeight p N k omega *
          |APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N)
              (endpoint s t D N k)) r omega| ^ (2 * p - 1) *
          |drift E D s t N k a r omega|)
        (P d) := by
  have hYi :=
    APrimeGeneralMovingWeightedCoordinateIntegrable.eventually_actual_weighted_flowY_integrable
      (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1 p hp
  have hGi :=
    APrimeGeneralMovingWeightedDriftIntegrable.eventually_actual_weighted_drift_integrable
      (E := E) (D := D) (c := c) (deltaWeight := deltaWeight)
      hE hD hs0 hst ht1 hc hreg p hp
  filter_upwards [hYi, hGi, eventually_ge_atTop 2] with N hYiN hGiN hN2
  intro k hk a r hr
  let v := endpoint s t D N k
  have hv : v ∈ Icc (s N) (t N) := by
    simpa [v, endpoint, mesh] using
      (MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos D N) _
        (cutNetPt_mem_netFinset hk))
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hNpos : 0 < N := by omega
  have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d s t (mesh D) N :=
    APrimeSmoothWeightActual.canonicalM_pos d s t (mesh D) N
  have hu : ∀ j < k, cutNetPt s (mesh D) N j < 1 := by
    intro j hj
    have hjtop : j ≤ cutNetTop s t (mesh D) N := hj.le.trans hk
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht1 N)
  have hcut : Continuous (cutoff E D deltaWeight s t N k) := by
    unfold cutoff
    exact APrimeSmoothWeightActual.continuous_cutoff d
      (E := E) (D := D) (δ := deltaWeight) (s := s) (mesh := mesh D)
      (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      hE hs1 hNpos hm hu
  have hcut0 : ∀ omega, 0 ≤ cutoff E D deltaWeight s t N k omega := by
    intro omega
    unfold cutoff
    exact Cutoff.cutChi_nonneg _
  have hactive :
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ∧ 2 ≤ N :=
    ⟨by simpa [mesh] using hk, hN2⟩
  have hweight : ∀ omega,
      weight E D s t deltaWeight p N k omega =
        cutoff E D deltaWeight s t N k omega ^ (2 * p) := by
    intro omega
    change (if k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ∧ 2 ≤ N
      then APrimeSmoothWeightActual.cutoff d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) omega ^ (2 * p)
      else 1) = _
    rw [if_pos hactive]
    simp [cutoff, mesh]
  have hYfields := hYiN k hk Step2.sigPM a r hr
  have hYregular :=
    APrimeGeneralMovingCrossYRegularity.actualY_hYm_hYi d hE hs0 hst ht1
      (deltaWeight := deltaWeight) hp hNpos hk Step2.sigPM a hr
  have hYint : Integrable
      (fun omega => |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^
        (2 * p)) (P d) := by
    have heq : ∀ omega,
        |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^ (2 * p) =
          weight E D s t deltaWeight p N k omega *
            |APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
                (s N) v) r omega| ^ (2 * p) := by
      intro omega
      have hY : actualY E D deltaWeight s t N k Step2.sigPM a r omega =
          cutoff E D deltaWeight s t N k omega *
            APrimeDuhamelModel.flowY d N
              (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
                (s N) v) r omega := by
        simp [actualY, APrimeGeneralMovingCrossYRegularity.actualY,
          APrimeDuhamelModel.flowY, cutoff, endpoint, mesh, v]
      rw [hY, abs_of_nonneg (mul_nonneg (hcut0 omega)
        (APrimeDuhamelModel.flowY_nonneg d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
          r omega)), hweight omega, mul_pow,
        abs_of_nonneg (APrimeDuhamelModel.flowY_nonneg d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
          r omega)]
    exact (hYfields.2).congr (Filter.Eventually.of_forall fun omega =>
      (heq omega).symm)
  have hGfields := hGiN k hk a r hr
  have hGint : Integrable
      (fun omega => |actualG E D deltaWeight s t N k a r omega| ^ (2 * p))
      (P d) := by
    have heq : ∀ omega,
        |actualG E D deltaWeight s t N k a r omega| ^ (2 * p) =
          weight E D s t deltaWeight p N k omega *
            |drift E D s t N k a r omega| ^ (2 * p) := by
      intro omega
      rw [actualG, abs_of_nonneg (mul_nonneg (hcut0 omega) (abs_nonneg _)),
        hweight omega, mul_pow]
    exact hGfields.congr (Filter.Eventually.of_forall fun omega =>
      (heq omega).symm)
  have hYmeas : AEStronglyMeasurable
      (actualY E D deltaWeight s t N k Step2.sigPM a r) (P d) := hYregular.1
  have hdriftMeas : Measurable (drift E D s t N k a r) := by
    have hr1 : r < 1 := hr.2.trans_lt hv1
    have hr' : r ∈ Icc (s N) v := by simpa [v, endpoint, mesh] using hr
    have hcont := (Gauss.continuous_uker_driftF_omega d E N
      (Gauss.window_im_ne_zero hE hv1 r hr')
      (Gauss.window_norm_mul_lt hE.le (hs0 N) hv1 r hr')
      Step2.sigPM a ((v : Real) : Complex)).norm.div_const
        (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)
    unfold drift APrimeGeneralMovingSmoothDriftNormBudget.drift
      APrimeDriftTimeFamily.driftAt
    exact hcont.measurable
  have hZmeas : AEStronglyMeasurable
      (actualG E D deltaWeight s t N k a r) (P d) := by
    apply (hcut.measurable.mul
      ((continuous_abs.measurable.comp hdriftMeas))).aestronglyMeasurable
  have hpR : (1 : Real) ≤ (p : Real) := by exact_mod_cast hp
  have h2pSub : (0 : Real) < 2 * (p : Real) - 1 := by linarith
  have hqYpos : 0 < 2 * (p : Real) / (2 * (p : Real) - 1) :=
    div_pos (by linarith) h2pSub
  have hcast : ((2 * p - 1 : Nat) : Real) = 2 * (p : Real) - 1 := by
    have hle : 1 ≤ 2 * p := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hconj : HolderConjugate
      (2 * (p : Real) / (2 * (p : Real) - 1)) (2 * (p : Real)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ h2pSub]
      linarith
    · field_simp
      ring
  have hpowY : ∀ omega,
      (|actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^ (2 * p - 1)) ^
        (2 * (p : Real) / (2 * (p : Real) - 1)) =
        |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^ (2 * p) := by
    intro omega
    rw [← Real.rpow_natCast _ (2 * p - 1), ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_natCast _ (2 * p)]
    congr 1
    rw [hcast]
    field_simp
    push_cast
    ring
  have hpowG : ∀ omega,
      |actualG E D deltaWeight s t N k a r omega| ^ (2 * (p : Real)) =
        |actualG E D deltaWeight s t N k a r omega| ^ (2 * p) := by
    intro omega
    rw [← Real.rpow_natCast _ (2 * p)]
    congr 1
    push_cast
    ring
  have hFmeas : AEStronglyMeasurable
      (fun omega => |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^
        (2 * p - 1)) (P d) :=
    (continuous_pow _).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable hYmeas)
  have hGabsMeas : AEStronglyMeasurable
      (fun omega => |actualG E D deltaWeight s t N k a r omega|) (P d) :=
    continuous_abs.comp_aestronglyMeasurable hZmeas
  have hFmem : MemLp
      (fun omega => |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^
        (2 * p - 1))
      (ENNReal.ofReal (2 * (p : Real) / (2 * (p : Real) - 1))) (P d) := by
    refine MomentDuhamel.memLp_ofReal_of_integrable_rpow hqYpos hFmeas ?_
    have heq :
        (fun omega => |(|actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^
          (2 * p - 1))| ^ (2 * (p : Real) / (2 * (p : Real) - 1))) =
        (fun omega => |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^
          (2 * p)) := by
      funext omega
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), hpowY omega]
    rw [heq]
    exact hYint
  have hGmem : MemLp (fun omega =>
      |actualG E D deltaWeight s t N k a r omega|)
      (ENNReal.ofReal (2 * (p : Real))) (P d) := by
    refine MomentDuhamel.memLp_ofReal_of_integrable_rpow (by linarith) hGabsMeas ?_
    have heq : (fun omega => |(|actualG E D deltaWeight s t N k a r omega|)| ^
        (2 * (p : Real))) =
        (fun omega => |actualG E D deltaWeight s t N k a r omega| ^ (2 * p)) := by
      funext omega
      rw [abs_abs, hpowG omega]
    rw [heq]
    exact hGint
  letI : ENNReal.HolderConjugate
      (ENNReal.ofReal (2 * (p : Real) / (2 * (p : Real) - 1)))
      (ENNReal.ofReal (2 * (p : Real))) := hconj.ennrealOfReal
  have hprod := hFmem.integrable_mul hGmem
  have hproduct : ∀ omega,
      weight E D s t deltaWeight p N k omega *
        |APrimeDuhamelModel.flowY d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
          r omega| ^ (2 * p - 1) * |drift E D s t N k a r omega| =
      |actualY E D deltaWeight s t N k Step2.sigPM a r omega| ^ (2 * p - 1) *
        |actualG E D deltaWeight s t N k a r omega| := by
    intro omega
    have hY : actualY E D deltaWeight s t N k Step2.sigPM a r omega =
        cutoff E D deltaWeight s t N k omega *
          APrimeDuhamelModel.flowY d N
            (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
            r omega := by
      simp [actualY, APrimeGeneralMovingCrossYRegularity.actualY,
        APrimeDuhamelModel.flowY, cutoff, endpoint, mesh, v]
    have hcutPow :
        cutoff E D deltaWeight s t N k omega ^ (2 * p) =
          cutoff E D deltaWeight s t N k omega ^ (2 * p - 1) *
            cutoff E D deltaWeight s t N k omega := by
      calc
        cutoff E D deltaWeight s t N k omega ^ (2 * p) =
            cutoff E D deltaWeight s t N k omega ^ ((2 * p - 1) + 1) := by
              congr 1 <;> omega
        _ = cutoff E D deltaWeight s t N k omega ^ (2 * p - 1) *
            cutoff E D deltaWeight s t N k omega := by rw [pow_add, pow_one]
    rw [hY, hweight omega,
      abs_of_nonneg (mul_nonneg (hcut0 omega)
        (APrimeDuhamelModel.flowY_nonneg d N
          (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
          r omega)),
      abs_of_nonneg (APrimeDuhamelModel.flowY_nonneg d N
        (APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v)
        r omega), actualG,
      abs_of_nonneg (mul_nonneg (hcut0 omega) (abs_nonneg _))]
    rw [hcutPow]
    ring
  exact hprod.congr (Filter.Eventually.of_forall fun omega =>
    (hproduct omega).symm)

/-- T995's accepted same-resident positive-cell witness accompanies this
full-space integrability result and rules out an empty-weight/empty-cell
vacuity reading. -/
noncomputable abbrev t995_nondegenerate_positive_weight_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_actual_weighted_drift_product_integrable
#print axioms t995_nondegenerate_positive_weight_witness

end
end RBM.APrimeGeneralMovingWeightedDriftProductIntegrable
