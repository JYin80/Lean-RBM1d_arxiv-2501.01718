/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingActualSmoothQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1071: exact full-space integrability input for the actual-smooth QV rate

This module supplies the `hQi` integrability premise consumed by
`APrimeDuhamelModel.momFlowDeriv_le`, for the actual-smooth T615 weight and the
fixed `Step2.sigPM` evolved QV rate.  Its only full-space size input is the
public deterministic QV envelope.  The conclusion includes the initial mesh
point and closed running intervals.
-/

namespace RBM.APrimeGeneralMovingWeightedQVIntegrable

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal actual smooth weight fixed by T615, with the T993 aliases. -/
noncomputable abbrev weight :=
  APrimeGeneralMovingActualSmoothQVNormBudget.weight

/-- The fixed-charge, evolved QV rate used by T591/T993. -/
noncomputable abbrev qv := APrimeGeneralMovingActualSmoothQVNormBudget.qv

/-- The actual T615 weight is pointwise nonnegative. -/
theorem weight_nonneg (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) (omega : Ω d) :
    0 ≤ weight E D s t deltaWeight p N k omega :=
  APrimeGeneralMovingActualSmoothQVNormBudget.weight_nonneg
    E D s t deltaWeight p N k omega

/-- The actual T615 weight is bounded above by one. -/
theorem weight_le_one (E D : Real) (s t : Nat → Real)
    (deltaWeight : Real) (p N k : Nat) (omega : Ω d) :
    weight E D s t deltaWeight p N k omega ≤ 1 :=
  APrimeGeneralMovingActualSmoothQVNormBudget.weight_le_one
    E D s t deltaWeight p N k omega

/-- For every fixed `p ≥ 1`, every active target-mesh endpoint (including
`k = 0`), every two-loop output coordinate, and every `r` in its closed
running cell, the literal actual-smooth `hQi` integrand is integrable on the
whole Gaussian space.  The rate is exactly the `Step2.sigPM` rate consumed by
the A-prime model; no restriction to the common good event is present. -/
theorem eventually_integrable_hQi
    {E D c : Real} {s t : Nat → Real} {deltaWeight : Real} {p : Nat}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (_hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        ∀ r ∈ Icc (s N)
          (APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t D N k),
          Integrable
            (fun omega =>
              weight E D s t deltaWeight p N k omega *
                |qv E D s t N k a r omega| ^ p)
            (P d) := by
  have henv := APrimeGeneralMovingQVNormBudget.eventually_abs_qv_le_envelope
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [henv, eventually_ge_atTop 1] with N henvN hN
  intro k hk a r hr
  have hv : APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t D N k ∈
      Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 :
      APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t D N k < 1 :=
    hv.2.trans_lt (ht1 N)
  have hqBound (omega : Ω d) :
      |qv E D s t N k a r omega| ≤
        APrimeGeneralMovingQVNormBudget.qvEnvelope D N := by
    exact henvN k hk r hr a omega
  have hq : Measurable (qv E D s t N k a r) := by
    let uu : Icc (s N)
        (APrimeGeneralMovingActualSmoothQVNormBudget.endpoint s t D N k) :=
      ⟨r, hr⟩
    have hembed : Measurable (fun omega : Ω d => (uu, omega)) :=
      measurable_const.prodMk measurable_id
    have hjoint := APrimeQVRateTime.measurable_qvAt_on_window
      d E D N Step2.sigPM a hE (hs0 N) hv.1 hv1
    have hcomp := hjoint.comp hembed
    simpa [qv, APrimeGeneralMovingActualSmoothQVNormBudget.qv,
      APrimeGeneralMovingQVNormBudget.qv,
      APrimeGeneralMovingActualSmoothQVNormBudget.endpoint,
      APrimeGeneralMovingQVNormBudget.endpoint, uu,
      Function.comp_def] using hcomp
  have hw : Measurable (weight E D s t deltaWeight p N k) :=
    APrimeGeneralMovingActualSmoothQVNormBudget.measurable_weight
      hE hst ht1 hN hk
  have hmeas : Measurable (fun omega =>
      weight E D s t deltaWeight p N k omega *
        |qv E D s t N k a r omega| ^ p) :=
    hw.mul ((continuous_abs.measurable.comp hq).pow_const p)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    ((APrimeGeneralMovingQVNormBudget.qvEnvelope D N) ^ p)
  exact Filter.Eventually.of_forall fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (weight_nonneg E D s t deltaWeight p N k omega)
      (pow_nonneg (abs_nonneg _) _))]
    calc
      weight E D s t deltaWeight p N k omega *
          |qv E D s t N k a r omega| ^ p ≤
        1 * |qv E D s t N k a r omega| ^ p :=
          mul_le_mul_of_nonneg_right
            (weight_le_one E D s t deltaWeight p N k omega)
            (pow_nonneg (abs_nonneg _) _)
      _ ≤ (APrimeGeneralMovingQVNormBudget.qvEnvelope D N) ^ p := by
        simpa only [one_mul] using
          pow_le_pow_left₀ (abs_nonneg _) (hqBound omega) p

/-- Re-export the accepted T995 witness: the actual smooth weight is strictly
positive at a nonempty active first cell on a genuine positive-length window,
with the schedule selected after the small-slot exponent. -/
abbrev T995_nonempty_actual_smooth_positive_cell :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms weight_nonneg
#print axioms weight_le_one
#print axioms eventually_integrable_hQi
#print axioms T995_nonempty_actual_smooth_positive_cell

end
end RBM.APrimeGeneralMovingWeightedQVIntegrable
