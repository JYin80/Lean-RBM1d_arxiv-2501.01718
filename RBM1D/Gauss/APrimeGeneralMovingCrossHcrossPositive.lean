/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossProductIntegrable
import RBM1D.Gauss.APrimeGeneralMovingCanonicalSharpFactor
import RBM1D.Gauss.APrimeGeneralMovingTargetTransitionExists

/-!
# T1089: positive-time cross input for the actual moving smooth weight

This file proves only the literal positive-time `hcross` premise consumed by
`APrimeDuhamelModel.momFlowDeriv_le`, for the actual smooth prefix weight,
target mesh, endpoint, cell, sample, and `Step2.sigPM` charge.
-/

namespace RBM.APrimeGeneralMovingCrossHcrossPositive

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The coefficient in the actual cutoff-gradient estimate. -/
noncomputable def crossMomentCoeff (p : ℕ) : ℝ :=
  ((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)

theorem crossMomentCoeff_one : crossMomentCoeff 1 = 15 / 2 := by
  norm_num [crossMomentCoeff]

/-- The literal flow observable at the moving target endpoint and fixed
`Step2.sigPM` charge. -/
noncomputable def actualFlowY (E D : ℝ) (s : ℕ → ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : Gauss.Ω d → ℝ :=
  APrimeDuhamelModel.flowY d N
    (fun u M => APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u M) r

/-- The actual smooth-weighted moment appearing in the literal `hcross`
slot of `momFlowDeriv_le`, with its T615 starting-size cutoff `N₀ = 2`. -/
noncomputable def actualWeightedMoment (E D deltaWeight : ℝ)
    (s t : ℕ → ℝ) (N k p : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  ∫ ω,
    APrimeSmoothWeightActual.weight d E D deltaWeight s t
      (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) ω *
    |actualFlowY E D s N k a r ω| ^ (2 * p) ∂(Gauss.P d)

/-- Explicit nonnegative `Bc = C_p/(4p√r) · ‖jointRate‖_(2p)` for `r>0`. -/
noncomputable def positiveTimeCrossBudget (E D deltaWeight : ℝ)
    (s t : ℕ → ℝ) (N k p : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  crossMomentCoeff p / (4 * (p : ℝ) * √r) *
    MomentDuhamel.momNorm (Gauss.P d) (2 * p)
      (APrimeCrossJointSplit.jointRate d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N)
        Step2.sigPM a
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r)

theorem positiveTimeCrossBudget_nonneg
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N k p : ℕ)
    (a : LoopArg (d.L N) 2) {r : ℝ} (hp : 1 ≤ p) (hr : 0 < r) :
    0 ≤ positiveTimeCrossBudget E D deltaWeight s t N k p a r := by
  unfold positiveTimeCrossBudget crossMomentCoeff
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hp)
  have hrR : 0 < √r := Real.sqrt_pos.2 hr
  exact mul_nonneg
    (div_nonneg (by positivity) (by positivity))
    (MomentDuhamel.momNorm_nonneg _ _ _)

/-- At the empty prefix the strict transition and cross derivative vanish.
This identity is independent of the positive-time estimate. -/
theorem zeroPrefix_crossPart_eq_zero
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N p : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) :
    APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0))
      (APrimeSmoothWeightActual.weightD d E D deltaWeight s t
        (APrimeGeneralMovingMesh.targetMesh D) 2 p N 0
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N)) r = 0 := by
  exact APrimeCrossJointSplit.crossPart_zero_k0 d E D deltaWeight s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 N
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N) p
    (APrimeSmoothWeightActual.canonicalM_pos d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N)
      (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0)) r

theorem zeroPrefix_jointRate_eq_zero
    (E D deltaWeight : ℝ) (s t : ℕ → ℝ) (N : ℕ)
    (a : LoopArg (d.L N) 2) (v r : ℝ) (hN : 0 < N) :
    APrimeCrossJointSplit.jointRate d E D deltaWeight s
      (APrimeGeneralMovingMesh.targetMesh D) N 0
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N)
      Step2.sigPM a v r = 0 := by
  exact APrimeGeneralMovingJointMeasurable.jointRate_k_zero hN Step2.sigPM a v r

/-- The literal positive-time `hcross` producer for the actual T615 weight.
For each fixed `p ≥ 1`, it holds eventually, uniformly over every active
moving-mesh prefix (including `k=0`), output, and time in the closed cell with
`r>0`. The `Bc` supplied here is explicit and nonnegative. -/
theorem eventually_positive_time_hcross
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Set.Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      0 < r →
        0 ≤ positiveTimeCrossBudget E D deltaWeight s t N k p a r ∧
        APrimeDuhamelModel.crossPart d N
          (APrimeDriftTimeFamily.momentAt d E D N p Step2.sigPM a (s N)
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k))
          (APrimeSmoothWeightActual.weightD d E D deltaWeight s t
            (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N)) r ≤
          2 * (p : ℝ) *
            (actualWeightedMoment E D deltaWeight s t N k p a r) ^
              ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
            positiveTimeCrossBudget E D deltaWeight s t N k p a r := by
  have hYevent :=
    APrimeGeneralMovingCrossYRegularity.eventually_actualY_hYm_hYi
      d (D := D) (deltaWeight := deltaWeight) hE hs0 hst ht1 p hp
  have hZevent :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hProductEvent :=
    APrimeGeneralMovingCrossProductIntegrable.eventually_actual_cross_product_integrable
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hYevent, hZevent, hProductEvent, eventually_ge_atTop 2]
    with N hYN hZN hPN hN2
  have hNpos : 0 < N := by omega
  intro k hk a r hr hr0
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let v := cutNetPt s mesh N k
  let m := APrimeSmoothWeightActual.canonicalM d s t mesh N
  let Y : Gauss.Ω d → ℝ :=
    APrimeGeneralMovingCrossYRegularity.actualY d E D deltaWeight s t N k
      Step2.sigPM a r
  let Z : Gauss.Ω d → ℝ :=
    APrimeCrossJointSplit.jointRate d E D deltaWeight s mesh N k m
      Step2.sigPM a v r
  have hN02 : 2 ≤ N := hN2
  have hm : 1 ≤ m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hv1 : v < 1 :=
    APrimeGeneralMovingJointMeasurable.target_endpoint_lt_one hst ht1 hk
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hactive : k ≤ cutNetTop s t mesh N := by simpa [mesh] using hk
  have hu : ∀ j < k, cutNetPt s mesh N j < 1 := by
    intro j hj
    exact APrimeGeneralMovingJointMeasurable.stored_time_lt_one hst ht1 hk hj
  have hYfields := hYN k hk Step2.sigPM a r hr
  have hYm : AEStronglyMeasurable Y (Gauss.P d) := by
    simpa only [Y] using hYfields.1
  have hYi : Integrable
      (fun ω => |Y ω| ^ (2 * p)) (Gauss.P d) := by
    simpa only [Y] using hYfields.2
  have hZmeas :=
    APrimeGeneralMovingJointMeasurable.measurable_prefixGradient_and_jointRate
      (deltaWeight := deltaWeight) hE hs0 hst ht1 hNpos hk Step2.sigPM a hr
  have hZm : AEStronglyMeasurable Z (Gauss.P d) := by
    exact hZmeas.2.aestronglyMeasurable
  have hZi : Integrable (fun ω => |Z ω| ^ (2 * p)) (Gauss.P d) := by
    simpa [Z, m, v, mesh] using hZN k hk Step2.sigPM a r hr
  have hProdInt : Integrable
      (fun ω => |Y ω| ^ (2 * p - 1) * |Z ω|)
      (Gauss.P d) := by
    simpa [Y, Z, m, v, mesh] using
      hPN k hk Step2.sigPM a r hr
  have hPhi :
      (∫ ω,
        |APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω *
          ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v r
            (Gauss.Hflow d N r ω)‖| ^ (2 * p) ∂(Gauss.P d)) =
      actualWeightedMoment E D deltaWeight s t N k p a r := by
    rw [actualWeightedMoment]
    apply integral_congr_ae
    filter_upwards with ω
    have hcω : 0 ≤ APrimeSmoothWeightActual.cutoff d E D deltaWeight
        s mesh N k m ω := Cutoff.cutChi_nonneg _
    have hXω : 0 ≤ ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
        (s N) v r (Gauss.Hflow d N r ω)‖ := norm_nonneg _
    have hweight : APrimeSmoothWeightActual.weight d E D deltaWeight s t mesh
        2 p N k m ω =
      (APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω) ^
          (2 * p) := by
      simp [APrimeSmoothWeightActual.weight, hactive, hN02]
    change
      |APrimeSmoothWeightActual.cutoff d E D deltaWeight s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p) =
      APrimeSmoothWeightActual.weight d E D deltaWeight s t mesh
        2 p N k m ω *
        |APrimeDuhamelModel.flowY d N
          (fun u M => APrimeDriftTimeFamily.coordAt d E D N Step2.sigPM a
            (s N) v u M) r ω| ^ (2 * p)
    rw [abs_mul, abs_of_nonneg hcω, abs_of_nonneg hXω,
      APrimeDuhamelModel.flowY, abs_of_nonneg hXω, hweight]
    ring
  have hcross := APrimeCrossJointSplit.crossPart_active_le_jointNorm
      d E D deltaWeight s t mesh 2 N k m p Step2.sigPM a v r
      hE hs1 (hs0 N) hv1 hr hr0 hNpos hm hu hactive hN02 hp
      hYm hZm hYi hZi hProdInt
  rw [hPhi] at hcross
  have hRateNorm :
      (∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d)) ^
          ((1 : ℝ) / (2 * (p : ℝ))) =
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z := by
    simp [MomentDuhamel.momNorm, Nat.cast_mul, Nat.cast_ofNat]
  rw [hRateNorm] at hcross
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hp))
  have hrR : (√r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr0)
  have hrewrite :
      (1 / (2 * √r)) * crossMomentCoeff p *
        (actualWeightedMoment E D deltaWeight s t N k p a r) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z =
      2 * (p : ℝ) *
        (actualWeightedMoment E D deltaWeight s t N k p a r) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
        positiveTimeCrossBudget E D deltaWeight s t N k p a r := by
    unfold positiveTimeCrossBudget
    field_simp [hpR, hrR]
    <;> ring
  refine ⟨positiveTimeCrossBudget_nonneg E D deltaWeight s t N k p a hp hr0,
    ?_⟩
  exact hcross.trans_eq hrewrite

/-- Accepted T995 witness: the loss-schedule hypotheses used by the positive
time result have a genuine positive cell and a same-sample common-event
member with positive actual smooth weight. -/
noncomputable abbrev t995_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

/-- Accepted T1049 witness for the canonical smoothing order. Its cardinal
factor statement includes every active index, including `k=0`. -/
noncomputable abbrev t1049_factor_and_resident {ε : ℝ} (hε : 0 < ε) :=
  APrimeGeneralMovingCanonicalSharpFactor.exists_t995_half_window_factor_and_resident hε

/-- Accepted T1051 scalar-ray witness: at `τ=c=1`, `δ=1/200`, the strict
transition has a positive-time sample at the active `k=2` cell. It is a
separate witness from T995's common-event sample. -/
noncomputable abbrev t1051_positive_transition_witness :=
  APrimeGeneralMovingTargetTransitionExists.eventually_exampleGrow_target_transition
    (τ := 1) (c := 1) (δ := 1 / 200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms crossMomentCoeff_one
#print axioms positiveTimeCrossBudget_nonneg
#print axioms zeroPrefix_crossPart_eq_zero
#print axioms zeroPrefix_jointRate_eq_zero
#print axioms eventually_positive_time_hcross
#print axioms t995_positive_cell_witness
#print axioms t1049_factor_and_resident
#print axioms t1051_positive_transition_witness

end
end RBM.APrimeGeneralMovingCrossHcrossPositive
