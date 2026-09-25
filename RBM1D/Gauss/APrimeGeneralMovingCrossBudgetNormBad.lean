/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossPositive
import RBM1D.Gauss.APrimeGeneralMovingJointRateNormBadPayment
import RBM1D.Gauss.APrimeGeneralMovingGoodMesh

/-!
# T1185: the norm-bad p=1 component of the general-moving cross budget

This module isolates the exact part of T1089's p=1 cross-budget coefficient
whose `jointRate` is restricted to the complement of the norm-good event.  It
does not estimate the full cross budget or its time integral.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetNormBad

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The literal T1089 `jointRate`, restricted to the norm-bad event.  The
underlying rate retains its strict transition indicator, canonical smoothing
order, moving endpoint, and `Step2.sigPM` charge. -/
noncomputable def normBadJointRate (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : Gauss.Ω d → ℝ :=
  (APrimeGeneralMovingGoodMesh.good N)ᶜ.indicator
    (fun ω => APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω)

/-- T1089's exact coefficient at `p=1`, applied to the norm of the
bad-restricted literal `jointRate`. -/
noncomputable def normBadCrossBudget (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
    (4 * (1 : ℝ) * √r) *
      MomentDuhamel.momNorm (Gauss.P d) 2
        (normBadJointRate E D deltaWeight s t N k a r)

/-- The restricted rate's squared integrand is integrable at every active
cell/time, by T1035's fixed-order producer followed by measurable restriction. -/
theorem eventually_integrable_normBadJointRate_sq
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        Integrable (fun ω =>
          |normBadJointRate E D deltaWeight s t N k a r ω| ^ 2)
          (Gauss.P d) := by
  have hraw := APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
    hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
  filter_upwards [hraw, eventually_ge_atTop 1] with N hrawN hN
  intro k hk a r hr
  let Z : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω
  let Bbad : Set (Gauss.Ω d) := (APrimeGeneralMovingGoodMesh.good N)ᶜ
  let Zbad : Gauss.Ω d → ℝ := Bbad.indicator Z
  have hNpos : 0 < N := by omega
  have hRawInt : Integrable (fun ω => |Z ω| ^ 2) (Gauss.P d) := by
    simpa [Z, mesh, pow_two] using hrawN k hk Step2.sigPM a r hr
  have hBbad : MeasurableSet Bbad := by
    exact (APrimeGeneralMovingGoodMesh.measurableSet_good N).compl
  have hsq : ∀ ω, |Zbad ω| ^ 2 =
      Bbad.indicator (fun ω => |Z ω| ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ Bbad
    · simp [Zbad, Set.indicator_of_mem hω]
    · simp [Zbad, Set.indicator_of_notMem hω]
  have hBadSqInt : Integrable (fun ω => |Zbad ω| ^ 2) (Gauss.P d) := by
    refine (hRawInt.indicator hBbad).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    exact (hsq ω).symm
  exact hBadSqInt

/-- Uniform over the active moving-mesh cells and all positive running times
in their closed cells, T1173's actual norm-bad second-moment payment gives
the exact p=1 T1089 coefficient bound
`(15/8) N⁻¹ / √r`.  This is only the named bad-restricted contribution. -/
theorem eventually_normBad_p1_crossBudget_le
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        0 < r →
          normBadCrossBudget E D deltaWeight s t N k a r ≤
            (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by
  have hsecond :=
    APrimeGeneralMovingJointRateNormBadPayment.eventually_jointRate_sq_integral_normBad_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight
  have hraw := APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
    hE hD hs0 hst ht1 hc hreg hdeltaWeight 1 (by norm_num)
  filter_upwards [hsecond, hraw, eventually_ge_atTop 1] with N hsecondN hrawN hN
  intro k hk a r hr hr0
  let Z : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω
  let Bbad : Set (Gauss.Ω d) := (APrimeGeneralMovingGoodMesh.good N)ᶜ
  let Zbad : Gauss.Ω d → ℝ := Bbad.indicator Z
  have hNpos : 0 < N := by omega
  have hBadMeas : MeasurableSet Bbad := by
    exact (APrimeGeneralMovingGoodMesh.measurableSet_good N).compl
  have hRawInt : Integrable (fun ω => |Z ω| ^ 2) (Gauss.P d) := by
    simpa [Z, mesh, pow_two] using hrawN k hk Step2.sigPM a r hr
  have hBadSqInt : Integrable (fun ω => |Zbad ω| ^ 2) (Gauss.P d) := by
    have hsq : ∀ ω, |Zbad ω| ^ 2 =
        Bbad.indicator (fun ω => |Z ω| ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ Bbad
      · simp [Zbad, Set.indicator_of_mem hω]
      · simp [Zbad, Set.indicator_of_notMem hω]
    refine (hRawInt.indicator hBadMeas).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    exact (hsq ω).symm
  have hsecond :
      ∫ ω in Bbad, |Z ω| ^ 2 ∂(Gauss.P d) ≤
        (N : ℝ) ^ (-(2 : ℝ)) := by
    have hsecond' := hsecondN k hk Step2.sigPM a r hr
    change
      ∫ ω in ({ω : Gauss.Ω Dims.exampleGrow |
          ‖Gauss.Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)})ᶜ,
        |APrimeCrossJointSplit.jointRate Dims.exampleGrow E D deltaWeight s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM Dims.exampleGrow s t
            (APrimeGeneralMovingMesh.targetMesh D) N)
          Step2.sigPM a (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) r ω| ^ 2
          ∂(Gauss.P Dims.exampleGrow) ≤ (N : ℝ) ^ (-(2 : ℝ)) at hsecond'
    simpa [Bbad, Z, mesh, APrimeGeneralMovingGoodMesh.good] using hsecond'
  have hIntegral :
      (∫ ω, |Zbad ω| ^ 2 ∂(Gauss.P d)) =
        ∫ ω in Bbad, |Z ω| ^ 2 ∂(Gauss.P d) := by
    rw [← integral_indicator hBadMeas]
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ Bbad
    · exact (by simp [Zbad, Set.indicator_of_mem hω] :
        |Zbad ω| ^ 2 = Bbad.indicator (fun ω => |Z ω| ^ 2) ω)
    · exact (by simp [Zbad, Set.indicator_of_notMem hω] :
        |Zbad ω| ^ 2 = Bbad.indicator (fun ω => |Z ω| ^ 2) ω)
  have hMomEq : MomentDuhamel.momNorm (Gauss.P d) 2 Zbad =
      √(∫ ω in Bbad, |Z ω| ^ 2 ∂(Gauss.P d)) := by
    simp only [MomentDuhamel.momNorm, Nat.cast_ofNat]
    rw [hIntegral, ← Real.sqrt_eq_rpow]
  have hsqrtN : √((N : ℝ) ^ (-(2 : ℝ))) =
      (N : ℝ) ^ (-(1 : ℝ)) := by
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNposR.le]
    congr 1
    ring
  have hnorm : MomentDuhamel.momNorm (Gauss.P d) 2 Zbad ≤
      (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [hMomEq]
    calc
      √(∫ ω in Bbad, |Z ω| ^ 2 ∂(Gauss.P d)) ≤
          √((N : ℝ) ^ (-(2 : ℝ))) := Real.sqrt_le_sqrt hsecond
      _ = (N : ℝ) ^ (-(1 : ℝ)) := hsqrtN
  have hrS : √r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr0)
  have hcoeff :
      APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
        (4 * √r) = (15 / 8 : ℝ) / √r := by
    rw [APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff_one]
    field_simp [hrS]
    ring
  have hcoeff0 : 0 ≤
    APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
        (4 * √r) := by
    rw [hcoeff]
    positivity
  calc
    normBadCrossBudget E D deltaWeight s t N k a r =
          ((15 / 8 : ℝ) / √r) * MomentDuhamel.momNorm (Gauss.P d) 2 Zbad := by
          unfold normBadCrossBudget
          simp only [mul_one]
          change
            (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff 1 /
              (4 * √r)) * MomentDuhamel.momNorm (Gauss.P d) 2 Zbad = _
          rw [hcoeff]
    _ ≤ ((15 / 8 : ℝ) / √r) * (N : ℝ) ^ (-(1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by ring

/-! T1173's explicit model witnesses that the retained hypotheses coexist
with an active `k=2` cell, a strictly positive running endpoint, and a sample
in the exact strict transition set. -/

noncomputable abbrev nondegenerate_active_k2_witness :=
  APrimeGeneralMovingJointRateNormBadPayment.nondegenerate_first_cell_active_k2_witness

#print axioms eventually_integrable_normBadJointRate_sq
#print axioms eventually_normBad_p1_crossBudget_le
#print axioms nondegenerate_active_k2_witness

end
end RBM.APrimeGeneralMovingCrossBudgetNormBad
