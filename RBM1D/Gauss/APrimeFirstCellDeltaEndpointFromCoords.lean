/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaTargetFamilyAssembly
import RBM1D.Gauss.APrimeFirstCellDeltaEndpointMinkowski

/-!
# T565: variable-delta endpoint norm from open coordinate moments

T557 converts the explicit canonical high-order coordinate premise into the
target-weight family bound.  T552 then adds the exact deterministic endpoint
baseline.  A final numerical lemma uses `R_v >= 1` and `N >= 1` to obtain the
coefficient-two endpoint norm bound.

The coordinate premise remains explicit throughout.
-/

namespace RBM.APrimeFirstCellDeltaEndpointFromCoords

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The actual endpoint bootstrap observable. -/
noncomputable abbrev endpointJ (N k : Nat) : Ω d -> Real :=
  fun omega => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
    N (endpoint N k) omega

/-- The target endpoint conclusion needed by the later cutoff adapter. -/
def endpointMomentAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k) p (endpointJ N k) ≤
    2 * (N : Real) ^ (delta / 4)

/-- Pure absorption of the coefficient-one endpoint expression. -/
theorem endpoint_expression_le_two_mul
    {delta R : Real} {N : Nat} (hDelta : 0 < delta)
    (hN : 1 ≤ N) (hR : 1 ≤ R) :
    1 / R ^ 4 + (N : Real) ^ (delta / 4) * R ^ (-(2 : Real)) ≤
      2 * (N : Real) ^ (delta / 4) := by
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpow0 : 0 ≤ (N : Real) ^ (delta / 4) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hNpow1 : 1 ≤ (N : Real) ^ (delta / 4) :=
    Real.one_le_rpow hNreal (by positivity)
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
  have hR4pos : 0 < R ^ 4 := (by norm_num : (0 : Real) < 1).trans_le hR4
  have hinv4 : 1 / R ^ 4 ≤ 1 := (div_le_one hR4pos).2 hR4
  have hRneg2 : R ^ (-(2 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have hscaled :
      (N : Real) ^ (delta / 4) * R ^ (-(2 : Real)) ≤
        (N : Real) ^ (delta / 4) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRneg2 hNpow0
  linarith

/-- Fixed-size composition from the open canonical high-order coordinate
premise.  T557 and T552 retain the same Gaussian measure, target weight, and
order `p`; the final step is deterministic arithmetic. -/
theorem endpointMomentAt_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p N k : Nat} (hp : 1 ≤ p)
    (hN : 81 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt
      tauPrime delta p N k) :
    endpointMomentAt tauPrime delta p N k := by
  let R : Real := APrimeFirstCellLoopCap.xRate (endpoint N k)
  let C : Real := (N : Real) ^ (delta / 4) * R ^ (-(2 : Real))
  have hfamily :=
    APrimeFirstCellDeltaTargetFamilyAssembly.targetFamilyMomentAt_of_coords
      hTau hDelta hp hN hk hcoords
  have hfamily' :
      APrimeFirstCellDeltaEndpointMinkowski.targetFamilyBoundAt
        tauPrime delta p N k C := by
    simpa only [C, R,
      APrimeFirstCellDeltaTargetFamilyAssembly.targetFamilyMomentAt,
      APrimeFirstCellDeltaEndpointMinkowski.targetFamilyBoundAt,
      APrimeFirstCellDeltaEndpointMinkowski.targetWeight] using hfamily
  have hend :=
    APrimeFirstCellDeltaEndpointMinkowski.endpointBoundAt_of_familyBound
      hTau hp hk hfamily'
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 1 ≤ R := by
    dsimp only [R, APrimeFirstCellLoopCap.xRate]
    exact APrimeFirstCellEndpointCoord.one_le_endpoint_ratR N hv.1 hv1
  have harith := endpoint_expression_le_two_mul hDelta
    (show 1 ≤ N by omega) hR
  dsimp only [endpointMomentAt]
  dsimp only [APrimeFirstCellDeltaEndpointMinkowski.endpointBoundAt] at hend
  exact hend.trans (by
    dsimp only [APrimeFirstCellDeltaEndpointMinkowski.endpointBaseline,
      C, R] at harith ⊢
    exact harith)

/-- Open coordinate premise, uniformly over every positive active prefix. -/
def actualCoordinatePremise
    (tauPrime delta : Real) (p : Nat) : Prop :=
  APrimeFirstCellDeltaFamilyAssembly.actualCoordinateMoments
    tauPrime delta p

/-- Endpoint conclusion, uniformly over every positive active prefix. -/
def actualEndpointMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N →
    endpointMomentAt tauPrime delta p N k

/-- Eventual uniform composition from the open coordinate premise. -/
theorem actualEndpointMoments_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 ≤ p)
    (hcoords : actualCoordinatePremise tauPrime delta p) :
    actualEndpointMoments tauPrime delta p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  intro k hk1 hk
  exact endpointMomentAt_of_coords hTau hDelta hp hN hk
    (hcoordsN k hk1 hk)

/-- Open canonical coordinate premise at the empty prefix. -/
def kZeroCoordinatePremise
    (tauPrime delta : Real) (p : Nat) : Prop :=
  APrimeFirstCellDeltaTargetFamilyAssembly.kZeroCoordinateMoments
    tauPrime delta p

/-- Exact empty-prefix identities together with the endpoint conclusion. -/
def kZeroEndpointMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧
    Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 0) = 1 ∧
    APrimeFirstCellDeltaEndpointMinkowski.endpointBaseline N 0 = 1 ∧
    (∀ omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 0 omega = 1) ∧
    (∀ omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 0 omega = 1) ∧
    endpointMomentAt tauPrime delta p N 0

/-- Eventual exact empty-prefix composition from the open coordinate
premise.  All boundary identities are proved independently of that premise. -/
theorem kZeroEndpointMoments_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime)
    (hDelta : 0 < delta) {p : Nat} (hp : 1 ≤ p)
    (hcoords : kZeroCoordinatePremise tauPrime delta p) :
    kZeroEndpointMoments tauPrime delta p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  have hz := APrimeFirstCellDeltaEndpointMinkowski.kZero_exact
    tauPrime delta p N
  refine ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, ?_, ?_⟩
  · exact APrimeFirstCellDeltaTargetWeight.canonicalWeight_k_zero
      tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N
  · exact endpointMomentAt_of_coords hTau hDelta hp hN
      (Nat.zero_le _) hcoordsN

#print axioms endpointJ
#print axioms endpointMomentAt
#print axioms endpoint_expression_le_two_mul
#print axioms endpointMomentAt_of_coords
#print axioms actualCoordinatePremise
#print axioms actualEndpointMoments
#print axioms actualEndpointMoments_of_coords
#print axioms kZeroCoordinatePremise
#print axioms kZeroEndpointMoments
#print axioms kZeroEndpointMoments_of_coords

end

end RBM.APrimeFirstCellDeltaEndpointFromCoords
