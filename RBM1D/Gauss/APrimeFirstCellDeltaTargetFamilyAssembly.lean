/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFamilyWeightTransfer
import RBM1D.Gauss.APrimeFirstCellDeltaFamilyAssembly

/-!
# T557: variable-delta target-family assembly

The open canonical order-`P` coordinate premise from T551 is assembled into
the canonical family maximum and then transferred through T550's two
coefficient-one comparisons to the target-weight order-`p` norm.
-/

namespace RBM.APrimeFirstCellDeltaTargetFamilyAssembly

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The target-weight order-`p` family conclusion at one mesh endpoint. -/
def targetFamilyMomentAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N k) p (familyMax N k) <=
    (N : Real) ^ (delta / 4) *
      APrimeFirstCellLoopCap.xRate
        (APrimeFirstCellMinkowskiExact.endpoint N k) ^ (-(2 : Real))

/-- Fixed-size composition.  T551 first forms the canonical order-`P`
family maximum; T550 then supplies the coefficient-one target/canonical
chain under the identical measure and canonical weight. -/
theorem targetFamilyMomentAt_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p N k : Nat} (hp : 1 <= p) (hN : 81 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt
      tauPrime delta p N k) :
    targetFamilyMomentAt tauPrime delta p N k := by
  have hcanonical :=
    APrimeFirstCellDeltaFamilyAssembly.familyMomentAt_of_coords
      hTau hDelta hp hN hk hcoords
  have htransfer :=
    APrimeFirstCellDeltaFamilyWeightTransfer.familyWeightTransferAt_of_bounds
      hTau hDelta hp (by omega) hk
  dsimp only [APrimeFirstCellDeltaFamilyAssembly.familyMomentAt] at hcanonical
  dsimp only [
    APrimeFirstCellDeltaFamilyWeightTransfer.familyWeightTransferAt]
    at htransfer
  dsimp only [targetFamilyMomentAt]
  exact htransfer.1.trans (htransfer.2.trans hcanonical)

/-- Target-family conclusion, uniformly over all positive active indices. -/
def actualTargetFamilyMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    targetFamilyMomentAt tauPrime delta p N k

/-- Eventual composition from the visibly open actual coordinate premise. -/
theorem actualTargetFamilyMoments_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p : Nat} (hp : 1 <= p)
    (hcoords : APrimeFirstCellDeltaFamilyAssembly.actualCoordinateMoments
      tauPrime delta p) :
    actualTargetFamilyMoments tauPrime delta p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  intro k hk1 hk
  exact targetFamilyMomentAt_of_coords hTau hDelta hp hN hk
    (hcoordsN k hk1 hk)

/-- Open coordinate premise for the exact empty prefix. -/
def kZeroCoordinateMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  APrimeFirstCellDeltaFamilyAssembly.kZeroCoordinateMoments
    tauPrime delta p

/-- Exact empty-prefix identities and the target-family conclusion. -/
def kZeroTargetFamilyMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 ∧
    (forall omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 0 omega = 1) ∧
    (forall omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 0 omega = 1) ∧
    targetFamilyMomentAt tauPrime delta p N 0

/-- Fixed-size exact `k=0` composition from the open coordinate premise. -/
theorem targetFamilyMomentAt_k_zero_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p N : Nat} (hp : 1 <= p) (hN : 81 <= N)
    (hcoords : APrimeFirstCellDeltaFamilyAssembly.coordinateMomentAt
      tauPrime delta p N 0) :
    APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 ∧
    (forall omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.targetWeight
        tauPrime delta p N 0 omega = 1) ∧
    (forall omega : Ω d,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N 0 omega = 1) ∧
    targetFamilyMomentAt tauPrime delta p N 0 := by
  have hcanonical :=
    APrimeFirstCellDeltaFamilyAssembly.familyMomentAt_k_zero_of_coords
      hTau hDelta hp hN hcoords
  have hNpos : 0 < N := by omega
  have htransfer :=
    APrimeFirstCellDeltaFamilyWeightTransfer.familyWeightTransferAt_of_bounds
      hTau hDelta hp hNpos (Nat.zero_le _)
  refine ⟨hcanonical.1, ?_, ?_, ?_⟩
  · exact APrimeFirstCellDeltaTargetWeight.targetWeight_k_zero
      tauPrime delta p N
  · exact APrimeFirstCellDeltaTargetWeight.canonicalWeight_k_zero
      tauPrime delta
        (APrimeFirstCellDeltaTargetWeight.highOrder delta p) N
  · dsimp only [APrimeFirstCellDeltaFamilyAssembly.familyMomentAt]
      at hcanonical
    dsimp only [
      APrimeFirstCellDeltaFamilyWeightTransfer.familyWeightTransferAt]
      at htransfer
    dsimp only [targetFamilyMomentAt]
    exact htransfer.1.trans (htransfer.2.trans hcanonical.2)

/-- Eventual exact `k=0` composition from the open coordinate premise. -/
theorem kZeroTargetFamilyMoments_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p : Nat} (hp : 1 <= p)
    (hcoords : kZeroCoordinateMoments tauPrime delta p) :
    kZeroTargetFamilyMoments tauPrime delta p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  exact targetFamilyMomentAt_k_zero_of_coords
    hTau hDelta hp hN hcoordsN

/-- A nonzero probability measure, two-member zero family, and two strictly
positive identical weights satisfy the generic finite-family input and the
target/canonical family comparison simultaneously. -/
theorem zero_family_target_compatibility_witness :
    exists mu : Measure Unit, exists wTarget wCanonical : Unit -> Real,
      exists f : Bool -> Unit -> Real, exists P0 p0 : Nat, exists c : Real,
        mu Set.univ = 1 ∧
        Fintype.card Bool = 2 ∧
        (forall omega, wTarget omega = 1) ∧
        (forall omega, wCanonical omega = 1) ∧
        APrimeFirstCellDeltaFamilyAssembly.SameWeightCoordinateInput
          mu wCanonical f P0 c ∧
        momNormW mu wTarget p0
            (fun omega => Finset.univ.sup' Finset.univ_nonempty
              (fun i => |f i omega|)) <=
          momNormW mu wCanonical P0
            (fun omega => Finset.univ.sup' Finset.univ_nonempty
              (fun i => |f i omega|)) := by
  refine ⟨Measure.dirac (), fun _ => 1, fun _ => 1,
    fun _ _ => 0, 1, 1, 0, by simp, by decide, by simp, by simp, ?_, ?_⟩
  · refine {
      order_one := by norm_num
      scale_nonneg := le_rfl
      weight_nonneg := by intro omega; norm_num
      integrable_coord := by intro i; simp
      coordinate_bound := by intro i; simp [momNormW]
    }
  · simp [momNormW]

end

end RBM.APrimeFirstCellDeltaTargetFamilyAssembly

namespace RBM.APrimeFirstCellDeltaTargetFamilyAssembly

#print axioms targetFamilyMomentAt_of_coords
#print axioms actualTargetFamilyMoments_of_coords
#print axioms targetFamilyMomentAt_k_zero_of_coords
#print axioms kZeroTargetFamilyMoments_of_coords
#print axioms zero_family_target_compatibility_witness

end RBM.APrimeFirstCellDeltaTargetFamilyAssembly
