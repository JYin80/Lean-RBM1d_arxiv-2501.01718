/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFamilyCardRoot

/-!
# T551: variable-delta finite-family assembly

T512's exact same-weight finite maximum inequality is combined with T548's
variable-delta family-cardinality root.  The actual coordinate estimate is
kept as an explicit open premise.
-/

namespace RBM.APrimeFirstCellDeltaFamilyAssembly

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)
open APrimeFirstCellDeltaTargetWeight (highOrder canonicalWeight)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The generic same-measure, same-weight hypotheses used by T512. -/
structure SameWeightCoordinateInput
    {Omega Iota : Type*} [MeasurableSpace Omega]
    [Fintype Iota] [Nonempty Iota]
    (mu : Measure Omega) (w : Omega -> Real)
    (f : Iota -> Omega -> Real) (P : Nat) (c : Real) : Prop where
  order_one : 1 <= P
  scale_nonneg : 0 <= c
  weight_nonneg : forall omega, 0 <= w omega
  integrable_coord : forall i,
    Integrable (fun omega => w omega * |f i omega| ^ (2 * P)) mu
  coordinate_bound : forall i, momNormW mu w P (f i) <= c

/-- T512 applied without changing the measure, weight, or moment order. -/
theorem momNormW_finsetMax_le_of_input
    {Omega Iota : Type*} [MeasurableSpace Omega]
    [Fintype Iota] [Nonempty Iota]
    {mu : Measure Omega} {w : Omega -> Real}
    {f : Iota -> Omega -> Real} {P : Nat} {c : Real}
    (h : SameWeightCoordinateInput mu w f P c) :
    momNormW mu w P
        (fun omega => Finset.univ.sup' Finset.univ_nonempty
          (fun i => |f i omega|)) <=
      (Fintype.card Iota : Real) ^ ((1 : Real) / (2 * (P : Real))) * c := by
  exact APrimeFirstCellFamilyHighMoment.momNormW_finsetMax_le
    mu w f P h.order_one h.scale_nonneg h.weight_nonneg
      h.integrable_coord h.coordinate_bound

/-- The open actual coordinate premise at the explicit order
`P = highOrder delta p`. -/
def coordinateMomentAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  let P := highOrder delta p
  forall a : LoopArg (d.L N) 2,
    momNormW (Gauss.P d) (canonicalWeight tauPrime delta P N k) P
        (Y N k a (endpoint N k)) <=
      (N : Real) ^ (delta / 5) *
        APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : Real))

/-- The canonical order-`highOrder delta p` family-maximum conclusion. -/
def familyMomentAt
    (tauPrime delta : Real) (p N k : Nat) : Prop :=
  let P := highOrder delta p
  momNormW (Gauss.P d) (canonicalWeight tauPrime delta P N k) P
      (familyMax N k) <=
    (N : Real) ^ (delta / 4) *
      APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : Real))

/-- Fixed-size assembly from the open actual coordinate premise.  T512 costs
the exact family root and T548 pays it by `N^(delta/20)`. -/
theorem familyMomentAt_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p N k : Nat} (hp : 1 <= p) (hN : 81 <= N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : coordinateMomentAt tauPrime delta p N k) :
    familyMomentAt tauPrime delta p N k := by
  let P0 := highOrder delta p
  let R := APrimeFirstCellLoopCap.xRate (endpoint N k)
  let c := (N : Real) ^ (delta / 5) * R ^ (-(2 : Real))
  have hP1 : 1 <= P0 := (APrimeFirstCellDeltaTargetWeight.highOrder_bounds
    delta hp).2.2
  have hNpos : (0 : Real) < N := by
    exact_mod_cast (show 0 < N by omega)
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 := by
    simpa only [endpoint] using hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < R := by
    dsimp only [R]
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos
      (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  have hc : 0 <= c := by
    exact mul_nonneg (Real.rpow_nonneg hNpos.le _)
      (Real.rpow_nonneg hR.le _)
  have hw0 : forall omega,
      0 <= canonicalWeight tauPrime delta P0 N k omega := by
    intro omega
    change 0 <= APrimeSmoothWeightActual.weight d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 P0 N k
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 P0 N k
      (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N) omega
  have hint : forall a : LoopArg (d.L N) 2,
      Integrable (fun omega =>
        canonicalWeight tauPrime delta P0 N k omega *
          |Y N k a (endpoint N k) omega| ^ (2 * P0)) (Gauss.P d) := by
    intro a
    have hi :=
      (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
        (δ := delta) hTau hP1 (by omega) hk a).2.hYi
    simpa only [canonicalWeight,
      APrimeFirstCellDeltaTargetWeight.canonicalWeight,
      APrimeFirstCellCanonicalPlateau.canonicalWeight,
      APrimeFirstCellSampleRegularity.weight,
      APrimeFirstCellMinkowskiExact.Y,
      APrimeFirstCellMinkowskiExact.endpoint,
      APrimeFirstCellSampleRegularity.Y,
      APrimeFirstCellSampleRegularity.endpoint,
      APrimeFirstCellGeneratorHle.endpoint] using hi
  have hinput : SameWeightCoordinateInput (Gauss.P d)
      (canonicalWeight tauPrime delta P0 N k)
      (fun a => Y N k a (endpoint N k)) P0 c := {
    order_one := hP1
    scale_nonneg := hc
    weight_nonneg := hw0
    integrable_coord := hint
    coordinate_bound := by
      intro a
      exact hcoords a
  }
  have hmax := momNormW_finsetMax_le_of_input hinput
  change momNormW (Gauss.P d) (canonicalWeight tauPrime delta P0 N k) P0
      (familyMax N k) <= _ at hmax
  dsimp only [familyMomentAt]
  change momNormW (Gauss.P d) (canonicalWeight tauPrime delta P0 N k) P0
      (familyMax N k) <=
    (N : Real) ^ (delta / 4) * R ^ (-(2 : Real))
  calc
    _ <= (Fintype.card (LoopArg (d.L N) 2) : Real) ^
          ((1 : Real) / (2 * (P0 : Real))) *
        ((N : Real) ^ (delta / 5) * R ^ (-(2 : Real))) := hmax
    _ <= (N : Real) ^ (delta / 20) *
        ((N : Real) ^ (delta / 5) * R ^ (-(2 : Real))) :=
      mul_le_mul_of_nonneg_right
        (APrimeFirstCellDeltaFamilyCardRoot.family_card_root_le
          hDelta hp hN) hc
    _ = (N : Real) ^ (delta / 4) * R ^ (-(2 : Real)) := by
      rw [← mul_assoc,
        APrimeFirstCellDeltaFamilyCardRoot.exponent_product_eq
          (show 1 <= N by omega)]

/-- The open coordinate premise, uniformly over every positive active index. -/
def actualCoordinateMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    coordinateMomentAt tauPrime delta p N k

/-- The corresponding family conclusion, uniformly over active indices. -/
def actualFamilyMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, forall k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    familyMomentAt tauPrime delta p N k

/-- Eventual assembly.  The actual coordinate premise remains an argument;
this theorem does not supply it. -/
theorem actualFamilyMoments_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p : Nat} (hp : 1 <= p)
    (hcoords : actualCoordinateMoments tauPrime delta p) :
    actualFamilyMoments tauPrime delta p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  intro k hk1 hk
  exact familyMomentAt_of_coords hTau hDelta hp hN hk
    (hcoordsN k hk1 hk)

/-- Open coordinate premise for the exact empty prefix. -/
def kZeroCoordinateMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, coordinateMomentAt tauPrime delta p N 0

/-- Exact empty-prefix endpoint together with its family consequence. -/
def kZeroFamilyMoments
    (tauPrime delta : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop,
    endpoint N 0 = 0 ∧ familyMomentAt tauPrime delta p N 0

/-- Fixed-size exact `k = 0` implication. -/
theorem familyMomentAt_k_zero_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p N : Nat} (hp : 1 <= p) (hN : 81 <= N)
    (hcoords : coordinateMomentAt tauPrime delta p N 0) :
    endpoint N 0 = 0 ∧ familyMomentAt tauPrime delta p N 0 := by
  refine ⟨?_, familyMomentAt_of_coords hTau hDelta hp hN
    (Nat.zero_le _) hcoords⟩
  simp [endpoint, cutNetPt_zero]

/-- Eventual exact `k = 0` implication from the explicitly open premise. -/
theorem kZeroFamilyMoments_of_coords
    {tauPrime delta : Real} (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    {p : Nat} (hp : 1 <= p)
    (hcoords : kZeroCoordinateMoments tauPrime delta p) :
    kZeroFamilyMoments tauPrime delta p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  exact familyMomentAt_k_zero_of_coords hTau hDelta hp hN hcoordsN

/-- A two-member zero family under a nonzero probability measure and the
strictly positive weight one satisfies the generic conditional interface. -/
theorem zero_family_input_witness :
    exists mu : Measure Unit, exists w : Unit -> Real,
      exists f : Bool -> Unit -> Real, exists P0 : Nat, exists c : Real,
        mu Set.univ = 1 ∧
        Fintype.card Bool = 2 ∧
        (forall omega, w omega = 1) ∧
        SameWeightCoordinateInput mu w f P0 c := by
  refine ⟨Measure.dirac (), fun _ => 1, fun _ _ => 0, 1, 0,
    by simp, by decide, by simp, ?_⟩
  refine {
    order_one := by norm_num
    scale_nonneg := le_rfl
    weight_nonneg := by intro omega; norm_num
    integrable_coord := by intro i; simp
    coordinate_bound := by intro i; simp [momNormW]
  }

end

end RBM.APrimeFirstCellDeltaFamilyAssembly

namespace RBM.APrimeFirstCellDeltaFamilyAssembly

#print axioms momNormW_finsetMax_le_of_input
#print axioms familyMomentAt_of_coords
#print axioms actualFamilyMoments_of_coords
#print axioms familyMomentAt_k_zero_of_coords
#print axioms kZeroFamilyMoments_of_coords
#print axioms zero_family_input_witness

end RBM.APrimeFirstCellDeltaFamilyAssembly
