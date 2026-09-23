/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMomentSharp
import RBM1D.Gauss.APrimeFirstCellEndpointSharpArithmetic
import RBM1D.Gauss.APrimeFirstCellEndpointHighMoment
import RBM1D.Gauss.APrimeFirstCellFamilyHighMoment

/-!
# T532: the actual sharp first-cell endpoint moment

T527's coordinate rate is assembled by T512's exact finite-family maximum
at the sharper T530 root cost.  T522's coefficient-one endpoint Minkowski
then adds the deterministic baseline, which T530 absorbs into the strict
`delta / 4` target uniformly over the actual ratio interval.
-/

namespace RBM.APrimeFirstCellEndpointSharpMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellQuantMomentSharp.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellQuantMomentSharp.alpha

/-- The sharp finite-family rate before the endpoint baseline is added. -/
def familySharpMomentAt (τ' : ℝ) (P N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' P N k) P (familyMax N k) ≤
    (N : ℝ) ^ (9 * delta / 40) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T527's coordinate family, T512's exact maximum theorem, and T530's
`delta / 40` root cost give the `9 * delta / 40` family rate. -/
theorem familySharpMomentAt_of_coords {τ' : ℝ} (hτ' : 0 < τ')
    {P N k : ℕ} (hP : 80000 ≤ P) (hN : 81 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellQuantMomentSharp.quantMomentAt' τ' P N k a) :
    familySharpMomentAt τ' P N k := by
  have hP1 : 1 ≤ P := by omega
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < etaT 0 0 / etaT 0 (endpoint N k) :=
    Step2Moment.ratR_pos (s := fun _ => 0) (N := N)
      (by norm_num) (by norm_num) hv1
  have hc : 0 ≤ (N : ℝ) ^ (delta / 5) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hR.le _)
  have hw0 : ∀ ω, 0 ≤ weight τ' P N k ω := fun ω =>
    APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω
  have hint : ∀ a : LoopArg (d.L N) 2,
      Integrable (fun ω => weight τ' P N k ω *
        |Y N k a (endpoint N k) ω| ^ (2 * P)) (Gauss.P d) := by
    intro a
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
      (δ := delta) hτ' hP1 (by omega) hk a).2.hYi
  have hmax := APrimeFirstCellFamilyHighMoment.momNormW_finsetMax_le
    (Gauss.P d) (weight τ' P N k)
      (fun a => Y N k a (endpoint N k)) P hP1 hc hw0 hint hcoords
  change momNormW (Gauss.P d) (weight τ' P N k) P (familyMax N k) ≤ _ at hmax
  calc
    _ ≤ (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^
          ((1 : ℝ) / (2 * (P : ℝ))) *
        ((N : ℝ) ^ (delta / 5) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) := hmax
    _ ≤ (N : ℝ) ^ (delta / 40) *
        ((N : ℝ) ^ (delta / 5) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_right
        (APrimeFirstCellEndpointSharpArithmetic.family_card_root_le hN hP) hc
    _ = (N : ℝ) ^ (9 * delta / 40) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) := by
      rw [← mul_assoc,
        APrimeFirstCellEndpointSharpArithmetic.sharp_exponent_product_eq
          (show 1 ≤ N by omega)]

/-- The final actual endpoint target under the unchanged order-`P`
canonical weight. -/
def endpointSharpMomentAt (τ' : ℝ) (P N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' P N k) P
      (fun ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
        N (endpoint N k) ω) ≤
    (N : ℝ) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T522's exact pointwise identity and coefficient-one Minkowski reduce
the endpoint claim to T530's deterministic baseline absorption. -/
theorem endpointSharpMomentAt_of_family {τ' : ℝ} (hτ' : 0 < τ')
    {P N k : ℕ} (hP : 80000 ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hfamily : familySharpMomentAt τ' P N k)
    (harith :
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(4 : ℝ)) +
          (N : ℝ) ^ (9 * delta / 40) *
            (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) ≤
        (N : ℝ) ^ (delta / 4) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :
    endpointSharpMomentAt τ' P N k := by
  let w := weight τ' P N k
  let M := familyMax N k
  let R := etaT 0 0 / etaT 0 (endpoint N k)
  let b := 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4
  have hP1 : 1 ≤ P := by omega
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < R := by
    dsimp [R]
    exact Step2Moment.ratR_pos (s := fun _ => 0) (N := N)
      (by norm_num) (by norm_num) hv1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hw0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 P N k
      (canonicalM τ' N) ω
  have hM0 : ∀ ω, 0 ≤ M ω := by
    intro ω
    dsimp [M, familyMax]
    let a := Classical.choice
      (inferInstance : Nonempty (LoopArg (d.L N) 2))
    exact (abs_nonneg (Y N k a (endpoint N k) ω)).trans
      (Finset.le_sup' (fun a => |Y N k a (endpoint N k) ω|)
        (Finset.mem_univ a))
  have hint : ∀ a : LoopArg (d.L N) 2,
      Integrable (fun ω => w ω *
        |Y N k a (endpoint N k) ω| ^ (2 * P)) (Gauss.P d) := by
    intro a
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
      (δ := delta) hτ' hP1 hN hk a).2.hYi
  have hMi : Integrable (fun ω => w ω * |M ω| ^ (2 * P)) (Gauss.P d) := by
    exact APrimeFirstCellFamilyHighMoment.integrable_weighted_finsetMax_pow
      (Gauss.P d) w (fun a => Y N k a (endpoint N k)) (2 * P) hw0 hint
  have htriangle :=
    APrimeFirstCellEndpointHighMoment.momNormW_const_add_le
      hP1 hw0 hw1 hM0 hMi hb
  have hid : (fun ω => Step2Moment.jSnorm (sample d) 0 60
      (fun _ => 0) N (endpoint N k) ω) = fun ω => b + M ω := by
    funext ω
    exact APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
      hτ' N k hk ω
  have hbEq : b = R ^ (-(4 : ℝ)) := by
    change 1 / R ^ (4 : ℕ) = R ^ (-(4 : ℝ))
    rw [Real.rpow_neg hR.le]
    simp only [one_div]
    exact congrArg Inv.inv (Real.rpow_natCast R 4).symm
  change momNormW (Gauss.P d) w P M ≤
    (N : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) at hfamily
  change R ^ (-(4 : ℝ)) +
      (N : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) ≤
    (N : ℝ) ^ (delta / 4) * R ^ (-(2 : ℝ)) at harith
  unfold endpointSharpMomentAt
  rw [hid]
  calc
    _ ≤ b + momNormW (Gauss.P d) w P M := htriangle
    _ ≤ b + (N : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) :=
      add_le_add (le_refl b) hfamily
    _ = R ^ (-(4 : ℝ)) +
        (N : ℝ) ^ (9 * delta / 40) * R ^ (-(2 : ℝ)) := by rw [hbEq]
    _ ≤ (N : ℝ) ^ (delta / 4) * R ^ (-(2 : ℝ)) := harith

/-- The active-index theorem records the actual ratio interval together
with the endpoint moment, uniformly after the fixed order `P`. -/
def actualEndpointSharpMoment (τ' : ℝ) (P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    1 ≤ etaT 0 0 / etaT 0 (endpoint N k) ∧
    etaT 0 0 / etaT 0 (endpoint N k) ≤ 2 ∧
    endpointSharpMomentAt τ' P N k

/-- The order `P` is fixed before the eventual threshold, which is common
to every active endpoint and output coordinate. -/
theorem actualEndpointSharpMoment_of_coords {τ' : ℝ} (hτ' : 0 < τ')
    (P : ℕ) (hP : 80000 ≤ P)
    (hcoords : APrimeFirstCellQuantMomentSharp.actualQuantMoment' τ' P) :
    actualEndpointSharpMoment τ' P := by
  filter_upwards [hcoords, eventually_ge_atTop 81,
    APrimeFirstCellScaleFloors.eventually_scalePackage hτ',
    APrimeFirstCellEndpointSharpArithmetic.eventually_endpoint_le]
      with N hcoordsN hN hscaleN harithN
  intro k hk1 hk
  have hscale := hscaleN k hk
  have hfamily := familySharpMomentAt_of_coords hτ' hP hN hk
    (hcoordsN k hk1 hk)
  exact ⟨hscale.one_le_ratio, hscale.ratio_le_two,
    endpointSharpMomentAt_of_family hτ' hP (by omega) hk hfamily
      (harithN _ hscale.one_le_ratio hscale.ratio_le_two)⟩

/-- The empty-prefix endpoint is retained separately with its exact
ratio-one target. -/
def kZeroEndpointSharpMoment (τ' : ℝ) (P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧ endpointSharpMomentAt τ' P N 0 ∧
      momNormW (Gauss.P d) (weight τ' P N 0) P
        (fun ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
          N (endpoint N 0) ω) ≤ (N : ℝ) ^ (delta / 4)

/-- T527's independent zero-coordinate branch is assembled at the exact
ratio one and then passed through T522 and T530. -/
theorem eventually_kZeroEndpointSharpMoment {τ' : ℝ} (hτ' : 0 < τ')
    (P : ℕ) (hP : 80000 ≤ P)
    (hzero : APrimeFirstCellQuantMomentSharp.kZeroQuantMoment' τ' P) :
    kZeroEndpointSharpMoment τ' P := by
  filter_upwards [hzero, eventually_ge_atTop 81,
    APrimeFirstCellEndpointSharpArithmetic.eventually_endpoint_le]
      with N hzeroN hN harithN
  have hv : endpoint N 0 = 0 := by simp [endpoint, cutNetPt_zero]
  have hfamily := familySharpMomentAt_of_coords hτ' hP hN (Nat.zero_le _)
    (fun a => (hzeroN a).2.1)
  have hR : etaT 0 0 / etaT 0 (endpoint N 0) = 1 := by
    simp [hv, etaT, mE_zero]
  have hendpoint := endpointSharpMomentAt_of_family hτ' hP (by omega)
    (Nat.zero_le _) hfamily (by
      simpa only [hR] using harithN 1 (by norm_num) (by norm_num))
  refine ⟨hv, hendpoint, ?_⟩
  simpa [endpointSharpMomentAt, hR] using hendpoint

/-- T527's same positive `k = 2` resident, literal sharp event, and
canonical weight one, now carrying the final endpoint bound and ratio range. -/
def positiveTwoEndpointSharpMomentResident (τ' : ℝ) (P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    weight τ' P N 2 ω = 1 ∧
    1 ≤ etaT 0 0 / etaT 0 (endpoint N 2) ∧
    etaT 0 0 / etaT 0 (endpoint N 2) ≤ 2 ∧
    endpointSharpMomentAt τ' P N 2

/-- Attach the uniform endpoint estimate to T527's unchanged resident. -/
theorem positiveTwoEndpointSharpMomentResident_of_coords {τ' : ℝ} {P : ℕ}
    (hresident :
      APrimeFirstCellQuantMomentSharp.positiveTwoQuantMomentResident' τ' P)
    (hactual : actualEndpointSharpMoment τ' P) :
    positiveTwoEndpointSharpMomentResident τ' P := by
  filter_upwards [hresident, hactual] with N hr ha
  obtain ⟨ω, hω, hk, hvpos, hvle, hw, _hcoords⟩ := hr
  obtain ⟨hR1, hR2, hendpoint⟩ := ha 2 (by norm_num) hk
  exact ⟨ω, hω, hk, hvpos, hvle, hw, hR1, hR2, hendpoint⟩

/-- One T527 parameter and literal sharp common event provide the active
endpoint theorem, exact zero branch, and positive canonical-weight resident. -/
theorem exists_endpointSharpMoment_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ P : ℕ, 80000 ≤ P →
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          τ' delta alpha N).Nonempty) ∧
      actualEndpointSharpMoment τ' P ∧
      kZeroEndpointSharpMoment τ' P ∧
      positiveTwoEndpointSharpMomentResident τ' P := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQuantMomentSharp.exists_quantMoment_with_resident'
  refine ⟨τ', hτ', ?_⟩
  intro P hP
  obtain ⟨hm, hprob, hne, hcoords, hzero, hresident⟩ :=
    hall P (by omega)
  have hactual := actualEndpointSharpMoment_of_coords hτ' P hP hcoords
  exact ⟨hm, hprob, hne, hactual,
    eventually_kZeroEndpointSharpMoment hτ' P hP hzero,
    positiveTwoEndpointSharpMomentResident_of_coords hresident hactual⟩

#print axioms familySharpMomentAt_of_coords
#print axioms endpointSharpMomentAt_of_family
#print axioms actualEndpointSharpMoment_of_coords
#print axioms eventually_kZeroEndpointSharpMoment
#print axioms positiveTwoEndpointSharpMomentResident_of_coords
#print axioms exists_endpointSharpMoment_with_resident

end
end RBM.APrimeFirstCellEndpointSharpMoment
