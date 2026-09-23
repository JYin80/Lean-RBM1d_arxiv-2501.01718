/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMomentSharp
import RBM1D.Gauss.APrimeFirstCellEndpointSharpArithmetic
import RBM1D.Gauss.APrimeFirstCellEndpointWidenedMoment

/-!
# T534: the widened sharp first-cell endpoint moment

For fixed `1 ≤ p ≤ P` and `P ≥ 80000`, T527's sharp coordinates are first
assembled at order `P` under the unchanged canonical weight.  T530 pays the
single finite-family root cost at exponent `delta / 40`.  Same-weight
Lyapunov and pointwise weight monotonicity then transfer the resulting
`9 delta / 40` family rate to the literal order-`p` target weight.  T522's
coefficient-one endpoint Minkowski inequality and T530's strict margin
absorb the deterministic endpoint baseline.
-/

namespace RBM.APrimeFirstCellEndpointWidenedSharpMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact
open APrimeFirstCellFamilyHighMoment (familyMax)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellQuantMomentSharp.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellQuantMomentSharp.alpha

/-- The sharp family maximum at the fixed high order and under its literal
canonical weight. -/
def familyHighSharpAt (τ' : ℝ) (P N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' P N k) P (familyMax N k) ≤
    (N : ℝ) ^ (9 * delta / 40) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T512's coefficient-one finite maximum pays T530's family root exactly
once on top of T527's `delta / 5` coordinate rate. -/
theorem familyHighSharpAt_of_coords {τ' : ℝ} (hτ' : 0 < τ') {P N k : ℕ}
    (hP : 80000 ≤ P) (hN : 81 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellQuantMomentSharp.quantMomentAt' τ' P N k a) :
    familyHighSharpAt τ' P N k := by
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

/-- The lower moment keeps the order-`P` canonical weight and the same
sharp family rate. -/
def familyLowSharpAt (τ' : ℝ) (p P N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' P N k) p (familyMax N k) ≤
    (N : ℝ) ^ (9 * delta / 40) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T521's Lyapunov theorem lowers the order without changing the weight,
measure, coefficient, or rate. -/
theorem familyLowSharpAt_of_high {τ' : ℝ} (hτ' : 0 < τ')
    {p P N k : ℕ} (hp : 1 ≤ p) (hpP : p ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hhigh : familyHighSharpAt τ' P N k) : familyLowSharpAt τ' p P N k :=
  (APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_momNormW_le
    hτ' hp hpP hN hk).trans hhigh

/-- The sharp family rate under the literal order-`p` widened target weight. -/
def familyWidenedSharpAt (τ' : ℝ) (p N k : ℕ) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k)
      p (familyMax N k) ≤
    (N : ℝ) ^ (9 * delta / 40) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T520's pointwise comparison and T524's coefficient-one weight
monotonicity transfer the same-weight estimate to the target weight. -/
theorem familyWidenedSharpAt_of_sameWeight {τ' : ℝ}
    (hτ' : 0 < τ') {p P N k : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P) (hN : 0 < N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hlow : familyLowSharpAt τ' p P N k) : familyWidenedSharpAt τ' p N k := by
  have hint :=
    (APrimeFirstCellFamilyLowMomentSameWeight.sameWeight_integrability
      hτ' (hp.trans hpP) hN hk (p := p)).1
  have hmono : momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k)
      p (familyMax N k) ≤
      momNormW (Gauss.P d) (weight τ' P N k) p (familyMax N k) := by
    apply APrimeFirstCellFamilyWidenedMoment.momNormW_mono_weight hp
    · intro ω
      exact APrimeWeight.widenedW_nonneg
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u ω => Step2Moment.jSnorm
          (sample d) 0 60 (fun _ => 0) N u ω)
        (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh (1 / 2000) p N k ω
    · intro ω
      exact APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hτ' N p P k ω hp hpP
    · exact hint
  exact hmono.trans hlow

/-- The final sharp endpoint target under the widened order-`p` weight. -/
def endpointWidenedSharpMomentAt (τ' : ℝ) (p N k : ℕ) : Prop :=
  momNormW (Gauss.P d)
      (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k) p
      (fun ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
        N (endpoint N k) ω) ≤
    (N : ℝ) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

private theorem one_div_pow_four_eq_rpow_neg_four {R : ℝ} (hR : 0 < R) :
    1 / R ^ 4 = R ^ (-(4 : ℝ)) := by
  rw [Real.rpow_neg hR.le, one_div, ← Real.rpow_natCast R 4]
  norm_num

/-- T522's exact endpoint identity and coefficient-one Minkowski inequality
reduce the endpoint target to T530's deterministic absorption. -/
theorem endpointWidenedSharpMomentAt_of_family {τ' : ℝ}
    (hτ' : 0 < τ') {p N k : ℕ} (hp : 1 ≤ p)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hfamily : familyWidenedSharpAt τ' p N k)
    (habsorb :
      1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 +
          (N : ℝ) ^ (9 * delta / 40) *
            (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) ≤
        (N : ℝ) ^ (delta / 4) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :
    endpointWidenedSharpMomentAt τ' p N k := by
  let w := APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k
  let M := familyMax N k
  let b := 1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) :=
    Step2Moment.ratR_pos (by norm_num) (by norm_num) hv1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hw0 : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact APrimeWeight.widenedW_nonneg
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u ω => Step2Moment.jSnorm
        (sample d) 0 60 (fun _ => 0) N u ω)
      (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
      (1 / 2000) p N k ω
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    exact APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh) 1
      (fun N u ω => Step2Moment.jSnorm
        (sample d) 0 60 (fun _ => 0) N u ω)
      (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
      (1 / 2000) p N k ω
  have hM0 : ∀ ω, 0 ≤ M ω := by
    intro ω
    dsimp [M, familyMax]
    let a := Classical.choice
      (inferInstance : Nonempty (LoopArg (d.L N) 2))
    exact (abs_nonneg (Y N k a (endpoint N k) ω)).trans
      (Finset.le_sup' (fun a => |Y N k a (endpoint N k) ω|)
        (Finset.mem_univ a))
  have hMi : Integrable (fun ω => w ω * |M ω| ^ (2 * p))
      (Gauss.P d) := by
    exact APrimeFirstCellEndpointWidenedMoment.integrable_targetWeight_familyMax_pow
      hτ' hk
  have htriangle :=
    APrimeFirstCellEndpointHighMoment.momNormW_const_add_le
      hp hw0 hw1 hM0 hMi hb
  have hid : (fun ω => Step2Moment.jSnorm (sample d) 0 60
      (fun _ => 0) N (endpoint N k) ω) = fun ω => b + M ω := by
    funext ω
    exact APrimeFirstCellEndpointHighMoment.jSnorm_endpoint_eq_familyMax
      hτ' N k hk ω
  have hsum : b + momNormW (Gauss.P d) w p M ≤
      b + (N : ℝ) ^ (9 * delta / 40) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) := by
    simpa only [add_comm] using add_le_add_left hfamily b
  unfold endpointWidenedSharpMomentAt
  rw [hid]
  exact htriangle.trans (hsum.trans habsorb)

/-- Positive active indices, uniformly after both moment orders have been
fixed before the eventual size threshold. -/
def actualEndpointWidenedSharpMoment (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    endpointWidenedSharpMomentAt τ' p N k

theorem actualEndpointWidenedSharpMoment_of_coords {τ' : ℝ}
    (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P) (hP : 80000 ≤ P)
    (hcoords : APrimeFirstCellQuantMomentSharp.actualQuantMoment' τ' P) :
    actualEndpointWidenedSharpMoment τ' p P := by
  filter_upwards [hcoords,
    APrimeFirstCellEndpointSharpArithmetic.eventually_endpoint_le,
    APrimeFirstCellScaleFloors.eventually_scalePackage hτ',
    eventually_ge_atTop 81] with N hcoordsN harithN hscaleN hN
  intro k hk1 hk
  have hscale := hscaleN k hk
  have hhigh := familyHighSharpAt_of_coords hτ' hP hN hk
    (hcoordsN k hk1 hk)
  have hlow := familyLowSharpAt_of_high hτ' hp hpP
    (show 0 < N by omega) hk hhigh
  have hfamily := familyWidenedSharpAt_of_sameWeight hτ' hp hpP
    (show 0 < N by omega) hk hlow
  let R := etaT 0 0 / etaT 0 (endpoint N k)
  have hR : 0 < R := zero_lt_one.trans_le hscale.one_le_ratio
  have hbase :
      1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N k) ^ 4 =
        R ^ (-(4 : ℝ)) := by
    simpa [R, Step2Moment.ratR] using one_div_pow_four_eq_rpow_neg_four hR
  have habsorb := harithN R hscale.one_le_ratio hscale.ratio_le_two
  apply endpointWidenedSharpMomentAt_of_family hτ' hp hk hfamily
  rw [hbase]
  exact habsorb

/-- The zero index is retained as a separate exact-ratio branch. -/
def kZeroEndpointWidenedSharpMoment (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧ endpointWidenedSharpMomentAt τ' p N 0 ∧
      momNormW (Gauss.P d)
        (APrimeFirstCellCrossOrderWeight.targetWeight τ' p N 0) p
        (fun ω => Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0)
          N (endpoint N 0) ω) ≤ (N : ℝ) ^ (delta / 4)

theorem eventually_kZeroEndpointWidenedSharpMoment {τ' : ℝ}
    (hτ' : 0 < τ') {p P : ℕ}
    (hp : 1 ≤ p) (hpP : p ≤ P) (hP : 80000 ≤ P)
    (hzero : APrimeFirstCellQuantMomentSharp.kZeroQuantMoment' τ' P) :
    kZeroEndpointWidenedSharpMoment τ' p P := by
  filter_upwards [hzero,
    APrimeFirstCellEndpointSharpArithmetic.eventually_endpoint_le,
    APrimeFirstCellScaleFloors.eventually_scalePackage hτ',
    eventually_ge_atTop 81] with N hzeroN harithN hscaleN hN
  have hk : 0 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N := Nat.zero_le _
  have hscale := hscaleN 0 hk
  have hhigh := familyHighSharpAt_of_coords hτ' hP hN hk
    (fun a => (hzeroN a).2.1)
  have hlow := familyLowSharpAt_of_high hτ' hp hpP
    (show 0 < N by omega) hk hhigh
  have hfamily := familyWidenedSharpAt_of_sameWeight hτ' hp hpP
    (show 0 < N by omega) hk hlow
  let R := etaT 0 0 / etaT 0 (endpoint N 0)
  have hR : 0 < R := zero_lt_one.trans_le hscale.one_le_ratio
  have hbase :
      1 / Step2Moment.ratR 0 (fun _ => 0) N (endpoint N 0) ^ 4 =
        R ^ (-(4 : ℝ)) := by
    simpa [R, Step2Moment.ratR] using one_div_pow_four_eq_rpow_neg_four hR
  have habsorb := harithN R hscale.one_le_ratio hscale.ratio_le_two
  have hendpoint := endpointWidenedSharpMomentAt_of_family hτ' hp hk hfamily (by
    rw [hbase]
    exact habsorb)
  have hv : endpoint N 0 = 0 := (hzeroN (Classical.choice inferInstance)).1
  refine ⟨hv, hendpoint, ?_⟩
  simpa [endpointWidenedSharpMomentAt, hv, etaT, mE_zero] using hendpoint

/-- The same T527 positive resident carries the final endpoint moment and
both the target and canonical weights equal to one. -/
def positiveTwoEndpointWidenedSharpMomentResident
    (τ' : ℝ) (p P : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    APrimeFirstCellCrossOrderWeight.targetWeight τ' p N 2 ω = 1 ∧
    weight τ' P N 2 ω = 1 ∧
    endpointWidenedSharpMomentAt τ' p N 2

theorem positiveTwoEndpointWidenedSharpMomentResident_of_coords
    {τ' : ℝ} {p P : ℕ}
    (hresident :
      APrimeFirstCellQuantMomentSharp.positiveTwoQuantMomentResident' τ' P)
    (hendpoint : actualEndpointWidenedSharpMoment τ' p P) :
    positiveTwoEndpointWidenedSharpMomentResident τ' p P := by
  filter_upwards [hresident, hendpoint,
    APrimeFirstCellCrossOrderWeight.eventually_targetWeight_two_one_on_sharpCommonEvent τ']
      with N hr he htarget
  obtain ⟨ω, hω, hk, hvpos, hvle, hweight, _hcoords⟩ := hr
  exact ⟨ω, hω, hk, hvpos, hvle, htarget ω hω p, hweight,
    he 2 (by norm_num) hk⟩

/-- One T527 parameter and literal sharp common event provide every fixed
pair `1 ≤ p ≤ P`, `P ≥ 80000`, including the exact zero branch and a
positive resident on which both weights equal one. -/
theorem exists_endpointWidenedSharpMoment_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ p P : ℕ,
      1 ≤ p → p ≤ P → 80000 ≤ P →
      (∀ N k ω, APrimeFirstCellCrossOrderWeight.targetWeight τ' p N k ω ≤
        weight τ' P N k ω) ∧
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
          τ' delta alpha N).Nonempty) ∧
      actualEndpointWidenedSharpMoment τ' p P ∧
      kZeroEndpointWidenedSharpMoment τ' p P ∧
      positiveTwoEndpointWidenedSharpMomentResident τ' p P := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellQuantMomentSharp.exists_quantMoment_with_resident'
  refine ⟨τ', hτ', ?_⟩
  intro p P hp hpP hP
  obtain ⟨hmeas, hprob, hne, hcoords, hzero, hresident⟩ :=
    hall P (hp.trans hpP)
  have hendpoint := actualEndpointWidenedSharpMoment_of_coords
    hτ' hp hpP hP hcoords
  exact ⟨fun N k ω =>
      APrimeFirstCellCrossOrderWeight.widenedW_le_minkowskiWeight
        hτ' N p P k ω hp hpP,
    hmeas, hprob, hne, hendpoint,
    eventually_kZeroEndpointWidenedSharpMoment
      hτ' hp hpP hP hzero,
    positiveTwoEndpointWidenedSharpMomentResident_of_coords
      hresident hendpoint⟩

#print axioms familyHighSharpAt_of_coords
#print axioms familyLowSharpAt_of_high
#print axioms familyWidenedSharpAt_of_sameWeight
#print axioms endpointWidenedSharpMomentAt_of_family
#print axioms actualEndpointWidenedSharpMoment_of_coords
#print axioms eventually_kZeroEndpointWidenedSharpMoment
#print axioms positiveTwoEndpointWidenedSharpMomentResident_of_coords
#print axioms exists_endpointWidenedSharpMoment_with_resident

end

end RBM.APrimeFirstCellEndpointWidenedSharpMoment
