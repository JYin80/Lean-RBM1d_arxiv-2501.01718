/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeFirstCellMinkowskiExact

/-!
# T500: the actual first-cell canonical-weight initial moment budget

T488 is first applied with the single constant weight one, uniformly in all
moving endpoints and outputs.  Pointwise domination by one then gives T494's
actual canonical-weight initial term at every active mesh index, including
zero, without changing the eventual size threshold with the index.
-/

namespace RBM.APrimeFirstCellInitialMomentBudget

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable abbrev delta : ℝ := APrimeFirstCellMinkowskiExact.delta

theorem delta_eq_one_over_two_thousand : delta = 1 / 2000 := rfl

theorem delta_pos : 0 < delta := by
  norm_num [delta_eq_one_over_two_thousand]

/-- The original initial-data package at the literal first-cell left endpoint. -/
theorem firstCell_boundsCore : BoundsCore (sample d) 0 (fun _ => 0) :=
  BoundsCore_zero (sample d) (by norm_num)

/-- Every positive first-cell parameter satisfies the original regime with
the explicit polynomial exponent `c = 1/2`. -/
theorem firstCell_cond272Reg {τ' : ℝ} (hτ' : 0 < τ') :
    Cond272Reg B 0 (fun _ => 0) (firstCellT τ') (1 / 2) := by
  have hscale : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((1 : ℝ) / 2) ≤ B.scale 0 N (firstCellT τ' N) := by
    filter_upwards [Dims.bandwidth_grow,
      eventually_le_rpow 2 (by norm_num : (0 : ℝ) < 1 / 8),
      eventually_ge_atTop 1] with N hW hN8 hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hW' : (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤ (d.W N : ℝ) := by
      simpa [d, Dims.exampleGrow_W] using hW
    have htwoN : 2 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (d.W N : ℝ) := by
      calc
        2 * (N : ℝ) ^ ((1 : ℝ) / 2) =
            (N : ℝ) ^ ((1 : ℝ) / 2) * 2 := by ring
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left hN8 (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
          (Real.rpow_add hNpos _ _).symm
        _ ≤ (d.W N : ℝ) := hW'
    have hhalf : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (d.W N : ℝ) / 2 := by
      nlinarith
    have htime : firstCellT τ' N ∈ Icc (firstCellS τ' N) (firstCellT τ' N) := by
      constructor
      · rw [firstCellS_eq_zero]
        exact (APrimeSupportRunning.firstT_bounds hτ' N).1
      · exact le_rfl
    exact hhalf.trans (firstCell_scale_ge_half N htime)
  refine ⟨?_, hscale⟩
  have hN30 : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ (30 : ℕ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    eventually_le_rpow ((2 : ℝ) ^ (30 : ℕ)) (by norm_num)
  filter_upwards [hscale, hN30] with N hA h30
  have hAmin := h30.trans hA
  have hinv : (B.scale 0 N (firstCellT τ' N))⁻¹ ≤
      ((2 : ℝ) ^ (30 : ℕ))⁻¹ := inv_anti₀ (by positivity) hAmin
  have htime : (1 / 2 : ℝ) ≤ 1 - firstCellT τ' N := by
    linarith [(APrimeSupportRunning.firstT_bounds hτ' N).2]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) htime 30
  change (B.scale 0 N (firstCellT τ' N))⁻¹ ≤
    ((1 - firstCellT τ' N) / (1 - 0)) ^ 30
  norm_num only [sub_zero, div_one]
  exact hinv.trans (by norm_num at hpow ⊢; exact hpow)

/-- Domination of a nonnegative weight by one gives moment-norm domination.
The unweighted absolute moment supplies the necessary integrability. -/
theorem momNormW_le_one_weight {Ω' : Type*} [MeasurableSpace Ω']
    (P' : Measure Ω') (w Y : Ω' → ℝ) (p : ℕ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∀ ω, w ω ≤ 1)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * p)) P') :
    momNormW P' w p Y ≤ momNormW P' (fun _ => 1) p Y := by
  have hi : (∫ ω, w ω * |Y ω| ^ (2 * p) ∂P') ≤
      ∫ ω, |Y ω| ^ (2 * p) ∂P' := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun ω => mul_nonneg (hw0 ω) (by positivity)) hint
    exact Eventually.of_forall fun ω =>
      mul_le_of_le_one_left (by positivity) (hw1 ω)
  unfold momNormW
  simp only [one_mul]
  exact Real.rpow_le_rpow
    (integral_nonneg fun ω => mul_nonneg (hw0 ω) (by positivity)) hi (by positivity)

/-- The exact normalized T488 initial-slot right-hand side at T494's endpoint. -/
noncomputable def initialBudget (N k : ℕ) : ℝ :=
  APrimeOneStep.initTerm ((N : ℝ) ^ (delta / 8))
    (etaT 0 0 / etaT 0 (APrimeFirstCellMinkowskiExact.endpoint N k))
    (APrimeInit.slotXi' ((N : ℝ) ^ (delta / 8))) /
    (etaT 0 0 / etaT 0 (APrimeFirstCellMinkowskiExact.endpoint N k)) ^ 4

/-- The actual canonical-weight initial moment, with no endpoint or weight
selection made before the eventual size threshold. -/
def initialBoundAt (τ' : ℝ) (p N k : ℕ) (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (APrimeFirstCellMinkowskiExact.weight τ' p N k) p
    (APrimeFirstCellMinkowskiExact.initial N k a) ≤ initialBudget N k

/-- One eventual threshold works for every active first-cell mesh point,
including `k = 0`, and every actual output coordinate. -/
theorem eventually_initialBoundAt {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ a : LoopArg (d.L N) 2, initialBoundAt τ' p N k a := by
  have ht0 : ∀ N, (0 : ℝ) ≤ firstCellT τ' N :=
    fun N => (APrimeSupportRunning.firstT_bounds hτ' N).1
  have ht1 : ∀ N, firstCellT τ' N < 1 :=
    fun N => (APrimeSupportRunning.firstT_bounds hτ' N).2.trans_lt (by norm_num)
  have hone := APrimeGeneralMovingInitialHinit.eventually_initial_hinit
    (E := 0) (D := 60) (c := 1 / 2) (δ := delta)
    (s := fun _ => 0) (t := firstCellT τ')
    (by norm_num) (by norm_num) (fun _ => le_rfl) ht0 ht1
    (by norm_num) (firstCell_cond272Reg hτ') firstCell_boundsCore delta_pos p hp
    (fun _ _ _ => 1) (fun _ _ => aestronglyMeasurable_const)
    (fun _ _ _ => zero_le_one) (fun _ _ _ => le_rfl)
  filter_upwards [hone] with N hN k hk a
  have hv := MomentDuhamelCut.netFinset_subset_Icc (ht0 N)
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  let v : TimeIcc (fun _ => 0) (firstCellT τ') N :=
    ⟨APrimeFirstCellMinkowskiExact.endpoint N k, hv⟩
  have hint := APrimeAssembly.integrable_initialEvolvedNormAt_pow_gauss d
    (E := 0) (by norm_num) (fun _ => le_rfl) ht0 ht1 p N v 60 a
  have hmono := momNormW_le_one_weight (P d)
    (APrimeFirstCellMinkowskiExact.weight τ' p N k)
    (APrimeFirstCellMinkowskiExact.initial N k a) p
    (fun ω => APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N k
      (APrimeFirstCellMinkowskiExact.canonicalM τ' N) ω)
    (fun ω => APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N k
      (APrimeFirstCellMinkowskiExact.canonicalM τ' N) ω)
    hint
  exact hmono.trans (hN (v, a))

/-- Exact simplification of the initial slot, with the moving eta ratio retained. -/
theorem initialBudget_eq {τ' : ℝ} (hτ' : 0 < τ') {N k : ℕ}
    (hN : 1 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N) :
    initialBudget N k = (N : ℝ) ^ (5 * delta / 32) *
      (etaT 0 0 / etaT 0 (APrimeFirstCellMinkowskiExact.endpoint N k)) ^ (-(2 : ℝ)) := by
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : APrimeFirstCellMinkowskiExact.endpoint N k < 1 :=
    hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  exact APrimeAssembly.initial_slot_scale_eq hN
    (Step2Moment.ratR_pos (s := fun _ => 0) (N := N)
      (by norm_num : |(0 : ℝ)| < 2) (by norm_num) hv1)

/-- The simplified budget is still uniform in every active index and output. -/
theorem eventually_initial_simplified {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ a : LoopArg (d.L N) 2,
        momNormW (P d) (APrimeFirstCellMinkowskiExact.weight τ' p N k) p
          (APrimeFirstCellMinkowskiExact.initial N k a) ≤
          (N : ℝ) ^ (5 * delta / 32) *
            (etaT 0 0 / etaT 0 (APrimeFirstCellMinkowskiExact.endpoint N k)) ^ (-(2 : ℝ)) := by
  filter_upwards [eventually_initialBoundAt hτ' p hp, eventually_ge_atTop 1]
    with N hbound hN k hk a
  have hb := hbound k hk a
  change _ ≤ initialBudget N k at hb
  rwa [initialBudget_eq hτ' hN hk] at hb

/-- The zeroth index is included in the same initial budget. -/
theorem eventually_initial_k_zero {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 ∧
      initialBoundAt τ' p N 0 a ∧
      momNormW (P d) (APrimeFirstCellMinkowskiExact.weight τ' p N 0) p
        (APrimeFirstCellMinkowskiExact.initial N 0 a) ≤ (N : ℝ) ^ (5 * delta / 32) := by
  filter_upwards [eventually_initialBoundAt hτ' p hp,
    eventually_initial_simplified hτ' p hp] with N hbound hsimpl a
  have hs := hsimpl 0 (Nat.zero_le _) a
  refine ⟨by simp [APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero],
    hbound 0 (Nat.zero_le _) a, ?_⟩
  simpa [APrimeFirstCellMinkowskiExact.endpoint, cutNetPt_zero, etaT, mE_zero] using hs

/-- A positive `k = 2` resident retains the literal sharp common event,
canonical weight one, and both actual moment estimates on the same sample. -/
def positiveTwoInitialResident (τ' α : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N,
    APrimeFirstCellMinkowskiExact.endpoint N 0 = 0 ∧
    0 < APrimeFirstCellMinkowskiExact.endpoint N 1 ∧
    APrimeFirstCellMinkowskiExact.endpoint N 1 <
      APrimeFirstCellMinkowskiExact.endpoint N 2 ∧
    APrimeFirstCellMinkowskiExact.endpoint N 2 ≤ firstCellT τ' N ∧
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    APrimeFirstCellMinkowskiExact.weight τ' p N 2 ω = 1 ∧
    ∀ a : LoopArg (d.L N) 2,
      initialBoundAt τ' p N 2 a ∧
      APrimeFirstCellMinkowskiExact.minkowskiBoundAt τ' α p N 2 a

theorem positiveTwoInitialResident_of_minkowski {τ' α : ℝ}
    (hτ' : 0 < τ') (hα : 0 < α) (p : ℕ) (hp : 1 ≤ p)
    (hresident : APrimeFirstCellMinkowskiExact.positiveTwoMinkowskiResident τ' α p) :
    positiveTwoInitialResident τ' α p := by
  filter_upwards [hresident, eventually_initialBoundAt hτ' p hp,
    APrimeFirstCellCanonicalPlateau.eventually_canonicalWeight_one_on_sharpCommonEvent
      hτ' delta_pos hα] with N hr hb hw
  obtain ⟨ω, hω, hu0, hu1, hu12, hv, hk, hmink⟩ := hr
  refine ⟨ω, hω, hu0, hu1, hu12, hv, hk, hw ω hω p, ?_⟩
  exact fun a => ⟨hb 2 hk a, hmink a⟩

/-- T494's one first-cell parameter and literal sharp common event also carry
the exact canonical-weight initial budget.  Nonemptiness and a weight-one
positive resident rule out a vacuous cutoff witness. -/
theorem exists_initialMomentBudget_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧
      Cond272Reg B 0 (fun _ => 0) (firstCellT τ') (1 / 2) ∧
      BoundsCore (sample d) 0 (fun _ => 0) ∧
      ∀ α : ℝ, 0 < α → ∀ p : ℕ, 1 ≤ p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N)) ∧
        HighProb (P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α) ∧
        (∀ᶠ N : ℕ in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N).Nonempty) ∧
        (∀ᶠ N : ℕ in atTop, ∀ k,
          k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
            APrimeSmoothTransition.transitionMesh N →
          ∀ a : LoopArg (d.L N) 2, initialBoundAt τ' p N k a) ∧
        APrimeFirstCellMinkowskiExact.actualMinkowskiBound τ' α p ∧
        APrimeFirstCellMinkowskiExact.kZeroMinkowskiBound τ' α p ∧
        positiveTwoInitialResident τ' α p := by
  obtain ⟨τ', hτ', hall⟩ := APrimeFirstCellMinkowskiExact.exists_minkowski_with_resident
  refine ⟨τ', hτ', firstCell_cond272Reg hτ', firstCell_boundsCore, ?_⟩
  intro α hα p hp
  obtain ⟨hm, hprob, hmink, hzero, hresident⟩ := hall α hα p hp
  have hne := HighProb.nonempty (by simp) hprob
  exact ⟨hm, hprob, hne, eventually_initialBoundAt hτ' p hp, hmink, hzero,
    positiveTwoInitialResident_of_minkowski hτ' hα p hp hresident⟩

#print axioms firstCell_boundsCore
#print axioms firstCell_cond272Reg
#print axioms momNormW_le_one_weight
#print axioms eventually_initialBoundAt
#print axioms initialBudget_eq
#print axioms eventually_initial_simplified
#print axioms eventually_initial_k_zero
#print axioms positiveTwoInitialResident_of_minkowski
#print axioms exists_initialMomentBudget_with_resident

end

end RBM.APrimeFirstCellInitialMomentBudget
