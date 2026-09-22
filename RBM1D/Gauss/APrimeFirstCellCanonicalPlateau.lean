/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellSampleRegularity

/-!
# T467: same-event canonical-weight positive first-cell plateau
-/

namespace RBM.APrimeFirstCellCanonicalPlateau

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (N k : ℕ) : ℝ :=
  APrimeFirstCellGeneratorHle.endpoint N k

noncomputable def canonicalWeight (τ' δ : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  APrimeFirstCellGeneratorHle.canonicalWeight τ' δ p N k

private noncomputable def actualH (N : ℕ) : ℝ :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 1

private theorem actualH_eq (N : ℕ) (hN : 1 ≤ N) :
    actualH N = ((N : ℝ) ^ (248 : ℕ))⁻¹ := by
  simp [actualH, cutNetPt, APrimeSmoothTransition.transitionMesh,
    max_eq_right (show (1 : ℝ) ≤ N by exact_mod_cast hN)]

private theorem actualH_mem (N : ℕ) (hN : 2 ≤ N) :
    actualH N ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  rw [actualH_eq N (by omega)]
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : (2 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
    calc
      (2 : ℝ) ≤ (N : ℝ) := hNr
      _ ≤ (N : ℝ) ^ (248 : ℕ) := by
        calc
          (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := by simp
          _ ≤ (N : ℝ) ^ (248 : ℕ) :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
  constructor
  · positivity
  · simpa [one_div] using
      (inv_le_inv₀ (show (0 : ℝ) < (N : ℝ) ^ 248 by linarith)
        (show (0 : ℝ) < 2 by norm_num)).2 hp

private theorem modulus_scale_actual (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (122 : ℝ) * |actualH N - 0| ^ ((1 : ℝ) / 2) =
      ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : (actualH N) ^ ((1 : ℝ) / 2) =
      ((N : ℝ) ^ (124 : ℕ))⁻¹ := by
    rw [← Real.sqrt_eq_rpow, actualH_eq N hN]
    have he : (N : ℝ) ^ (248 : ℕ) =
        ((N : ℝ) ^ (124 : ℕ)) ^ (2 : ℕ) := by
      rw [← pow_mul]
    rw [he, Real.sqrt_inv, Real.sqrt_sq (by positivity)]
  have hh0 : 0 ≤ actualH N := by rw [actualH_eq N hN]; positivity
  simp only [sub_zero, abs_of_nonneg hh0, hsqrt]
  rw [Real.rpow_ofNat (N : ℝ) 122]
  have he : (N : ℝ) ^ (124 : ℕ) =
      (N : ℝ) ^ (122 : ℕ) * (N : ℝ) ^ (2 : ℕ) := by
    rw [← pow_add]
  rw [he]
  field_simp

/-- The canonical smoothing order gives weight one at `k = 2` on every
sample satisfying the literal norm cap.  The proof controls its own
`prefixSample`; it does not transfer the result from smoothing order `m=N`. -/
theorem eventually_canonicalWeight_two_one_of_norm {τ' δ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d,
      ‖Xmat d N ω‖ ≤ (N : ℝ) → ∀ p : ℕ,
        canonicalWeight τ' δ p N 2 ω = 1 := by
  have hmod := APrimeSlotFields.eventually_modulus_jSnorm_event d
    (E := 0) (D := 60) (t₀ := 1 / 2)
    (s := fun _ => 0) (t := fun _ => 1 / 2)
    (Good := fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => subset_rfl)
  filter_upwards [hmod, eventually_ge_atTop 2] with N hmodN hN ω hω p
  by_cases hactive : 2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧ 2 ≤ N
  · have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT τ') APrimeSmoothTransition.transitionMesh N :=
      APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
        (firstCellT τ') APrimeSmoothTransition.transitionMesh N
    have hmesh : 0 < APrimeSmoothTransition.transitionMesh N :=
      APrimeSupportRunning.mesh_pos N
    have ht : firstCellT τ' N < 1 :=
      (APrimeSupportRunning.firstT_bounds hτ' N).2.trans_lt (by norm_num)
    have hst : (0 : ℝ) ≤ firstCellT τ' N :=
      (APrimeSupportRunning.firstT_bounds hτ' N).1
    have hJ : ∀ j < 2, Step2Moment.jSnorm (sample d) 0 60
        (fun _ => 0) N
        (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N j) ω ≤
          1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
      intro j hj
      interval_cases j
      · have h0 := APrimeFirstCellCommon.J_zero N ω
        change Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N 0 ω = 1 at h0
        have hinv : 0 ≤ ((N : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
        have hzero : Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N
            (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0) ω = 1 := by
          simpa only [cutNetPt, Nat.cast_zero, zero_div, add_zero] using h0
        rw [hzero]
        linarith
      · have hmN := hmodN ω hω (actualH N) (actualH_mem N hN) 0
            (by constructor <;> norm_num)
        have h0 := APrimeFirstCellCommon.J_zero N ω
        change Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N 0 ω = 1 at h0
        have hmN' :
            |Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N (actualH N) ω - 1| ≤
              ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
          simpa only [show (2 : ℝ) + 2 * 60 = 122 by norm_num, h0,
            modulus_scale_actual N (by omega)] using hmN
        have hle : Step2Moment.jSnorm (sample d) 0 60 (fun _ => 0) N
            (actualH N) ω ≤ 1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ :=
          le_trans (le_add_of_sub_left_le ((le_abs_self _).trans hmN')) le_rfl
        simpa only [actualH] using hle
    have hB0 : (0 : ℝ) ≤ 1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
    have hS := APrimeSmoothWeightActual.prefixSample_le_of_jSnorm_bound d
      (E := 0) (D := 60) (B := 1 + ((N : ℝ) ^ (2 : ℕ))⁻¹)
      (s := fun _ => 0) (t := firstCellT τ')
      (mesh := APrimeSmoothTransition.transitionMesh)
      (N := N) (k := 2)
      (m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT τ') APrimeSmoothTransition.transitionMesh N)
      (by norm_num) hst ht hmesh (by omega) hm hactive.1 hB0 ω hJ
    have hcal := APrimeSmoothWeightActual.canonicalM_calibration d
      (fun _ => 0) (firstCellT τ') APrimeSmoothTransition.transitionMesh
      N 2 hactive.1
    have hinv2 : ((N : ℝ) ^ (2 : ℕ))⁻¹ ≤ 1 :=
      (inv_le_one₀ (pow_pos (by exact_mod_cast (show 0 < N by omega)) _)).2
        (one_le_pow₀ (by exact_mod_cast (show 1 ≤ N by omega)))
    have hinv10 : (N : ℝ) ^ (-(10 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ N by omega))
        (by norm_num)
    have hq : (0 : ℝ) ≤
        1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ + (N : ℝ) ^ (-(10 : ℝ)) := by positivity
    have hS3 : APrimeSmoothWeightActual.prefixSample d 0 60 (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω ≤
          3 * Real.exp 1 := by
      calc
        _ ≤ Real.exp 1 *
            (1 + ((N : ℝ) ^ (2 : ℕ))⁻¹ + (N : ℝ) ^ (-(10 : ℝ))) :=
          hS.trans (mul_le_mul_of_nonneg_right hcal hq)
        _ ≤ 3 * Real.exp 1 := by nlinarith [Real.exp_pos 1]
    have hnδ : (1 : ℝ) ≤ (N : ℝ) ^ (2 * δ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hΘ : 3 * Real.exp 1 ≤ APrimeSmoothWeightActual.threshold δ N := by
      unfold APrimeSmoothWeightActual.threshold
      nlinarith [sq_nonneg (Real.exp 1 - 1),
        mul_nonneg (show (0 : ℝ) ≤ 8 * (Real.exp 1) ^ 2 by positivity)
          (sub_nonneg.mpr hnδ)]
    have hΘpos := APrimeSmoothWeightActual.threshold_pos (δ := δ)
      (N := N) (by omega : 0 < N)
    have hcut : APrimeSmoothWeightActual.cutoff d 0 60 δ (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
        (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
          (firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω = 1 := by
      unfold APrimeSmoothWeightActual.cutoff
      apply Cutoff.cutChi_eq_one
      exact (div_le_one hΘpos).2 (hS3.trans hΘ)
    unfold canonicalWeight APrimeFirstCellGeneratorHle.canonicalWeight
      APrimeFirstCellGeneratorHle.actualWeight APrimeSmoothWeightActual.weight
    simp [hactive, hcut]
  · unfold canonicalWeight APrimeFirstCellGeneratorHle.canonicalWeight
      APrimeFirstCellGeneratorHle.actualWeight APrimeSmoothWeightActual.weight
    simp [hactive]

/-- Every sample in the literal T434 sharp/common event has canonical weight
one; the sample is not replaced or intersected with a second witness. -/
theorem eventually_canonicalWeight_one_on_sharpCommonEvent
    {τ' δ α : ℝ} (hτ' : 0 < τ') (hδ : 0 < δ) (_hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α N,
      ∀ p : ℕ, canonicalWeight τ' δ p N 2 ω = 1 := by
  filter_upwards [eventually_canonicalWeight_two_one_of_norm hτ' hδ]
    with N hweight
  intro ω hω p
  have hcommon : ω ∈ APrimeFirstCellMovingSupport.commonEvent τ'
      (APrimeFirstCellEGAllOutputRunning.sourceLoss α)
      (APrimeFirstCellEGAllOutputRunning.sourceLoss α) (δ / 16) N := hω.2
  have hdyn := APrimeFirstCellMovingSupport.commonEvent_to_dynamic_support hcommon
  have hraw := APrimeSupportRunning.good_subset τ' (δ / 16) N hdyn
  exact hweight ω hraw.1.1.1 p

/-- T434's full same-event resident, with its `m = N` weight field replaced
by the canonical smoothing order. -/
def positiveCanonicalSharpPlateau (τ' δ α : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, canonicalWeight τ' δ p N 2 ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧
    u2 ≤ firstCellT τ' N ∧
    firstCellT τ' N ≤ 1 / 2 ∧
    APrimeFullQV.SourceEvent (sample d) 0 N u2 ω
      (APrimeFirstCellSourceAllTime.ellSource
        (APrimeFirstCellEGAllOutputRunning.sourceLoss α) N)
      (APrimeFirstCellSourceAllTime.sourceC4
        (APrimeFirstCellEGAllOutputRunning.sourceLoss α) N u2) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeSupportRunning.jG N r ω ≤ 2) ∧
    APrimeSupportRunning.jG N 0 ω ≤ 2 ∧
    APrimeSupportRunning.jG N u2 ω ≤ 2

/-- Replace the old `m = N` field of T434 on the very same resident by the
direct canonical-order estimate. -/
theorem positiveCanonicalSharpPlateau_of_sharp {τ' δ α : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hα : 0 < α)
    (hsharp : APrimeFirstCellSharpCommonEvent.positiveSharpPlateau τ' δ α) :
    positiveCanonicalSharpPlateau τ' δ α := by
  filter_upwards [hsharp,
    eventually_canonicalWeight_one_on_sharpCommonEvent hτ' hδ hα]
      with N hresident hcanonical
  dsimp only [APrimeFirstCellSharpCommonEvent.positiveSharpPlateau] at hresident
  obtain ⟨ω, hω, hk, _holdWeight, hu2pos, hu2le, hTle, hsource,
    hJall, hJ0, hJu2⟩ := hresident
  exact ⟨ω, hω, hk, hcanonical ω hω, hu2pos, hu2le, hTle,
    hsource, hJall, hJ0, hJu2⟩

/-- Closed producer with T434's parameter order, literal event, and
same-event positive resident. -/
theorem exists_sharpCommonEvent_with_canonical_plateau :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ α : ℝ, 0 < α →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' δ α) ∧
        positiveCanonicalSharpPlateau τ' δ α := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellSharpCommonEvent.exists_sharpCommonEvent_with_positive_plateau
  refine ⟨τ', hτ', ?_⟩
  intro δ hδ hδ100 α hα
  obtain ⟨hmeas, hp, hsharp⟩ := hall δ hδ hδ100 α hα
  exact ⟨hmeas, hp,
    positiveCanonicalSharpPlateau_of_sharp hτ' hδ hα hsharp⟩

/-- The zero prefix also has canonical weight one. -/
theorem canonicalWeight_k_zero (τ' δ : ℝ) (p N : ℕ) (ω : Ω d) :
    canonicalWeight τ' δ p N 0 ω = 1 := by
  unfold canonicalWeight APrimeFirstCellGeneratorHle.canonicalWeight
    APrimeFirstCellGeneratorHle.actualWeight
  exact APrimeSmoothWeightActual.weight_zero_prefix d 0 60 δ (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N
    (APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N)
    (APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh N) ω

#print axioms eventually_canonicalWeight_two_one_of_norm
#print axioms eventually_canonicalWeight_one_on_sharpCommonEvent
#print axioms positiveCanonicalSharpPlateau_of_sharp
#print axioms exists_sharpCommonEvent_with_canonical_plateau
#print axioms canonicalWeight_k_zero

end
end RBM.APrimeFirstCellCanonicalPlateau
