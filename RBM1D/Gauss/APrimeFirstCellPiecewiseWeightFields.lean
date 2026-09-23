/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellTargetWeightWitness

/-!
# T573: exact first-cell fields for the p-independent piecewise weight

This file specializes `APrimeWeight.jSnorm_piecewiseW_fields` to the actual first-cell
data.  The weight is independent of the moment order and is definitionally the
`piecewiseW` required by the first-cell weighted-moment ticket.

No moment, event, slot, or closure hypothesis is introduced here.
-/

namespace RBM.APrimeFirstCellPiecewiseWeightFields

open Filter MeasureTheory Gauss Step2Bootstrap CutHypTheta Cutoff

noncomputable section

/-- The actual normalized first-cell observable, with `E = 0`, `D = 60`, and `s = 0`. -/
noncomputable abbrev actualJ :
    ℕ → ℝ → Ω Dims.exampleGrow → ℝ :=
  fun N u omega =>
    Step2Moment.jSnorm (sample Dims.exampleGrow) 0 60 (fun _ => 0) N u omega

/-- The p-independent first-cell weight.  This is definitionally
`piecewiseW(canonicalR, 1, actualJ, 0, firstCellT tauPrime, transitionMesh)`. -/
noncomputable def weight (tauPrime delta : ℝ) (N k : ℕ) :
    Ω Dims.exampleGrow → ℝ :=
  APrimeWeight.piecewiseW
    (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh) 1 actualJ
    (fun _ => 0) (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    delta N k

/-- Literal definitional alignment with the p-independent weight used by T571. -/
theorem weight_eq_piecewiseW (tauPrime delta : ℝ) (N k : ℕ) :
    weight tauPrime delta N k =
      APrimeWeight.piecewiseW
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT tauPrime)
          APrimeSmoothTransition.transitionMesh) 1
        (fun N u omega => Step2Moment.jSnorm
          (sample Dims.exampleGrow) 0 60 (fun _ => 0) N u omega)
        (fun _ => 0) (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        delta N k := by
  rfl

/-- All four exact structural weight fields, with no asymptotic or activity restriction. -/
theorem fields (tauPrime : ℝ) :
    (∀ delta N k,
      AEStronglyMeasurable (weight tauPrime delta N k) (P Dims.exampleGrow)) ∧
    (∀ delta N k omega, 0 ≤ weight tauPrime delta N k omega) ∧
    (∀ delta N k omega, weight tauPrime delta N k omega ≤ 1) ∧
    (∀ delta N k omega,
      omega ∈ prefNet actualJ (fun _ => 0) APrimeSmoothTransition.transitionMesh
        (fun N _ => (N : ℝ) ^ (2 * delta) * 1) N k →
      1 ≤ weight tauPrime delta N k omega) := by
  simpa only [actualJ, weight] using
    (APrimeWeight.jSnorm_piecewiseW_fields
      (P := P Dims.exampleGrow) (X := sample Dims.exampleGrow)
      0 60 (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh)

/-- Exact measurability under the actual Gaussian measure. -/
theorem weight_aestronglyMeasurable (tauPrime delta : ℝ) (N k : ℕ) :
    AEStronglyMeasurable (weight tauPrime delta N k) (P Dims.exampleGrow) :=
  (fields tauPrime).1 delta N k

/-- Pointwise nonnegativity, including inactive indices and small `N`. -/
theorem weight_nonneg (tauPrime delta : ℝ) (N k : ℕ)
    (omega : Ω Dims.exampleGrow) :
    0 ≤ weight tauPrime delta N k omega :=
  (fields tauPrime).2.1 delta N k omega

/-- Pointwise upper bound one, including inactive indices and small `N`. -/
theorem weight_le_one (tauPrime delta : ℝ) (N k : ℕ)
    (omega : Ω Dims.exampleGrow) :
    weight tauPrime delta N k omega ≤ 1 :=
  (fields tauPrime).2.2.1 delta N k omega

/-- Exact prefix domination with coefficient one for every `delta`, `N`, and `k`. -/
theorem one_le_weight_of_mem_prefNet (tauPrime delta : ℝ) (N k : ℕ)
    (omega : Ω Dims.exampleGrow)
    (homega : omega ∈ prefNet actualJ (fun _ => 0)
      APrimeSmoothTransition.transitionMesh
      (fun N _ => (N : ℝ) ^ (2 * delta) * 1) N k) :
    1 ≤ weight tauPrime delta N k omega :=
  (fields tauPrime).2.2.2 delta N k omega homega

/-- The empty prefix has exactly weight one, for all parameters and samples. -/
theorem weight_k_zero (tauPrime delta : ℝ) (N : ℕ)
    (omega : Ω Dims.exampleGrow) :
    weight tauPrime delta N 0 omega = 1 := by
  apply le_antisymm (weight_le_one tauPrime delta N 0 omega)
  apply one_le_weight_of_mem_prefNet tauPrime delta N 0 omega
  intro j hj
  omega

/-- The actual zero scalar sample lies on the weight-one plateau at the positive prefix
`k = 2`, eventually.  This is a satisfiability witness and uses no stochastic moment or
event assumption. -/
theorem eventually_weight_zeroSample_eq_one :
    ∀ᶠ N : ℕ in atTop,
      weight 1 (1 / 8) N 2
        (APrimeSmoothTransition.scalarSample Dims.exampleGrow 0) = 1 := by
  have h := APrimeFirstCellTargetWeightWitness.eventually_exampleGrow_target_weights_one
    (τ := (1 : ℝ)) (δ := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [h] with N hN
  simpa only [weight, actualJ] using hN.1

/-- At the explicit transition scalar sample the same actual p-independent weight
vanishes at `k = 2`, eventually. -/
theorem eventually_weight_transitionSample_eq_zero :
    ∀ᶠ N : ℕ in atTop,
      weight 1 (1 / 8) N 2
        (APrimeSmoothTransition.scalarSample Dims.exampleGrow
          (2 / Real.sqrt ((APrimeSmoothTransition.transitionMesh N)⁻¹))) = 0 := by
  have hgeometry := APrimeSmoothTransition.eventually_exampleGrow_transition
    (τ := (1 : ℝ)) (δ := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hconst := eventually_le_rpow (128 * Real.exp 1)
    (by norm_num : (0 : ℝ) < 3 / 8)
  filter_upwards [hgeometry, Dims.bandwidth_grow, hconst,
    eventually_ge_atTop 2] with N hgeom hband hconstN hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by positivity
  have hband' : (N : ℝ) ^ (5 / 8 : ℝ) ≤ (Dims.exampleGrow.W N : ℝ) := by
    convert hband using 1 <;> norm_num
  have hlarge :
      128 * Real.exp 1 * (N : ℝ) ^ (1 / 4 : ℝ) ≤
        (Dims.exampleGrow.W N : ℝ) := by
    calc
      128 * Real.exp 1 * (N : ℝ) ^ (1 / 4 : ℝ) ≤
          (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hconstN (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (5 / 8 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      _ ≤ (Dims.exampleGrow.W N : ℝ) := hband'
  let mesh := APrimeSmoothTransition.transitionMesh
  let omega := APrimeSmoothTransition.scalarSample Dims.exampleGrow
    (2 / Real.sqrt ((mesh N)⁻¹))
  have hJlower := APrimeSmoothTransition.jSnorm_transition_lower
    Dims.exampleGrow N hgeom.1 (by
      have hmesh : (mesh N)⁻¹ ≤ 1 / 8 := by
        dsimp [mesh, APrimeSmoothTransition.transitionMesh]
        rw [max_eq_right hNr]
        have hp : (8 : ℝ) ≤ (N : ℝ) ^ (248 : ℕ) := by
          have hN8 : (8 : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := by
            have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
            nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN2 3]
          exact hN8.trans (pow_le_pow_right₀ hNr (by norm_num : 3 ≤ 248))
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hp)
      exact hmesh) (by norm_num : (2 : ℝ) ≤ 60)
  have htheta : 0 < Real.exp 1 * APrimePrior.priorLevel (1 / 8)
      (fun _ => 1) N :=
    mul_pos (Real.exp_pos 1) (APrimePrior.priorLevel_pos hN1 (by norm_num))
  have hcut : 2 * (Real.exp 1 * APrimePrior.priorLevel (1 / 8)
      (fun _ => 1) N) ≤ |actualJ N (cutNetPt (fun _ => 0) mesh N 1) omega| := by
    have hscale : 2 * (Real.exp 1 * APrimePrior.priorLevel (1 / 8)
        (fun _ => 1) N) ≤ (Dims.exampleGrow.W N : ℝ) / 64 := by
      simp only [APrimePrior.priorLevel]
      have hpow : (N : ℝ) ^ (2 * (1 / 8 : ℝ)) =
          (N : ℝ) ^ (1 / 4 : ℝ) := by norm_num
      rw [hpow]
      linarith
    have hJ0 : 0 ≤ actualJ N (cutNetPt (fun _ => 0) mesh N 1) omega :=
      APrimeFirstCellTargetWeightWitness.jSnorm_nonneg_all_time
        Dims.exampleGrow 0 60 (fun _ => 0) N _ omega
    rw [abs_of_nonneg hJ0]
    apply hscale.trans
    simpa only [actualJ, mesh, omega, cutNetPt, Nat.cast_one, zero_add, one_div]
      using hJlower
  rw [weight, APrimeWeight.piecewiseW, ite_eq_left ⟨hgeom.2.1, hN1⟩]
  unfold APrimeWeight.prefixSoftW
  exact softW_eq_zero (by simp [APrimeWeight.canonicalR]) htheta (by simp) hcut

/-- The actual first-cell p-independent weight is genuinely nonconstant on its Gaussian
sample space: at the same positive prefix it is eventually one at one explicit scalar
sample and zero at another. -/
theorem eventually_weight_nonconstant_witness :
    ∀ᶠ N : ℕ in atTop,
      weight 1 (1 / 8) N 2
          (APrimeSmoothTransition.scalarSample Dims.exampleGrow 0) = 1 ∧
      weight 1 (1 / 8) N 2
          (APrimeSmoothTransition.scalarSample Dims.exampleGrow
            (2 / Real.sqrt ((APrimeSmoothTransition.transitionMesh N)⁻¹))) = 0 := by
  filter_upwards [eventually_weight_zeroSample_eq_one,
    eventually_weight_transitionSample_eq_zero] with N hone hzero
  exact ⟨hone, hzero⟩

#print axioms actualJ
#print axioms weight
#print axioms weight_eq_piecewiseW
#print axioms fields
#print axioms weight_aestronglyMeasurable
#print axioms weight_nonneg
#print axioms weight_le_one
#print axioms one_le_weight_of_mem_prefNet
#print axioms weight_k_zero
#print axioms eventually_weight_zeroSample_eq_one
#print axioms eventually_weight_transitionSample_eq_zero
#print axioms eventually_weight_nonconstant_witness

end

end RBM.APrimeFirstCellPiecewiseWeightFields
