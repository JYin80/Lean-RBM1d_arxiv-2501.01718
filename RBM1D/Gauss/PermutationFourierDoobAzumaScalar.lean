/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierDoobCondMGF
import Mathlib.Probability.Moments.SubGaussian

/-!
# Scalar Azuma bounds for actual-prefix Fourier means

This finite-permutation auxiliary result applies Azuma to the shifted
successive differences of the actual-prefix real and imaginary means.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

private noncomputable def prefixFourierCoordMean (W : ℕ) (x χ : Fin W → ℂ) (isReal : Bool)
    (j : ℕ) : PermΩ W → ℝ :=
  if isReal then prefixFourierRealMean W j x χ else prefixFourierImagMean W j x χ

private noncomputable def shiftedFourierCoordProcess (W : ℕ) (x χ : Fin W → ℂ) (isReal : Bool)
    : ℕ → PermΩ W → ℝ
  | 0 => fun _ => 0
  | i + 1 => fun π => prefixFourierCoordMean W x χ isReal (i + 1) π -
      prefixFourierCoordMean W x χ isReal i π

private noncomputable def shiftedFourierCoordVariance (W : ℕ) : ℕ → NNReal
  := fun n => if n = 0 then 0 else ⟨64 / (W : ℝ) ^ 2, by positivity⟩

private theorem prefixFourierCoordMean_measurable (W : ℕ) (x χ : Fin W → ℂ)
    (isReal : Bool) (j : ℕ) :
    Measurable[prefixSigma W j] (prefixFourierCoordMean W x χ isReal j) := by
  cases isReal with
  | false => exact prefixFourierImagMean_measurable W j x χ
  | true => exact prefixFourierRealMean_measurable W j x χ

private theorem shiftedFourierCoordProcess_stronglyAdapted
    (W : ℕ) (x χ : Fin W → ℂ) (isReal : Bool) :
    StronglyAdapted (prefixFiltration W)
      (shiftedFourierCoordProcess W x χ isReal) := by
  intro n
  cases n with
  | zero => exact stronglyMeasurable_const
  | succ n =>
    have hnext : Measurable[prefixSigma W (n + 1)]
        (prefixFourierCoordMean W x χ isReal (n + 1)) :=
      prefixFourierCoordMean_measurable W x χ isReal (n + 1)
    have hmono : prefixSigma W n ≤ prefixSigma W (n + 1) :=
      prefixSigma_mono W (by omega)
    have hnow : Measurable[prefixSigma W (n + 1)]
        (prefixFourierCoordMean W x χ isReal n) :=
      Measurable.mono (prefixFourierCoordMean_measurable W x χ isReal n)
        hmono (le_refl _)
    change StronglyMeasurable[prefixSigma W (n + 1)]
      (fun π => prefixFourierCoordMean W x χ isReal (n + 1) π -
        prefixFourierCoordMean W x χ isReal n π)
    exact (hnext.sub hnow).stronglyMeasurable

private theorem shiftedFourierCoordProcess_sum_eq
    (W : ℕ) (x χ : Fin W → ℂ) (isReal : Bool) (π : PermΩ W) :
    (∑ i ∈ Finset.range (W + 1), shiftedFourierCoordProcess W x χ isReal i π) =
      prefixFourierCoordMean W x χ isReal W π -
        prefixFourierCoordMean W x χ isReal 0 π := by
  calc
    (∑ i ∈ Finset.range (W + 1), shiftedFourierCoordProcess W x χ isReal i π) =
        ∑ i ∈ Finset.range W,
          (prefixFourierCoordMean W x χ isReal (i + 1) π -
            prefixFourierCoordMean W x χ isReal i π) := by
      rw [Finset.sum_range_succ']
      simp [shiftedFourierCoordProcess]
    _ = prefixFourierCoordMean W x χ isReal W π -
        prefixFourierCoordMean W x χ isReal 0 π := by
      simpa using Finset.sum_range_sub
        (fun i => prefixFourierCoordMean W x χ isReal i π) W

private theorem shiftedFourierCoordVariance_sum (W : ℕ) (hW : 2 ≤ W) :
    (∑ i ∈ Finset.range (W + 1), shiftedFourierCoordVariance W i) =
      (64 : NNReal) / (W : NNReal) := by
  let q : NNReal := ⟨64 / (W : ℝ) ^ 2, by positivity⟩
  have hconst : (∑ i ∈ Finset.range W, q) = (W : NNReal) * q := by
    simp [Finset.sum_const, Finset.card_range]
  calc
    (∑ i ∈ Finset.range (W + 1), shiftedFourierCoordVariance W i) =
        (∑ i ∈ Finset.range W, shiftedFourierCoordVariance W (i + 1)) +
          shiftedFourierCoordVariance W 0 := by
      rw [Finset.sum_range_succ']
    _ = (∑ i ∈ Finset.range W, q) + 0 := by
      congr 1
    _ = (W : NNReal) * q := by rw [hconst]; simp
    _ = (64 : NNReal) / (W : NNReal) := by
      apply NNReal.coe_injective
      change (W : ℝ) * (64 / (W : ℝ) ^ 2) = 64 / (W : ℝ)
      have hWpos : (W : ℝ) ≠ 0 := by positivity
      field_simp

private theorem prefixFourierCoordProcess_hasSubgaussianMGF
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ) (isReal : Bool)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) :
    HasSubgaussianMGF
      (fun π => ∑ i ∈ Finset.range (W + 1),
        shiftedFourierCoordProcess W x χ isReal i π)
      (∑ i ∈ Finset.range (W + 1), shiftedFourierCoordVariance W i)
      (uniformPerm W) := by
  let Y := shiftedFourierCoordProcess W x χ isReal
  let cY := shiftedFourierCoordVariance W
  have hAdapt : StronglyAdapted (prefixFiltration W) Y :=
    shiftedFourierCoordProcess_stronglyAdapted W x χ isReal
  have hZero : HasSubgaussianMGF (Y 0) (cY 0) (uniformPerm W) := by
    simp only [Y, cY, shiftedFourierCoordProcess, shiftedFourierCoordVariance]
    exact HasSubgaussianMGF.fun_zero
  have hCond : ∀ i < W + 1 - 1,
      HasCondSubgaussianMGF ((prefixFiltration W) i) ((prefixFiltration W).le i)
        (Y (i + 1)) (cY (i + 1)) (uniformPerm W) := by
    intro i hi
    have hiW : i < W := by omega
    let k : Fin W := ⟨i, hiW⟩
    have hmgf : HasCondSubgaussianMGF (prefixSigma W k.val) le_top
        (fun π => prefixFourierCoordMean W x χ isReal (k.val + 1) π -
          prefixFourierCoordMean W x χ isReal k.val π)
        ⟨64 / (W : ℝ) ^ 2, by positivity⟩ (uniformPerm W) := by
      cases isReal with
      | false =>
        simpa [prefixFourierCoordMean] using
          uniformPerm_prefixFourierImag_hasCondSubgaussianMGF W hW k x χ hx hχ
      | true =>
        simpa [prefixFourierCoordMean] using
          uniformPerm_prefixFourierReal_hasCondSubgaussianMGF W hW k x χ hx hχ
    change HasCondSubgaussianMGF (prefixSigma W i) le_top
      (shiftedFourierCoordProcess W x χ isReal (i + 1))
      (shiftedFourierCoordVariance W (i + 1)) (uniformPerm W)
    simpa [shiftedFourierCoordProcess, shiftedFourierCoordVariance,
      prefixFourierCoordMean, k] using hmgf
  simpa [Y, cY] using
    (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF hAdapt hZero (W + 1) hCond)

private theorem scalar_tail_bound_of_shifted_process
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ) (isReal : Bool)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (uniformPerm W).real {π | s ≤
      prefixFourierCoordMean W x χ isReal W π -
        prefixFourierCoordMean W x χ isReal 0 π} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) ∧
    (uniformPerm W).real {π |
      s ≤ prefixFourierCoordMean W x χ isReal 0 π -
        prefixFourierCoordMean W x χ isReal W π} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
  have hmgf := prefixFourierCoordProcess_hasSubgaussianMGF W hW x χ isReal hx hχ
  have hsum := shiftedFourierCoordVariance_sum W hW
  have htail := hmgf.measure_ge_le hs
  have hneg := hmgf.neg.measure_ge_le hs
  have hprocess (π : PermΩ W) :
      (∑ i ∈ Finset.range (W + 1), shiftedFourierCoordProcess W x χ isReal i π) =
        prefixFourierCoordMean W x χ isReal W π -
          prefixFourierCoordMean W x χ isReal 0 π :=
    shiftedFourierCoordProcess_sum_eq W x χ isReal π
  constructor
  · calc
      (uniformPerm W).real {π | s ≤
          prefixFourierCoordMean W x χ isReal W π -
            prefixFourierCoordMean W x χ isReal 0 π} =
          (uniformPerm W).real {π | s ≤
            ∑ i ∈ Finset.range (W + 1), shiftedFourierCoordProcess W x χ isReal i π} := by
        congr 1
        ext π
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h
          rw [hprocess π]
          exact h
        · intro h
          rw [← hprocess π]
          exact h
      _ ≤ Real.exp (-s ^ 2 / (2 * ∑ i ∈ Finset.range (W + 1),
          shiftedFourierCoordVariance W i)) := htail
      _ = Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
        rw [hsum]
        push_cast
        have hWpos : (W : ℝ) ≠ 0 := by positivity
        field_simp
        ring_nf
  · calc
      (uniformPerm W).real {π |
          s ≤ prefixFourierCoordMean W x χ isReal 0 π -
            prefixFourierCoordMean W x χ isReal W π} =
          (uniformPerm W).real {π | s ≤ -(
            ∑ i ∈ Finset.range (W + 1), shiftedFourierCoordProcess W x χ isReal i π)} := by
        congr 1
        ext π
        simp only [Set.mem_setOf_eq]
        have hnegprocess : -(∑ i ∈ Finset.range (W + 1),
            shiftedFourierCoordProcess W x χ isReal i π) =
            prefixFourierCoordMean W x χ isReal 0 π -
              prefixFourierCoordMean W x χ isReal W π := by
          rw [hprocess π]
          ring
        constructor
        · intro h
          rw [hnegprocess]
          exact h
        · intro h
          rw [← hnegprocess]
          exact h
      _ ≤ Real.exp (-s ^ 2 / (2 * ∑ i ∈ Finset.range (W + 1),
          shiftedFourierCoordVariance W i)) := hneg
      _ = Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
        rw [hsum]
        push_cast
        have hWpos : (W : ℝ) ≠ 0 := by positivity
        field_simp
        ring_nf

private theorem prefixFourierCoordMean_full (W : ℕ) (x χ : Fin W → ℂ)
    (isReal : Bool) (π : PermΩ W) :
    prefixFourierCoordMean W x χ isReal W π =
      if isReal then (permutationFourierSum W x χ π).re
      else (permutationFourierSum W x χ π).im := by
  cases isReal <;> simp [prefixFourierCoordMean, prefixFourierRealMean,
    prefixFourierImagMean, prefixCellMean_eq_of_width_le]

private theorem prefixFourierCoordMean_zero (W : ℕ) (x χ : Fin W → ℂ)
    (isReal : Bool) (π : PermΩ W) :
    prefixFourierCoordMean W x χ isReal 0 π =
      (∑ ρ : PermΩ W, if isReal then (permutationFourierSum W x χ ρ).re
        else (permutationFourierSum W x χ ρ).im) / Fintype.card (PermΩ W) := by
  cases isReal <;> simp [prefixFourierCoordMean, prefixFourierRealMean,
    prefixFourierImagMean, prefixCellMean_zero]

/-- Pointwise telescoping of the real Doob differences gives the observable
minus its exact finite uniform mean. -/
theorem prefixFourierRealMean_telescoping (W : ℕ) (x χ : Fin W → ℂ)
    (π : PermΩ W) :
    (∑ i ∈ Finset.range W,
      (prefixFourierRealMean W (i + 1) x χ π - prefixFourierRealMean W i x χ π)) =
      (permutationFourierSum W x χ π).re -
        (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
          Fintype.card (PermΩ W) := by
  calc
    _ = prefixFourierRealMean W W x χ π - prefixFourierRealMean W 0 x χ π := by
      simpa using Finset.sum_range_sub
        (fun i => prefixFourierRealMean W i x χ π) W
    _ = _ := by
      change prefixCellMean W W (fun ρ => (permutationFourierSum W x χ ρ).re) π -
          prefixCellMean W 0 (fun ρ => (permutationFourierSum W x χ ρ).re) π = _
      rw [prefixCellMean_eq_of_width_le W W le_rfl, prefixCellMean_zero]

/-- Pointwise telescoping of the imaginary Doob differences gives the
observable minus its exact finite uniform mean. -/
theorem prefixFourierImagMean_telescoping (W : ℕ) (x χ : Fin W → ℂ)
    (π : PermΩ W) :
    (∑ i ∈ Finset.range W,
      (prefixFourierImagMean W (i + 1) x χ π - prefixFourierImagMean W i x χ π)) =
      (permutationFourierSum W x χ π).im -
        (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
          Fintype.card (PermΩ W) := by
  calc
    _ = prefixFourierImagMean W W x χ π - prefixFourierImagMean W 0 x χ π := by
      simpa using Finset.sum_range_sub
        (fun i => prefixFourierImagMean W i x χ π) W
    _ = _ := by
      change prefixCellMean W W (fun ρ => (permutationFourierSum W x χ ρ).im) π -
          prefixCellMean W 0 (fun ρ => (permutationFourierSum W x χ ρ).im) π = _
      rw [prefixCellMean_eq_of_width_le W W le_rfl, prefixCellMean_zero]

/-- Width zero and width one have singleton permutation spaces; their
prefix means equal the observable at every prefix. -/
theorem prefixFourierDoobAzuma_zero_one_check
    (j : ℕ) (x₀ χ₀ : Fin 0 → ℂ) (π₀ : PermΩ 0)
    (x₁ χ₁ : Fin 1 → ℂ) (π₁ : PermΩ 1) :
    prefixFourierRealMean 0 j x₀ χ₀ π₀ =
      (permutationFourierSum 0 x₀ χ₀ π₀).re ∧
    prefixFourierImagMean 0 j x₀ χ₀ π₀ =
      (permutationFourierSum 0 x₀ χ₀ π₀).im ∧
    prefixFourierRealMean 1 j x₁ χ₁ π₁ =
      (permutationFourierSum 1 x₁ χ₁ π₁).re ∧
    prefixFourierImagMean 1 j x₁ χ₁ π₁ =
      (permutationFourierSum 1 x₁ χ₁ π₁).im :=
  prefixFourierComponents_zero_one j x₀ χ₀ π₀ x₁ χ₁ π₁

/-- The last actual-prefix reveal has zero real and imaginary increments. -/
theorem prefixFourierDoobAzuma_last_reveal_check
    (W : ℕ) (k : Fin W) (x χ : Fin W → ℂ) (π : PermΩ W)
    (hk : k.val + 1 = W) :
    prefixFourierRealMean W (k.val + 1) x χ π =
      prefixFourierRealMean W k.val x χ π ∧
    prefixFourierImagMean W (k.val + 1) x χ π =
      prefixFourierImagMean W k.val x χ π :=
  prefixFourierComponents_last_eq W k x χ π hk

/-- The width-two first reveal is nonconstant and has positive mass on both
permutations, so the tail theorem is substantive. -/
theorem uniformPerm_prefixFourierDoobAzuma_two_witness :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} ∧
      prefixFourierRealMean 2 1 x χ (Equiv.refl _) -
        prefixFourierRealMean 2 0 x χ (Equiv.refl _) = 2 ∧
      HasCondSubgaussianMGF (prefixSigma 2 0) le_top
        (fun π : PermΩ 2 => prefixFourierRealMean 2 1 x χ π -
          prefixFourierRealMean 2 0 x χ π)
        ⟨16, by norm_num⟩ (uniformPerm 2) :=
  uniformPerm_prefixFourier_condMGF_two_witness

/- The four exported tails below are centered at the exact finite uniform mean. -/

/-- The centered real actual-prefix Fourier mean has the scalar Azuma upper tail
with exponent `-W s²/128`. -/
theorem uniformPerm_prefixFourierReal_centered_upper_tail
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (uniformPerm W).real {π |
      s ≤ (permutationFourierSum W x χ π).re -
        (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
          Fintype.card (PermΩ W)} ≤ Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
  obtain ⟨hup, _⟩ := scalar_tail_bound_of_shifted_process W hW x χ true hx hχ s hs
  have hset : {π : PermΩ W | s ≤ (permutationFourierSum W x χ π).re -
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
        Fintype.card (PermΩ W)} =
      {π | s ≤ prefixFourierCoordMean W x χ true W π -
        prefixFourierCoordMean W x χ true 0 π} := by
    ext π
    simp only [Set.mem_setOf_eq]
    rw [prefixFourierCoordMean_full, prefixFourierCoordMean_zero]
    rfl
  rw [hset]
  exact hup

/-- The centered real actual-prefix Fourier mean has the scalar Azuma lower tail
with exponent `-W s²/128`. -/
theorem uniformPerm_prefixFourierReal_centered_lower_tail
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (uniformPerm W).real {π |
      s ≤ (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
          Fintype.card (PermΩ W) - (permutationFourierSum W x χ π).re} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
  obtain ⟨_, hlo⟩ := scalar_tail_bound_of_shifted_process W hW x χ true hx hχ s hs
  have hset : {π : PermΩ W | s ≤
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).re) /
        Fintype.card (PermΩ W) - (permutationFourierSum W x χ π).re} =
      {π | s ≤ prefixFourierCoordMean W x χ true 0 π -
        prefixFourierCoordMean W x χ true W π} := by
    ext π
    simp only [Set.mem_setOf_eq]
    rw [prefixFourierCoordMean_full, prefixFourierCoordMean_zero]
    rfl
  rw [hset]
  exact hlo

/-- The centered imaginary actual-prefix Fourier mean has the scalar Azuma upper tail
with exponent `-W s²/128`. -/
theorem uniformPerm_prefixFourierImag_centered_upper_tail
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (uniformPerm W).real {π |
      s ≤ (permutationFourierSum W x χ π).im -
        (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
          Fintype.card (PermΩ W)} ≤ Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
  obtain ⟨hup, _⟩ := scalar_tail_bound_of_shifted_process W hW x χ false hx hχ s hs
  have hset : {π : PermΩ W | s ≤ (permutationFourierSum W x χ π).im -
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
        Fintype.card (PermΩ W)} =
      {π | s ≤ prefixFourierCoordMean W x χ false W π -
        prefixFourierCoordMean W x χ false 0 π} := by
    ext π
    simp only [Set.mem_setOf_eq]
    rw [prefixFourierCoordMean_full, prefixFourierCoordMean_zero]
    rfl
  rw [hset]
  exact hup

/-- The centered imaginary actual-prefix Fourier mean has the scalar Azuma lower tail
with exponent `-W s²/128`. -/
theorem uniformPerm_prefixFourierImag_centered_lower_tail
    (W : ℕ) (hW : 2 ≤ W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (uniformPerm W).real {π |
      s ≤ (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
          Fintype.card (PermΩ W) - (permutationFourierSum W x χ π).im} ≤
      Real.exp (-(W : ℝ) * s ^ 2 / 128) := by
  obtain ⟨_, hlo⟩ := scalar_tail_bound_of_shifted_process W hW x χ false hx hχ s hs
  have hset : {π : PermΩ W | s ≤
      (∑ ρ : PermΩ W, (permutationFourierSum W x χ ρ).im) /
        Fintype.card (PermΩ W) - (permutationFourierSum W x χ π).im} =
      {π | s ≤ prefixFourierCoordMean W x χ false 0 π -
        prefixFourierCoordMean W x χ false W π} := by
    ext π
    simp only [Set.mem_setOf_eq]
    rw [prefixFourierCoordMean_full, prefixFourierCoordMean_zero]
    rfl
  rw [hset]
  exact hlo

#print axioms prefixFourierRealMean_telescoping
#print axioms prefixFourierImagMean_telescoping
#print axioms prefixFourierDoobAzuma_zero_one_check
#print axioms prefixFourierDoobAzuma_last_reveal_check
#print axioms uniformPerm_prefixFourierDoobAzuma_two_witness
#print axioms uniformPerm_prefixFourierReal_centered_upper_tail
#print axioms uniformPerm_prefixFourierReal_centered_lower_tail
#print axioms uniformPerm_prefixFourierImag_centered_upper_tail
#print axioms uniformPerm_prefixFourierImag_centered_lower_tail

end RBM.Gauss
