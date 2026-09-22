/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellBlockScalarTail

/-!
# Finite-net tail for one actual Gaussian block (T424)

This file combines the deterministic quarter-net reduction with the actual-model fixed-vector
tail.  The result concerns one ordered pair of distinct adjacent blocks.
-/

namespace RBM.APrimeFirstCellBlockNetTail

open Real MeasureTheory Matrix Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator ComplexConjugate

noncomputable section

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow

/-- Strict operator-norm excess at `8` produces a strict fixed-vector excess at `4` on any
quarter-net. -/
theorem exists_net_pair_of_norm_gt_eight {W : ℕ}
    (M : Matrix (Fin W) (Fin W) ℂ) (V : Finset (Gauss.BlockVec W))
    (hV : Gauss.IsQuarterSphereNet V) (hM : 8 < ‖M‖) :
    ∃ v ∈ V, ∃ w ∈ V,
      4 < ‖inner ℂ v (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M w)‖ := by
  have hnet := Gauss.l2_opNorm_le_two_blockBilinearMax M V hV
  have hmax : 4 < Gauss.blockBilinearMax M V := by linarith
  by_contra h
  push Not at h
  have hsup : Gauss.blockBilinearMax M V ≤ 4 := by
    unfold Gauss.blockBilinearMax
    change (((V ×ˢ V).sup fun p =>
      ‖inner ℂ p.1 (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M p.2)‖₊ : ℝ≥0) : ℝ) ≤ 4
    norm_cast
    apply Finset.sup_le
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact_mod_cast h p.1 hp1 p.2 hp2
  exact (not_lt_of_ge hsup) hmax

/-- The strict block-norm event is measurable. -/
theorem measurableSet_blockNorm_gt_eight (N : ℕ)
    (x y : ZMod (d.L N)) :
    MeasurableSet
      {ω : Gauss.Ω d | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖} := by
  exact measurableSet_lt measurable_const
    (APrimeFirstCellJGAllTime.measurable_xBlock N x y).norm

/-- Actual per-block finite-net tail for an ordered pair of distinct adjacent blocks. -/
theorem block_opNorm_tail (N : ℕ)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1) :
    (Gauss.P d).real
        {ω : Gauss.Ω d | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖} ≤
      4 * (9 : ℝ) ^ (4 * d.W N) * Real.exp (-24 * (d.W N : ℝ)) := by
  classical
  obtain ⟨V, hV, hcard⟩ := Gauss.exists_quarterSphereNet (d.W N)
  let scalarEvent : Gauss.BlockVec (d.W N) × Gauss.BlockVec (d.W N) → Set (Gauss.Ω d) :=
    fun p => {ω | 4 < ‖inner ℂ p.1
      (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
        (APrimeFirstCellJGAllTime.xBlock N ω x y) p.2)‖}
  have hsub :
      {ω : Gauss.Ω d | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖} ⊆
        ⋃ p ∈ V ×ˢ V, scalarEvent p := by
    intro ω hω
    obtain ⟨v, hv, w, hw, hvw⟩ :=
      exists_net_pair_of_norm_gt_eight
        (APrimeFirstCellJGAllTime.xBlock N ω x y) V hV hω
    exact Set.mem_iUnion.mpr ⟨(v, w),
      Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hv, hw⟩, hvw⟩⟩
  have hpair (p : Gauss.BlockVec (d.W N) × Gauss.BlockVec (d.W N))
      (hp : p ∈ V ×ˢ V) :
      (Gauss.P d).real (scalarEvent p) ≤
        4 * Real.exp (-24 * (d.W N : ℝ)) := by
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have htail := APrimeFirstCellBlockScalarTail.fixed_block_bilinear_tail
      N hxy hadj (hV.1 p.1 hp1) (hV.1 p.2 hp2) (r := (4 : ℝ)) (by norm_num)
    have htail' :
        (Gauss.P d).real (scalarEvent p) ≤
          4 * Real.exp (-(3 / 2 : ℝ) * (d.W N : ℝ) * (4 : ℝ) ^ 2) := by
      simpa only [scalarEvent] using htail
    calc
      (Gauss.P d).real (scalarEvent p) ≤
          4 * Real.exp (-(3 / 2 : ℝ) * (d.W N : ℝ) * (4 : ℝ) ^ 2) := htail'
      _ = 4 * Real.exp (-24 * (d.W N : ℝ)) := by
        congr 2
        ring
  have hcardNat : (V ×ˢ V).card ≤ 9 ^ (4 * d.W N) := by
    rw [Finset.card_product]
    calc
      V.card * V.card ≤ 9 ^ (2 * d.W N) * 9 ^ (2 * d.W N) :=
        Nat.mul_le_mul hcard hcard
      _ = 9 ^ (4 * d.W N) := by
        rw [← pow_add]
        congr 2
        omega
  have hcardReal : ((V ×ˢ V).card : ℝ) ≤ (9 : ℝ) ^ (4 * d.W N) := by
    exact_mod_cast hcardNat
  calc
    (Gauss.P d).real
        {ω : Gauss.Ω d | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖} ≤
        (Gauss.P d).real (⋃ p ∈ V ×ˢ V, scalarEvent p) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ p ∈ V ×ˢ V, (Gauss.P d).real (scalarEvent p) :=
      measureReal_biUnion_finset_le (V ×ˢ V) scalarEvent
    _ ≤ ∑ _p ∈ V ×ˢ V, 4 * Real.exp (-24 * (d.W N : ℝ)) := by
      exact Finset.sum_le_sum fun p hp => hpair p hp
    _ = ((V ×ˢ V).card : ℝ) * (4 * Real.exp (-24 * (d.W N : ℝ))) := by
      simp [mul_comm]
    _ ≤ (9 : ℝ) ^ (4 * d.W N) * (4 * Real.exp (-24 * (d.W N : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
    _ = 4 * (9 : ℝ) ^ (4 * d.W N) * Real.exp (-24 * (d.W N : ℝ)) := by ring

/-- The bound includes the endpoint `W = 1`. -/
theorem block_opNorm_tail_width_one (N : ℕ) (hW : d.W N = 1)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1) :
    (Gauss.P d).real
        {ω : Gauss.Ω d | 8 < ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖} ≤
      4 * (9 : ℝ) ^ 4 * Real.exp (-24) := by
  have h := block_opNorm_tail N hxy hadj
  rw [hW] at h
  norm_num at h ⊢
  exact h

/-- The concrete `N = 0` block has width one. -/
theorem block_opNorm_tail_zero
    {x y : ZMod (d.L 0)} (hxy : x ≠ y)
    (hadj : zdist (d.L 0) (x - y) ≤ 1) :
    (Gauss.P d).real
        {ω : Gauss.Ω d | 8 < ‖APrimeFirstCellJGAllTime.xBlock 0 ω x y‖} ≤
      4 * (9 : ℝ) ^ 4 * Real.exp (-24) := by
  exact block_opNorm_tail_width_one 0
    APrimeFirstCellBlockScalarTail.exampleGrow_width_zero hxy hadj

#print axioms exists_net_pair_of_norm_gt_eight
#print axioms measurableSet_blockNorm_gt_eight
#print axioms block_opNorm_tail
#print axioms block_opNorm_tail_width_one
#print axioms block_opNorm_tail_zero

end

end RBM.APrimeFirstCellBlockNetTail
