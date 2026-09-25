/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.StrictProbabilityBridge
import RBM1D.Gauss.DistEq
import RBM1D.Gauss.FlucAvg

/-!
# Fixed-spectral-parameter Gaussian bad-event measurability

The two exceptional events in Theorem 2.3, (2.3) and (2.4), are measurable for each fixed
spectral parameter. Their distinct entry and block scales are represented by distinct `ζ`
families below. This file proves measurability and the exact adapters to
`Band.strictBadSet`; it supplies no local-law probability estimate.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- The strict entry event in (2.3), with the union over both matrix indices. -/
noncomputable def entryLocalLawBad (d : Dims) (N : ℕ) (z : ℂ) (ρ : ℝ) : Set (Ω d) :=
  {ω | ∃ ij : d.Idx N × d.Idx N,
    (d.W N : ℝ) ^ ρ * ((band d).zScale N z)⁻¹ ^ ((1 : ℝ) / 2) <
      ‖(RBM.green (Xmat d N ω) z - RBM.msc z •
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖}

/-- The strict block event in (2.4), with the union over every spatial block.

The expression is parsed as `W⁻¹ * (∑ Gₓₓ) - m`, so the centering is outside the normalized
block sum, exactly as in the paper. -/
noncomputable def blockLocalLawBad (d : Dims) (N : ℕ) (z : ℂ) (ρ : ℝ) : Set (Ω d) :=
  {ω | ∃ a : ZMod (d.L N),
    (d.W N : ℝ) ^ ρ * ((band d).zScale N z)⁻¹ <
      ‖(d.W N : ℂ)⁻¹ * ∑ x : Fin (d.W N),
        RBM.green (Xmat d N ω) z (a, x) (a, x) - RBM.msc z‖}

theorem measurable_green_Xmat (d : Dims) (N : ℕ) (z : ℂ) (i j : d.Idx N) :
    Measurable fun ω : Ω d => RBM.green (Xmat d N ω) z i j := by
  simpa [Hflow] using (measurable_green_apply d N 1 z i j)

theorem measurableSet_entryLocalLawBad (d : Dims) (N : ℕ) (z : ℂ) (ρ : ℝ) :
    MeasurableSet (entryLocalLawBad d N z ρ) := by
  classical
  have hset : entryLocalLawBad d N z ρ = ⋃ ij : d.Idx N × d.Idx N,
      {ω : Ω d | (d.W N : ℝ) ^ ρ * ((band d).zScale N z)⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(RBM.green (Xmat d N ω) z - RBM.msc z •
          (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2‖} := by
    ext ω
    simp [entryLocalLawBad]
  rw [hset]
  apply MeasurableSet.iUnion
  intro ij
  have hmeas : Measurable fun ω : Ω d =>
      (RBM.green (Xmat d N ω) z - RBM.msc z •
        (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) ij.1 ij.2 := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have hfun : (fun ω : Ω d => RBM.green (Xmat d N ω) z ij.1 ij.2 -
        RBM.msc z * (1 : Matrix (d.Idx N) (d.Idx N) ℂ) ij.1 ij.2) =
        (fun ω : Ω d => RBM.green (Xmat d N ω) z ij.1 ij.2) -
        (fun _ : Ω d => RBM.msc z * (1 : Matrix (d.Idx N) (d.Idx N) ℂ) ij.1 ij.2) := by
      funext ω
      rfl
    rw [hfun]
    exact (measurable_green_Xmat d N z ij.1 ij.2).sub measurable_const
  exact measurableSet_lt measurable_const hmeas.norm

theorem measurableSet_blockLocalLawBad (d : Dims) (N : ℕ) (z : ℂ) (ρ : ℝ) :
    MeasurableSet (blockLocalLawBad d N z ρ) := by
  classical
  have hset : blockLocalLawBad d N z ρ = ⋃ a : ZMod (d.L N),
      {ω : Ω d | (d.W N : ℝ) ^ ρ * ((band d).zScale N z)⁻¹ <
        ‖(d.W N : ℂ)⁻¹ * ∑ x : Fin (d.W N),
            RBM.green (Xmat d N ω) z (a, x) (a, x) - RBM.msc z‖} := by
    ext ω
    simp [blockLocalLawBad]
  rw [hset]
  apply MeasurableSet.iUnion
  intro a
  have hs : Measurable fun ω : Ω d =>
      ∑ x : Fin (d.W N), RBM.green (Xmat d N ω) z (a, x) (a, x) := by
    exact Finset.measurable_sum _ fun x _ => measurable_green_Xmat d N z (a, x) (a, x)
  exact measurableSet_lt measurable_const ((measurable_const.mul hs).sub measurable_const).norm

/-- The concrete centered Green entry family for the exact transfer matrix `Hband = Xmat`. -/
noncomputable def entryLocalLawXi (d : Dims) (z : ℕ → ℂ) :
    ∀ N, (band d).Idx N × (band d).Idx N → Ω d → ℝ :=
  fun N ij ω => ‖(RBM.green ((transfer_gauss d).Hband N ω) (z N) -
    RBM.msc (z N) • (1 : Matrix ((band d).Idx N) ((band d).Idx N) ℂ)) ij.1 ij.2‖

/-- The entry threshold factor in (2.3), namely `(zScale⁻¹)^(1/2)`. -/
noncomputable def entryLocalLawZeta (d : Dims) (z : ℕ → ℂ) :
    ∀ N, (band d).Idx N × (band d).Idx N → Ω d → ℝ :=
  fun N _ _ => ((band d).zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)

/-- The centered W-normalized diagonal block trace for the exact transfer matrix `Hband = Xmat`. -/
noncomputable def blockLocalLawXi (d : Dims) (z : ℕ → ℂ) :
    ∀ N, ZMod (d.L N) → Ω d → ℝ :=
  fun N a ω => ‖(d.W N : ℂ)⁻¹ * ∑ x : Fin (d.W N),
    RBM.green ((transfer_gauss d).Hband N ω) (z N) (a, x) (a, x) - RBM.msc (z N)‖

/-- Explicit parse check: normalization multiplies the Green sum before subtraction of `m`. -/
theorem blockLocalLawXi_normalized_sum_sub_center (d : Dims) (z : ℕ → ℂ) (N : ℕ)
    (a : ZMod (d.L N)) (ω : Ω d) :
    blockLocalLawXi d z N a ω =
      ‖(d.W N : ℂ)⁻¹ *
        (∑ x : Fin (d.W N), RBM.green ((transfer_gauss d).Hband N ω) (z N)
          (a, x) (a, x)) - RBM.msc (z N)‖ := rfl

/-- The block threshold factor in (2.4), namely `zScale⁻¹`, distinct from the entry factor. -/
noncomputable def blockLocalLawZeta (d : Dims) (z : ℕ → ℂ) :
    ∀ N, ZMod (d.L N) → Ω d → ℝ :=
  fun N _ _ => ((band d).zScale N (z N))⁻¹

theorem entryLocalLawBad_eq_strictBadSet (d : Dims) (N : ℕ) (z : ℕ → ℂ) (ρ : ℝ) :
    entryLocalLawBad d N (z N) ρ =
      (band d).strictBadSet (entryLocalLawXi d z) (entryLocalLawZeta d z) ρ N := by
  ext ω
  simp only [entryLocalLawBad, RBM.Band.strictBadSet, entryLocalLawXi, entryLocalLawZeta,
    transfer_gauss_Hband, band_W, Set.mem_ofPred_eq]
  rfl

theorem blockLocalLawBad_eq_strictBadSet (d : Dims) (N : ℕ) (z : ℕ → ℂ) (ρ : ℝ) :
    blockLocalLawBad d N (z N) ρ =
      (band d).strictBadSet (blockLocalLawXi d z) (blockLocalLawZeta d z) ρ N := by
  ext ω
  simp only [blockLocalLawBad, RBM.Band.strictBadSet, blockLocalLawXi, blockLocalLawZeta,
    transfer_gauss_Hband, band_W, Set.mem_ofPred_eq]
  rfl

theorem strictBadSet_entryLocalLaw_measurable (d : Dims) (z : ℕ → ℂ) (ρ : ℝ) :
    ∀ N, MeasurableSet
      ((band d).strictBadSet (entryLocalLawXi d z) (entryLocalLawZeta d z) ρ N) := by
  intro N
  rw [← entryLocalLawBad_eq_strictBadSet d N z ρ]
  exact measurableSet_entryLocalLawBad d N (z N) ρ

theorem strictBadSet_blockLocalLaw_measurable (d : Dims) (z : ℕ → ℂ) (ρ : ℝ) :
    ∀ N, MeasurableSet
      ((band d).strictBadSet (blockLocalLawXi d z) (blockLocalLawZeta d z) ρ N) := by
  intro N
  rw [← blockLocalLawBad_eq_strictBadSet d N z ρ]
  exact measurableSet_blockLocalLawBad d N (z N) ρ

/-- Nondegenerate growing-width domain witness at the fixed spectral parameter `z = i/2`.

The positive imaginary part makes every `zScale` strictly positive. `exampleGrow` has both block
count and block width tending to infinity, so this witness does not rely on empty index sets. -/
theorem exampleGrow_fixed_z_domain :
    SpecSeqN 1 (1 / 4) (fun _ : ℕ => lemE (Complex.I / 2))
      (fun _ : ℕ => Complex.I / 2) ∧
    Tendsto (fun N => Dims.exampleGrow.W N) Filter.atTop Filter.atTop ∧
    Tendsto (fun N => Dims.exampleGrow.L N) Filter.atTop Filter.atTop ∧
    (∀ N : ℕ, 0 < (band Dims.exampleGrow).zScale N (Complex.I / 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply SpecSeqN.of_z (κ := 1) (τ := 1 / 4)
    · norm_num
    · norm_num
    · norm_num
    · filter_upwards [eventually_ge_atTop 4] with N hN
      have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
      have hroot : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
        calc
          (2 : ℝ) = (4 : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (by norm_num) hN4 (by norm_num)
      have hpow : (N : ℝ) ^ (-(3 : ℝ) / 4) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      calc
        (N : ℝ) ^ (-1 + (1 / 4 : ℝ)) = (N : ℝ) ^ (-(3 : ℝ) / 4) := by congr 1; ring
        _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := hpow
        _ = ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
          rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
            Real.rpow_neg (by positivity)]
        _ ≤ (2 : ℝ)⁻¹ :=
          (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2 hroot
        _ = 1 / 2 := by norm_num
        _ ≤ (Complex.I / 2).im := by norm_num
  · simpa [Dims.exampleGrow_W] using Dims.tendsto_growW
  · simpa [Dims.exampleGrow_L] using Dims.tendsto_growL
  · intro N
    apply (band Dims.exampleGrow).zScale_pos
    norm_num

#print axioms entryLocalLawBad
#print axioms blockLocalLawBad
#print axioms measurable_green_Xmat
#print axioms measurableSet_entryLocalLawBad
#print axioms measurableSet_blockLocalLawBad
#print axioms entryLocalLawXi
#print axioms entryLocalLawZeta
#print axioms blockLocalLawXi
#print axioms blockLocalLawZeta
#print axioms blockLocalLawXi_normalized_sum_sub_center
#print axioms entryLocalLawBad_eq_strictBadSet
#print axioms blockLocalLawBad_eq_strictBadSet
#print axioms strictBadSet_entryLocalLaw_measurable
#print axioms strictBadSet_blockLocalLaw_measurable
#print axioms exampleGrow_fixed_z_domain

end RBM.Gauss
