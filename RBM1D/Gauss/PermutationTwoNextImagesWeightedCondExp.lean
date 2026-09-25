/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationTwoNextImagesCondExp

/-!
# Conditional expectation of a weighted pair of successive permutation images

The formula follows by expanding the deterministic weight over ordered image
pairs and applying the already proved pair-indicator conditional law.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

/-- Conditional expectation of a deterministic function of two successive
images, given the prefix before the first image. -/
theorem uniformPerm_twoNextImages_weighted_condExp
    (W : ℕ) (k j : Fin W) (f : Fin W → Fin W → ℝ)
    (hj : j.val = k.val + 1) :
    (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k) (ρ j)) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      (∑ v ∈ unusedImages W k π,
        ∑ w ∈ unusedImages W k π, if v ≠ w then f v w else 0) /
        ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))) := by
  classical
  let indicator : Fin W → Fin W → PermΩ W → ℝ :=
    fun v w ρ => if ρ k = v ∧ ρ j = w then 1 else 0
  let summand : Fin W → Fin W → PermΩ W → ℝ :=
    fun v w ρ => if ρ k = v ∧ ρ j = w then f v w else 0
  have hsumdef (v w : Fin W) : summand v w = f v w • indicator v w := by
    funext ρ
    simp [summand, indicator, smul_eq_mul, mul_ite]
  have hdecomp : (fun ρ : PermΩ W => f (ρ k) (ρ j)) =
      ∑ v : Fin W, ∑ w : Fin W, summand v w := by
    funext ρ
    simp only [Finset.sum_apply]
    have hinner (v : Fin W) :
        (∑ w : Fin W, if ρ k = v ∧ ρ j = w then f v w else 0) =
          if ρ k = v then f v (ρ j) else 0 := by
      by_cases hv : ρ k = v
      · simp [hv, Finset.sum_ite_eq', eq_comm]
      · simp [hv]
    simp_rw [summand, hinner]
    simp [Finset.sum_ite_eq', eq_comm]
  have hcondPair :
      (uniformPerm W)[(∑ p : Fin W × Fin W, summand p.1 p.2) |
          prefixSigma W k.val]
        =ᵐ[uniformPerm W]
      ∑ p : Fin W × Fin W,
        (uniformPerm W)[summand p.1 p.2 | prefixSigma W k.val] := by
    simpa using
      (condExp_finsetSum (μ := uniformPerm W) (s := Finset.univ)
        (f := fun p : Fin W × Fin W => summand p.1 p.2)
        (fun p _ => Integrable.of_finite) (prefixSigma W k.val))
  have hcond :
      (uniformPerm W)[(∑ v : Fin W, ∑ w : Fin W, summand v w) |
          prefixSigma W k.val]
        =ᵐ[uniformPerm W]
      ∑ v : Fin W, ∑ w : Fin W,
        (uniformPerm W)[summand v w | prefixSigma W k.val] := by
    simpa only [Fintype.sum_prod_type] using hcondPair
  have hsingle (v w : Fin W) :
      (uniformPerm W)[summand v w | prefixSigma W k.val] =ᵐ[uniformPerm W]
        (fun π => f v w *
          (if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
            then (1 : ℝ) /
              ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
            else 0)) := by
    have hs := condExp_smul (μ := uniformPerm W)
      (m := prefixSigma W k.val) (c := f v w) (indicator v w)
    have hb := uniformPerm_two_successiveImages_condExp W k j v w hj
    filter_upwards [hs, hb] with π hsπ hbπ
    calc
      (uniformPerm W)[summand v w | prefixSigma W k.val] π
          = f v w * (uniformPerm W)[indicator v w | prefixSigma W k.val] π := by
              rw [hsumdef v w]
              exact hsπ
      _ = f v w *
          (if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
            then (1 : ℝ) /
              ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
            else 0) := by rw [hbπ]
  have hall : ∀ᵐ π ∂uniformPerm W, ∀ v : Fin W, ∀ w : Fin W,
      (uniformPerm W)[summand v w | prefixSigma W k.val] π =
        f v w *
          (if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
            then (1 : ℝ) /
              ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
            else 0) := by
    filter_upwards [ae_all_iff.mpr (fun v => ae_all_iff.mpr (hsingle v))] with π hπ v w
    exact hπ v w
  have hcollapse :
      (∑ v : Fin W, ∑ w : Fin W,
        (uniformPerm W)[summand v w | prefixSigma W k.val]) =ᵐ[uniformPerm W]
      (fun π =>
        (∑ v ∈ unusedImages W k π,
          ∑ w ∈ unusedImages W k π, if v ≠ w then f v w else 0) /
          ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))) := by
    filter_upwards [hall] with π hπ
    simp only [Finset.sum_apply]
    calc
      (∑ v : Fin W, ∑ w : Fin W,
          (uniformPerm W)[summand v w | prefixSigma W k.val] π)
          = ∑ v : Fin W, ∑ w : Fin W,
              if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π then
                f v w / ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
              else 0 := by
                  apply Finset.sum_congr rfl
                  intro v _
                  apply Finset.sum_congr rfl
                  intro w _
                  rw [hπ v w]
                  by_cases h : v ≠ w ∧ v ∈ unusedImages W k π ∧
                    w ∈ unusedImages W k π
                  · simp [h, div_eq_mul_inv, mul_comm]
                  · simp [h]
      _ = (∑ v ∈ unusedImages W k π,
            ∑ w ∈ unusedImages W k π, if v ≠ w then f v w else 0) /
            ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ))) := by
              let U := unusedImages W k π
              let d : ℝ :=
                ((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)
              have hpairSum (g : Fin W → Fin W → ℝ) :
                  (∑ v ∈ (Finset.univ : Finset (Fin W)),
                    ∑ w ∈ (Finset.univ : Finset (Fin W)),
                    if v ≠ w ∧ v ∈ U ∧ w ∈ U then g v w else 0) =
                  ∑ v ∈ U, ∑ w ∈ U, if v ≠ w then g v w else 0 := by
                calc
                  _ = ∑ v ∈ (Finset.univ : Finset (Fin W)),
                      ∑ w ∈ U,
                        if v ≠ w ∧ v ∈ U ∧ w ∈ U then g v w else 0 := by
                        apply Finset.sum_congr rfl
                        intro v hv
                        symm
                        apply Finset.sum_subset (by simp)
                        intro w hw hwn
                        simp [hwn]
                  _ = ∑ v ∈ U, ∑ w ∈ U, if v ≠ w then g v w else 0 := by
                        calc
                          _ = ∑ v ∈ U, ∑ w ∈ U,
                                if v ≠ w ∧ v ∈ U ∧ w ∈ U then g v w else 0 := by
                                  symm
                                  apply Finset.sum_subset (by simp)
                                  intro v hv hvn
                                  simp [hvn]
                          _ = _ := by
                                apply Finset.sum_congr rfl
                                intro v hv
                                apply Finset.sum_congr rfl
                                intro w hw
                                by_cases hne : v ≠ w <;> simp [hv, hw, hne]
              change (∑ v ∈ (Finset.univ : Finset (Fin W)),
                ∑ w ∈ (Finset.univ : Finset (Fin W)),
                if v ≠ w ∧ v ∈ U ∧ w ∈ U then f v w / d else 0) =
                (∑ v ∈ U, ∑ w ∈ U, if v ≠ w then f v w else 0) / d
              calc
                _ = ∑ v ∈ U, ∑ w ∈ U,
                      if v ≠ w then f v w / d else 0 :=
                        hpairSum (fun v w => f v w / d)
                _ = _ := by
                      calc
                        _ = ∑ v ∈ U,
                              (∑ w ∈ U, if v ≠ w then f v w else 0) / d := by
                                apply Finset.sum_congr rfl
                                intro v hv
                                rw [Finset.sum_div]
                                simp [div_eq_mul_inv]
                        _ = _ := by rw [Finset.sum_div]
  calc
    (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k) (ρ j)) | prefixSigma W k.val]
        =ᵐ[uniformPerm W]
          (uniformPerm W)[(∑ v : Fin W, ∑ w : Fin W, summand v w) |
            prefixSigma W k.val] := by
              exact condExp_congr_ae (μ := uniformPerm W) (m := prefixSigma W k.val)
                (Filter.Eventually.of_forall (fun ρ => congrFun hdecomp ρ))
    _ =ᵐ[uniformPerm W]
          ∑ v : Fin W, ∑ w : Fin W,
            (uniformPerm W)[summand v w | prefixSigma W k.val] := hcond
    _ =ᵐ[uniformPerm W]
          (fun π =>
            (∑ v ∈ unusedImages W k π,
              ∑ w ∈ unusedImages W k π, if v ≠ w then f v w else 0) /
              ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))) := hcollapse

/-- Both real factors in the ordered-pair denominator are positive for
adjacent valid indices. -/
theorem twoNextImages_weighted_condExp_denominator_pos
    (W : ℕ) (k j : Fin W) (hj : j.val = k.val + 1) :
    0 < ((W - k.val : ℕ) : ℝ) ∧ 0 < ((W - k.val - 1 : ℕ) : ℝ) :=
  twoImages_condExp_denominator_pos W k j hj

/-- Width zero has no coordinate, and width one has no adjacent valid pair. -/
theorem twoNextImages_weighted_condExp_boundary_zero : ¬ Nonempty (Fin 0) :=
  twoImages_condExp_no_index_zero

theorem twoNextImages_weighted_condExp_boundary_one :
    ¬ ∃ k j : Fin 1, j.val = k.val + 1 :=
  twoImages_condExp_no_pair_one

private def twoPointWeight (v w : Fin 2) : ℝ :=
  if v = 1 ∧ w = 0 then 1 else 0

/-- At width two, a genuinely nonconstant weight has conditional mean `1/2`.
Both ordered outcomes occur in positive atoms of the empty-prefix sigma-field. -/
theorem uniformPerm_twoNextImages_weighted_condExp_two_witness :
    twoPointWeight 0 1 = 0 ∧ twoPointWeight 1 0 = 1 ∧
    (uniformPerm 2)[(fun ρ : PermΩ 2 => twoPointWeight (ρ 0) (ρ 1)) |
      prefixSigma 2 0] =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) ∧
    0 < uniformPerm 2 {ρ | ρ = (Equiv.refl (Fin 2) : PermΩ 2)} ∧
    0 < uniformPerm 2 {ρ | ρ = (Equiv.swap 0 1 : PermΩ 2)} := by
  have hu (π : PermΩ 2) : unusedImages 2 0 π = Finset.univ := by
    ext v
    rw [mem_unusedImages_iff]
    constructor
    · intro _
      simp
    · intro _ i hi
      exact (Fin.not_lt_zero i hi).elim
  have h := uniformPerm_twoNextImages_weighted_condExp
    2 (0 : Fin 2) 1 twoPointWeight (by decide)
  have hmean (π : PermΩ 2) :
      (∑ v ∈ unusedImages 2 0 π,
        ∑ w ∈ unusedImages 2 0 π,
          if v ≠ w then twoPointWeight v w else 0) /
          ((((2 - (0 : Fin 2).val : ℕ) : ℝ) *
            ((2 - (0 : Fin 2).val - 1 : ℕ) : ℝ))) = (1 : ℝ) / 2 := by
    rw [hu π]
    norm_num [twoPointWeight]
  have hidpos :
      0 < uniformPerm 2 {ρ | ρ = (Equiv.refl (Fin 2) : PermΩ 2)} := by
    have h := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
      (Equiv.refl (Fin 2) : PermΩ 2)).2
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using h
  have hswappos :
      0 < uniformPerm 2 {ρ | ρ = (Equiv.swap 0 1 : PermΩ 2)} := by
    have h := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
      (Equiv.swap 0 1 : PermΩ 2)).2
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [twoPointWeight]
  · norm_num [twoPointWeight]
  · filter_upwards [h] with π hπ
    rw [hmean π] at hπ
    simpa using hπ
  · exact hidpos
  · exact hswappos

/-- At the last eligible adjacent pair, `k = W - 2`, the denominator is two. -/
theorem uniformPerm_twoNextImages_weighted_condExp_last
    (W : ℕ) (k j : Fin W) (f : Fin W → Fin W → ℝ)
    (hj : j.val = k.val + 1) (hlast : j.val + 1 = W) :
    (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k) (ρ j)) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π =>
      (∑ v ∈ unusedImages W k π,
        ∑ w ∈ unusedImages W k π, if v ≠ w then f v w else 0) / 2) := by
  have h := uniformPerm_twoNextImages_weighted_condExp W k j f hj
  have hden : W - k.val = 2 := by omega
  filter_upwards [h] with π hπ
  simpa [hden] using hπ

#print axioms uniformPerm_twoNextImages_weighted_condExp
#print axioms twoNextImages_weighted_condExp_denominator_pos
#print axioms twoNextImages_weighted_condExp_boundary_zero
#print axioms twoNextImages_weighted_condExp_boundary_one
#print axioms uniformPerm_twoNextImages_weighted_condExp_two_witness
#print axioms uniformPerm_twoNextImages_weighted_condExp_last

end RBM.Gauss
