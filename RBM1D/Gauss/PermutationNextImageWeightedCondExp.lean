/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageFinsetCondExp

/-!
# Conditional expectation of a weighted next image

For a uniform permutation, the conditional expectation of a deterministic
function of the next image is its average over the images not yet revealed.
The proof expands the function into a finite sum of singleton indicators and
uses the already established singleton conditional expectation.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

/-- Conditional expectation of a deterministic function of the next image,
given all images before its index. -/
theorem uniformPerm_nextImage_weighted_condExp
    (W : ℕ) (k : Fin W) (f : Fin W → ℝ) :
    (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k)) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ)) := by
  classical
  let indicator : Fin W → PermΩ W → ℝ :=
    fun v ρ => if ρ k = v then (1 : ℝ) else 0
  let summand : Fin W → PermΩ W → ℝ :=
    fun v ρ => if ρ k = v then f v else 0
  have hsumdef (v : Fin W) : summand v = f v • indicator v := by
    funext ρ
    simp [summand, indicator, smul_eq_mul, mul_ite]
  have hdecomp : (fun ρ : PermΩ W => f (ρ k)) = ∑ v : Fin W, summand v := by
    funext ρ
    simp only [summand, indicator, Finset.sum_apply]
    simp [Finset.sum_ite_eq', eq_comm]
  have hcond :
      (uniformPerm W)[∑ v : Fin W, summand v | prefixSigma W k.val]
        =ᵐ[uniformPerm W]
      ∑ v : Fin W,
        (uniformPerm W)[summand v | prefixSigma W k.val] := by
    simpa using
      (condExp_finsetSum
        (μ := uniformPerm W) (s := Finset.univ) (f := summand)
        (fun v _ => Integrable.of_finite) (prefixSigma W k.val))
  have hcondInput := condExp_congr_ae
    (μ := uniformPerm W) (m := prefixSigma W k.val)
    (Filter.Eventually.of_forall (fun ρ => congrFun hdecomp ρ))
  have hsingle : ∀ v : Fin W,
      (uniformPerm W)[summand v | prefixSigma W k.val] =ᵐ[uniformPerm W]
        (fun π => f v * (if v ∈ unusedImages W k π
          then (1 : ℝ) / ((W - k.val : ℕ) : ℝ) else 0)) := by
    intro v
    have hs := condExp_smul (μ := uniformPerm W)
      (m := prefixSigma W k.val) (c := f v) (indicator v)
    have hb := uniformPerm_nextImage_condExp W k v
    filter_upwards [hs, hb] with π hsπ hbπ
    calc
      (uniformPerm W)[summand v | prefixSigma W k.val] π
          = f v * (uniformPerm W)[indicator v | prefixSigma W k.val] π := by
              rw [hsumdef v]
              exact hsπ
      _ = f v * (if v ∈ unusedImages W k π
            then (1 : ℝ) / ((W - k.val : ℕ) : ℝ) else 0) := by rw [hbπ]
  have hall : ∀ᵐ π ∂uniformPerm W, ∀ v : Fin W,
      (uniformPerm W)[summand v | prefixSigma W k.val] π =
        f v * (if v ∈ unusedImages W k π
          then (1 : ℝ) / ((W - k.val : ℕ) : ℝ) else 0) :=
    ae_all_iff.2 hsingle
  have hcollapse :
      (∑ v : Fin W,
        (uniformPerm W)[summand v | prefixSigma W k.val]) =ᵐ[uniformPerm W]
        (fun π =>
          (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ)) := by
    filter_upwards [hall] with π hπ
    simp only [Finset.sum_apply]
    calc
      (∑ v : Fin W, (uniformPerm W)[summand v | prefixSigma W k.val] π)
          = ∑ v : Fin W,
              if v ∈ unusedImages W k π then
                f v / ((W - k.val : ℕ) : ℝ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro v _
                  rw [hπ v]
                  by_cases hv : v ∈ unusedImages W k π <;>
                    simp [hv, div_eq_mul_inv, mul_comm]
      _ = ∑ v ∈ (Finset.univ.filter
              (fun v : Fin W => v ∈ unusedImages W k π)),
              f v / ((W - k.val : ℕ) : ℝ) := by
                rw [← Finset.sum_filter]
      _ = ∑ v ∈ unusedImages W k π,
              f v / ((W - k.val : ℕ) : ℝ) := by
                have hu : Finset.univ.filter
                    (fun v : Fin W => v ∈ unusedImages W k π) =
                    unusedImages W k π := by ext v; simp
                rw [hu]
      _ = (∑ v ∈ unusedImages W k π, f v) /
              ((W - k.val : ℕ) : ℝ) := by rw [Finset.sum_div]
  calc
    (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k)) | prefixSigma W k.val]
        =ᵐ[uniformPerm W]
          (uniformPerm W)[∑ v : Fin W, summand v | prefixSigma W k.val] :=
            hcondInput
    _ =ᵐ[uniformPerm W]
          ∑ v : Fin W, (uniformPerm W)[summand v | prefixSigma W k.val] := hcond
    _ =ᵐ[uniformPerm W]
          (fun π =>
            (∑ v ∈ unusedImages W k π, f v) / ((W - k.val : ℕ) : ℝ)) := hcollapse

/-- Width zero has no valid next-image index. -/
theorem uniformPerm_nextImage_weighted_condExp_no_index_zero : ¬ Nonempty (Fin 0) :=
  no_next_index_zero

/-- At width one, the next image is deterministic. -/
theorem uniformPerm_nextImage_weighted_condExp_one (f : Fin 1 → ℝ) :
    (uniformPerm 1)[(fun ρ : PermΩ 1 => f (ρ 0)) | prefixSigma 1 0]
      =ᵐ[uniformPerm 1] (fun _ => f 0) := by
  have h := uniformPerm_nextImage_weighted_condExp 1 (0 : Fin 1) f
  have hu (π : PermΩ 1) : unusedImages 1 0 π = {0} := by
    ext v
    fin_cases v <;> simp [unusedImages]
  filter_upwards [h] with π hπ
  simpa [hu π] using hπ

/-- A nonconstant function on two points gives a nontrivial width-two
instance of the weighted conditional expectation formula. -/
theorem uniformPerm_nextImage_weighted_condExp_two_witness :
    (fun v : Fin 2 => if v = 0 then (0 : ℝ) else 1) 0 ≠
        (fun v : Fin 2 => if v = 0 then (0 : ℝ) else 1) 1 ∧
      (0 : ℝ) < (2 - (0 : Fin 2).val : ℕ) ∧
      (uniformPerm 2)[(fun ρ : PermΩ 2 =>
        (if ρ 0 = 0 then (0 : ℝ) else 1)) | prefixSigma 2 0]
        =ᵐ[uniformPerm 2]
      (fun π =>
        (∑ v ∈ unusedImages 2 0 π,
          (if v = 0 then (0 : ℝ) else 1)) / (2 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simpa using uniformPerm_nextImage_weighted_condExp 2 (0 : Fin 2)
    (fun v => if v = 0 then (0 : ℝ) else 1)

/-- On the last valid reveal the weighted formula reduces to the value at the
unique unused image. -/
theorem uniformPerm_nextImage_weighted_condExp_last (W : ℕ) (k : Fin W)
    (f : Fin W → ℝ) (hk : k.val + 1 = W) :
    (uniformPerm W)[(fun ρ : PermΩ W => f (ρ k)) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π => ∑ v ∈ unusedImages W k π, f v) := by
  have h := uniformPerm_nextImage_weighted_condExp W k f
  have hden : (W - k.val : ℕ) = 1 := by omega
  filter_upwards [h] with π hπ
  simpa [hden] using hπ

/-- The denominator in the weighted conditional expectation is positive at
every valid index. -/
theorem uniformPerm_nextImage_weighted_condExp_denominator_pos
    (W : ℕ) (k : Fin W) : 0 < ((W - k.val : ℕ) : ℝ) := by
  exact_mod_cast Nat.sub_pos_of_lt k.isLt

#print axioms uniformPerm_nextImage_weighted_condExp
#print axioms uniformPerm_nextImage_weighted_condExp_no_index_zero
#print axioms uniformPerm_nextImage_weighted_condExp_one
#print axioms uniformPerm_nextImage_weighted_condExp_two_witness
#print axioms uniformPerm_nextImage_weighted_condExp_last
#print axioms uniformPerm_nextImage_weighted_condExp_denominator_pos

end RBM.Gauss
