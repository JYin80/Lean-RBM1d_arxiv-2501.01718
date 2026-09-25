/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageUniformCell
import RBM1D.Gauss.PermutationPrefixSigmaAtom
import RBM1D.Gauss.PermutationUnusedImageMeasurable
import RBM1D.Gauss.PermutationUnusedImagesPrefixStable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectation of the next image under a uniform permutation

The real-valued conditional expectation is determined almost everywhere by
the unused images at the revealed prefix. This is a finite auxiliary result.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

private def nextImageIndicator (W : ℕ) (k : Fin W) (v : Fin W) : PermΩ W → ℝ :=
  fun ρ => if ρ k = v then 1 else 0

private noncomputable def nextImageMean (W : ℕ) (k : Fin W) (v : Fin W) : PermΩ W → ℝ :=
  fun π => if v ∈ unusedImages W k π then 1 / ((W - k.val : ℕ) : ℝ) else 0

private theorem nextImageIndicator_integrable (W : ℕ) (k v : Fin W) :
    Integrable (nextImageIndicator W k v) (uniformPerm W) :=
  Integrable.of_finite

private theorem nextImageMean_integrable (W : ℕ) (k v : Fin W) :
    Integrable (nextImageMean W k v) (uniformPerm W) :=
  Integrable.of_finite

private theorem nextImageMean_aestronglyMeasurable (W : ℕ) (k v : Fin W) :
    AEStronglyMeasurable[prefixSigma W k.val]
      (nextImageMean W k v) (uniformPerm W) := by
  have hset := measurableSet_unusedImage_prefixSigma W k v
  have hm : Measurable[prefixSigma W k.val] (nextImageMean W k v) := by
    unfold nextImageMean
    exact Measurable.ite hset measurable_const measurable_const
  exact hm.aestronglyMeasurable

private theorem nextImage_cell_integrals (W : ℕ) (k v : Fin W) (π : PermΩ W) :
    ∫ ρ in {ρ | ρ ∈ prefixCell W k.val π}, nextImageMean W k v ρ ∂uniformPerm W =
      ∫ ρ in {ρ | ρ ∈ prefixCell W k.val π}, nextImageIndicator W k v ρ ∂uniformPerm W := by
  classical
  let C : Set (PermΩ W) := {ρ | ρ ∈ prefixCell W k.val π}
  let E : Set (PermΩ W) := {ρ | ρ k = v}
  have hC : MeasurableSet C := MeasurableSet.of_discrete
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hleft :
      ∫ ρ in C, nextImageMean W k v ρ ∂uniformPerm W =
        (uniformPerm W C).toReal * nextImageMean W k v π := by
    have hcongr := setIntegral_congr_fun (μ := uniformPerm W) hC
      (show Set.EqOn (nextImageMean W k v)
        (fun _ => nextImageMean W k v π) C from by
        intro ρ hρ
        simp only [C, Set.mem_ofPred_eq] at hρ
        simp [nextImageMean, unusedImages_eq_of_mem_prefixCell W k π ρ hρ])
    rw [hcongr, setIntegral_const]
    simp [measureReal_def, smul_eq_mul]
  have hright :
      ∫ ρ in C, nextImageIndicator W k v ρ ∂uniformPerm W =
        (uniformPerm W (C ∩ E)).toReal := by
    have hfun : nextImageIndicator W k v = E.indicator (fun _ => (1 : ℝ)) := by
      funext ρ
      simp [nextImageIndicator, E, Set.indicator]
    rw [hfun, setIntegral_indicator hE, setIntegral_const]
    simp [measureReal_def, smul_eq_mul]
  change (∫ ρ in C, nextImageMean W k v ρ ∂uniformPerm W) =
    ∫ ρ in C, nextImageIndicator W k v ρ ∂uniformPerm W
  rw [hleft, hright]
  change ((uniformPerm W) {ρ | ρ ∈ prefixCell W k.val π}).toReal *
      nextImageMean W k v π =
    ((uniformPerm W) {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v}).toReal
  by_cases hv : v ∈ unusedImages W k π
  · have hcard := prefixCell_card_eq_unused_mul_fiber W k π v hv
    have hN : (0 : ℝ) < (W - k.val : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt k.isLt
    have hT : (0 : ℝ) < Fintype.card (PermΩ W) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (PermΩ W))
    rw [uniformPerm_nextImage_event, uniformPerm_prefixCell_event]
    simp only [nextImageMean, if_pos hv, ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [hcard]
    push_cast
    field_simp
  · have hzero : Fintype.card (prefixCellNextFiber W k π v) = 0 := by
      have hnot : ¬ ∀ i : Fin W, i < k → π i ≠ v := by
        simpa [mem_unusedImages_iff] using hv
      push Not at hnot
      obtain ⟨i, hi, hiv⟩ := hnot
      exact prefixCellNextFiber_card_zero_of_used W k π v i hi hiv
    rw [uniformPerm_nextImage_event]
    simp [nextImageMean, hv, hzero]

private theorem nextImage_setIntegral_eq (W : ℕ) (k v : Fin W)
    (s : Set (PermΩ W)) (hs : MeasurableSet[prefixSigma W k.val] s) :
    ∫ ρ in s, nextImageMean W k v ρ ∂uniformPerm W =
      ∫ ρ in s, nextImageIndicator W k v ρ ∂uniformPerm W := by
  classical
  let cells : Finset (Finset (PermΩ W)) :=
    Finset.univ.image (prefixCell W k.val)
  let selected : Finset (Finset (PermΩ W)) :=
    cells.filter (fun C => (C : Set (PermΩ W)) ⊆ s)
  have hcell_sub (π : PermΩ W) (hπ : π ∈ s) :
      (prefixCell W k.val π : Set (PermΩ W)) ⊆ s := by
    letI : MeasurableSpace (PermΩ W) := prefixSigma W k.val
    intro ρ hρ
    have hρatom : ρ ∈ measurableAtom π := by
      rw [measurableAtom_prefixSigma_eq_prefixCell]
      exact hρ
    exact measurableAtom_subset hs hπ hρatom
  have hcover : (⋃ C ∈ selected, (C : Set (PermΩ W))) = s := by
    ext ρ
    simp only [Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨C, hC, hρ⟩
      exact (Finset.mem_filter.mp hC).2 hρ
    · intro hρ
      refine ⟨prefixCell W k.val ρ, ?_, mem_prefixCell W k.val ρ⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨ρ, Finset.mem_univ _, rfl⟩
      · exact hcell_sub ρ hρ
  have hdisj : Set.Pairwise (↑selected : Set (Finset (PermΩ W)))
      (fun C D => Disjoint (C : Set (PermΩ W)) (D : Set (PermΩ W))) := by
    intro C hC D hD hne
    obtain ⟨π, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hD).1
    rcases (prefixCell_partition W k.val).2 π τ with heq | hd
    · exact False.elim (hne heq)
    · exact Finset.disjoint_coe.mpr hd
  have hmeas (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      MeasurableSet (C : Set (PermΩ W)) := Finset.measurableSet C
  have hgint (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      IntegrableOn (nextImageMean W k v) (C : Set (PermΩ W)) (uniformPerm W) :=
    (nextImageMean_integrable W k v).integrableOn
  have hfint (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      IntegrableOn (nextImageIndicator W k v) (C : Set (PermΩ W)) (uniformPerm W) :=
    (nextImageIndicator_integrable W k v).integrableOn
  rw [← hcover,
    integral_biUnion_finset selected hmeas hdisj hgint,
    integral_biUnion_finset selected hmeas hdisj hfint]
  apply Finset.sum_congr rfl
  intro C hC
  obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
  rw [← hπ]
  exact nextImage_cell_integrals W k v π

/-- Given a uniformly random finite permutation, the conditional expectation
of the indicator of the next image is the reciprocal of the number of unused
images on the event that the requested image remains unused. -/
theorem uniformPerm_nextImage_condExp
    (W : ℕ) (k : Fin W) (v : Fin W) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v then (1 : ℝ) else 0) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      if v ∈ unusedImages W k π
      then (1 : ℝ) / ((W - k.val : ℕ) : ℝ) else 0) := by
  have h := ae_eq_condExp_of_forall_setIntegral_eq
    (μ := uniformPerm W) (m := prefixSigma W k.val) (m₀ := inferInstance)
    le_top (nextImageIndicator_integrable W k v)
    (fun s _ _ => (nextImageMean_integrable W k v).integrableOn)
    (fun s hs _ => nextImage_setIntegral_eq W k v s hs)
    (nextImageMean_aestronglyMeasurable W k v)
  change (fun π : PermΩ W =>
      if v ∈ unusedImages W k π
      then (1 : ℝ) / ((W - k.val : ℕ) : ℝ) else 0)
      =ᵐ[uniformPerm W]
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v then (1 : ℝ) else 0) | prefixSigma W k.val] at h
  exact h.symm

/-- Width zero has no valid next-image coordinate. -/
theorem uniformPerm_nextImage_condExp_no_index_zero : ¬ Nonempty (Fin 0) :=
  no_next_index_zero

/-- Before the sole reveal at width one, the next image has conditional
probability one. -/
theorem uniformPerm_nextImage_condExp_one :
    (uniformPerm 1)[(fun ρ : PermΩ 1 =>
      if ρ 0 = 0 then (1 : ℝ) else 0) | prefixSigma 1 0]
      =ᵐ[uniformPerm 1] (fun _ => (1 : ℝ)) := by
  simpa [unusedImages] using
    uniformPerm_nextImage_condExp 1 (0 : Fin 1) (0 : Fin 1)

/-- At width two with no coordinate revealed, both distinct next images
have conditional probability one half. -/
theorem uniformPerm_nextImage_condExp_two :
    (uniformPerm 2)[(fun ρ : PermΩ 2 =>
      if ρ 0 = 0 then (1 : ℝ) else 0) | prefixSigma 2 0]
        =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) ∧
      (uniformPerm 2)[(fun ρ : PermΩ 2 =>
        if ρ 0 = 1 then (1 : ℝ) else 0) | prefixSigma 2 0]
        =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) ∧
      (0 : Fin 2) ≠ 1 := by
  refine ⟨?_, ?_, by decide⟩
  · simpa [unusedImages] using
      uniformPerm_nextImage_condExp 2 (0 : Fin 2) (0 : Fin 2)
  · simpa [unusedImages] using
      uniformPerm_nextImage_condExp 2 (0 : Fin 2) (1 : Fin 2)

/-- At the last valid reveal, the unique unused image has conditional
probability one and every used image has conditional probability zero. -/
theorem uniformPerm_nextImage_condExp_last (W : ℕ) (k v : Fin W)
    (hk : k.val + 1 = W) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v then (1 : ℝ) else 0) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W => if v ∈ unusedImages W k π then (1 : ℝ) else 0) := by
  have h : W - k.val = 1 := by omega
  simpa [h] using uniformPerm_nextImage_condExp W k v

#print axioms uniformPerm_nextImage_condExp
#print axioms uniformPerm_nextImage_condExp_no_index_zero
#print axioms uniformPerm_nextImage_condExp_one
#print axioms uniformPerm_nextImage_condExp_two
#print axioms uniformPerm_nextImage_condExp_last

end RBM.Gauss
