/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationTwoNextImagesCell
import RBM1D.Gauss.PermutationNextImageCondExp

/-!
# Conditional expectation of two successive permutation images

The conditional expectation is computed from the exact mass of the ordered
event on each actual prefix cell.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

private def twoImagesIndicator (W : ℕ) (k j : Fin W) (v w : Fin W) :
    PermΩ W → ℝ :=
  fun ρ => if ρ k = v ∧ ρ j = w then 1 else 0

private noncomputable def twoImagesMean (W : ℕ) (k : Fin W) (v w : Fin W) :
    PermΩ W → ℝ :=
  fun π =>
    if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
    then (1 : ℝ) /
      ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
    else 0

private theorem twoImagesIndicator_integrable (W : ℕ) (k j v w : Fin W) :
    Integrable (twoImagesIndicator W k j v w) (uniformPerm W) :=
  Integrable.of_finite

private theorem twoImagesMean_integrable (W : ℕ) (k v w : Fin W) :
    Integrable (twoImagesMean W k v w) (uniformPerm W) :=
  Integrable.of_finite

private theorem twoImagesMean_aestronglyMeasurable (W : ℕ) (k v w : Fin W) :
    AEStronglyMeasurable[prefixSigma W k.val]
      (twoImagesMean W k v w) (uniformPerm W) := by
  have hv := measurableSet_unusedImage_prefixSigma W k v
  have hw := measurableSet_unusedImage_prefixSigma W k w
  have hset : MeasurableSet[prefixSigma W k.val]
      {π : PermΩ W | v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π} := by
    by_cases hne : v ≠ w
    · have heq :
          {π : PermΩ W | v ≠ w ∧ v ∈ unusedImages W k π ∧
            w ∈ unusedImages W k π} =
            {π : PermΩ W | v ∈ unusedImages W k π} ∩
              {π : PermΩ W | w ∈ unusedImages W k π} := by
          ext π
          simp [hne]
      rw [heq]
      exact hv.inter hw
    · simp [hne]
  have hm : Measurable[prefixSigma W k.val] (twoImagesMean W k v w) := by
    unfold twoImagesMean
    exact Measurable.ite hset measurable_const measurable_const
  exact hm.aestronglyMeasurable

private theorem twoImages_cell_integrals (W : ℕ) (k j v w : Fin W)
    (hj : j.val = k.val + 1) (π : PermΩ W) :
    ∫ ρ in {ρ | ρ ∈ prefixCell W k.val π},
        twoImagesMean W k v w ρ ∂uniformPerm W =
      ∫ ρ in {ρ | ρ ∈ prefixCell W k.val π},
        twoImagesIndicator W k j v w ρ ∂uniformPerm W := by
  classical
  let C : Set (PermΩ W) := {ρ | ρ ∈ prefixCell W k.val π}
  let E : Set (PermΩ W) := {ρ | ρ k = v ∧ ρ j = w}
  have hC : MeasurableSet C := MeasurableSet.of_discrete
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hleft :
      ∫ ρ in C, twoImagesMean W k v w ρ ∂uniformPerm W =
        (uniformPerm W C).toReal * twoImagesMean W k v w π := by
    have hcongr := setIntegral_congr_fun (μ := uniformPerm W) hC
      (show Set.EqOn (twoImagesMean W k v w)
        (fun _ => twoImagesMean W k v w π) C from by
        intro ρ hρ
        simp only [C, Set.mem_ofPred_eq] at hρ
        simp [twoImagesMean, unusedImages_eq_of_mem_prefixCell W k π ρ hρ])
    rw [hcongr, setIntegral_const]
    simp [measureReal_def, smul_eq_mul]
  have hright :
      ∫ ρ in C, twoImagesIndicator W k j v w ρ ∂uniformPerm W =
        (uniformPerm W (C ∩ E)).toReal := by
    have hfun : twoImagesIndicator W k j v w =
        E.indicator (fun _ => (1 : ℝ)) := by
      funext ρ
      simp [twoImagesIndicator, E, Set.indicator]
    rw [hfun, setIntegral_indicator hE, setIntegral_const]
    simp [measureReal_def, smul_eq_mul]
  change (∫ ρ in C, twoImagesMean W k v w ρ ∂uniformPerm W) =
    ∫ ρ in C, twoImagesIndicator W k j v w ρ ∂uniformPerm W
  rw [hleft, hright]
  change ((uniformPerm W) {ρ | ρ ∈ prefixCell W k.val π}).toReal *
      twoImagesMean W k v w π =
    ((uniformPerm W) {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w}).toReal
  by_cases hvalid : v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
  · rcases hvalid with ⟨hne, hv, hw⟩
    have hquot := uniformPerm_two_successiveImages_given_actualPrefix
      W k j π v w hj hv hw hne
    have hCpos := (uniformPerm_actualPrefix_event_pos_ne_top W k π).1
    have hCtop := (uniformPerm_actualPrefix_event_pos_ne_top W k π).2
    have hDpos : (0 : ℝ) <
        ((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ) := by
      have h₁ : 0 < W - k.val := by omega
      have h₂ : 0 < W - k.val - 1 := by omega
      exact mul_pos (by exact_mod_cast h₁) (by exact_mod_cast h₂)
    have hCnonzero :
        ((uniformPerm W) {ρ | ρ ∈ prefixCell W k.val π}).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hCpos, hCtop⟩
    have hreal := congrArg ENNReal.toReal hquot
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_mul,
      ENNReal.toReal_natCast] at hreal
    have hreal' := (div_eq_iff hCnonzero).mp hreal
    rw [twoImagesMean, if_pos ⟨hne, hv, hw⟩]
    calc
      _ = (1 / (((W - k.val : ℕ) : ℝ) *
          ((W - k.val - 1 : ℕ) : ℝ))) *
          ((uniformPerm W) {ρ | ρ ∈ prefixCell W k.val π}).toReal := mul_comm _ _
      _ = _ := hreal'.symm
  · have hzero : ∀ ρ : PermΩ W,
        ρ ∈ prefixCell W k.val π → ¬ (ρ k = v ∧ ρ j = w) := by
      intro ρ hρ hpair
      have hused (x : Fin W) (hx : ρ k = x ∨ ρ j = x) :
          x ∈ unusedImages W k π := by
        apply (mem_unusedImages_iff W k π x).mpr
        intro i hi hix
        have hpre : ρ i = π i := by
          exact (Finset.mem_filter.mp hρ).2 i (by exact hi)
        have hρix : ρ i = x := hpre.trans hix
        rcases hx with hkx | hjx
        · exact (Fin.ne_of_lt hi) (ρ.injective (hρix.trans hkx.symm))
        · have hi' : i ≠ j := by
            intro hij
            subst i
            omega
          exact hi' (ρ.injective (hρix.trans hjx.symm))
      have hv := hused v (Or.inl hpair.1)
      have hw := hused w (Or.inr hpair.2)
      have hne : v ≠ w := by
        intro hvw
        have hkj : k ≠ j := by
          intro hkj
          have := congrArg Fin.val hkj
          omega
        exact hkj (ρ.injective (hpair.1.trans (hvw.trans hpair.2.symm)))
      exact hvalid ⟨hne, hv, hw⟩
    have hEzero :
        uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w} = 0 := by
      have hempty :
          {ρ : PermΩ W | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w} = ∅ := by
        ext ρ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hzero ρ h.1 ⟨h.2.1, h.2.2⟩
      rw [hempty, measure_empty]
    simp [twoImagesMean, hvalid, hEzero]

private theorem twoImages_setIntegral_eq (W : ℕ) (k j v w : Fin W) (hj : j.val = k.val + 1)
    (s : Set (PermΩ W)) (hs : MeasurableSet[prefixSigma W k.val] s) :
    ∫ ρ in s, twoImagesMean W k v w ρ ∂uniformPerm W =
      ∫ ρ in s, twoImagesIndicator W k j v w ρ ∂uniformPerm W := by
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
      IntegrableOn (twoImagesMean W k v w) (C : Set (PermΩ W)) (uniformPerm W) :=
    (twoImagesMean_integrable W k v w).integrableOn
  have hfint (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      IntegrableOn (twoImagesIndicator W k j v w) (C : Set (PermΩ W)) (uniformPerm W) :=
    (twoImagesIndicator_integrable W k j v w).integrableOn
  rw [← hcover,
    integral_biUnion_finset selected hmeas hdisj hgint,
    integral_biUnion_finset selected hmeas hdisj hfint]
  apply Finset.sum_congr rfl
  intro C hC
  obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
  rw [← hπ]
  exact twoImages_cell_integrals W k j v w hj π

/-- The ordered pair of successive images has conditional probability given
by the reciprocal of the number of ordered pairs of unused images. -/
theorem uniformPerm_two_successiveImages_condExp
    (W : ℕ) (k j : Fin W) (v w : Fin W)
    (hj : j.val = k.val + 1) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v ∧ ρ j = w then (1 : ℝ) else 0) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
      then (1 : ℝ) /
        ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
      else 0) := by
  have h := ae_eq_condExp_of_forall_setIntegral_eq
    (μ := uniformPerm W) (m := prefixSigma W k.val) (m₀ := inferInstance)
    le_top (twoImagesIndicator_integrable W k j v w)
    (fun s _ _ => (twoImagesMean_integrable W k v w).integrableOn)
    (fun s hs _ => twoImages_setIntegral_eq W k j v w hj s hs)
    (twoImagesMean_aestronglyMeasurable W k v w)
  change (fun π : PermΩ W =>
      if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
      then (1 : ℝ) /
        ((((W - k.val : ℕ) : ℝ) * ((W - k.val - 1 : ℕ) : ℝ)))
      else 0) =ᵐ[uniformPerm W]
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v ∧ ρ j = w then (1 : ℝ) else 0) | prefixSigma W k.val] at h
  exact h.symm

/-- Adjacent valid indices leave at least two images, so both denominator
factors are strictly positive. -/
theorem twoImages_condExp_denominator_pos (W : ℕ) (k j : Fin W)
    (hj : j.val = k.val + 1) :
    0 < ((W - k.val : ℕ) : ℝ) ∧
      0 < ((W - k.val - 1 : ℕ) : ℝ) := by
  have hjlt := j.isLt
  constructor
  · exact_mod_cast (show 0 < W - k.val by omega)
  · exact_mod_cast (show 0 < W - k.val - 1 by omega)

/-- Width zero has no index, and width one has no adjacent valid pair. -/
theorem twoImages_condExp_no_index_zero : ¬ Nonempty (Fin 0) :=
  uniformPerm_two_successiveImages_no_index_zero

theorem twoImages_condExp_no_pair_one :
    ¬ ∃ k j : Fin 1, j.val = k.val + 1 :=
  uniformPerm_two_successiveImages_no_pair_one

/-- Both ordered events have conditional probability one half at width two.
An equal ordered pair has conditional probability zero. -/
theorem uniformPerm_two_successiveImages_condExp_two :
    (uniformPerm 2)[(fun ρ : PermΩ 2 =>
      if ρ 0 = 0 ∧ ρ 1 = 1 then (1 : ℝ) else 0) | prefixSigma 2 0]
      =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) ∧
    (uniformPerm 2)[(fun ρ : PermΩ 2 =>
      if ρ 0 = 1 ∧ ρ 1 = 0 then (1 : ℝ) else 0) | prefixSigma 2 0]
      =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) ∧
    (uniformPerm 2)[(fun ρ : PermΩ 2 =>
      if ρ 0 = 0 ∧ ρ 1 = 0 then (1 : ℝ) else 0) | prefixSigma 2 0]
      =ᵐ[uniformPerm 2] (fun _ => (0 : ℝ)) := by
  have hu (x : Fin 2) (π : PermΩ 2) :
      x ∈ unusedImages 2 0 π := by
    apply (mem_unusedImages_iff 2 0 π x).mpr
    intro i hi
    exact (Fin.not_lt_zero i hi).elim
  refine ⟨?_, ?_, ?_⟩
  · simpa [hu, show (0 : Fin 2) ≠ 1 by decide] using
      uniformPerm_two_successiveImages_condExp 2 0 1 0 1 (by decide)
  · simpa [hu, show (1 : Fin 2) ≠ 0 by decide] using
      uniformPerm_two_successiveImages_condExp 2 0 1 1 0 (by decide)
  · simpa using
      uniformPerm_two_successiveImages_condExp 2 0 1 0 0 (by decide)

/-- The first ordered event at width two is nonempty, proper, and has
positive mass; its conditioning cell also has positive mass. -/
theorem twoImages_condExp_two_nondegenerate :
    (Equiv.refl (Fin 2) : PermΩ 2) ∈
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
        ρ 0 = 0 ∧ ρ 1 = 1} ∧
    (Equiv.swap 0 1 : PermΩ 2) ∉
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
        ρ 0 = 0 ∧ ρ 1 = 1} ∧
    0 < uniformPerm 2
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
        ρ 0 = 0 ∧ ρ 1 = 1} ∧
    0 < uniformPerm 2
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} := by
  obtain ⟨_, _, hid, _, hcell, hnum, _⟩ :=
    uniformPerm_two_successiveImages_two_witness
  refine ⟨hid, ?_, hnum, hcell⟩
  simp [prefixCell]

/-- At the last eligible pair, each valid ordering has mass one half
conditional on the already revealed prefix. -/
theorem uniformPerm_two_successiveImages_condExp_last
    (W : ℕ) (k j : Fin W) (v w : Fin W)
    (hj : j.val = k.val + 1) (hlast : j.val + 1 = W) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v ∧ ρ j = w then (1 : ℝ) else 0) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      if v ≠ w ∧ v ∈ unusedImages W k π ∧ w ∈ unusedImages W k π
      then (1 : ℝ) / 2 else 0) := by
  have hk : W - k.val = 2 := by omega
  simpa [hk] using uniformPerm_two_successiveImages_condExp W k j v w hj

#print axioms uniformPerm_two_successiveImages_condExp
#print axioms twoImages_condExp_denominator_pos
#print axioms twoImages_condExp_no_index_zero
#print axioms twoImages_condExp_no_pair_one
#print axioms uniformPerm_two_successiveImages_condExp_two
#print axioms twoImages_condExp_two_nondegenerate
#print axioms uniformPerm_two_successiveImages_condExp_last

end RBM.Gauss
