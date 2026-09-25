/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationPrefixSigmaAtom
import RBM1D.Gauss.PermutationPrefixCellMass
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
The conditional expectation of any real function on a finite uniform
permutation space is its average on the actual prefix cell.
This is a finite auxiliary result, not a paper local-law assertion.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

/-- The real average of `F` on the actual prefix cell containing `π`. -/
noncomputable def prefixCellMean (W k : ℕ) (F : PermΩ W → ℝ) : PermΩ W → ℝ :=
  fun π => (∑ ρ ∈ prefixCell W k π, F ρ) / (prefixCell W k π).card

private theorem prefixCellMean_eq_of_mem (W k : ℕ) (F : PermΩ W → ℝ)
    (π ρ : PermΩ W) (hρ : ρ ∈ prefixCell W k π) :
    prefixCellMean W k F ρ = prefixCellMean W k F π := by
  have hc : prefixCell W k ρ = prefixCell W k π :=
    (prefixCell_eq_iff_agree W k ρ π).2 (by
      intro i hi
      simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
      exact hρ i hi)
  simp [prefixCellMean, hc]

private theorem prefixCellMean_measurable (W k : ℕ) (F : PermΩ W → ℝ) :
    Measurable[prefixSigma W k] (prefixCellMean W k F) := by
  classical
  change ∀ ⦃s : Set ℝ⦄, MeasurableSet s →
    MeasurableSet[prefixSigma W k] ((prefixCellMean W k F) ⁻¹' s)
  intro s hs
  let cellUnion : Set (PermΩ W) :=
    ⋃ π : {π : PermΩ W // prefixCellMean W k F π ∈ s},
      (prefixCell W k π.1 : Set (PermΩ W))
  have hEq : (prefixCellMean W k F) ⁻¹' s = cellUnion := by
    ext ρ
    simp only [cellUnion, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨⟨ρ, h⟩, mem_prefixCell W k ρ⟩
    · rintro ⟨π, hρ⟩
      have hval := prefixCellMean_eq_of_mem W k F π.1 ρ hρ
      simpa [hval] using π.2
  rw [hEq]
  apply MeasurableSet.iUnion
  intro π
  exact measurableSet_prefixCell W k π.1

private theorem prefixCellMean_integrable (W k : ℕ) (F : PermΩ W → ℝ) :
    Integrable (prefixCellMean W k F) (uniformPerm W) :=
  Integrable.of_finite

private theorem prefixCellMean_aestronglyMeasurable (W k : ℕ)
    (F : PermΩ W → ℝ) :
    AEStronglyMeasurable[prefixSigma W k] (prefixCellMean W k F) (uniformPerm W) :=
  (prefixCellMean_measurable W k F).aestronglyMeasurable

private theorem prefixCellF_integrable (W k : ℕ) (F : PermΩ W → ℝ) :
    Integrable F (uniformPerm W) := Integrable.of_finite

private theorem prefixCell_mean_integral (W k : ℕ) (F : PermΩ W → ℝ)
    (π : PermΩ W) :
    ∫ ρ in {ρ | ρ ∈ prefixCell W k π}, prefixCellMean W k F ρ ∂uniformPerm W =
      ∫ ρ in {ρ | ρ ∈ prefixCell W k π}, F ρ ∂uniformPerm W := by
  classical
  let C : Finset (PermΩ W) := prefixCell W k π
  have hC : MeasurableSet (C : Set (PermΩ W)) := Finset.measurableSet C
  have hmean : ∀ ρ ∈ C, prefixCellMean W k F ρ = prefixCellMean W k F π := by
    intro ρ hρ
    exact prefixCellMean_eq_of_mem W k F π ρ hρ
  have hleft := setIntegral_finset C
    ((prefixCellMean_integrable W k F).integrableOn)
  have hright := setIntegral_finset C ((prefixCellF_integrable W k F).integrableOn)
  -- The finite uniform measure assigns the same mass to every point.
  have hsingle (ρ : PermΩ W) : (uniformPerm W {ρ}).toReal =
      (1 : ℝ) / Fintype.card (PermΩ W) := by
    rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
  have hleft' :
      (∫ ρ in (C : Set (PermΩ W)), prefixCellMean W k F ρ ∂uniformPerm W) =
        ∑ ρ ∈ C, (1 / (Fintype.card (PermΩ W) : ℝ)) * prefixCellMean W k F π := by
    calc
      (∫ ρ in (C : Set (PermΩ W)), prefixCellMean W k F ρ ∂uniformPerm W) =
          ∑ ρ ∈ C, (1 / (Fintype.card (PermΩ W) : ℝ)) *
            prefixCellMean W k F ρ := by
        simpa only [measureReal_def, hsingle, smul_eq_mul] using hleft
      _ = ∑ ρ ∈ C, (1 / (Fintype.card (PermΩ W) : ℝ)) *
            prefixCellMean W k F π := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [hmean ρ hρ]
  have hright' :
      (∫ ρ in (C : Set (PermΩ W)), F ρ ∂uniformPerm W) =
        ∑ ρ ∈ C, (1 / (Fintype.card (PermΩ W) : ℝ)) * F ρ := by
    simpa only [measureReal_def, hsingle, smul_eq_mul] using hright
  have hsum : (∑ ρ ∈ C, F ρ) = (C.card : ℝ) * prefixCellMean W k F π := by
    rw [prefixCellMean, show prefixCell W k π = C from rfl]
    have hpos : (0 : ℝ) < C.card := by
      exact_mod_cast prefixCell_card_pos W k π
    field_simp
  have hCset : {ρ | ρ ∈ prefixCell W k π} = (C : Set (PermΩ W)) := by
    ext ρ
    rfl
  rw [hCset, hleft', hright']
  calc
    (∑ ρ ∈ C, (1 / (Fintype.card (PermΩ W) : ℝ)) * prefixCellMean W k F π) =
        (1 / (Fintype.card (PermΩ W) : ℝ)) * (C.card : ℝ) *
          prefixCellMean W k F π := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      ring
    _ = (1 / (Fintype.card (PermΩ W) : ℝ)) *
          ((C.card : ℝ) * prefixCellMean W k F π) := by ring
    _ = (1 / (Fintype.card (PermΩ W) : ℝ)) * (∑ ρ ∈ C, F ρ) := by
      rw [← hsum]
    _ = ∑ ρ ∈ C, (1 / (Fintype.card (PermΩ W) : ℝ)) * F ρ := by
      rw [← Finset.mul_sum]

private theorem prefixCell_setIntegral_eq (W k : ℕ) (F : PermΩ W → ℝ)
    (s : Set (PermΩ W)) (hs : MeasurableSet[prefixSigma W k] s) :
    ∫ ρ in s, prefixCellMean W k F ρ ∂uniformPerm W =
      ∫ ρ in s, F ρ ∂uniformPerm W := by
  classical
  let cells : Finset (Finset (PermΩ W)) := Finset.univ.image (prefixCell W k)
  let selected : Finset (Finset (PermΩ W)) :=
    cells.filter (fun C => (C : Set (PermΩ W)) ⊆ s)
  have hcell_sub (π : PermΩ W) (hπ : π ∈ s) :
      (prefixCell W k π : Set (PermΩ W)) ⊆ s := by
    letI : MeasurableSpace (PermΩ W) := prefixSigma W k
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
      refine ⟨prefixCell W k ρ, ?_, mem_prefixCell W k ρ⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨ρ, Finset.mem_univ _, rfl⟩
      · exact hcell_sub ρ hρ
  have hdisj : Set.Pairwise (↑selected : Set (Finset (PermΩ W)))
      (fun C D => Disjoint (C : Set (PermΩ W)) (D : Set (PermΩ W))) := by
    intro C hC D hD hne
    obtain ⟨π, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hD).1
    rcases (prefixCell_partition W k).2 π τ with heq | hd
    · exact False.elim (hne heq)
    · exact Finset.disjoint_coe.mpr hd
  have hmeas (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      MeasurableSet (C : Set (PermΩ W)) := Finset.measurableSet C
  have hgint (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      IntegrableOn (prefixCellMean W k F) (C : Set (PermΩ W)) (uniformPerm W) :=
    (prefixCellMean_integrable W k F).integrableOn
  have hfint (C : Finset (PermΩ W)) (_ : C ∈ selected) :
      IntegrableOn F (C : Set (PermΩ W)) (uniformPerm W) :=
    (prefixCellF_integrable W k F).integrableOn
  rw [← hcover,
    integral_biUnion_finset selected hmeas hdisj hgint,
    integral_biUnion_finset selected hmeas hdisj hfint]
  apply Finset.sum_congr rfl
  intro C hC
  obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
  rw [← hπ]
  exact prefixCell_mean_integral W k F π

/-- Under a uniform random finite permutation, the conditional expectation of
any real function is its average on the actual cell determined by the revealed
prefix. The average is defined using the positive cardinality of that cell. -/
theorem uniformPerm_prefixCell_condExp (W k : ℕ) (F : PermΩ W → ℝ) :
    (uniformPerm W)[F | prefixSigma W k]
      =ᵐ[uniformPerm W] prefixCellMean W k F := by
  have h := ae_eq_condExp_of_forall_setIntegral_eq
    (μ := uniformPerm W) (m := prefixSigma W k) (m₀ := inferInstance)
    le_top (prefixCellF_integrable W k F)
    (fun s _ _ => (prefixCellMean_integrable W k F).integrableOn)
    (fun s hs _ => prefixCell_setIntegral_eq W k F s hs)
    (prefixCellMean_aestronglyMeasurable W k F)
  exact h.symm

/-- After all positions have been revealed, conditional expectation agrees
almost everywhere with the original function. -/
theorem uniformPerm_prefixCell_condExp_of_width_le (W k : ℕ) (hWk : W ≤ k)
    (F : PermΩ W → ℝ) :
    (uniformPerm W)[F | prefixSigma W k] =ᵐ[uniformPerm W] F := by
  filter_upwards [uniformPerm_prefixCell_condExp W k F] with π hπ
  simpa [prefixCellMean, prefixCell_eq_singleton_of_width_le W k hWk] using hπ

/-- At prefix length zero, conditional expectation is the full-space mean. -/
theorem uniformPerm_prefixCell_condExp_zero (W : ℕ) (F : PermΩ W → ℝ) :
    (uniformPerm W)[F | prefixSigma W 0] =ᵐ[uniformPerm W]
      fun _ => (∑ ρ, F ρ) / Fintype.card (PermΩ W) := by
  filter_upwards [uniformPerm_prefixCell_condExp W 0 F] with π hπ
  simpa [prefixCellMean, prefixCell_eq_univ_of_zero] using hπ

/-- If no positions are revealed, the conditional average is the full-space
mean and is constant in the sample point. -/
theorem prefixCellMean_zero (W : ℕ) (F : PermΩ W → ℝ) (π : PermΩ W) :
    prefixCellMean W 0 F π = (∑ ρ, F ρ) / Fintype.card (PermΩ W) := by
  simp [prefixCellMean, prefixCell_eq_univ_of_zero]

/-- Revealing the full permutation determines the function pointwise. -/
theorem prefixCellMean_eq_of_width_le (W k : ℕ) (hWk : W ≤ k)
    (F : PermΩ W → ℝ) (π : PermΩ W) : prefixCellMean W k F π = F π := by
  simp [prefixCellMean, prefixCell_eq_singleton_of_width_le W k hWk]

/-- Width zero has the unique constant conditional average, at every prefix. -/
theorem prefixCellMean_zero_width (k : ℕ) (F : PermΩ 0 → ℝ) (π : PermΩ 0) :
    prefixCellMean 0 k F π = F π := by
  have hcell : prefixCell 0 k π = {π} := by
    ext ρ
    simp only [Finset.mem_singleton]
    constructor
    · intro _
      exact Subsingleton.elim (ρ : PermΩ 0) π
    · intro h
      subst ρ
      exact mem_prefixCell 0 k π
  simp [prefixCellMean, hcell]

/-- Width one has the same singleton average for every prefix. -/
theorem prefixCellMean_one (k : ℕ) (F : PermΩ 1 → ℝ) (π : PermΩ 1) :
    prefixCellMean 1 k F π = F π := by
  have hcell : prefixCell 1 k π = {π} := by
    ext ρ
    simp only [Finset.mem_singleton]
    constructor
    · intro _
      exact Subsingleton.elim (ρ : PermΩ 1) π
    · intro h
      subst ρ
      exact mem_prefixCell 1 k π
  simp [prefixCellMean, hcell]

private theorem uniformPerm_singleton_pos (W : ℕ) (π : PermΩ W) :
    0 < uniformPerm W {π} := by
  rw [uniformPerm, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
  apply ENNReal.div_pos
  · norm_num
  · exact ENNReal.natCast_ne_top _

/-- Every width-two zero-prefix cell has mean one half for the indicator of
the identity permutation. -/
theorem prefixCellMean_two_zero_indicator_all (π : PermΩ 2) :
    prefixCellMean 2 0
      (fun ρ => if ρ = (Equiv.refl (Fin 2) : PermΩ 2) then 1 else 0) π = 1 / 2 := by
  simp [prefixCellMean, prefixCell_eq_univ_of_zero, Fintype.card_perm]

/-- The width-two identity indicator has constant conditional mean one half
before any coordinate is revealed. -/
theorem uniformPerm_prefixCell_condExp_two_zero_indicator :
    (uniformPerm 2)[(fun ρ : PermΩ 2 =>
      if ρ = (Equiv.refl (Fin 2) : PermΩ 2) then 1 else 0) | prefixSigma 2 0]
      =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) := by
  filter_upwards [uniformPerm_prefixCell_condExp 2 0
    (fun ρ : PermΩ 2 => if ρ = (Equiv.refl (Fin 2) : PermΩ 2) then 1 else 0)]
    with π hπ
  simpa [prefixCellMean_two_zero_indicator_all] using hπ

/-- At width two and prefix zero, the identity indicator has two positive
atoms and its cell average is one half. -/
theorem prefixCellMean_two_zero_indicator :
    prefixCellMean 2 0
      (fun ρ => if ρ = (Equiv.refl (Fin 2) : PermΩ 2) then 1 else 0)
      (Equiv.refl (Fin 2)) = 1 / 2 ∧
      prefixCell 2 0 (Equiv.refl (Fin 2)) = Finset.univ ∧
      (Equiv.refl (Fin 2) : PermΩ 2) ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
      (Equiv.swap 0 1 : PermΩ 2) ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
      (Equiv.swap 0 1 : PermΩ 2) ≠ Equiv.refl (Fin 2) ∧
      0 < uniformPerm 2 {(Equiv.refl (Fin 2) : PermΩ 2)} ∧
      0 < uniformPerm 2 {(Equiv.swap 0 1 : PermΩ 2)} := by
  classical
  refine ⟨?_, prefixCell_eq_univ_of_zero .., mem_prefixCell .., ?_, ?_, ?_, ?_⟩
  · simp [prefixCellMean, prefixCell_eq_univ_of_zero, Fintype.card_perm]
  · simp [prefixCell]
  · exact (by decide : (Equiv.swap (0 : Fin 2) 1 : PermΩ 2) ≠ Equiv.refl (Fin 2))
  · exact uniformPerm_singleton_pos 2 _
  · exact uniformPerm_singleton_pos 2 _

#print axioms uniformPerm_prefixCell_condExp
#print axioms uniformPerm_prefixCell_condExp_of_width_le
#print axioms uniformPerm_prefixCell_condExp_zero
#print axioms uniformPerm_prefixCell_condExp_two_zero_indicator
#print axioms prefixCellMean_zero
#print axioms prefixCellMean_eq_of_width_le
#print axioms prefixCellMean_zero_width
#print axioms prefixCellMean_one
#print axioms prefixCellMean_two_zero_indicator

end RBM.Gauss
