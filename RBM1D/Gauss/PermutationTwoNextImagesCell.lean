/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageUniformCell

/-!
# Two successive images on an actual permutation prefix cell

The event quotient is obtained by refining a positive actual prefix cell one
image at a time. This is a finite event identity, not a conditional law.
-/

open MeasureTheory ProbabilityTheory

namespace RBM.Gauss

/-- The actual prefix cell after fixing one unused image is precisely the
corresponding one-image event in the preceding actual prefix cell. -/
private theorem prefixCell_succ_eq_nextImage_event (W : ℕ) (k j : Fin W)
    (π : PermΩ W) (v : Fin W) (hj : j.val = k.val + 1)
    (π₁ : PermΩ W) (hπ₁ : π₁ ∈ prefixCell W k.val π ∧ π₁ k = v) :
    prefixCell W j.val π₁ =
      Finset.univ.filter (fun ρ : PermΩ W =>
        ρ ∈ prefixCell W k.val π ∧ ρ k = v) := by
  classical
  ext ρ
  simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and]
  have hprefix : ∀ i : Fin W, i.val < k.val → π₁ i = π i := by
    intro i hi
    have hmem : ∀ i : Fin W, i.val < k.val → π₁ i = π i := by
      simpa [prefixCell] using hπ₁.1
    exact hmem i hi
  constructor
  · intro h
    constructor
    · intro i hi
      have hρ := h i (by omega)
      exact hρ.trans (hprefix i (by omega))
    · have hρ := h k (by omega)
      exact hρ.trans hπ₁.2
  · rintro ⟨hcell, hρk⟩ i hi
    by_cases hik : i.val < k.val
    · have hcell' : ∀ i : Fin W, i.val < k.val → ρ i = π i := by
        simpa [prefixCell] using hcell
      have hρ := hcell' i hik
      exact hρ.trans (hprefix i hik).symm
    · have hieq : i = k := Fin.ext (by omega)
      subst i
      exact hρk.trans hπ₁.2.symm

/-- Exact probability of two distinct successive unused images, conditional
on a positive actual-prefix cell. -/
theorem uniformPerm_two_successiveImages_given_actualPrefix
    (W : ℕ) (k j : Fin W) (π : PermΩ W) (v w : Fin W)
    (hj : j.val = k.val + 1)
    (hv : v ∈ unusedImages W k π)
    (hw : w ∈ unusedImages W k π) (hne : v ≠ w) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
        (1 : ENNReal) /
          (((W - k.val : ℕ) : ENNReal) *
            ((W - k.val - 1 : ℕ) : ENNReal)) := by
  have hv' : ∀ i : Fin W, i < k → π i ≠ v :=
    (mem_unusedImages_iff W k π v).mp hv
  have hw' : ∀ i : Fin W, i < k → π i ≠ w :=
    (mem_unusedImages_iff W k π w).mp hw
  have hfirst := prefixCellNextFiber_card_pos_of_unused W k π v hv
  obtain ⟨x, hx⟩ := Fintype.card_pos_iff.mp hfirst
  let π₁ : PermΩ W := x
  have hcell₁ : π₁ ∈ prefixCell W k.val π ∧ π₁ k = v := hx
  have hrefine := prefixCell_succ_eq_nextImage_event W k j π v hj π₁ hcell₁
  have hw₁ : w ∈ unusedImages W j π₁ := by
    apply (mem_unusedImages_iff W j π₁ w).mpr
    intro i hij hiw
    have hival : i.val < k.val ∨ i.val = k.val := by omega
    rcases hival with hlt | heq
    · have hprefix := (Finset.mem_filter.mp hcell₁.1).2 i (by omega)
      exact hw' i (Fin.lt_def.mpr hlt) (hprefix.symm.trans hiw)
    · have hi : i = k := Fin.ext heq
      subst i
      exact hne (hcell₁.2.symm.trans hiw)
  have hBpos := (uniformPerm_actualPrefix_event_pos_ne_top W j π₁).1
  have hBtop := (uniformPerm_actualPrefix_event_pos_ne_top W j π₁).2
  have hApos := (uniformPerm_actualPrefix_event_pos_ne_top W k π).1
  have hquot₁ := uniformPerm_nextImage_given_actualPrefix W k π v hv'
  have hquot₂ := uniformPerm_nextImage_given_actualPrefix W j π₁ w
    ((mem_unusedImages_iff W j π₁ w).mp hw₁)
  have hB : uniformPerm W {ρ | ρ ∈ prefixCell W j.val π₁} =
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v} := by
    congr 1
    ext ρ
    rw [hrefine]
    simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and]
  have hC : uniformPerm W {ρ | ρ ∈ prefixCell W j.val π₁ ∧ ρ j = w} =
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w} := by
    congr 1
    ext ρ
    rw [hrefine]
    simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    tauto
  have hA : uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} := rfl
  calc
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w} /
        uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
      uniformPerm W {ρ | ρ ∈ prefixCell W j.val π₁ ∧ ρ j = w} /
        uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} := by rw [hC]
    _ =
      (uniformPerm W {ρ | ρ ∈ prefixCell W j.val π₁ ∧ ρ j = w} /
        uniformPerm W {ρ | ρ ∈ prefixCell W j.val π₁}) *
      (uniformPerm W {ρ | ρ ∈ prefixCell W j.val π₁} /
        uniformPerm W {ρ | ρ ∈ prefixCell W k.val π}) := by
          exact (ENNReal.div_mul_div_cancel (ne_of_gt hBpos) hBtop).symm
    _ = ((1 : ENNReal) / ((W - j.val : ℕ) : ENNReal)) *
        ((1 : ENNReal) / ((W - k.val : ℕ) : ENNReal)) := by
          rw [hquot₂, hB, hquot₁]
    _ = (1 : ENNReal) /
        (((W - k.val : ℕ) : ENNReal) *
          ((W - k.val - 1 : ℕ) : ENNReal)) := by
          have hsub : W - j.val = W - k.val - 1 := by omega
          rw [hsub]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          simp only [one_mul]
          have hAposNat : 0 < W - k.val := Nat.sub_pos_of_lt k.isLt
          have hBposNat : 0 < W - k.val - 1 := by omega
          have hAne : ((W - k.val : ℕ) : ENNReal) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hAposNat)
          have hBne : ((W - k.val - 1 : ℕ) : ENNReal) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hBposNat)
          have hBfinite := ENNReal.natCast_ne_top (W - k.val - 1)
          have hAfin := ENNReal.natCast_ne_top (W - k.val)
          calc
            (((W - k.val - 1 : ℕ) : ENNReal)⁻¹) *
                (((W - k.val : ℕ) : ENNReal)⁻¹) =
              (((W - k.val : ℕ) : ENNReal)⁻¹) *
                (((W - k.val - 1 : ℕ) : ENNReal)⁻¹) := mul_comm _ _
            _ = (((W - k.val : ℕ) : ENNReal) *
                ((W - k.val - 1 : ℕ) : ENNReal))⁻¹ :=
              (ENNReal.mul_inv (Or.inr hBfinite) (Or.inl hAfin)).symm
            _ = 1 / (((W - k.val : ℕ) : ENNReal) *
                ((W - k.val - 1 : ℕ) : ENNReal)) := by rw [one_div]


/-- Width zero has no first reveal index, and width one has no two adjacent
valid reveal indices. -/
theorem uniformPerm_two_successiveImages_no_index_zero : ¬ Nonempty (Fin 0) :=
  no_next_index_zero

theorem uniformPerm_two_successiveImages_no_pair_one :
    ¬ ∃ k j : Fin 1, j.val = k.val + 1 := by
  rintro ⟨k, j, hj⟩
  have hk := k.isLt
  have hj' := j.isLt
  omega

/-- At the last eligible pair of reveals, the two-step quotient is one half. -/
theorem uniformPerm_two_successiveImages_last
    (W : ℕ) (k j : Fin W) (π : PermΩ W) (v w : Fin W)
    (hj : j.val = k.val + 1) (hlast : j.val + 1 = W)
    (hv : v ∈ unusedImages W k π)
    (hw : w ∈ unusedImages W k π) (hne : v ≠ w) :
    uniformPerm W {ρ | ρ ∈ prefixCell W k.val π ∧ ρ k = v ∧ ρ j = w} /
      uniformPerm W {ρ | ρ ∈ prefixCell W k.val π} =
        (1 : ENNReal) / 2 := by
  rw [uniformPerm_two_successiveImages_given_actualPrefix W k j π v w hj hv hw hne]
  have hk2 : W - k.val = 2 := by omega
  norm_num [hk2]

/-- The two ordered outcomes at width two each have half the empty-prefix
cell mass; identity and transposition witness their nonempty events. -/
theorem uniformPerm_two_successiveImages_two_witness :
    uniformPerm 2
        {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
          ρ 0 = 0 ∧ ρ 1 = 1} /
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} =
        (1 : ENNReal) / 2 ∧
    uniformPerm 2
        {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧
          ρ 0 = 1 ∧ ρ 1 = 0} /
      uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} =
        (1 : ENNReal) / 2 ∧
    (Equiv.refl (Fin 2) : PermΩ 2) ∈
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧ ρ 0 = 0 ∧ ρ 1 = 1} ∧
    (Equiv.swap 0 1 : PermΩ 2) ∈
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧ ρ 0 = 1 ∧ ρ 1 = 0} ∧
    0 < uniformPerm 2 {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2))} ∧
    0 < uniformPerm 2
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧ ρ 0 = 0 ∧ ρ 1 = 1} ∧
    0 < uniformPerm 2
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧ ρ 0 = 1 ∧ ρ 1 = 0} := by
  have huv (v : Fin 2) : v ∈ unusedImages 2 0 (Equiv.refl (Fin 2)) := by
    apply (mem_unusedImages_iff 2 0 (Equiv.refl (Fin 2)) v).mpr
    intro i hi
    exact (Fin.not_lt_zero i hi).elim
  have h01 := uniformPerm_two_successiveImages_given_actualPrefix 2 0 1
    (Equiv.refl (Fin 2)) 0 1 (by decide) (huv 0) (huv 1) (by decide)
  have h10 := uniformPerm_two_successiveImages_given_actualPrefix 2 0 1
    (Equiv.refl (Fin 2)) 1 0 (by decide) (huv 1) (huv 0) (by decide)
  have hcellpos := (uniformPerm_actualPrefix_event_pos_ne_top 2 0
    (Equiv.refl (Fin 2))).1
  have hAtomId : 0 < uniformPerm 2
      {ρ | ρ = (Equiv.refl (Fin 2) : PermΩ 2)} := by
    have h := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
      (Equiv.refl (Fin 2) : PermΩ 2)).2
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using h
  have hAtomSwap : 0 < uniformPerm 2
      {ρ | ρ = (Equiv.swap 0 1 : PermΩ 2)} := by
    have h := (uniformPerm_prefixCell_full_mass_pos 2 2 (by omega)
      (Equiv.swap 0 1 : PermΩ 2)).2
    simpa [prefixCell_eq_singleton_of_width_le 2 2 (by omega)] using h
  have hnum01 : 0 < uniformPerm 2
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧ ρ 0 = 0 ∧ ρ 1 = 1} := by
    apply lt_of_lt_of_le hAtomId
    apply measure_mono
    intro ρ hρ
    simp only [Set.mem_ofPred_eq] at hρ
    subst ρ
    simp [prefixCell]
  have hnum10 : 0 < uniformPerm 2
      {ρ | ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2)) ∧ ρ 0 = 1 ∧ ρ 1 = 0} := by
    apply lt_of_lt_of_le hAtomSwap
    apply measure_mono
    intro ρ hρ
    simp only [Set.mem_ofPred_eq] at hρ
    subst ρ
    simp [prefixCell]
  refine ⟨?_, ?_, ?_, ?_, hcellpos, hnum01, hnum10⟩
  · simpa using h01
  · simpa using h10
  · simp [prefixCell]
  · simp [prefixCell]

#print axioms uniformPerm_two_successiveImages_given_actualPrefix
#print axioms uniformPerm_two_successiveImages_no_index_zero
#print axioms uniformPerm_two_successiveImages_no_pair_one
#print axioms uniformPerm_two_successiveImages_last
#print axioms uniformPerm_two_successiveImages_two_witness

end RBM.Gauss
