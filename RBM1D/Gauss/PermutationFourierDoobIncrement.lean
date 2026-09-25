/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFiberMeanRange
import RBM1D.Gauss.PermutationPrefixCellFiberBridge
import RBM1D.Gauss.PermutationPrefixCellCard
import RBM1D.Gauss.PermutationNextImageUniformCell

/-!
# Pointwise increments of actual Fourier prefix-cell means

The means below are normalized finite sums over the actual prefix cells.  The
proof partitions a positive prefix cell into its positive next-image fibers,
then averages the accepted fiber-mean range estimate.
-/

namespace RBM.Gauss

private noncomputable def prefixCellNextImageSigmaEquiv (W : ℕ) (k : Fin W)
    (π : PermΩ W) : (Σ v : Fin W, prefixCellNextFiber W k π v) ≃
      {ρ : PermΩ W // ρ ∈ prefixCell W k.val π} where
  toFun x := ⟨x.2.1, x.2.2.1⟩
  invFun x := ⟨x.1 k, ⟨x.1, x.2, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨v, ⟨ρ, hcell, hnext⟩⟩
    dsimp
    subst v
    rfl
  right_inv x := by cases x; rfl

/-- Sum partition of an actual prefix cell by its next image. -/
private theorem prefixCell_sum_eq_sum_all_nextFibers (W : ℕ) (k : Fin W)
    (π : PermΩ W) (f : PermΩ W → ℂ) :
    (∑ ρ ∈ prefixCell W k.val π, f ρ) =
      ∑ v : Fin W, ∑ ρ : prefixCellNextFiber W k π v, f ρ.1 := by
  classical
  let e := prefixCellNextImageSigmaEquiv W k π
  calc
    (∑ ρ ∈ prefixCell W k.val π, f ρ) =
        ∑ ρ : {ρ : PermΩ W // ρ ∈ prefixCell W k.val π}, f ρ.1 := by
          exact Finset.sum_subtype (prefixCell W k.val π)
            (by intro ρ; simp [prefixCell]) f
    _ = ∑ x : Σ v : Fin W, prefixCellNextFiber W k π v, f (e x).1 := by
          exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = ∑ v : Fin W, ∑ ρ : prefixCellNextFiber W k π v, f ρ.1 := by
          rw [Fintype.sum_sigma]
          rfl

/-- A used image has an empty next-image fiber. -/
private theorem nextFiber_card_eq_zero_of_not_unused (W : ℕ) (k : Fin W)
    (π : PermΩ W) (v : Fin W) (hv : v ∉ unusedImages W k π) :
    Fintype.card (prefixCellNextFiber W k π v) = 0 := by
  classical
  have hnot : ¬ ∀ i : Fin W, i < k → π i ≠ v := by
    simpa [mem_unusedImages_iff] using hv
  push Not at hnot
  obtain ⟨i, hi, hiv⟩ := hnot
  exact prefixCellNextFiber_card_zero_of_used W k π v i hi hiv

/-- Restrict the sum partition to the unused images, whose fibers are positive. -/
private theorem prefixCell_sum_eq_sum_unused_nextFibers (W : ℕ) (k : Fin W)
    (π : PermΩ W) (f : PermΩ W → ℂ) :
    (∑ ρ ∈ prefixCell W k.val π, f ρ) =
      ∑ v ∈ unusedImages W k π,
        ∑ ρ : prefixCellNextFiber W k π v, f ρ.1 := by
  classical
  rw [prefixCell_sum_eq_sum_all_nextFibers]
  unfold unusedImages
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with hused
  · rfl
  · have hnot : v ∉ unusedImages W k π := by
      intro hu
      exact hused ((mem_unusedImages_iff W k π v).mp hu)
    have hcard := nextFiber_card_eq_zero_of_not_unused W k π v hnot
    have hempty : IsEmpty (prefixCellNextFiber W k π v) := Fintype.card_eq_zero_iff.mp hcard
    letI := hempty
    simp

/-- The next actual prefix cell is precisely the fiber of the revealed image. -/
private theorem prefixCell_succ_eq_nextFiber (W : ℕ) (k : Fin W) (π : PermΩ W) :
    prefixCell W (k.val + 1) π =
      Finset.univ.filter (fun ρ : PermΩ W =>
        ρ ∈ prefixCell W k.val π ∧ ρ k = π k) := by
  classical
  ext ρ
  simp only [prefixCell, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    constructor
    · intro i hi
      exact h i (by omega)
    · exact h k (by simp)
  · rintro ⟨hpre, hk⟩ i hi
    by_cases hik : i = k
    · simpa [hik] using hk
    · exact hpre i (by omega)

/-- Actual finite average of the Fourier observable on the prefix cell. -/
noncomputable def prefixFourierMean (W j : ℕ) (x χ : Fin W → ℂ)
    (π : PermΩ W) : ℂ :=
  (∑ ρ ∈ prefixCell W j π, permutationFourierSum W x χ ρ) /
    ((prefixCell W j π).card : ℂ)

private noncomputable def nextFiberFourierMean (W : ℕ) (k : Fin W)
    (x χ : Fin W → ℂ) (π : PermΩ W) (v : Fin W) : ℂ :=
  (∑ ρ : prefixCellNextFiber W k π v, permutationFourierSum W x χ ρ.1) /
    (Fintype.card (prefixCellNextFiber W k π v) : ℂ)

private theorem nextFiberFourierMean_range (W : ℕ) (hW : 2 ≤ W)
    (k : Fin W) (x χ : Fin W → ℂ) (hx : ∀ i, ‖x i‖ ≤ 2)
    (hχ : ∀ i, ‖χ i‖ ≤ 1) (π : PermΩ W) {a b : Fin W}
    (ha : a ∈ unusedImages W k π) (hb : b ∈ unusedImages W k π) :
    ‖nextFiberFourierMean W k x χ π a -
      nextFiberFourierMean W k x χ π b‖ ≤ 8 / (W : ℝ) := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [sub_self, norm_zero]
    positivity
  have hpos := prefixCellNextFiber_card_pos_of_unused W k π a ha
  have hpos' : 0 < Fintype.card (permutationPrefixFiber W k (fun i => π i) a) := by
    rw [← prefixCellNextFiber_card_eq]
    exact hpos
  have hmean := norm_permutationFourierSum_prefixFiber_mean_sub_le W hW k
    (fun i => π i) a b hab
    ((mem_unusedImages_iff W k π a).mp ha)
    ((mem_unusedImages_iff W k π b).mp hb) hpos' x χ hx hχ
  have hA := Fintype.sum_equiv (prefixCellNextFiberEquiv W k π a)
    (fun ρ : prefixCellNextFiber W k π a =>
      permutationFourierSum W x χ ρ.1)
    (fun ρ : permutationPrefixFiber W k (fun i => π i) a =>
      permutationFourierSum W x χ ρ.1) (fun _ => rfl)
  have hB := Fintype.sum_equiv (prefixCellNextFiberEquiv W k π b)
    (fun ρ : prefixCellNextFiber W k π b =>
      permutationFourierSum W x χ ρ.1)
    (fun ρ : permutationPrefixFiber W k (fun i => π i) b =>
      permutationFourierSum W x χ ρ.1) (fun _ => rfl)
  rw [← hA, ← hB, ← prefixCellNextFiber_card_eq,
    ← prefixCellNextFiber_card_eq] at hmean
  simpa [nextFiberFourierMean] using hmean

/-- Pointwise `8/W` bound for the actual finite prefix-cell Fourier means. -/
theorem norm_permutationFourierSum_actualPrefix_increment_le
    (W : ℕ) (hW : 2 ≤ W) (k : Fin W) (x χ : Fin W → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ 2) (hχ : ∀ i, ‖χ i‖ ≤ 1) (π : PermΩ W) :
    ‖prefixFourierMean W (k.val + 1) x χ π - prefixFourierMean W k.val x χ π‖ ≤
      8 / (W : ℝ) := by
  classical
  let U := unusedImages W k π
  let m := U.card
  let n := Fintype.card (prefixCellNextFiber W k π (π k))
  have hU : 0 < m := by
    dsimp [m, U]
    rw [unusedImages_card]
    exact Nat.sub_pos_of_lt k.isLt
  have hπU : π k ∈ U := by
    apply (mem_unusedImages_iff W k π (π k)).mpr
    intro i hi he
    exact (ne_of_lt hi) (π.injective he)
  have hn : 0 < n := by
    dsimp [n]
    exact prefixCellNextFiber_card_pos_of_unused W k π (π k) hπU
  have hcard : (prefixCell W k.val π).card = m * n := by
    have hmul := prefixCell_card_eq_unused_mul_fiber W k π (π k) hπU
    rw [← unusedImages_card W k π] at hmul
    simpa [m, n, U] using hmul
  have hfiber_eq (v : Fin W) (hv : v ∈ U) :
      Fintype.card (prefixCellNextFiber W k π v) = n := by
    dsimp [n]
    exact prefixCellNextFiber_card_eq_of_unused W k π v (π k) hv hπU
  let eSucc : {ρ : PermΩ W // ρ ∈ prefixCell W (k.val + 1) π} ≃
      prefixCellNextFiber W k π (π k) := {
    toFun := fun ρ => by
      rcases ρ with ⟨ρ, hρ⟩
      have hp : ∀ i : Fin W, i.val ≤ k.val → ρ i = π i := by
        simpa [prefixCell] using hρ
      refine ⟨ρ, ?_⟩
      constructor
      · have hpre : ∀ i : Fin W, i.val < k.val → ρ i = π i := by
          intro i hi
          exact hp i (by omega)
        simpa [prefixCell] using hpre
      · exact hp k le_rfl
    invFun := fun ρ => by
      rcases ρ with ⟨ρ, ⟨hcell, hk⟩⟩
      have hp : ∀ i : Fin W, i.val < k.val → ρ i = π i := by
        simpa [prefixCell] using hcell
      refine ⟨ρ, ?_⟩
      have hgoal : ∀ i : Fin W, i.val ≤ k.val → ρ i = π i := by
        intro i hi
        by_cases hik : i = k
        · subst i
          exact hk
        · exact hp i (by omega)
      simpa [prefixCell] using hgoal
    left_inv := by intro ρ; cases ρ; rfl
    right_inv := by
      intro ρ
      rcases ρ with ⟨ρ, ⟨hcell, hk⟩⟩
      apply Subtype.ext
      rfl
  }
  have hsuccessorSum :
      (∑ ρ ∈ prefixCell W (k.val + 1) π,
        permutationFourierSum W x χ ρ) =
      ∑ ρ : prefixCellNextFiber W k π (π k),
        permutationFourierSum W x χ ρ.1 := by
    rw [Finset.sum_subtype (prefixCell W (k.val + 1) π)
      (by intro ρ; rfl)]
    exact Fintype.sum_equiv eSucc _ _ (fun _ => rfl)
  have hprefixSum :
      (∑ ρ ∈ prefixCell W k.val π, permutationFourierSum W x χ ρ) =
        ∑ v ∈ U, ∑ ρ : prefixCellNextFiber W k π v,
          permutationFourierSum W x χ ρ.1 := by
    exact prefixCell_sum_eq_sum_unused_nextFibers W k π _
  have hprefixMean : prefixFourierMean W k.val x χ π =
      (∑ v ∈ U, nextFiberFourierMean W k x χ π v) / (m : ℂ) := by
    rw [prefixFourierMean, hprefixSum, hcard]
    have hmeanSum :
        (∑ v ∈ U, nextFiberFourierMean W k x χ π v) =
          (∑ v ∈ U, ∑ ρ : prefixCellNextFiber W k π v,
            permutationFourierSum W x χ ρ.1) / (n : ℂ) := by
      simp only [nextFiberFourierMean]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hfiber_eq v hv]
    rw [hmeanSum]
    push_cast
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hU)
    field_simp
  have hnextMean : prefixFourierMean W (k.val + 1) x χ π =
      nextFiberFourierMean W k x χ π (π k) := by
    rw [prefixFourierMean, hsuccessorSum]
    have hcard' : (prefixCell W (k.val + 1) π).card =
        Fintype.card (prefixCellNextFiber W k π (π k)) := by
      simpa using Fintype.card_congr eSucc
    rw [hcard']
    rfl
  have hdiff :
      prefixFourierMean W (k.val + 1) x χ π - prefixFourierMean W k.val x χ π =
        ∑ v ∈ U,
          (nextFiberFourierMean W k x χ π (π k) -
            nextFiberFourierMean W k x χ π v) / (m : ℂ) := by
    rw [hnextMean, hprefixMean]
    have hsumIdentity :
        (∑ v ∈ U,
          (nextFiberFourierMean W k x χ π (π k) -
            nextFiberFourierMean W k x χ π v) / (m : ℂ)) =
          ((m : ℂ) * nextFiberFourierMean W k x χ π (π k) -
            ∑ v ∈ U, nextFiberFourierMean W k x χ π v) / (m : ℂ) := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      simp [m, U]
    rw [hsumIdentity]
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hU)
    field_simp
  rw [hdiff]
  calc
    ‖∑ v ∈ U,
        (nextFiberFourierMean W k x χ π (π k) -
          nextFiberFourierMean W k x χ π v) / (m : ℂ)‖ ≤
      ∑ v ∈ U,
        ‖(nextFiberFourierMean W k x χ π (π k) -
          nextFiberFourierMean W k x χ π v) / (m : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ U, (8 / (W : ℝ)) / (m : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right
        (nextFiberFourierMean_range W hW k x χ hx hχ π hπU hv)
        (by positivity)
    _ = 8 / (W : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hU
      have hmEq : (m : ℝ) * ((8 / (W : ℝ)) / (m : ℝ)) = 8 / (W : ℝ) :=
        mul_div_cancel₀ _ (ne_of_gt hmR)
      simpa [m, mul_comm] using hmEq

/-- The final reveal does not change the actual prefix-cell mean. -/
theorem prefixFourierMean_last_eq (W : ℕ) (k : Fin W)
    (x χ : Fin W → ℂ) (π : PermΩ W) (hk : k.val + 1 = W) :
    prefixFourierMean W (k.val + 1) x χ π =
      prefixFourierMean W k.val x χ π := by
  classical
  have hcard : (prefixCell W k.val π).card = 1 := by
    rw [prefixCell_card_eq_factorial, Nat.min_eq_left (Nat.le_of_lt k.isLt)]
    rw [show W - k.val = 1 by omega]
    norm_num
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hπ : π ∈ prefixCell W k.val π := mem_prefixCell W k.val π
  have hπa : π = a := by simpa [ha] using hπ
  have hpre : prefixCell W k.val π = {π} := by simpa [hπa] using ha
  have hlast : prefixCell W (k.val + 1) π = {π} := by
    rw [hk]
    exact prefixCell_eq_singleton_of_width_le W W le_rfl π
  simp [prefixFourierMean, hpre, hlast]

private noncomputable def permFinTwoEquiv : PermΩ 2 ≃ Fin 2 where
  toFun σ := σ 0
  invFun i := if i = 0 then Equiv.refl _ else Equiv.swap 0 1
  left_inv σ := by
    rcases Fin.eq_zero_or_eq_succ (σ 0) with hzero | ⟨j, hj⟩
    · have hne : σ 1 ≠ (0 : Fin 2) := by
        intro h10
        have hneq : (0 : Fin 2) ≠ 1 := by decide
        exact hneq (σ.injective (hzero.trans h10.symm))
      have hone : σ 1 = 1 := by
        rcases Fin.eq_zero_or_eq_succ (σ 1) with h | ⟨j, hj⟩
        · exact (hne h).elim
        · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
          subst j
          simpa using hj
      apply Equiv.ext
      intro i
      fin_cases i
      · change (if σ 0 = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1) 0 = σ 0
        rw [hzero]
        rfl
      · change (if σ 0 = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1) 1 = σ 1
        rw [hzero]
        simpa using hone.symm
    · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      have hone : σ 0 = 1 := by simpa using hj
      have hne : σ 1 ≠ (1 : Fin 2) := by
        intro h11
        have hneq : (1 : Fin 2) ≠ 0 := by decide
        exact hneq ((σ.injective (hone.trans h11.symm)).symm)
      have hzero' : σ 1 = 0 := by
        rcases Fin.eq_zero_or_eq_succ (σ 1) with h | ⟨j, hj⟩
        · exact h
        · have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
          subst j
          exact (hne (by simpa using hj)).elim
      apply Equiv.ext
      intro i
      fin_cases i
      · change (if σ 0 = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1) 0 = σ 0
        rw [hone]
        simp
      · change (if σ 0 = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1) 1 = σ 1
        rw [hone]
        simpa using hzero'.symm
  right_inv i := by
    fin_cases i <;> simp

/-- An explicit actual-prefix example at width two has a nonzero first
increment: `M₀ = 0` and `M₁ = 2` for the identity permutation. -/
theorem prefixFourierMean_two_nonconstant_witness :
    ∃ x χ : Fin 2 → ℂ,
      (∀ i, ‖x i‖ ≤ 2) ∧ (∀ i, ‖χ i‖ ≤ 1) ∧
      prefixFourierMean 2 0 x χ (Equiv.refl _) = 0 ∧
      prefixFourierMean 2 1 x χ (Equiv.refl _) = 2 := by
  classical
  let x : Fin 2 → ℂ := fun i => if i = 0 then 2 else -2
  let χ : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  have hx : ∀ i, ‖x i‖ ≤ 2 := by
    intro i
    fin_cases i <;> norm_num [x]
  have hχ : ∀ i, ‖χ i‖ ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [χ]
  have hId : permutationFourierSum 2 x χ (Equiv.refl _) = 2 := by
    norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ]
  have hSwap : permutationFourierSum 2 x χ (Equiv.swap 0 1) = -2 := by
    norm_num [permutationFourierSum, Fin.sum_univ_two, x, χ,
      Equiv.swap_apply_def]
  have hsum : (∑ ρ : PermΩ 2, permutationFourierSum 2 x χ ρ) = 0 := by
    have h := Fintype.sum_equiv permFinTwoEquiv.symm
      (fun i : Fin 2 => permutationFourierSum 2 x χ (permFinTwoEquiv.symm i))
      (fun ρ : PermΩ 2 => permutationFourierSum 2 x χ ρ) (fun _ => rfl)
    rw [← h]
    simp [Fin.sum_univ_two, permFinTwoEquiv, hId, hSwap]
  have hcard0 : (prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2)).card = 2 := by
    rw [prefixCell_eq_univ_of_zero]
    have h := Fintype.card_congr permFinTwoEquiv
    simpa using h
  have hsum0 :
      (∑ ρ ∈ prefixCell 2 0 (Equiv.refl (Fin 2) : PermΩ 2),
        permutationFourierSum 2 x χ ρ) = 0 := by
    rw [prefixCell_eq_univ_of_zero]
    rw [Finset.sum_subtype (Finset.univ : Finset (PermΩ 2)) (by intro ρ; rfl)]
    exact hsum
  have hcell1 : prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2) =
      {Equiv.refl (Fin 2)} := by
    have hc : (prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2)).card = 1 := by
      rw [prefixCell_card_eq_factorial, Nat.min_eq_left (by decide : 1 ≤ 2)]
      norm_num
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hmem := mem_prefixCell 2 1 (Equiv.refl (Fin 2) : PermΩ 2)
    have hEq : (Equiv.refl (Fin 2) : PermΩ 2) = a := by simpa [ha] using hmem
    simpa [hEq] using ha
  refine ⟨x, χ, hx, hχ, ?_, ?_⟩
  · simp [prefixFourierMean, hsum0, hcard0]
  · simp [prefixFourierMean, hcell1, hId]

#print axioms prefixFourierMean
#print axioms norm_permutationFourierSum_actualPrefix_increment_le
#print axioms prefixFourierMean_last_eq
#print axioms prefixFourierMean_two_nonconstant_witness

end RBM.Gauss
