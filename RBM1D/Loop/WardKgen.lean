/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.WardGeneral
import RBM1D.Loop.TreeRepGeneral

/-!
# Ward's identity and cyclic invariance for the primitive loop itself

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.6 without hypotheses.

`RBM.ward_of_isPrimitive` and `RBM.isPrimitive_rot` hold for any solution of Definition 2.12
with bounded `2`-loops.  Lemma 3.4 (`RBM.isPrimitive_Kgen`, `RBM.norm_Kgen_two_le`) provides
such a solution, the tree representation `Kgen`, and by uniqueness it is *the* primitive loop.
So both statements hold for `K = Kgen` with `m = m^{(E)}`, `|E| < 2`, for every `0 ≤ t < 1`,
with no further assumption.

## Main results

* `RBM.Kgen_rot`        : `K_{t, rot(σ,a)} = K_{t,σ,a}`
* `RBM.ward_Kgen`       : **Lemma 3.6, (3.13)**,
  `∑_x K_{t,(+,μ,-),(a',x)} = (K_{t,(+,μ),a'} - K_{t,(-,μ),a'}) / (2 W i η_t)`
-/

namespace RBM

open LoopIdx

section RotateGood


theorem eq_cons_dropLast_tail (l : List Bool) (hl : 2 ≤ l.length) :
    l = l[0]'(by omega) :: l.tail.dropLast ++ [l[l.length - 1]'(by omega)] := by
  rcases l with _ | ⟨a, t⟩
  · simp at hl
  · have ht : t ≠ [] := by
      rintro rfl
      simp at hl
    simp only [List.getElem_cons_zero, List.tail_cons, List.length_cons, Nat.add_sub_cancel,
      List.cons_append, List.cons.injEq, true_and]
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    congr 2
    rw [List.getLast_eq_getElem]
    rcases t with _ | ⟨b, t'⟩
    · exact absurd rfl ht
    · simp

/-- A cyclic charge list with both charges has a cyclic pair `σ[i] = -`, `σ[i+1 mod n] = +`. -/
theorem exists_false_true (σ : List Bool) (ht : true ∈ σ) (hf : false ∈ σ) :
    ∃ i, ∃ hi : i < σ.length, σ[i] = false ∧
      σ[(i + 1) % σ.length]'(Nat.mod_lt _ (by omega)) = true := by
  have hn : 0 < σ.length := List.length_pos_of_mem ht
  by_contra hno
  push Not at hno
  obtain ⟨i0, hi0, hi0f⟩ := List.mem_iff_getElem.mp hf
  have hall : ∀ k, σ[(i0 + k) % σ.length]'(Nat.mod_lt _ hn) = false := by
    intro k
    induction k with
    | zero => simp [Nat.mod_eq_of_lt hi0, hi0f]
    | succ k ih =>
      have h := hno _ (Nat.mod_lt _ hn) ih
      have e : ((i0 + k) % σ.length + 1) % σ.length = (i0 + (k + 1)) % σ.length := by
        rw [← Nat.add_assoc, Nat.add_mod (i0 + k) 1, Nat.add_mod ((i0 + k) % σ.length) 1,
          Nat.mod_mod]
      simp only [e, ne_eq, Bool.not_eq_true] at h
      exact h
  obtain ⟨j, hj, hjt⟩ := List.mem_iff_getElem.mp ht
  have := hall (j + σ.length - i0)
  have e : (i0 + (j + σ.length - i0)) % σ.length = j := by
    rw [show i0 + (j + σ.length - i0) = j + σ.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  simp only [e] at this
  rw [hjt] at this
  exact absurd this (by decide)

/-- A cyclic charge list with both charges has a rotation `(+, μ, -)`. -/
theorem exists_rotate_true_false (σ : List Bool) (ht : true ∈ σ) (hf : false ∈ σ) :
    ∃ r μ, σ.rotate r = true :: μ ++ [false] := by
  obtain ⟨i, hi, hfi, hti⟩ := exists_false_true σ ht hf
  have hn : 2 ≤ σ.length := by
    by_contra h
    have h1 : σ.length = 1 := by have := List.length_pos_of_mem ht; omega
    simp only [h1, Nat.mod_one] at hti
    have : i = 0 := by omega
    subst this
    rw [hfi] at hti
    exact absurd hti (by decide)
  set r := (i + 1) % σ.length with hr
  have hlen : (σ.rotate r).length = σ.length := List.length_rotate _ _
  have h0 : (σ.rotate r)[0]'(by omega) = true := by
    rw [List.getElem_rotate]
    simp only [zero_add, hr, Nat.mod_mod]
    exact hti
  have hlast : (σ.rotate r)[(σ.rotate r).length - 1]'(by omega) = false := by
    rw [List.getElem_rotate]
    have e : ((σ.rotate r).length - 1 + r) % σ.length = i := by
      rw [hlen, hr]
      rcases Nat.lt_or_ge (i + 1) σ.length with h | h
      · rw [Nat.mod_eq_of_lt h, show σ.length - 1 + (i + 1) = i + σ.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hi' : i + 1 = σ.length := by omega
        rw [hi', Nat.mod_self, add_zero, Nat.mod_eq_of_lt (by omega)]
        omega
    simp only [e]
    exact hfi
  refine ⟨r, (σ.rotate r).tail.dropLast,
    (eq_cons_dropLast_tail (σ.rotate r) (by omega)).trans ?_⟩
  rw [h0, hlast]

end RotateGood

variable {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] {E : ℝ} (hE : |E| < 2)
include hL hE

omit [NeZero L] hL in
theorem norm_mSigma_le_one (s : Bool) : ‖mSigma E s‖ ≤ 1 :=
  (norm_mSigma hE.le s).le

/-- **Cyclic invariance of the primitive loop**, for `0 ≤ t < 1`. -/
theorem Kgen_rot {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (h2 : 2 ≤ I.length) : Kgen L W (mSigma E) t I.rot = Kgen L W (mSigma E) t I :=
  isPrimitive_rot L hL W (mSigma E)
    (isPrimitive_Kgen hL W (mSigma E) (norm_mSigma_le_one hE) ht1) subset_rfl
    (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹ * (1 - t)⁻¹)
    (fun _ hs J hJ hJ2 => norm_Kgen_two_le hL W (mSigma E) (norm_mSigma_le_one hE) ht1 hs J
      hJ hJ2) t ⟨ht0, le_rfl⟩ I hI h2

/-- **Lemma 3.6, (3.13), for the primitive loop**: for `0 ≤ t < 1` and every loop
`(+, μ, -; a', x)`,
`∑_x K_{t,(+,μ,-),(a',x)} = (K_{t,(+,μ),a'} - K_{t,(-,μ),a'}) / (2 W i η_t)`. -/
theorem ward_Kgen {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (μ : List Bool) (a' : List (ZMod L))
    (hμ : μ.length + 1 = a'.length) :
    ∑ x : ZMod L, Kgen L W (mSigma E) t ⟨true :: μ ++ [false], a' ++ [x]⟩
      = (Kgen L W (mSigma E) t ⟨true :: μ, a'⟩ - Kgen L W (mSigma E) t ⟨false :: μ, a'⟩)
          / (2 * W * Complex.I * etaT E t) :=
  sum_fullLoop_eq L hL W hE
    (isPrimitive_Kgen hL W (mSigma E) (norm_mSigma_le_one hE) ht1) ht1 subset_rfl
    (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹ * (1 - t)⁻¹)
    (fun _ hs J hJ hJ2 => norm_Kgen_two_le hL W (mSigma E) (norm_mSigma_le_one hE) ht1 hs J
      hJ hJ2) ⟨ht0, le_rfl⟩ μ a' hμ

section AllSum

/-!
### Sums over all label lists

`allSum n g = ∑_{a ∈ (ZMod L)ⁿ} g a`, as a recursion on lists (prepending the first label).
-/

omit hL hE

variable (L) in
/-- `∑_{a ∈ (ZMod L)ⁿ} g a`. -/
noncomputable def allSum : ℕ → (List (ZMod L) → ℂ) → ℂ
  | 0, g => g []
  | n + 1, g => ∑ x : ZMod L, allSum n (fun l => g (x :: l))

theorem allSum_congr (n : ℕ) {g g' : List (ZMod L) → ℂ}
    (h : ∀ l : List (ZMod L), l.length = n → g l = g' l) : allSum L n g = allSum L n g' := by
  induction n generalizing g g' with
  | zero => exact h [] rfl
  | succ n ih =>
    exact Finset.sum_congr rfl fun x _ => ih fun l hl => h (x :: l) (by simp [hl])

theorem allSum_sum (n : ℕ) {ι : Type*} (s : Finset ι) (g : ι → List (ZMod L) → ℂ) :
    allSum L n (fun l => ∑ i ∈ s, g i l) = ∑ i ∈ s, allSum L n (g i) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [allSum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => ih (fun i l => g i (x :: l))

theorem allSum_linear (n : ℕ) (c : ℂ) (g g' : List (ZMod L) → ℂ) :
    allSum L n (fun l => c * (g l - g' l)) = c * (allSum L n g - allSum L n g') := by
  induction n generalizing g g' with
  | zero => rfl
  | succ n ih =>
    simp only [allSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => ih _ _

/-- Peeling off the last label. -/
theorem allSum_succ_last (n : ℕ) (g : List (ZMod L) → ℂ) :
    allSum L (n + 1) g = allSum L n (fun l => ∑ x : ZMod L, g (l ++ [x])) := by
  induction n generalizing g with
  | zero => simp [allSum]
  | succ n ih =>
    conv_lhs => rw [allSum]
    conv_rhs => rw [allSum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ih]
    simp only [List.cons_append]

/-- Rotating the labels does not change the sum. -/
theorem allSum_rotate (n : ℕ) (g : List (ZMod L) → ℂ) :
    allSum L n (fun l => g (l.rotate 1)) = allSum L n g := by
  rcases n with _ | n
  · rfl
  · conv_lhs => rw [allSum]
    conv_rhs => rw [allSum_succ_last]
    rw [← allSum_sum]
    refine allSum_congr n fun l _ => Finset.sum_congr rfl fun x _ => ?_
    simp [List.rotate_cons_succ]

end AllSum


section Reduction

/-!
### Reduction to pure loops (the proof of Corollary 3.7, (3.15))

`totalSum K σ = ∑_{a ∈ (ZMod L)ⁿ} K_{σ,a}`.  For `σ = (+, μ, -)` Ward's identity sums out the
last label; a mixed `σ` is first rotated into that shape (cyclic invariance).  Iterating,
`‖totalSum σ‖ ≤ 2ⁿ⁻¹ ∑_{m=1}^n ‖κ‖^{n-m} P_m`, where `P_m` bounds the pure loops of length `m`.
-/

omit hL hE

variable (L) in
/-- `∑_{a ∈ (ZMod L)ⁿ} K_{σ,a}`, `n = |σ|`. -/
noncomputable def totalSum (K : LoopIdx (ZMod L) → ℂ) (σ : List Bool) : ℂ :=
  allSum L σ.length (fun a => K ⟨σ, a⟩)

/-- The pure loops of length `m`: `‖∑_a K_{(+,…,+),a}‖ + ‖∑_a K_{(-,…,-),a}‖`. -/
noncomputable def pureNorm (K : LoopIdx (ZMod L) → ℂ) (m : ℕ) : ℝ :=
  ‖totalSum L K (List.replicate m true)‖ + ‖totalSum L K (List.replicate m false)‖

/-- Ward's identity summed over all labels. -/
theorem totalSum_ward (K : LoopIdx (ZMod L) → ℂ) (κ : ℂ) (μ : List Bool)
    (hw : ∀ a' : List (ZMod L), a'.length = μ.length + 1 →
      ∑ x : ZMod L, K ⟨true :: μ ++ [false], a' ++ [x]⟩
        = κ * (K ⟨true :: μ, a'⟩ - K ⟨false :: μ, a'⟩)) :
    totalSum L K (true :: μ ++ [false])
      = κ * (totalSum L K (true :: μ) - totalSum L K (false :: μ)) := by
  have hlen : (true :: μ ++ [false]).length = (μ.length + 1) + 1 := by simp
  rw [totalSum, hlen, allSum_succ_last, allSum_congr _ hw, allSum_linear]
  rfl

/-- `totalSum` is invariant under rotating the charges. -/
theorem totalSum_rotate (K : LoopIdx (ZMod L) → ℂ) (σ : List Bool) (hσ : 2 ≤ σ.length)
    (hcyc : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → K J.rot = K J) (r : ℕ) :
    totalSum L K (σ.rotate r) = totalSum L K σ := by
  induction r with
  | zero => rw [List.rotate_zero]
  | succ r ih =>
    rw [← List.rotate_rotate, ← ih]
    set τ := σ.rotate r
    have hτ : 2 ≤ τ.length := by rw [List.length_rotate]; exact hσ
    rw [totalSum, totalSum, List.length_rotate, ← allSum_rotate]
    refine allSum_congr _ fun a ha => ?_
    exact hcyc ⟨τ, a⟩ ha.symm (by show 2 ≤ a.length; rw [ha]; exact hτ)

theorem totalSum_nonneg_aux (n : ℕ) (κ : ℂ) (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    0 ≤ ∑ m ∈ Finset.Icc 1 n, ‖κ‖ ^ (n - m) * P m :=
  Finset.sum_nonneg fun m _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (hP m)

/-- **The reduction (3.15)**: `‖∑_a K_{σ,a}‖ ≤ 2ⁿ⁻¹ ∑_{m=1}^n ‖κ‖^{n-m} P_m`. -/
theorem norm_totalSum_le (K : LoopIdx (ZMod L) → ℂ) (κ : ℂ)
    (hcyc : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → K J.rot = K J)
    (hward : ∀ (μ : List Bool) (a' : List (ZMod L)), a'.length = μ.length + 1 →
      ∑ x : ZMod L, K ⟨true :: μ ++ [false], a' ++ [x]⟩
        = κ * (K ⟨true :: μ, a'⟩ - K ⟨false :: μ, a'⟩)) :
    ∀ n, 1 ≤ n → ∀ σ : List Bool, σ.length = n →
      ‖totalSum L K σ‖ ≤ 2 ^ (n - 1) * ∑ m ∈ Finset.Icc 1 n, ‖κ‖ ^ (n - m) * pureNorm K m := by
  have hP : ∀ m, 0 ≤ pureNorm K m := fun m => by unfold pureNorm; positivity
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn σ hσ
    have hS := totalSum_nonneg_aux n κ (pureNorm K) hP
    have h2 : (1 : ℝ) ≤ 2 ^ (n - 1) := one_le_pow₀ (by norm_num)
    -- the pure case
    have pure : ∀ b : Bool, σ = List.replicate n b →
        ‖totalSum L K σ‖ ≤ 2 ^ (n - 1) * ∑ m ∈ Finset.Icc 1 n, ‖κ‖ ^ (n - m) * pureNorm K m := by
      intro b hb
      have h1 : ‖totalSum L K σ‖ ≤ ‖κ‖ ^ (n - n) * pureNorm K n := by
        rw [Nat.sub_self, pow_zero, one_mul, pureNorm, hb]
        cases b
        · exact le_add_of_nonneg_left (norm_nonneg _)
        · exact le_add_of_nonneg_right (norm_nonneg _)
      calc ‖totalSum L K σ‖ ≤ ∑ m ∈ Finset.Icc 1 n, ‖κ‖ ^ (n - m) * pureNorm K m :=
            h1.trans (Finset.single_le_sum (f := fun m => ‖κ‖ ^ (n - m) * pureNorm K m)
              (fun m _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (hP m))
              (Finset.mem_Icc.2 ⟨hn, le_rfl⟩))
        _ ≤ _ := le_mul_of_one_le_left hS h2
    by_cases ht : true ∈ σ
    · by_cases hf : false ∈ σ
      · -- mixed: rotate into `(+, μ, -)` and apply Ward
        obtain ⟨r, μ, hr⟩ := exists_rotate_true_false σ ht hf
        have hlenr : (σ.rotate r).length = n := by rw [List.length_rotate, hσ]
        have hμ : μ.length + 2 = n := by rw [← hlenr, hr]; simp
        have h2σ : 2 ≤ σ.length := by omega
        rw [← totalSum_rotate K σ h2σ hcyc r, hr,
          totalSum_ward K κ μ (fun a' ha' => hward μ a' ha')]
        have hA := ih (n - 1) (by omega) (by omega) (true :: μ) (by simp; omega)
        have hB := ih (n - 1) (by omega) (by omega) (false :: μ) (by simp; omega)
        set S' := ∑ m ∈ Finset.Icc 1 (n - 1), ‖κ‖ ^ (n - 1 - m) * pureNorm K m
        have hstep : ‖κ‖ * S' ≤ ∑ m ∈ Finset.Icc 1 n, ‖κ‖ ^ (n - m) * pureNorm K m := by
          rw [Finset.mul_sum]
          calc ∑ m ∈ Finset.Icc 1 (n - 1), ‖κ‖ * (‖κ‖ ^ (n - 1 - m) * pureNorm K m)
              = ∑ m ∈ Finset.Icc 1 (n - 1), ‖κ‖ ^ (n - m) * pureNorm K m := by
                refine Finset.sum_congr rfl fun m hm => ?_
                rw [Finset.mem_Icc] at hm
                rw [← mul_assoc, ← pow_succ', show n - 1 - m + 1 = n - m by omega]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.Icc_subset_Icc le_rfl (by omega))
                (fun m _ _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (hP m))
        calc ‖κ * (totalSum L K (true :: μ) - totalSum L K (false :: μ))‖
            ≤ ‖κ‖ * (‖totalSum L K (true :: μ)‖ + ‖totalSum L K (false :: μ)‖) := by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
          _ ≤ ‖κ‖ * (2 ^ (n - 1 - 1) * S' + 2 ^ (n - 1 - 1) * S') := by gcongr
          _ = 2 ^ (n - 1) * (‖κ‖ * S') := by
              have h2' : (2 : ℝ) ^ (n - 1) = 2 * 2 ^ (n - 1 - 1) := by
                rw [← pow_succ']
                congr 1
                omega
              rw [h2']
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hstep (by positivity)
      · exact pure true (List.eq_replicate_iff.2 ⟨hσ, fun b hb => by
          cases b
          · exact absurd hb hf
          · rfl⟩)
    · have hf : ∀ b ∈ σ, b = false := fun b hb => by
        cases b
        · rfl
        · exact absurd hb ht
      exact pure false (List.eq_replicate_iff.2 ⟨hσ, hf⟩)

end Reduction

end RBM
