/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxEndpointHigherDifference

/-!
# All-order actual first-cell squared-block-loop face

This module upgrades the accepted all-order endpoint-vector estimates to the squared
Hilbert--Schmidt block loop on the same first-cell event.
-/

namespace RBM.Gauss

open Filter MeasureTheory
open scoped BigOperators

/-- Public existential successor for T1472's private endpoint constant. -/
theorem firstCell_endpointHigher_successor (M : ℕ) :
    ∃ C : ℝ, 320 ≤ C ∧ ∀ {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow},
      ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
        (firstCellMinorEndpointDelta b) N →
      0 < b → firstCellMinorEndpointDelta b N ≤ 1 / 4 →
      8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 →
      1 ≤ N → u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) →
      ∀ (S : Finset (Dims.exampleGrow.Idx N)) (k : Dims.exampleGrow.Idx N)
        (l : List (Dims.exampleGrow.Idx N)),
        l.Nodup → (∀ j ∈ l, j ∉ S) → k ∉ S → (∀ j ∈ l, j ≠ k) →
        ∀ a : ZMod (Dims.exampleGrow.L N), S.card + l.length ≤ M →
          (((Dims.exampleGrow.W N : ℝ)⁻¹) *
            ∑ r : Fin (Dims.exampleGrow.W N),
              ‖iterDeltaFam l (fun U =>
                gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2 ≤
            C * (N : ℝ) ^ (C * b) *
              (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length)) ∧
          (((Dims.exampleGrow.W N : ℝ)⁻¹) *
            ∑ r : Fin (Dims.exampleGrow.W N),
              ‖iterDeltaFam l (fun U =>
                gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2 ≤
            C * (N : ℝ) ^ (C * b) *
              (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length)) := by
  refine ⟨?_, ?_⟩
  rotate_left
  constructor
  rotate_left
  · intro τ' b N u ω hω hb hδ hMδ hN hu S k l hnd hfresh hk hlk a hbudget
    exact firstCell_randomLmax_minor_endpoint_higher_difference_row_column_le
      hω hb hδ hMδ hN hu S k l hnd hfresh hk hlk a hbudget
  · change 320 ≤ max 320 _
    exact le_max_left _ _

noncomputable def firstCellEndpointSuccessorC (M : ℕ) : ℝ :=
  Classical.choose (firstCell_endpointHigher_successor M)

theorem firstCellEndpointSuccessorC_spec (M : ℕ) :
    320 ≤ firstCellEndpointSuccessorC M ∧ ∀ {τ' b : ℝ} {N : ℕ}
      {u : ℝ} {ω : Ω Dims.exampleGrow},
      ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
        (firstCellMinorEndpointDelta b) N →
      0 < b → firstCellMinorEndpointDelta b N ≤ 1 / 4 →
      8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 →
      1 ≤ N → u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N) →
      ∀ (S : Finset (Dims.exampleGrow.Idx N)) (k : Dims.exampleGrow.Idx N)
        (l : List (Dims.exampleGrow.Idx N)),
        l.Nodup → (∀ j ∈ l, j ∉ S) → k ∉ S → (∀ j ∈ l, j ≠ k) →
        ∀ a : ZMod (Dims.exampleGrow.L N), S.card + l.length ≤ M →
          (((Dims.exampleGrow.W N : ℝ)⁻¹) *
            ∑ r : Fin (Dims.exampleGrow.W N),
              ‖iterDeltaFam l (fun U =>
                gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2 ≤
            firstCellEndpointSuccessorC M *
              (N : ℝ) ^ (firstCellEndpointSuccessorC M * b) *
              (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length)) ∧
          (((Dims.exampleGrow.W N : ℝ)⁻¹) *
            ∑ r : Fin (Dims.exampleGrow.W N),
              ‖iterDeltaFam l (fun U =>
                gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2 ≤
            firstCellEndpointSuccessorC M *
              (N : ℝ) ^ (firstCellEndpointSuccessorC M * b) *
              (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length)) := by
  exact Classical.choose_spec (firstCell_endpointHigher_successor M)

private theorem deltaFam_commute {α : Type*} [DecidableEq α]
    (κ j : α) (Y : Finset α → ℂ) :
    deltaFam κ (deltaFam j Y) = deltaFam j (deltaFam κ Y) := by
  funext S
  simp only [deltaFam_apply, Finset.insert_comm]
  ring

private theorem iterDeltaFam_perm {α : Type*} [DecidableEq α]
    {l l' : List α} (h : l.Perm l') (Y : Finset α → ℂ) :
    iterDeltaFam l Y = iterDeltaFam l' Y := by
  induction h generalizing Y with
  | nil => rfl
  | cons a _ ih =>
      simpa only [iterDeltaFam_cons] using ih (deltaFam a Y)
  | swap a b t =>
      simp only [iterDeltaFam_cons]
      exact congrArg (iterDeltaFam t) (deltaFam_commute a b Y)
  | trans _ _ ih₁ ih₂ => exact (ih₁ Y).trans (ih₂ Y)

private theorem list_perm_cons_erase {α : Type*} [BEq α] [LawfulBEq α]
    (l : List α) (κ : α) (hκ : κ ∈ l) : l.Perm (κ :: l.erase κ) := by
  induction l with
  | nil => simp at hκ
  | cons x xs ih =>
      by_cases hx : x = κ
      · subst x
        simp
      · have hkxs : κ ∈ xs := by
          rcases List.mem_cons.mp hκ with heq | hmem
          · exact False.elim (hx heq.symm)
          · exact hmem
        have hperm := ih hkxs
        have h1 : List.Perm (x :: xs) (x :: κ :: xs.erase κ) := List.Perm.cons x hperm
        have h2 : List.Perm (x :: κ :: xs.erase κ) (κ :: x :: xs.erase κ) :=
          List.Perm.swap κ x (xs.erase κ)
        have hErase : (x :: xs).erase κ = x :: xs.erase κ := by simp [hx]
        rw [hErase]
        exact h1.trans h2

private theorem iterDeltaFam_right_zero_of_base
    {α : Type*} [DecidableEq α] (κ : α) (Y : Finset α → ℂ)
    (hY : ∀ U, κ ∈ U → Y U = 0) :
    ∀ l S, κ ∈ S → iterDeltaFam l Y S = 0 := by
  intro l
  induction l generalizing Y with
  | nil => intro S hS; exact hY S hS
  | cons j l ih =>
      intro S hS
      rw [iterDeltaFam_cons]
      apply ih
      · intro U hU
        simp only [deltaFam_apply, hY U hU,
          hY (insert j U) (Finset.mem_insert_of_mem hU), sub_self]
      · exact hS

private theorem iterDeltaFam_right_pivot_erases
    {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α]
    (κ : α) (l : List α) (Y : Finset α → ℂ)
    (hκ : κ ∈ l) (hY : ∀ U, κ ∈ U → Y U = 0) :
    iterDeltaFam l Y = iterDeltaFam (l.erase κ) Y := by
  rw [iterDeltaFam_perm (list_perm_cons_erase l κ hκ) Y, iterDeltaFam_cons]
  have hdelta : deltaFam κ Y = Y := by
    funext U
    simp only [deltaFam_apply, hY (insert κ U) (Finset.mem_insert_self κ U), sub_zero]
  rw [hdelta]

noncomputable def firstCellHigherLoopBaseC (M : ℕ) : ℝ :=
  (1 + 4 * (M : ℝ)) * firstCellEndpointSuccessorC M

private theorem firstCell_higher_block_difference_sq_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N))
    (l : List (Dims.exampleGrow.Idx N)) (hnd : l.Nodup)
    (hfresh : ∀ j ∈ l, j ∉ S) (hbudget : S.card + l.length ≤ M)
    (a c : ZMod (Dims.exampleGrow.L N)) :
    (((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2) *
      ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
        ‖iterDeltaFam l (fun U =>
          gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U) S‖ ^ 2 ≤
      firstCellHigherLoopBaseC M * (N : ℝ) ^
        (firstCellHigherLoopBaseC M * b) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length) := by
  classical
  let W : ℝ := Dims.exampleGrow.W N
  let C₀ := firstCellEndpointSuccessorC M
  let Γ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)
  let X := C₀ * (N : ℝ) ^ (C₀ * b)
  let A : Finset (Fin (Dims.exampleGrow.W N)) :=
    Finset.univ.filter (fun s => (c, s) ∈ l.toFinset)
  have hCspec := firstCellEndpointSuccessorC_spec M
  have hC320 : 320 ≤ C₀ := hCspec.1
  have hC0 : 0 ≤ C₀ := by linarith
  have hWpos : 0 < W := by
    dsimp [W]
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hWinv0 : 0 < W⁻¹ := inv_pos.mpr hWpos
  have hΓ0 : 0 ≤ Γ := Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') (firstCellMinorEndpointDelta b) N := hω.1
  have hWlow := inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellMinorEndpointDelta b) (E := 0)
    (by norm_num) (hδquarter.trans (by norm_num)) hflow hu
  have hΓpos : 0 < Γ := by
    have : 0 < 4 * Γ := lt_of_lt_of_le hWinv0 hWlow
    linarith
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hAcard : A.card ≤ l.length := by
    have himage : Finset.image (fun s : Fin (Dims.exampleGrow.W N) => (c, s)) A ⊆
        l.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
      have hs' := Finset.mem_filter.mp hs
      exact hs'.2
    have hinj : Set.InjOn (fun s : Fin (Dims.exampleGrow.W N) => (c, s)) (↑A) := by
      intro s hs t ht hst
      exact congrArg Prod.snd hst
    calc
      A.card = (Finset.image (fun s : Fin (Dims.exampleGrow.W N) => (c, s)) A).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ l.toFinset.card := Finset.card_le_card himage
      _ ≤ l.length := List.toFinset_card_le l
  have hcol : ∀ s : Fin (Dims.exampleGrow.W N),
      (∑ r : Fin (Dims.exampleGrow.W N),
        ‖iterDeltaFam l (fun U =>
          gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) (c, s) U) S‖ ^ 2) ≤
        W * X * Γ ^ (1 + l.length) +
          (if (c, s) ∈ l.toFinset then W * X * Γ ^ l.length else 0) := by
    intro s
    let k : Dims.exampleGrow.Idx N := (c, s)
    let F : Fin (Dims.exampleGrow.W N) → Finset (Dims.exampleGrow.Idx N) → ℂ :=
      fun r U => gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U
    have hYzero : ∀ r U, k ∈ U → F r U = 0 := by
      intro r U hU
      exact gEnt_eq_zero_right hU
    by_cases hkS : k ∈ S
    · have hzero (r : Fin (Dims.exampleGrow.W N)) :=
        iterDeltaFam_right_zero_of_base k (F r) (hYzero r) l S hkS
      have hsumzero :
          (∑ r : Fin (Dims.exampleGrow.W N),
            ‖iterDeltaFam l (fun U =>
              gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        have hz := hzero r
        simpa [F, hz]
      rw [hsumzero]
      positivity
    · by_cases hkl : k ∈ l
      · let l' : List (Dims.exampleGrow.Idx N) := l.erase k
        have hperm := list_perm_cons_erase l k hkl
        have hlenEq : l.length = l'.length + 1 := by
          have h := hperm.length_eq
          simp only [List.length_cons] at h
          simpa [l'] using h
        have hnd' : l'.Nodup := by
          dsimp [l']
          exact hnd.erase k
        have hknot : k ∉ l' := by
          dsimp [l']
          intro hmem
          exact (List.Nodup.mem_erase_iff hnd).mp hmem |>.1 rfl
        have hfresh' : ∀ j ∈ l', j ∉ S := by
          intro j hj
          have hjl : j ∈ l := List.mem_of_mem_erase (by simpa [l'] using hj)
          exact hfresh j hjl
        have hbudget' : S.card + l'.length ≤ M := by omega
        have hkS' : k ∉ S := hkS
        have hlk' : ∀ j ∈ l', j ≠ k := by
          intro j hj hEq
          subst j
          exact hknot hj
        have hdiffEq (r : Fin (Dims.exampleGrow.W N)) :
            iterDeltaFam l (F r) S = iterDeltaFam l' (F r) S := by
          simpa [l'] using congrFun
            (iterDeltaFam_right_pivot_erases k l (F r) hkl (hYzero r)) S
        have hend := (hCspec.2 hω hb hδquarter hMδ hN hu S k l' hnd'
          hfresh' hkS' hlk' a hbudget').1
        have hraw :
            (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l (F r) S‖ ^ 2) ≤
              W * X * Γ ^ l.length := by
          have hnorm : (W⁻¹) *
              (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l' (F r) S‖ ^ 2) ≤
                X * Γ ^ (1 + l'.length) := by
            simpa [W, X, C₀, Γ, F] using hend
          have hmul :
              (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l' (F r) S‖ ^ 2) ≤
                W * (X * Γ ^ (1 + l'.length)) := by
            have hcancel : W * W⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hWpos)
            calc
              _ = W * (W⁻¹ *
                  (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l' (F r) S‖ ^ 2)) := by
                    rw [← mul_assoc, hcancel, one_mul]
              _ ≤ W * (X * Γ ^ (1 + l'.length)) :=
                    mul_le_mul_of_nonneg_left hnorm hWpos.le
          have hsumEq :
              (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l (F r) S‖ ^ 2) =
                ∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l' (F r) S‖ ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                rw [hdiffEq r]
          have hlenNat : 1 + l'.length = l.length := by omega
          calc
            _ = ∑ r : Fin (Dims.exampleGrow.W N),
                ‖iterDeltaFam l' (F r) S‖ ^ 2 := hsumEq
            _ ≤ W * (X * Γ ^ (1 + l'.length)) := hmul
            _ = W * X * Γ ^ l.length := by rw [hlenNat]; ring
        have hkMemList : (c, s) ∈ l.toFinset := List.mem_toFinset.mpr hkl
        have hraw' :
            (∑ r : Fin (Dims.exampleGrow.W N),
              ‖iterDeltaFam l (fun U =>
                gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) (c, s) U) S‖ ^ 2) ≤
              W * X * Γ ^ l.length := by simpa [F, k] using hraw
        rw [if_pos hkMemList]
        exact le_trans hraw' (le_add_of_nonneg_left (by positivity))
      · have hknotS : k ∉ S := hkS
        have hlk : ∀ j ∈ l, j ≠ k := by
          intro j hj hEq
          subst j
          exact hkl hj
        have hend := (hCspec.2 hω hb hδquarter hMδ hN hu S k l hnd
          hfresh hknotS hlk a hbudget).1
        have hraw :
            (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l (F r) S‖ ^ 2) ≤
              W * X * Γ ^ (1 + l.length) := by
          have hnorm : (W⁻¹) *
              (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l (F r) S‖ ^ 2) ≤
                X * Γ ^ (1 + l.length) := by
            simpa [W, X, C₀, Γ, F] using hend
          calc
            _ = W * (W⁻¹ *
                (∑ r : Fin (Dims.exampleGrow.W N), ‖iterDeltaFam l (F r) S‖ ^ 2)) := by
                  have hcancel : W * W⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hWpos)
                  rw [← mul_assoc, hcancel, one_mul]
            _ ≤ W * (X * Γ ^ (1 + l.length)) :=
                  mul_le_mul_of_nonneg_left hnorm hWpos.le
            _ = W * X * Γ ^ (1 + l.length) := by ring
        have hkMemList : (c, s) ∉ l.toFinset := by
          exact fun hm => hkl (List.mem_toFinset.mp hm)
        rw [if_neg hkMemList]
        simpa [F, k] using hraw
  have hcolsum :
      (∑ s : Fin (Dims.exampleGrow.W N),
        ∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) (c, s) U) S‖ ^ 2) ≤
        W * (W * X * Γ ^ (1 + l.length)) +
          (A.card : ℝ) * (W * X * Γ ^ l.length) := by
    calc
      _ ≤ ∑ s : Fin (Dims.exampleGrow.W N),
          (W * X * Γ ^ (1 + l.length) +
            (if (c, s) ∈ l.toFinset then W * X * Γ ^ l.length else 0)) :=
          Finset.sum_le_sum fun s _ => hcol s
      _ = W * (W * X * Γ ^ (1 + l.length)) +
            (A.card : ℝ) * (W * X * Γ ^ l.length) := by
          rw [Finset.sum_add_distrib]
          have hcount :
              (∑ s : Fin (Dims.exampleGrow.W N),
                if (c, s) ∈ l.toFinset then (1 : ℝ) else 0) = (A.card : ℝ) := by
            rw [← Finset.sum_filter]
            simp [A]
          rw [show (∑ s : Fin (Dims.exampleGrow.W N),
              if (c, s) ∈ l.toFinset then W * X * Γ ^ l.length else 0) =
              (∑ s : Fin (Dims.exampleGrow.W N),
                if (c, s) ∈ l.toFinset then (1 : ℝ) else 0) *
                (W * X * Γ ^ l.length) by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro s hs
                split_ifs <;> simp]
          rw [hcount]
          have hsumconst (K : ℝ) :
              (∑ _s : Fin (Dims.exampleGrow.W N), K) = W * K := by
            calc
              _ = (Finset.univ.card : ℝ) * K := by
                    simp only [Finset.sum_const, nsmul_eq_mul]
                    rfl
              _ = W * K := by
                    dsimp [W]
                    exact congrArg (fun x : ℝ => x * K)
                      (by
                        exact_mod_cast (Fintype.card_fin (Dims.growW N)))
          rw [hsumconst]
  have hprod :
      (((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2) *
        (W * (W * X * Γ ^ (1 + l.length)) +
          (A.card : ℝ) * (W * X * Γ ^ l.length)) ≤
        X * Γ ^ (1 + l.length) +
          (M : ℝ) * (W⁻¹) * X * Γ ^ l.length := by
    have hfirst : (((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2) *
        (W * (W * X * Γ ^ (1 + l.length))) = X * Γ ^ (1 + l.length) := by
      have hcancel : W⁻¹ * W = 1 := inv_mul_cancel₀ (ne_of_gt hWpos)
      calc
        _ = (W⁻¹ * W) * (W⁻¹ * W) * (X * Γ ^ (1 + l.length)) := by ring
        _ = X * Γ ^ (1 + l.length) := by rw [hcancel]; ring
    have hsecond : (((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2) *
        ((A.card : ℝ) * (W * X * Γ ^ l.length)) =
        (A.card : ℝ) * W⁻¹ * X * Γ ^ l.length := by
      have hcancel : W⁻¹ * W = 1 := inv_mul_cancel₀ (ne_of_gt hWpos)
      calc
        _ = (A.card : ℝ) * W⁻¹ * (W⁻¹ * W) * X * Γ ^ l.length := by ring
        _ = (A.card : ℝ) * W⁻¹ * X * Γ ^ l.length := by rw [hcancel]; ring
    rw [mul_add, hfirst, hsecond]
    have hcardcast : (A.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans hAcard (by omega))
    have hterm : (A.card : ℝ) * W⁻¹ * X * Γ ^ l.length ≤
        (M : ℝ) * W⁻¹ * X * Γ ^ l.length := by
      have hcardW : (A.card : ℝ) * W⁻¹ ≤ (M : ℝ) * W⁻¹ :=
        mul_le_mul_of_nonneg_right hcardcast (inv_nonneg.mpr hWpos.le)
      calc
        _ = ((A.card : ℝ) * W⁻¹) * (X * Γ ^ l.length) := by ring
        _ ≤ ((M : ℝ) * W⁻¹) * (X * Γ ^ l.length) :=
          mul_le_mul_of_nonneg_right hcardW (by positivity)
        _ = (M : ℝ) * W⁻¹ * X * Γ ^ l.length := by ring
    linarith
  have hbase :
      (((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2) *
        ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U) S‖ ^ 2 ≤
        X * Γ ^ (1 + l.length) +
          (M : ℝ) * W⁻¹ * X * Γ ^ l.length := by
    have hsumEq :
        (∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U) S‖ ^ 2) =
        ∑ s : Fin (Dims.exampleGrow.W N),
          ∑ r : Fin (Dims.exampleGrow.W N),
            ‖iterDeltaFam l (fun U =>
              gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) (c, s) U) S‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [hsumEq]
    exact le_trans (mul_le_mul_of_nonneg_left hcolsum
      (sq_nonneg W⁻¹)) hprod
  have hD : firstCellHigherLoopBaseC M = (1 + 4 * (M : ℝ)) * C₀ := rfl
  have hDnonneg : 0 ≤ firstCellHigherLoopBaseC M := by
    rw [hD]
    positivity
  have hcoef : (1 + 4 * (M : ℝ)) * C₀ ≤ firstCellHigherLoopBaseC M := by rw [hD]
  have hΓpow : 0 ≤ Γ ^ (1 + l.length) := pow_nonneg hΓ0 _
  have hpowMon : (N : ℝ) ^ (C₀ * b) ≤
      (N : ℝ) ^ (firstCellHigherLoopBaseC M * b) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    rw [hD]
    have hM : 1 ≤ (1 + 4 * (M : ℝ)) := by norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hM) hb.le, hC0]
  have hcoef0 : 0 ≤ C₀ * (N : ℝ) ^ (C₀ * b) := hX0
  have hbetter : (M : ℝ) * W⁻¹ * X * Γ ^ l.length ≤
      4 * (M : ℝ) * X * Γ ^ (1 + l.length) := by
    have hpow : Γ ^ (1 + l.length) = Γ * Γ ^ l.length := by
      calc
        Γ ^ (1 + l.length) = Γ ^ 1 * Γ ^ l.length := by rw [pow_add]
        _ = Γ * Γ ^ l.length := by simp
    rw [hpow]
    have hfactor : 0 ≤ (M : ℝ) * X * Γ ^ l.length := by positivity
    have hA := mul_le_mul_of_nonneg_right hWlow hfactor
    calc
      _ = W⁻¹ * ((M : ℝ) * X * Γ ^ l.length) := by ring
      _ ≤ (4 * Γ) * ((M : ℝ) * X * Γ ^ l.length) := hA
      _ = 4 * (M : ℝ) * X * (Γ * Γ ^ l.length) := by ring
  have hfinal : X * Γ ^ (1 + l.length) +
      (M : ℝ) * W⁻¹ * X * Γ ^ l.length ≤
      firstCellHigherLoopBaseC M * (N : ℝ) ^
        (firstCellHigherLoopBaseC M * b) * Γ ^ (1 + l.length) := by
    have hrough : X * Γ ^ (1 + l.length) +
        (M : ℝ) * W⁻¹ * X * Γ ^ l.length ≤
        ((1 + 4 * (M : ℝ)) * X) * Γ ^ (1 + l.length) := by
      calc
        _ ≤ X * Γ ^ (1 + l.length) +
            4 * (M : ℝ) * X * Γ ^ (1 + l.length) := add_le_add le_rfl hbetter
        _ = ((1 + 4 * (M : ℝ)) * X) * Γ ^ (1 + l.length) := by ring
    dsimp [X] at hrough ⊢
    calc
      _ ≤ ((1 + 4 * (M : ℝ)) * (C₀ * (N : ℝ) ^ (C₀ * b))) *
          Γ ^ (1 + l.length) := hrough
      _ = firstCellHigherLoopBaseC M *
          (N : ℝ) ^ (C₀ * b) * Γ ^ (1 + l.length) := by rw [hD]; ring
      _ ≤ firstCellHigherLoopBaseC M *
          (N : ℝ) ^ (firstCellHigherLoopBaseC M * b) * Γ ^ (1 + l.length) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpowMon hDnonneg) hΓpow
  exact le_trans hbase hfinal

private theorem real_rpow_half_nat_sq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x ^ ((n : ℝ) / 2)) ^ 2 = x ^ n := by
  calc
    (x ^ ((n : ℝ) / 2)) ^ 2 = (x ^ ((n : ℝ) / 2)) ^ (2 : ℝ) := by
      exact (Real.rpow_natCast (x ^ ((n : ℝ) / 2)) 2).symm
    _ = x ^ (((n : ℝ) / 2) * 2) := by rw [← Real.rpow_mul hx]
    _ = x ^ (n : ℝ) := by congr 1 <;> ring
    _ = x ^ n := Real.rpow_natCast x n

private def BlockL2Oracle {α ι : Type*} [DecidableEq α] [Fintype ι]
    (w Γ B : ℝ) (budget grade : ℕ) (I : Finset α)
    (Y : ι → Finset α → ℂ) : Prop :=
  ∀ (l : List α) (S : Finset α), l.Nodup →
    (∀ κ ∈ l, κ ∉ I) → (∀ κ ∈ l, κ ∉ S) →
    S.card + l.length ≤ budget →
      (w⁻¹) ^ 2 * ∑ i : ι, ‖iterDeltaFam l (Y i) S‖ ^ 2 ≤
        B * Γ ^ (grade + l.length)

private theorem iterDeltaFam_mul_sum_l2_bound
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (w Γ B : ℝ) (budget : ℕ) (I : Finset α)
    (Y Z : ι → Finset α → ℂ) (p q : ℕ)
    (hw : 0 < w) (hΓ : 0 < Γ) (hB : 0 ≤ B)
    (hY : BlockL2Oracle w Γ B (budget + 1) p I Y)
    (hZ : BlockL2Oracle w Γ B (budget + 1) q I Z) :
    ∀ (l : List α) (S : Finset α), l.Nodup →
      (∀ κ ∈ l, κ ∉ I) → (∀ κ ∈ l, κ ∉ S) →
      S.card + l.length ≤ budget →
        (w⁻¹) ^ 2 * ∑ i : ι,
          ‖iterDeltaFam l (fun U => Y i U * Z i U) S‖ ≤
          (2 : ℝ) ^ l.length * B *
            Γ ^ (((p + q + l.length : ℕ) : ℝ) / 2) := by
  classical
  intro l
  revert budget I Y Z p q hY hZ
  induction l with
  | nil =>
      intro budget I Y Z p q hY hZ
      intro S hnd hI hS hbudget
      let t : ℝ := (w⁻¹) ^ 2
      let f : ι → ℝ := fun i => ‖Y i S‖
      let g : ι → ℝ := fun i => ‖Z i S‖
      have ht : 0 ≤ t := by positivity
      have hbudget1 : S.card + ([] : List α).length ≤ budget + 1 := by omega
      have hf2 : t * ∑ i, f i ^ 2 ≤ B * Γ ^ p := by
        simpa [BlockL2Oracle, t, f] using hY [] S (by simp) (by simp) (by simp) hbudget1
      have hg2 : t * ∑ i, g i ^ 2 ≤ B * Γ ^ q := by
        simpa [BlockL2Oracle, t, g] using hZ [] S (by simp) (by simp) (by simp) hbudget1
      have hf0 : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hg0 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hcross0 : 0 ≤ ∑ i, f i * g i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) f g
      have hscaledSq : (t * ∑ i, f i * g i) ^ 2 ≤
          (B * Γ ^ p) * (B * Γ ^ q) := by
        calc
          _ = t ^ 2 * (∑ i, f i * g i) ^ 2 := by ring
          _ ≤ t ^ 2 * ((∑ i, f i ^ 2) * (∑ i, g i ^ 2)) :=
            mul_le_mul_of_nonneg_left hcs (sq_nonneg t)
          _ = (t * ∑ i, f i ^ 2) * (t * ∑ i, g i ^ 2) := by ring
          _ ≤ (B * Γ ^ p) * (B * Γ ^ q) := by
            exact mul_le_mul hf2 hg2 (mul_nonneg ht hg0)
              (mul_nonneg hB (pow_nonneg hΓ.le p))
      have hpow : (Γ ^ (((p + q : ℕ) : ℝ) / 2)) ^ 2 = Γ ^ (p + q) :=
        real_rpow_half_nat_sq Γ hΓ.le (p + q)
      have htargetSq : (B * Γ ^ (((p + q : ℕ) : ℝ) / 2)) ^ 2 =
          (B * Γ ^ p) * (B * Γ ^ q) := by
        rw [mul_pow, hpow, pow_add]
        ring
      have htarget0 : 0 ≤ B * Γ ^ (((p + q : ℕ) : ℝ) / 2) :=
        mul_nonneg hB (Real.rpow_nonneg hΓ.le _)
      have hsumle : t * ∑ i, f i * g i ≤
          B * Γ ^ (((p + q : ℕ) : ℝ) / 2) :=
        (sq_le_sq₀ (mul_nonneg ht hcross0) htarget0).mp
          (by rw [htargetSq]; exact hscaledSq)
      simpa [t, f, g, iterDeltaFam_nil, norm_mul] using hsumle
  | cons κ l ih =>
      intro budget I Y Z p q hY hZ
      intro S hnd hI hS hbudget
      obtain ⟨budget', rfl⟩ : ∃ budget', budget = budget' + 1 :=
        ⟨budget - 1, by simp only [List.length_cons] at hbudget; omega⟩
      have hκI : κ ∉ I := hI κ (List.mem_cons_self ..)
      have hκS : κ ∉ S := hS κ (List.mem_cons_self ..)
      have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
      have hκl : κ ∉ l := (List.nodup_cons.mp hnd).1
      have hI' : ∀ j ∈ l, j ∉ insert κ I := by
        intro j hj hjI
        rcases Finset.mem_insert.mp hjI with hEq | hjI
        · exact hκl (hEq ▸ hj)
        · exact hI j (List.mem_cons_of_mem κ hj) hjI
      have hS' : ∀ j ∈ l, j ∉ insert κ S := by
        intro j hj hjS
        rcases Finset.mem_insert.mp hjS with hEq | hjS
        · exact hκl (hEq ▸ hj)
        · exact hS j (List.mem_cons_of_mem κ hj) hjS
      have hbudget' : S.card + l.length ≤ budget' := by
        simp only [List.length_cons] at hbudget
        omega
      have hYdelta : BlockL2Oracle w Γ B (budget' + 1) (p + 1)
          (insert κ I) (fun i U => deltaFam κ (Y i) U) := by
        intro l' T hnd' hI'' hT' hbud'
        by_cases hκT : κ ∈ T
        · have hzero (i : ι) : iterDeltaFam l'
              (fun U => deltaFam κ (Y i) U) T = 0 := by
            apply iterDeltaFam_right_zero_of_base κ (deltaFam κ (Y i))
            · intro U hU
              simp [deltaFam_apply, Finset.insert_eq_of_mem hU]
            · exact hκT
          have hsumzero : ∑ i : ι,
              ‖iterDeltaFam l' (fun U => deltaFam κ (Y i) U) T‖ ^ 2 = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [hzero i]
            simp
          rw [hsumzero]
          simpa using mul_nonneg hB (pow_nonneg hΓ.le _)
        · have hκl' : κ ∉ l' := by
            intro hmem
            exact hI'' κ hmem (Finset.mem_insert_self κ I)
          have hndFull : (κ :: l').Nodup := List.nodup_cons.mpr ⟨hκl', hnd'⟩
          have hIFull : ∀ j ∈ κ :: l', j ∉ I := by
            intro j hj
            rcases List.mem_cons.mp hj with hEq | hj
            · exact hEq ▸ hκI
            · intro hjI
              exact hI'' j hj (Finset.mem_insert_of_mem hjI)
          have hTFull : ∀ j ∈ κ :: l', j ∉ T := by
            intro j hj
            rcases List.mem_cons.mp hj with hEq | hj
            · exact hEq ▸ hκT
            · exact hT' j hj
          have hbudFull : T.card + (κ :: l').length ≤ budget' + 2 := by
            simp only [List.length_cons]
            omega
          have hbase := hY (κ :: l') T hndFull hIFull hTFull hbudFull
          simp only [iterDeltaFam_cons, List.length_cons] at hbase
          change (w⁻¹) ^ 2 * ∑ i : ι,
              ‖iterDeltaFam l' (deltaFam κ (Y i)) T‖ ^ 2 ≤
            B * Γ ^ (p + 1 + l'.length)
          have hexp : p + (l'.length + 1) = p + 1 + l'.length := by omega
          simpa only [hexp] using hbase
      have hYshift : BlockL2Oracle w Γ B (budget' + 1) p
          (insert κ I) (fun i U => shiftFam κ (Y i) U) := by
        intro l' T hnd' hI'' hT' hbud'
        have hκl' : κ ∉ l' := by
          intro hmem
          exact hI'' κ hmem (Finset.mem_insert_self κ I)
        have hIorig : ∀ j ∈ l', j ∉ I := by
          intro j hj hjI
          exact hI'' j hj (Finset.mem_insert_of_mem hjI)
        have hTorig : ∀ j ∈ l', j ∉ insert κ T := by
          intro j hj hjT
          rcases Finset.mem_insert.mp hjT with hEq | hjT
          · exact hκl' (hEq ▸ hj)
          · exact hT' j hj hjT
        have hbudOrig : (insert κ T).card + l'.length ≤ budget' + 2 := by
          have hcard := Finset.card_insert_le κ T
          omega
        have hbase := hY l' (insert κ T) hnd' hIorig hTorig hbudOrig
        change (w⁻¹) ^ 2 * ∑ i : ι,
            ‖iterDeltaFam l' (shiftFam κ (Y i)) T‖ ^ 2 ≤
          B * Γ ^ (p + l'.length)
        have hshift (i : ι) :
            iterDeltaFam l' (shiftFam κ (Y i)) T =
              iterDeltaFam l' (Y i) (insert κ T) := by
          rw [iterDeltaFam_shiftFam]
          rfl
        simpa only [hshift] using hbase
      have hZdelta : BlockL2Oracle w Γ B (budget' + 1) (q + 1)
          (insert κ I) (fun i U => deltaFam κ (Z i) U) := by
        intro l' T hnd' hI'' hT' hbud'
        by_cases hκT : κ ∈ T
        · have hzero (i : ι) : iterDeltaFam l'
              (fun U => deltaFam κ (Z i) U) T = 0 := by
            apply iterDeltaFam_right_zero_of_base κ (deltaFam κ (Z i))
            · intro U hU
              simp [deltaFam_apply, Finset.insert_eq_of_mem hU]
            · exact hκT
          have hsumzero : ∑ i : ι,
              ‖iterDeltaFam l' (fun U => deltaFam κ (Z i) U) T‖ ^ 2 = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [hzero i]
            simp
          rw [hsumzero]
          simpa using mul_nonneg hB (pow_nonneg hΓ.le _)
        · have hκl' : κ ∉ l' := by
            intro hmem
            exact hI'' κ hmem (Finset.mem_insert_self κ I)
          have hndFull : (κ :: l').Nodup := List.nodup_cons.mpr ⟨hκl', hnd'⟩
          have hIFull : ∀ j ∈ κ :: l', j ∉ I := by
            intro j hj
            rcases List.mem_cons.mp hj with hEq | hj
            · exact hEq ▸ hκI
            · intro hjI
              exact hI'' j hj (Finset.mem_insert_of_mem hjI)
          have hTFull : ∀ j ∈ κ :: l', j ∉ T := by
            intro j hj
            rcases List.mem_cons.mp hj with hEq | hj
            · exact hEq ▸ hκT
            · exact hT' j hj
          have hbudFull : T.card + (κ :: l').length ≤ budget' + 2 := by
            simp only [List.length_cons]
            omega
          have hbase := hZ (κ :: l') T hndFull hIFull hTFull hbudFull
          simp only [iterDeltaFam_cons, List.length_cons] at hbase
          change (w⁻¹) ^ 2 * ∑ i : ι,
              ‖iterDeltaFam l' (deltaFam κ (Z i)) T‖ ^ 2 ≤
            B * Γ ^ (q + 1 + l'.length)
          have hexp : q + (l'.length + 1) = q + 1 + l'.length := by omega
          simpa only [hexp] using hbase
      have hZsame : BlockL2Oracle w Γ B (budget' + 1) q
          (insert κ I) Z := by
        intro l' T hnd' hI'' hT' hbud'
        have hIorig : ∀ j ∈ l', j ∉ I := by
          intro j hj hjI
          exact hI'' j hj (Finset.mem_insert_of_mem hjI)
        exact hZ l' T hnd' hIorig hT' (by omega)
      have hA := ih (budget := budget') (I := insert κ I)
        (Y := fun i U => deltaFam κ (Y i) U) (Z := Z) (p := p + 1) (q := q)
        hYdelta hZsame S hnd'
        hI' (by intro j hj; exact hS j (List.mem_cons_of_mem κ hj)) hbudget'
      have hB := ih (budget := budget') (I := insert κ I)
        (Y := fun i U => shiftFam κ (Y i) U)
        (Z := fun i U => deltaFam κ (Z i) U) (p := p) (q := q + 1)
        hYshift hZdelta S hnd' hI'
        (by intro j hj; exact hS j (List.mem_cons_of_mem κ hj)) hbudget'
      have hsplit (i : ι) :
          iterDeltaFam (κ :: l) (fun U => Y i U * Z i U) S =
            iterDeltaFam l (fun U => deltaFam κ (Y i) U * Z i U) S +
              iterDeltaFam l (fun U => shiftFam κ (Y i) U * deltaFam κ (Z i) U) S := by
        rw [iterDeltaFam_cons, deltaFam_mul, iterDeltaFam_add]
      have htri : (∑ i : ι,
          ‖iterDeltaFam (κ :: l) (fun U => Y i U * Z i U) S‖) ≤
          (∑ i : ι, ‖iterDeltaFam l
            (fun U => deltaFam κ (Y i) U * Z i U) S‖) +
          (∑ i : ι, ‖iterDeltaFam l
            (fun U => shiftFam κ (Y i) U * deltaFam κ (Z i) U) S‖) := by
        calc
          _ ≤ ∑ i : ι, (‖iterDeltaFam l
                (fun U => deltaFam κ (Y i) U * Z i U) S‖ +
              ‖iterDeltaFam l
                (fun U => shiftFam κ (Y i) U * deltaFam κ (Z i) U) S‖) :=
              Finset.sum_le_sum fun i hi => by rw [hsplit i]; exact norm_add_le _ _
          _ = _ := Finset.sum_add_distrib
      have hcommon : (p + 1 + q + l.length : ℕ) =
          p + q + (κ :: l).length := by simp [List.length_cons]; omega
      have hcommon' : (p + (q + 1) + l.length : ℕ) =
          p + q + (κ :: l).length := by simp [List.length_cons]; omega
      have hA' : (w⁻¹) ^ 2 *
          (∑ i : ι, ‖iterDeltaFam l
            (fun U => deltaFam κ (Y i) U * Z i U) S‖) ≤
          (2 : ℝ) ^ l.length * B *
          Γ ^ (((p + q + (κ :: l).length : ℕ) : ℝ) / 2) := by
        simpa [hcommon] using hA
      have hB' : (w⁻¹) ^ 2 *
          (∑ i : ι, ‖iterDeltaFam l
            (fun U => shiftFam κ (Y i) U * deltaFam κ (Z i) U) S‖) ≤
          (2 : ℝ) ^ l.length * B *
          Γ ^ (((p + q + (κ :: l).length : ℕ) : ℝ) / 2) := by
        simpa [hcommon'] using hB
      have hscaled : (w⁻¹) ^ 2 *
          (∑ i : ι, ‖iterDeltaFam (κ :: l)
            (fun U => Y i U * Z i U) S‖) ≤
          (2 : ℝ) ^ (κ :: l).length * B *
            Γ ^ (((p + q + (κ :: l).length : ℕ) : ℝ) / 2) := by
        calc
          _ ≤ (w⁻¹) ^ 2 *
              ((∑ i : ι, ‖iterDeltaFam l
                (fun U => deltaFam κ (Y i) U * Z i U) S‖) +
               (∑ i : ι, ‖iterDeltaFam l
                (fun U => shiftFam κ (Y i) U * deltaFam κ (Z i) U) S‖)) :=
              mul_le_mul_of_nonneg_left htri (sq_nonneg _)
          _ = (w⁻¹) ^ 2 * (∑ i : ι, ‖iterDeltaFam l
                (fun U => deltaFam κ (Y i) U * Z i U) S‖) +
              (w⁻¹) ^ 2 * (∑ i : ι, ‖iterDeltaFam l
                (fun U => shiftFam κ (Y i) U * deltaFam κ (Z i) U) S‖) := by rw [mul_add]
          _ ≤ (2 : ℝ) ^ l.length * B *
              Γ ^ (((p + q + (κ :: l).length : ℕ) : ℝ) / 2) +
              (2 : ℝ) ^ l.length * B *
              Γ ^ (((p + q + (κ :: l).length : ℕ) : ℝ) / 2) :=
              add_le_add hA' hB'
          _ = (2 : ℝ) ^ (κ :: l).length * B *
              Γ ^ (((p + q + (κ :: l).length : ℕ) : ℝ) / 2) := by
              simp only [List.length_cons, pow_succ]
              ring
      exact hscaled

private theorem iterDeltaFam_re_eq_iterDeltaVec
    {α : Type*} [DecidableEq α] (l : List α)
    (Y : Finset α → ℂ) (S : Finset α) :
    (iterDeltaFam l Y S).re =
      iterDeltaVec l (fun U => (Y U).re) S := by
  induction l generalizing Y S with
  | nil => rfl
  | cons κ l ih =>
      simp only [iterDeltaFam_cons, iterDeltaVec_cons]
      rw [ih]
      congr 1

private theorem iterDeltaFam_sum
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (l : List α) (F : ι → Finset α → ℂ) (S : Finset α) :
    iterDeltaFam l (fun U => ∑ i, F i U) S =
      ∑ i, iterDeltaFam l (F i) S := by
  induction l generalizing F S with
  | nil => rfl
  | cons κ l ih =>
      simp only [iterDeltaFam_cons]
      have hδ : deltaFam κ (fun U => ∑ i, F i U) =
          fun U => ∑ i, deltaFam κ (F i) U := by
        funext U
        simp [deltaFam, Finset.sum_sub_distrib]
      rw [hδ, ih]

private theorem iterDeltaVec_real_scale
    {α : Type*} [DecidableEq α] (l : List α) (c : ℝ)
    (Y : Finset α → ℝ) (S : Finset α) :
    iterDeltaVec l (fun U => c * Y U) S = c * iterDeltaVec l Y S := by
  induction l generalizing Y S with
  | nil => rfl
  | cons κ l ih =>
      simp only [iterDeltaVec_cons]
      have hδ : deltaVecFam κ (fun U => c * Y U) =
          fun U => c * deltaVecFam κ Y U := by
        funext U
        simp [deltaVecFam]
        ring
      rw [hδ, ih]

private theorem firstCell_sum_block_ite_real {L W : ℕ} [NeZero L] [NeZero W]
    (f : ZMod L × Fin W → ZMod L × Fin W → ℝ) (a b : ZMod L) :
    (∑ p : ZMod L × Fin W, ∑ q : ZMod L × Fin W,
        (if p.1 = b then if q.1 = a then f p q else 0 else 0)) =
      ∑ β : Fin W, ∑ α : Fin W, f (b, β) (a, α) := by
  have hq : ∀ p : ZMod L × Fin W,
      (∑ q : ZMod L × Fin W,
          (if p.1 = b then if q.1 = a then f p q else 0 else 0)) =
        if p.1 = b then ∑ α : Fin W, f p (a, α) else 0 := by
    intro p
    by_cases hp : p.1 = b
    · simp only [if_pos hp, Fintype.sum_prod_type]
      refine (Finset.sum_eq_single a ?_ ?_).trans ?_
      · intro q₁ _ hne
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ a) h
      · simp
    · simp [hp]
  simp_rw [hq]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b ?_ ?_).trans ?_
  · intro p₁ _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ b) h
  · simp

private theorem embeddedMinorLoop_eq_offset_sum
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (S : Finset (Dims.exampleGrow.Idx N))
    (a b : ZMod (Dims.exampleGrow.L N)) :
    embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) S ω a b =
      ((Dims.exampleGrow.W N : ℝ)⁻¹) ^ 2 *
        ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω
            (a, p.1) (b, p.2) S‖ ^ 2 := by
  classical
  unfold embeddedMinorLoop
  congr 1
  conv_lhs => rw [Fintype.sum_prod_type]
  change (∑ p : Dims.exampleGrow.Idx N, ∑ q : Dims.exampleGrow.Idx N,
      (if p.1 = a ∧ q.1 = b then
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2 else 0)) = _
  let f : Dims.exampleGrow.Idx N → Dims.exampleGrow.Idx N → ℝ := fun p q =>
    ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2
  have hterm (p q : Dims.exampleGrow.Idx N) :
      (if p.1 = a ∧ q.1 = b then
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2 else 0) =
        (if p.1 = a then
          if q.1 = b then ‖gEnt Dims.exampleGrow N u (zt 0 u) ω p q S‖ ^ 2
          else 0 else 0) := by
    by_cases hp : p.1 = a
    · by_cases hq : q.1 = b
      · rw [if_pos ⟨hp, hq⟩, if_pos hp, if_pos hq]
      · rw [if_neg (by intro h; exact hq h.2), if_pos hp, if_neg hq]
    · rw [if_neg (by intro h; exact hp h.1), if_neg hp]
  simp_rw [hterm]
  conv_rhs => rw [Fintype.sum_prod_type]
  change (∑ p : ZMod (Dims.exampleGrow.L N) × Fin (Dims.exampleGrow.W N),
      ∑ q : ZMod (Dims.exampleGrow.L N) × Fin (Dims.exampleGrow.W N),
        (if p.1 = a then if q.1 = b then f p q else 0 else 0)) =
    ∑ β : Fin (Dims.exampleGrow.W N),
      ∑ α : Fin (Dims.exampleGrow.W N), f (a, β) (b, α)
  exact firstCell_sum_block_ite_real
    (L := Dims.exampleGrow.L N) (W := Dims.exampleGrow.W N)
    (f := f) (a := b) (b := a)

private theorem iterDeltaFam_star
    {α : Type*} [DecidableEq α] (l : List α)
    (Y : Finset α → ℂ) :
    iterDeltaFam l (fun U => star (Y U)) =
      fun S => star (iterDeltaFam l Y S) := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ l ih =>
      funext S
      simp only [iterDeltaFam_cons]
      have hδ : deltaFam κ (fun U => star (Y U)) =
          fun U => star (deltaFam κ Y U) := by
        funext U
        simp [deltaFam]
      rw [hδ, ih]

noncomputable def firstCellHigherLoopC (M : ℕ) : ℝ :=
  (2 : ℝ) ^ M * firstCellHigherLoopBaseC (M + 1)

private theorem firstCellHigherLoopDelta_small {b : ℝ} (M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      firstCellMinorEndpointDelta b N ≤ 1 / 4 ∧
        8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 := by
  have hpsi := firstCellPsi_le_rpow_neg_quarter
  have hMpow : ∀ᶠ N : ℕ in atTop,
      8 * (M : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow _ (by norm_num)
  have hfourpow : ∀ᶠ N : ℕ in atTop,
      4 ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow 4 (by norm_num)
  filter_upwards [hpsi, hMpow, hfourpow, eventually_ge_atTop 1]
    with N hpsiN hMpowN hfourpowN hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hδle : firstCellMinorEndpointDelta b N ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
    have hmul := mul_le_mul_of_nonneg_left hpsiN
      (Real.rpow_nonneg (Nat.cast_nonneg N) (firstCellMinorEndpointBeta b))
    have hpow : (N : ℝ) ^ firstCellMinorEndpointBeta b *
        (N : ℝ) ^ (-(1 : ℝ) / 4) =
          (N : ℝ) ^ (firstCellMinorEndpointBeta b - 1 / 4) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      firstCellMinorEndpointDelta b N =
          (N : ℝ) ^ firstCellMinorEndpointBeta b * firstCellPsi N := rfl
      _ ≤ (N : ℝ) ^ firstCellMinorEndpointBeta b *
          (N : ℝ) ^ (-(1 : ℝ) / 4) := hmul
      _ = (N : ℝ) ^ (firstCellMinorEndpointBeta b - 1 / 4) := hpow
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        have hbeta := firstCellMinorEndpointBeta_le_one_sixteenth b
        linarith
  have hnegpow : (N : ℝ) ^ (-(3 : ℝ) / 16) =
      ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ := by
    rw [show -(3 : ℝ) / 16 = -((3 : ℝ) / 16) by ring,
      Real.rpow_neg (Nat.cast_nonneg N)]
  have hquarter : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ 1 / 4 := by
    rw [hnegpow]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hfourpowN
    norm_num at hinv ⊢
    exact hinv
  have hsmall : firstCellMinorEndpointDelta b N ≤ 1 / 4 := hδle.trans hquarter
  have hbudget : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMpos : (0 : ℝ) < 8 * (M : ℝ) := by
        exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
      have hinv : ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ ≤ (8 * (M : ℝ))⁻¹ :=
        inv_anti₀ hMpos hMpowN
      have hdeltaInv : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ (8 * (M : ℝ))⁻¹ := by
        rw [hnegpow]
        exact hinv
      calc
        8 * (M : ℝ) * firstCellMinorEndpointDelta b N
            ≤ 8 * (M : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 16) :=
              mul_le_mul_of_nonneg_left hδle (by positivity)
        _ ≤ 8 * (M : ℝ) * (8 * (M : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left hdeltaInv (by positivity)
        _ = 1 := by field_simp
  exact ⟨hsmall, hbudget⟩

-- The shifted product induction expands over all subsets of the deletion list.
set_option maxHeartbeats 1000000 in
theorem firstCell_randomLmax_higher_loop_face_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * ((M + 1 : ℕ) : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N)
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N))
    (l : List (Dims.exampleGrow.Idx N))
    (hnd : l.Nodup) (hfresh : ∀ j ∈ l, j ∉ S)
    (hbudget : S.card + l.length ≤ M)
    (a c : ZMod (Dims.exampleGrow.L N)) :
    |iterDeltaVec l (fun U =>
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c) S| ≤
      firstCellHigherLoopC M * (N : ℝ) ^ (firstCellHigherLoopC M * b) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^
          (1 + (l.length : ℝ) / 2) := by
  classical
  let W : ℝ := Dims.exampleGrow.W N
  let Γ : ℝ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)
  let D : ℝ := firstCellHigherLoopBaseC (M + 1)
  let B : ℝ := D * (N : ℝ) ^ (D * b)
  let C : ℝ := firstCellHigherLoopC M
  let g : (Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N)) →
      Finset (Dims.exampleGrow.Idx N) → ℂ := fun p U =>
        gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U
  let Y := fun p U => star (g p U)
  have hCspec := firstCellEndpointSuccessorC_spec (M + 1)
  have hCpos : 0 < firstCellEndpointSuccessorC (M + 1) := by
    linarith [hCspec.1]
  have hDpos : 0 < D := by
    dsimp [D, firstCellHigherLoopBaseC]
    positivity
  have hDnonneg : 0 ≤ D := hDpos.le
  have hCnonneg : 0 ≤ C := by
    dsimp [C, firstCellHigherLoopC]
    positivity
  have hCgeD : D ≤ C := by
    dsimp [C, firstCellHigherLoopC]
    calc
      D = 1 * D := by ring
      _ ≤ (2 : ℝ) ^ M * D :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) hDnonneg
  have hWpos : 0 < W := by
    dsimp [W]
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hWlow := inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellMinorEndpointDelta b) (E := 0)
    (by norm_num) (hδquarter.trans (by norm_num)) hω.1 hu
  have hΓpos : 0 < Γ := by
    have hWinv : 0 < W⁻¹ := inv_pos.mpr hWpos
    have hΓ0 : 0 ≤ Γ := Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
    have : 0 < 4 * Γ := lt_of_lt_of_le hWinv (by simpa [W, Γ] using hWlow)
    linarith
  have hΓ0 : 0 ≤ Γ := Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbaseL2 : BlockL2Oracle W Γ B (M + 1) 1
      (∅ : Finset (Dims.exampleGrow.Idx N)) g := by
    intro l' T hnd' _hI hT hbudget'
    have hblock := firstCell_higher_block_difference_sq_le
      (τ' := τ') (b := b) (N := N) (u := u) (ω := ω) (M := M + 1)
      hω hb hδquarter hMδ hN hu T l' hnd' hT hbudget' a c
    simpa [BlockL2Oracle, W, Γ, B, D, firstCellHigherLoopBaseC, g] using hblock
  have hY : BlockL2Oracle W Γ B (M + 1) 1
      (∅ : Finset (Dims.exampleGrow.Idx N)) Y := by
    intro l' T hnd' _hI hT hbudget'
    have h := hbaseL2 l' T hnd' (by simp) hT hbudget'
    have hnorm : ∀ i : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
        ‖iterDeltaFam l' (fun U => star (g i U)) T‖ =
          ‖iterDeltaFam l' (g i) T‖ := by
      intro i
      rw [iterDeltaFam_star]
      simp
    calc
      (W⁻¹) ^ 2 * ∑ i, ‖iterDeltaFam l' (Y i) T‖ ^ 2 =
          (W⁻¹) ^ 2 * ∑ i, ‖iterDeltaFam l' (g i) T‖ ^ 2 := by
            congr 2
            funext i
            rw [hnorm i]
      _ ≤ B * Γ ^ (1 + l'.length) := h
  have hProd := iterDeltaFam_mul_sum_l2_bound
    (w := W) (Γ := Γ) (B := B) (budget := M)
    (I := (∅ : Finset (Dims.exampleGrow.Idx N)))
    (Y := Y) (Z := g) (p := 1) (q := 1)
    hWpos hΓpos hB0 hY hbaseL2 l S hnd (by simp) hfresh hbudget
  let Q : Finset (Dims.exampleGrow.Idx N) → ℂ := fun U =>
    ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
      star (g p U) * g p U
  have hloopEq (U : Finset (Dims.exampleGrow.Idx N)) :
      embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c =
        W⁻¹ ^ 2 * ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          (star (g p U) * g p U).re := by
    rw [embeddedMinorLoop_eq_offset_sum]
    simp only [g]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro p hp
    calc
      ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U‖ ^ 2 =
          Complex.normSq (gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U) := by
            rw [Complex.normSq_eq_norm_sq]
      _ = (star (gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U) *
          gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U).re := by
            have hz := Complex.normSq_eq_conj_mul_self
              (z := gEnt Dims.exampleGrow N u (zt 0 u) ω (a, p.1) (c, p.2) U)
            have hr := congrArg Complex.re hz
            simpa [Complex.star_def] using hr
  have hloopDiff :
      iterDeltaVec l (fun U =>
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c) S =
        W⁻¹ ^ 2 * (iterDeltaFam l Q S).re := by
    rw [show (fun U : Finset (Dims.exampleGrow.Idx N) =>
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c) =
        (fun U => W⁻¹ ^ 2 * ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          (star (g p U) * g p U).re) by
            funext U
            exact hloopEq U]
    rw [iterDeltaVec_real_scale]
    rw [show (fun U : Finset (Dims.exampleGrow.Idx N) =>
        ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          (star (g p U) * g p U).re) = (fun U => (Q U).re) by
            funext U
            simp [Q, Complex.re_sum]]
    rw [← iterDeltaFam_re_eq_iterDeltaVec]
  have hWsq : 0 ≤ W⁻¹ ^ 2 := sq_nonneg W⁻¹
  have hsumNorm :
      |iterDeltaVec l (fun U =>
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c) S| ≤
        W⁻¹ ^ 2 * ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U => star (g p U) * g p U) S‖ := by
    rw [hloopDiff, abs_mul, abs_of_nonneg hWsq]
    calc
      W⁻¹ ^ 2 * |(iterDeltaFam l Q S).re| ≤
          W⁻¹ ^ 2 * ‖iterDeltaFam l Q S‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hWsq
      _ ≤ W⁻¹ ^ 2 * ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U => star (g p U) * g p U) S‖ := by
            apply mul_le_mul_of_nonneg_left _ hWsq
            change ‖iterDeltaFam l
              (fun U => ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
                star (g p U) * g p U) S‖ ≤ _
            rw [iterDeltaFam_sum]
            exact norm_sum_le _ _
  have hExp : (((1 + 1 + l.length : ℕ) : ℝ) / 2) =
      1 + (l.length : ℝ) / 2 := by push_cast; ring
  have hprodBound : W⁻¹ ^ 2 *
      ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
        ‖iterDeltaFam l (fun U => star (g p U) * g p U) S‖ ≤
      (2 : ℝ) ^ l.length * B * Γ ^ (1 + (l.length : ℝ) / 2) := by
    simpa only [Y, hExp] using hProd
  have hlen : l.length ≤ M := by omega
  have htwo : (2 : ℝ) ^ l.length ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hlen)
  have hcoef : (2 : ℝ) ^ l.length * D ≤ C := by
    dsimp [C, firstCellHigherLoopC]
    exact mul_le_mul_of_nonneg_right htwo hDnonneg
  have hNpow : (N : ℝ) ^ (D * b) ≤ (N : ℝ) ^ (C * b) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    exact mul_le_mul_of_nonneg_right hCgeD hb.le
  have hscale : (2 : ℝ) ^ l.length * B ≤ C * (N : ℝ) ^ (C * b) := by
    dsimp [B]
    calc
      _ = ((2 : ℝ) ^ l.length * D) * (N : ℝ) ^ (D * b) := by ring
      _ ≤ C * (N : ℝ) ^ (D * b) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ ≤ C * (N : ℝ) ^ (C * b) :=
        mul_le_mul_of_nonneg_left hNpow hCnonneg
  have hΓexp : 0 ≤ Γ ^ (1 + (l.length : ℝ) / 2) := Real.rpow_nonneg hΓ0 _
  calc
    |iterDeltaVec l (fun U =>
        embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c) S|
        ≤ W⁻¹ ^ 2 * ∑ p : Fin (Dims.exampleGrow.W N) × Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U => star (g p U) * g p U) S‖ := hsumNorm
    _ ≤ (2 : ℝ) ^ l.length * B * Γ ^ (1 + (l.length : ℝ) / 2) := hprodBound
    _ ≤ C * (N : ℝ) ^ (C * b) * Γ ^ (1 + (l.length : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hscale hΓexp

/-- A same-event positive-time actual Gaussian witness for the all-order squared-block-loop
face.  For each fixed loss and budget, one resident sample works for every eligible base,
deletion list, and original block pair. -/
theorem firstCell_randomLmax_actual_higher_loop_face_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      ∀ b : ℝ, 0 < b → ∀ M : ℕ,
        ∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
              (firstCellMinorEndpointDelta b) N,
            1 ≤ N ∧ firstCellMinorEndpointDelta b N ≤ 1 / 4 ∧
              8 * ((M + 1 : ℕ) : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 ∧
              ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
                0 < u ∧ u < firstCellT τ' N ∧
                  (∀ i : Dims.exampleGrow.Idx N,
                    0 < ∫ ω', ‖Hflow Dims.exampleGrow N u ω' i i‖ ^ 2
                      ∂(P Dims.exampleGrow)) ∧
                  ∀ S : Finset (Dims.exampleGrow.Idx N),
                    ∀ l : List (Dims.exampleGrow.Idx N),
                      l.Nodup → (∀ j ∈ l, j ∉ S) → S.card + l.length ≤ M →
                        ∀ a c : ZMod (Dims.exampleGrow.L N),
                          |iterDeltaVec l (fun U =>
                            embeddedMinorLoop Dims.exampleGrow N u (zt 0 u) U ω a c) S| ≤
                            firstCellHigherLoopC M * (N : ℝ) ^
                              (firstCellHigherLoopC M * b) *
                              (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^
                                (1 + (l.length : ℝ) / 2) := by
  obtain ⟨τ', hτ', hll, hsource⟩ :=
    firstCell_randomLmax_actual_endpoint_higher_difference_witness
  refine ⟨τ', hτ', hll, ?_⟩
  intro b hb M
  have hactual := hsource b hb (M + 1)
  have hsmall := firstCellHigherLoopDelta_small (b := b) (M + 1)
  filter_upwards [hactual, hsmall, eventually_ge_atTop 1]
    with N hactualN hsmallN hN
  rcases hactualN with ⟨ω, hω, u, hu, hu0, hut, hdiag, _⟩
  rcases hsmallN with ⟨hδquarter, hMδ⟩
  refine ⟨ω, hω, hN, hδquarter, hMδ, u, hu, hu0, hut, hdiag, ?_⟩
  intro S l hnd hfresh hbudget a c
  exact firstCell_randomLmax_higher_loop_face_le
    hω hb hδquarter hMδ hN hu S l hnd hfresh hbudget a c

#print axioms firstCell_randomLmax_higher_loop_face_le
#print axioms firstCell_randomLmax_actual_higher_loop_face_witness

end RBM.Gauss
