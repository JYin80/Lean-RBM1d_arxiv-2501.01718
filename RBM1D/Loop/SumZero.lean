/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Layer

/-!
# Lemma 3.10: symmetry and the sum-zero property of the self-energy

Paper p.40–45.

**Lemma 3.10 (1)** says `Σ^(∅)(t, σ^(alt), d)` is translation invariant and symmetric,
`Σ(d) = Σ(-d)`.  The paper calls this a "simple consequence of the explicit expression"; here
it is proved for **every** `σ` and every layer `π` (`SigmaPi_add_const`, `SigmaPi_neg`), from
the corresponding properties of each edge weight (`selfW_add_const`, `selfW_neg`).

**(3.47)–(3.48)**: summing `K^(π)` over all boundary labels `a` turns every boundary edge into
its row sum `(1 - t m_i m_{i+1})^{-1}` (`S^(B) 1 = 1`), so
`∑_a K^(π)(t,σ,a) = ∏_i (1 - t m_i m_{i+1})^{-1} · ∑_d Σ^(π)(t,σ,d)` (`sum_Kpi_eq`), an exact
identity.
-/

namespace RBM

open Finset

section Symmetry

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- If every edge weight is translation invariant, so is the self-energy. -/
theorem selfW_add_const (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (hE : ∀ e x y c, E e (x + c) (y + c) = E e x y) (d : Fin n → ZMod L) (c : ZMod L) :
    selfW L F E (fun v => d v + c) = selfW L F E d := by
  unfold selfW
  rw [← Equiv.sum_comp (Equiv.addRight (fun _ : ↥(nodes F) => c))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, Pi.add_apply, add_left_inj, hE]

/-- If every edge weight satisfies `E(-x,-y) = E(x,y)`, the self-energy is even. -/
theorem selfW_neg (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (ZMod L) (ZMod L) ℂ)
    (hE : ∀ e x y, E e (-x) (-y) = E e x y) (d : Fin n → ZMod L) :
    selfW L F E (fun v => -d v) = selfW L F E d := by
  unfold selfW
  rw [← Equiv.sum_comp (Equiv.neg (↥(nodes F) → ZMod L))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.neg_apply, Pi.neg_apply, neg_inj, hE]

omit [NeZero n] in
theorem Theta_sub_one_add_const (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y c : ZMod L) :
    (Theta L ξ - 1) (x + c) (y + c) = (Theta L ξ - 1) x y := by
  simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, Theta_apply_add_right L hL hξ]

omit [NeZero n] in
theorem Theta_sub_one_neg (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y : ZMod L) :
    (Theta L ξ - 1) (-x) (-y) = (Theta L ξ - 1) x y := by
  have h1 : Theta L ξ (-x) (-y) = Theta L ξ x y := by
    have := Theta_apply_add_right L hL hξ (-x) (-y) (x + y)
    rw [show -x + (x + y) = y by ring, show -y + (x + y) = x by ring] at this
    rw [← this]
    exact congrFun (congrFun (Theta_transpose L hL hξ) x) y
  simp only [Matrix.sub_apply, Matrix.one_apply, neg_inj, h1]

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **Lemma 3.10 (1), translation invariance**, for every `σ` and `π`:
`Σ^(π)(t,σ,d + c) = Σ^(π)(t,σ,d)`. -/
theorem SigmaPi_add_const (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (d : Fin n → ZMod L) (c : ZMod L) :
    SigmaPi L m t σ π (fun v => d v + c) = SigmaPi L m t σ π d := by
  unfold SigmaPi selfE
  refine sum_congr rfl fun F _ => selfW_add_const F _ (fun e x y c => ?_) d c
  exact Theta_sub_one_add_const hL (hm _ _) x y c

/-- **Lemma 3.10 (1), symmetry**, for every `σ` and `π`: `Σ^(π)(t,σ,-d) = Σ^(π)(t,σ,d)`. -/
theorem SigmaPi_neg (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
    (d : Fin n → ZMod L) :
    SigmaPi L m t σ π (fun v => -d v) = SigmaPi L m t σ π d := by
  unfold SigmaPi selfE
  refine sum_congr rfl fun F _ => selfW_neg F _ (fun e x y => ?_) d
  exact Theta_sub_one_neg hL (hm _ _) x y

end Symmetry

section RowSums

variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Column sums of `Θ_ξ`: `∑_x (Θ_ξ)_{xy} = (1 - ξ)^{-1}`. -/
theorem sum_Theta_col (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (y : ZMod L) :
    ∑ x : ZMod L, Theta L ξ x y = (1 - ξ)⁻¹ := by
  rw [← sum_Theta_row L hL hξ y]
  refine sum_congr rfl fun x _ => ?_
  exact congrFun (congrFun (Theta_transpose L hL hξ) y) x

variable (m : Bool → ℂ) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hm

/-- **(3.47)–(3.48)**: `∑_a K^(π)(t,σ,a) = ∏_i (1 - t m_i m_{i+1})^{-1} ∑_d Σ^(π)(t,σ,d)`. -/
theorem sum_Kpi_eq (hL : 3 ≤ L) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    ∑ a : Fin n → ZMod L, Kpi L m t σ a π =
      (∏ v, (1 - (t : ℂ) * (m (σ v) * m (σ (v + 1))))⁻¹) *
        ∑ d : Fin n → ZMod L, SigmaPi L m t σ π d := by
  simp_rw [Kpi_eq_sum_SigmaPi]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum, mul_comm]
  congr 1
  have h := (prod_univ_sum (fun _ : Fin n => (univ : Finset (ZMod L)))
    (fun v x => thetaEdge L m t (σ v) (σ (v + 1)) x (d v))).symm
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine prod_congr rfl fun v _ => ?_
  exact sum_Theta_col hL (hm _ _) (d v)

end RowSums

end RBM
