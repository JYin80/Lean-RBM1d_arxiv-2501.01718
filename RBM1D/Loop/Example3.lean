/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Tree

/-!
# Example 2.16: the tree representation at `n = 3`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Example 2.16 and Lemma 3.4 at
`n = 3`.  This is the first case in which the tree representation is non-trivial: the
`3`-gon has `T SP = {∅}` (`RBM.TSP_three`), a single tree, the star with one internal
vertex, and the claim is that

  `K_{t,σ,(a₁,a₂,a₃)} = W⁻² m₁m₂m₃ ∑_b (Θ_{t m₁m₂})_{a₁b} (Θ_{t m₂m₃})_{a₂b} (Θ_{t m₃m₁})_{a₃b}`

solves (2.48) with the initial value of Definition 2.12.  The boundary edge at `aᵢ` carries
`Θ_{t mᵢ mᵢ₊₁}`, the convention fixed in `RBM1D.Loop.Tree` (`RBM.thetaEdge`).

## Index check at `n = 3`

`RBM.primRhs_three` expands the general right-hand side of (2.48), built from
`cutGlueL`/`cutGlueR`, into its three terms `(k,l) = (1,2), (1,3), (2,3)`.  The terms
`(1,2)` and `(2,3)` agree with the paper's display after swapping the dummy indices
(symmetry of `S^(B)`).  The wrap-around term `(1,3)` comes out as `K_{(σ₁,σ₃),(b,a₃)}`,
the paper writes `K_{(σ₃,σ₁),(a₃,b)}`: these are the same `2`-loop read from a different
starting point, so they agree for any `K` invariant under cyclic rotation of loops
(`RBM.primRhs_three_paper`), and in particular for `RBM.kTwo`, where it is the symmetry of
`Θ` (`RBM.kTwo_rotate`).

## Main results

* `RBM.primRhs_three`, `RBM.primRhs_three_paper` : the index check
* `RBM.rhs_kTwo_left`, `RBM.rhs_kTwo_right` : substituting (2.57) for the short chain
  (the second step of Example 2.16), `W · W⁻¹ = 1`
* `RBM.kThree`, `RBM.kThree_eq_starGamma` : the star value, and its agreement with
  `RBM.starGamma` of `RBM1D.Loop.Tree`
* `RBM.hasDerivAt_kThree` : **the tree representation solves (2.48) at `n = 3`**
* `RBM.kThree_zero` : the initial value of Definition 2.12
* `RBM.hasDerivAt_kLoop3` : the same in the general form `primRhs`
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

section IndexCheck

/-- **Index check at `n = 3`.** The general right-hand side of (2.48) has the three terms
`(k,l) = (1,2), (1,3), (2,3)`, in this order. -/
theorem primRhs_three (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (σ₁ σ₂ σ₃ : Bool)
    (a₁ a₂ a₃ : ZMod L) :
    primRhs L W K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩
      = (W : ℂ) * ((∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[σ₁, σ₂, σ₃], [x, a₂, a₃]⟩ * SB L x y * K ⟨[σ₁, σ₂], [a₁, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[σ₁, σ₃], [x, a₃]⟩ * SB L x y * K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, y]⟩)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            K ⟨[σ₁, σ₂, σ₃], [a₁, x, a₃]⟩ * SB L x y * K ⟨[σ₂, σ₃], [a₂, y]⟩)) := by
  have h13 : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have h1 : Ioc 1 3 = ({2, 3} : Finset ℕ) := by decide
  have h2 : Ioc 2 3 = ({3} : Finset ℕ) := by decide
  have h3 : Ioc 3 3 = (∅ : Finset ℕ) := by decide
  have hlen : (LoopIdx.mk [σ₁, σ₂, σ₃] [a₁, a₂, a₃]).length = 3 := rfl
  rw [primRhs, hlen, h13, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h1, h2, h3, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  simp only [add_assoc]
  rfl

omit [NeZero L] in
/-- `S^(B)` is symmetric, entrywise. -/
theorem SB_apply_comm (x y : ZMod L) : SB L x y = SB L y x :=
  congrFun (congrFun (SB_transpose L) y) x

/-- The index check against the paper's display of Example 2.16, for `K` invariant under
cyclic rotation of `2`-loops. -/
theorem primRhs_three_paper (W : ℕ) (K : LoopIdx (ZMod L) → ℂ)
    (hrot : ∀ (s s' : Bool) (x y : ZMod L), K ⟨[s, s'], [x, y]⟩ = K ⟨[s', s], [y, x]⟩)
    (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    primRhs L W K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩
      = (W : ℂ) * ((∑ b : ZMod L, ∑ c : ZMod L,
            K ⟨[σ₁, σ₂], [a₁, b]⟩ * SB L b c * K ⟨[σ₁, σ₂, σ₃], [c, a₂, a₃]⟩)
          + (∑ b : ZMod L, ∑ c : ZMod L,
            K ⟨[σ₂, σ₃], [a₂, b]⟩ * SB L b c * K ⟨[σ₁, σ₂, σ₃], [a₁, c, a₃]⟩)
          + (∑ b : ZMod L, ∑ c : ZMod L,
            K ⟨[σ₃, σ₁], [a₃, b]⟩ * SB L b c * K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, c]⟩)) := by
  rw [primRhs_three]
  have e12 : (∑ x : ZMod L, ∑ y : ZMod L,
      K ⟨[σ₁, σ₂, σ₃], [x, a₂, a₃]⟩ * SB L x y * K ⟨[σ₁, σ₂], [a₁, y]⟩)
      = ∑ b : ZMod L, ∑ c : ZMod L,
          K ⟨[σ₁, σ₂], [a₁, b]⟩ * SB L b c * K ⟨[σ₁, σ₂, σ₃], [c, a₂, a₃]⟩ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [SB_apply_comm L c b]; ring
  have e23 : (∑ x : ZMod L, ∑ y : ZMod L,
      K ⟨[σ₁, σ₂, σ₃], [a₁, x, a₃]⟩ * SB L x y * K ⟨[σ₂, σ₃], [a₂, y]⟩)
      = ∑ b : ZMod L, ∑ c : ZMod L,
          K ⟨[σ₂, σ₃], [a₂, b]⟩ * SB L b c * K ⟨[σ₁, σ₂, σ₃], [a₁, c, a₃]⟩ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [SB_apply_comm L c b]; ring
  have e13 : (∑ x : ZMod L, ∑ y : ZMod L,
      K ⟨[σ₁, σ₃], [x, a₃]⟩ * SB L x y * K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, y]⟩)
      = ∑ b : ZMod L, ∑ c : ZMod L,
          K ⟨[σ₃, σ₁], [a₃, b]⟩ * SB L b c * K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, c]⟩ := by
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hrot]
  rw [e12, e23, e13]
  ring

end IndexCheck

section Substitution

variable {L} (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ)

omit [NeZero W] in
/-- `(2.57)` is invariant under reading the `2`-loop from the other end. -/
theorem kTwo_rotate (hL : 3 ≤ L) (s s' : Bool) (ht : ‖(t : ℂ) * (m s * m s')‖ < 1)
    (x y : ZMod L) : kTwo L W m t s s' x y = kTwo L W m t s' s y x := by
  have hΘ := congrFun (congrFun (Theta_transpose L hL ht) y) x
  simp only [Matrix.transpose_apply] at hΘ
  rw [kTwo, kTwo, mul_comm (m s') (m s), hΘ]

/-- Substituting (2.57) for a short chain on the right: `W · W⁻¹ = 1` and
`W ∑_{x,y} f(x) S_{xy} K_{(s,s'),(a,y)} = ∑_x (m m' Θ_{t m m'} S)_{ax} f(x)`. -/
theorem rhs_kTwo_left (s s' : Bool) (a : ZMod L) (f : ZMod L → ℂ) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L, f x * SB L x y * kTwo L W m t s s' a y
      = ∑ x : ZMod L, ((m s * m s') • (thetaEdge L m t s s' * SB L)) a x * f x := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul, kTwo, thetaEdge]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [SB_apply_comm L x y]
  field_simp

/-- The same with the short chain on the left, as in the wrap-around term `(1,3)`. -/
theorem rhs_kTwo_right (hL : 3 ≤ L) (s s' : Bool) (ht : ‖(t : ℂ) * (m s * m s')‖ < 1)
    (a : ZMod L) (f : ZMod L → ℂ) :
    (W : ℂ) * ∑ x : ZMod L, ∑ y : ZMod L, kTwo L W m t s s' x a * SB L x y * f y
      = ∑ y : ZMod L, ((m s * m s') • (thetaEdge L m t s' s * SB L)) a y * f y := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [kTwo_rotate W m t hL s s' ht x a, kTwo, thetaEdge]
  field_simp

end Substitution

section Star

variable {L}

/-- The star value at `n = 3` (Lemma 3.4 with `T SP = {∅}`):
`W⁻² m₁m₂m₃ ∑_b (Θ_{t m₁m₂})_{a₁b} (Θ_{t m₂m₃})_{a₂b} (Θ_{t m₃m₁})_{a₃b}`. -/
noncomputable def kThree (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ σ₃ : Bool)
    (a₁ a₂ a₃ : ZMod L) : ℂ :=
  (W : ℂ)⁻¹ ^ 2 * (m σ₁ * m σ₂ * m σ₃) * ∑ b : ZMod L,
    thetaEdge L m t σ₁ σ₂ a₁ b * thetaEdge L m t σ₂ σ₃ a₂ b * thetaEdge L m t σ₃ σ₁ a₃ b

/-- `kThree` is the star graph of `RBM1D.Loop.Tree` with the prefactor of (3.5). -/
theorem kThree_eq_starGamma (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ σ₃ : Bool)
    (a₁ a₂ a₃ : ZMod L) :
    kThree W m t σ₁ σ₂ σ₃ a₁ a₂ a₃
      = (W : ℂ)⁻¹ ^ 2 * (m σ₁ * m σ₂ * m σ₃) * starGamma L m t ![σ₁, σ₂, σ₃] ![a₁, a₂, a₃] := by
  rw [kThree, starGamma]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_three]
  rfl

/-- Moving a matrix factor through the star sum:
`∑_x M_{ax} ∑_b N_{xb} g(b) = ∑_b (MN)_{ab} g(b)`. -/
theorem sum_mul_sum_eq (M N : Matrix (ZMod L) (ZMod L) ℂ) (a : ZMod L) (g : ZMod L → ℂ) :
    ∑ x : ZMod L, M a x * ∑ b : ZMod L, N x b * g b = ∑ b : ZMod L, (M * N) a b * g b := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The derivative of an edge: `∂_t (Θ_{t μ})_{ab} = μ (Θ S^(B) Θ)_{ab}` (2.51). -/
theorem hasDerivAt_thetaEdge (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (a b : ZMod L) :
    HasDerivAt (fun r : ℝ => thetaEdge L m r s s' a b)
      ((thetaEdge L m t s s' * SB L * thetaEdge L m t s s') a b * (m s * m s')) t := by
  have h1 := hasDerivAt_Theta_apply L hL ht a b
  have h2 : HasDerivAt (fun ζ : ℂ => ζ * (m s * m s')) (m s * m s') (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).mul_const (m s * m s')
  exact (h1.comp (t : ℂ) h2).comp_ofReal


/-- **Example 2.16: the tree representation solves (2.48) at `n = 3`.**
Each of the three edges of the star contributes one term of (2.48), by (2.51): the edge
at `aᵢ` gives the term in which the short chain is `(σᵢ, σᵢ₊₁)`. -/
theorem hasDerivAt_kThree (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
    (σ₁ σ₂ σ₃ : Bool)
    (h₁₂ : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h₂₃ : ‖(t : ℂ) * (m σ₂ * m σ₃)‖ < 1)
    (h₃₁ : ‖(t : ℂ) * (m σ₃ * m σ₁)‖ < 1) (a₁ a₂ a₃ : ZMod L) :
    HasDerivAt (fun s => kThree W m s σ₁ σ₂ σ₃ a₁ a₂ a₃)
      ((W : ℂ) * ((∑ x : ZMod L, ∑ y : ZMod L,
            kThree W m t σ₁ σ₂ σ₃ x a₂ a₃ * SB L x y * kTwo L W m t σ₁ σ₂ a₁ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kTwo L W m t σ₁ σ₃ x a₃ * SB L x y * kThree W m t σ₁ σ₂ σ₃ a₁ a₂ y)
          + (∑ x : ZMod L, ∑ y : ZMod L,
            kThree W m t σ₁ σ₂ σ₃ a₁ x a₃ * SB L x y * kTwo L W m t σ₂ σ₃ a₂ y))) t := by
  have h₁₃ : ‖(t : ℂ) * (m σ₁ * m σ₃)‖ < 1 := by rwa [mul_comm (m σ₁)]
  set A := thetaEdge L m t σ₁ σ₂ with hA
  set B := thetaEdge L m t σ₂ σ₃ with hB
  set C := thetaEdge L m t σ₃ σ₁ with hC
  set c := (W : ℂ)⁻¹ ^ 2 * (m σ₁ * m σ₂ * m σ₃)
  -- the derivative, by the product rule on each summand
  have hd : HasDerivAt (fun s => kThree W m s σ₁ σ₂ σ₃ a₁ a₂ a₃)
      (c * ∑ b : ZMod L,
        (((A * SB L * A) a₁ b * (m σ₁ * m σ₂) * B a₂ b
            + A a₁ b * ((B * SB L * B) a₂ b * (m σ₂ * m σ₃))) * C a₃ b
          + A a₁ b * B a₂ b * ((C * SB L * C) a₃ b * (m σ₃ * m σ₁)))) t := by
    refine HasDerivAt.const_mul c (HasDerivAt.fun_sum fun b _ => ?_)
    exact ((hasDerivAt_thetaEdge hL m σ₁ σ₂ h₁₂ a₁ b).mul
      (hasDerivAt_thetaEdge hL m σ₂ σ₃ h₂₃ a₂ b)).mul
      (hasDerivAt_thetaEdge hL m σ₃ σ₁ h₃₁ a₃ b)
  refine hd.congr_deriv ?_
  -- substitute (2.57) for the short chains
  rw [mul_add, mul_add,
    rhs_kTwo_left W m t σ₁ σ₂ a₁ (fun x => kThree W m t σ₁ σ₂ σ₃ x a₂ a₃),
    rhs_kTwo_right W m t hL σ₁ σ₃ h₁₃ a₃ (fun y => kThree W m t σ₁ σ₂ σ₃ a₁ a₂ y),
    rhs_kTwo_left W m t σ₂ σ₃ a₂ (fun x => kThree W m t σ₁ σ₂ σ₃ a₁ x a₃)]
  rw [← hA, ← hB, ← hC]
  -- move the matrix factor of each term through the star sum
  have e1 : ∑ x : ZMod L, ((m σ₁ * m σ₂) • (A * SB L)) a₁ x * kThree W m t σ₁ σ₂ σ₃ x a₂ a₃
      = c * (m σ₁ * m σ₂) * ∑ b : ZMod L, (A * SB L * A) a₁ b * (B a₂ b * C a₃ b) := by
    rw [← sum_mul_sum_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [kThree, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    ring
  have e2 : ∑ x : ZMod L, ((m σ₂ * m σ₃) • (B * SB L)) a₂ x * kThree W m t σ₁ σ₂ σ₃ a₁ x a₃
      = c * (m σ₂ * m σ₃) * ∑ b : ZMod L, (B * SB L * B) a₂ b * (A a₁ b * C a₃ b) := by
    rw [← sum_mul_sum_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [kThree, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    ring_nf
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e3 : ∑ y : ZMod L, ((m σ₁ * m σ₃) • (C * SB L)) a₃ y * kThree W m t σ₁ σ₂ σ₃ a₁ a₂ y
      = c * (m σ₃ * m σ₁) * ∑ b : ZMod L, (C * SB L * C) a₃ b * (A a₁ b * B a₂ b) := by
    rw [← sum_mul_sum_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [kThree, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    ring_nf
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1, e2, e3, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- At `t = 0` the star value is the initial value of Definition 2.12 for `n = 3`:
`W⁻² m₁m₂m₃ 1(a₁ = a₂ = a₃)`. -/
theorem kThree_zero (W : ℕ) (m : Bool → ℂ) (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    kThree W m 0 σ₁ σ₂ σ₃ a₁ a₂ a₃ = primInit L W m ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ := by
  have hsum : (∑ b : ZMod L, thetaEdge L m 0 σ₁ σ₂ a₁ b * thetaEdge L m 0 σ₂ σ₃ a₂ b
      * thetaEdge L m 0 σ₃ σ₁ a₃ b) = if a₂ = a₁ ∧ a₃ = a₁ then 1 else 0 := by
    simp only [thetaEdge, Complex.ofReal_zero, zero_mul, Theta_zero, Matrix.one_apply,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    by_cases h2 : a₂ = a₁ <;> by_cases h3 : a₃ = a₁ <;> simp [h2, h3]
  have hall : (∀ x ∈ [a₁, a₂, a₃], ∀ y ∈ [a₁, a₂, a₃], x = y) ↔ (a₂ = a₁ ∧ a₃ = a₁) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨-, h12, h13⟩, -, -⟩
      exact ⟨h12.symm, h13.symm⟩
    · rintro ⟨rfl, rfl⟩
      simp
  rw [kThree, hsum, primInit]
  simp only [LoopIdx.length, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, hall]
  split_ifs <;> ring

/-- Examples 2.15 and 2.16 as one function of the loop index (`n = 2` and `n = 3`). -/
noncomputable def kLoop3 (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (ZMod L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwo L W m t σ₁ σ₂ a₁ a₂
  | [σ₁, σ₂, σ₃], [a₁, a₂, a₃] => kThree W m t σ₁ σ₂ σ₃ a₁ a₂ a₃
  | _, _ => 0

/-- **Example 2.16, general form**: at `n = 3` the tree value satisfies (2.48) with the
right-hand side built from the cut-and-glue operators, the `2`-loops being (2.57). -/
theorem hasDerivAt_kLoop3 (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
    (σ₁ σ₂ σ₃ : Bool)
    (h₁₂ : ‖(t : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h₂₃ : ‖(t : ℂ) * (m σ₂ * m σ₃)‖ < 1)
    (h₃₁ : ‖(t : ℂ) * (m σ₃ * m σ₁)‖ < 1) (a₁ a₂ a₃ : ZMod L) :
    HasDerivAt (fun s => kLoop3 W m s ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩)
      (primRhs L W (kLoop3 W m t) ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩) t := by
  rw [primRhs_three]
  exact hasDerivAt_kThree hL W m σ₁ σ₂ σ₃ h₁₂ h₂₃ h₃₁ a₁ a₂ a₃

/-- Example 2.16 with the paper's `m(σ)` at `|E| ≤ 2` (`RBM.mSigma`), for `0 ≤ t < 1`. -/
theorem hasDerivAt_kLoop3_mSigma (hL : 3 ≤ L) (W : ℕ) [NeZero W] {E t : ℝ} (hE : |E| ≤ 2)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    HasDerivAt (fun s => kLoop3 W (mSigma E) s ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩)
      (primRhs L W (kLoop3 W (mSigma E) t) ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩) t :=
  hasDerivAt_kLoop3 hL W (mSigma E) σ₁ σ₂ σ₃ (norm_mul_mSigma_lt_one hE ht0 ht1 σ₁ σ₂)
    (norm_mul_mSigma_lt_one hE ht0 ht1 σ₂ σ₃) (norm_mul_mSigma_lt_one hE ht0 ht1 σ₃ σ₁)
    a₁ a₂ a₃

/-- At `t = 0`, `kLoop3` is the initial value of Definition 2.12 on loops of length `3`. -/
theorem kLoop3_zero (W : ℕ) (m : Bool → ℂ) (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    kLoop3 W m 0 ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ = primInit L W m ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ :=
  kThree_zero W m σ₁ σ₂ σ₃ a₁ a₂ a₃

end Star

end RBM
