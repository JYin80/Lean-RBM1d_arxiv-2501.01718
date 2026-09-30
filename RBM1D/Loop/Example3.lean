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
`3`-gon has `T SP = {∅}`, a single tree, the star with one internal
vertex, and the claim is that

  `K_{t,σ,(a₁,a₂,a₃)} = W⁻² m₁m₂m₃ ∑_b (Θ_{t m₁m₂})_{a₁b} (Θ_{t m₂m₃})_{a₂b} (Θ_{t m₃m₁})_{a₃b}`

solves (2.48) with the initial value of Definition 2.12.  The boundary edge at `aᵢ` carries
`Θ_{t mᵢ mᵢ₊₁}`, the convention fixed in `RBM1D.Loop.Tree` (`RBM.thetaEdge`).

## Index check at `n = 3`

At `n = 3` the general right-hand side of (2.48), built from `cutGlueL`/`cutGlueR`, expands
into its three terms `(k,l) = (1,2), (1,3), (2,3)`.  The terms
`(1,2)` and `(2,3)` agree with the paper's display after swapping the dummy indices
(symmetry of `S^(B)`).  The wrap-around term `(1,3)` comes out as `K_{(σ₁,σ₃),(b,a₃)}`,
the paper writes `K_{(σ₃,σ₁),(a₃,b)}`: these are the same `2`-loop read from a different
starting point, so they agree for any `K` invariant under cyclic rotation of loops, and in
particular for `RBM.kTwo`, where it is the symmetry of
`Θ` (`RBM.kTwo_rotate`).

## Main results

* `RBM.rhs_kTwo_left`, `RBM.rhs_kTwo_right` : substituting (2.57) for the short chain
  (the second step of Example 2.16), `W · W⁻¹ = 1`
* `RBM.kThree` : the star value
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

section SymmetricKernel

omit [NeZero L] in
/-- `S^(B)` is symmetric, entrywise. -/
theorem SB_apply_comm (x y : ZMod L) : SB L x y = SB L y x :=
  congrFun (congrFun (SB_transpose L) y) x

end SymmetricKernel

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

/-- The derivative of an edge: `∂_t (Θ_{t μ})_{ab} = μ (Θ S^(B) Θ)_{ab}` (2.51). -/
theorem hasDerivAt_thetaEdge (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (a b : ZMod L) :
    HasDerivAt (fun r : ℝ => thetaEdge L m r s s' a b)
      ((thetaEdge L m t s s' * SB L * thetaEdge L m t s s') a b * (m s * m s')) t := by
  have h1 := hasDerivAt_Theta_apply L hL ht a b
  have h2 : HasDerivAt (fun ζ : ℂ => ζ * (m s * m s')) (m s * m s') (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).mul_const (m s * m s')
  exact (h1.comp (t : ℂ) h2).comp_ofReal


end Star

end RBM
