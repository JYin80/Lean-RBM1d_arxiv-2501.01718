/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Bounds

/-!
# Definition 5.2: the tensor propagator and the evolution kernel

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Definition 5.2 (p. 53) and Lemma 7.1 (p. 76).

For an `n`-loop the paper introduces two linear operators on tensors
`A : (Z_L)^n -> C`:

* (5.16) the generator   `(Theta_{t,sigma} . A)_a = sum_i sum_c (xi_i * Theta_{t xi_i})_{a_i c} A_{a^(i)}`
* (5.17) the propagator  `(U_{s,t,sigma} . A)_a = sum_b prod_i K_i(a_i, b_i) A_b`,
  where `K_i = (1 - s xi_i S^(B)) (1 - t xi_i S^(B))^{-1}` and `xi_i = m(sigma_i) m(sigma_{i+1})`.

The whole section rests on the single-edge identity (5.18)

  `(1 - s xi S^(B)) (1 - t xi S^(B))^{-1} = 1 - (s - t) xi  S^(B) Theta^(B)_{t xi}`,

after which Lemma 7.1 is just `norm_Theta_le` plus a product-sum interchange.

## Deviation from the paper's notation

The paper carries the sign vector `sigma` and forms `xi_i = m(sigma_i) m(sigma_{i+1})`.
Here the edge parameters `xi : Fin n -> C` are taken as *data*; `RBM.xiOf` recovers the
paper's choice.  This is strictly more general and keeps the sign bookkeeping out of the
analytic lemmas.  Recorded in `docs/paper-deltas.md` as a modelling choice, not an error.

## Main results

* `RBM.edgeKer_eq`             : (5.18)
* `RBM.norm_edgeKer_le`, `RBM.sum_norm_edgeKer_row_le` : the edge factor is bounded
* `RBM.Uker`, `RBM.ThetaOp`    : (5.17), (5.16)
* `RBM.norm_Uker_apply_le`     : Lemma 7.1 / (7.1), with an explicit constant
-/

namespace RBM

open Matrix Finset
open scoped Matrix.Norms.Operator

/-- The `n` external block indices of an `n`-loop. -/
abbrev LoopArg (L n : ℕ) := Fin n → ZMod L

section Interchange

variable (L : ℕ) [NeZero L]

/-- Product-sum interchange over the `n`-fold index set: this is what turns the
`n`-fold sum in (5.17) into a product of `n` row sums. -/
theorem sum_prod_pi {R : Type*} [CommSemiring R] {n : ℕ} (g : Fin n → ZMod L → R) :
    ∑ b : LoopArg L n, ∏ i, g i (b i) = ∏ i, ∑ j : ZMod L, g i j := by
  rw [← Finset.sum_prod_piFinset (Finset.univ : Finset (ZMod L)) g, Fintype.piFinset_univ]

/-- Every row of a matrix has `l^1` norm at most the `l^infty` operator norm. -/
theorem sum_norm_row_le (M : Matrix (ZMod L) (ZMod L) ℂ) (a : ZMod L) :
    ∑ b : ZMod L, ‖M a b‖ ≤ ‖M‖ := by
  have h : ∑ b : ZMod L, ‖M a b‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : ZMod L, ‖M i j‖₊) (Finset.mem_univ a)
  exact_mod_cast h

end Interchange

section Edge

variable (L : ℕ) [NeZero L]

/-- The single-edge factor of (5.17): `(1 - s xi S^(B)) (1 - t xi S^(B))^{-1}`. -/
noncomputable def edgeKer (ξ s t : ℂ) : Matrix (ZMod L) (ZMod L) ℂ :=
  (1 - (s * ξ) • SB L) * Theta L (t * ξ)

/-- **(5.18)**: the edge factor is the identity plus an `(s - t)`-small correction.
This is the identity the whole of §5 and §7.1 is built on. -/
theorem edgeKer_eq (hL : 3 ≤ L) {ξ s t : ℂ} (ht : ‖t * ξ‖ < 1) :
    edgeKer L ξ s t = 1 - ((s - t) * ξ) • (SB L * Theta L (t * ξ)) := by
  have hsplit : (1 : Matrix (ZMod L) (ZMod L) ℂ) - (s * ξ) • SB L
      = (1 - (t * ξ) • SB L) - ((s - t) * ξ) • SB L := by
    have h : (s * ξ) • SB L = (t * ξ) • SB L + ((s - t) * ξ) • SB L := by
      rw [← add_smul]
      congr 1
      ring
    rw [h]
    abel
  rw [edgeKer, hsplit, Matrix.sub_mul, mul_Theta L hL ht, Matrix.smul_mul]

/-- At `s = t` the edge factor is the identity. -/
theorem edgeKer_self (hL : 3 ≤ L) {ξ t : ℂ} (ht : ‖t * ξ‖ < 1) :
    edgeKer L ξ t t = 1 := by
  rw [edgeKer_eq L hL ht, sub_self, zero_mul, zero_smul, sub_zero]

/-- The edge factor is bounded in the `l^infty` operator norm. -/
theorem norm_edgeKer_le (hL : 3 ≤ L) {ξ s t : ℂ} (ht : ‖t * ξ‖ < 1) :
    ‖edgeKer L ξ s t‖ ≤ 1 + ‖(s - t) * ξ‖ * (1 - ‖t * ξ‖)⁻¹ := by
  have hsb : ‖SB L * Theta L (t * ξ)‖ ≤ (1 - ‖t * ξ‖)⁻¹ := by
    calc ‖SB L * Theta L (t * ξ)‖ ≤ ‖SB L‖ * ‖Theta L (t * ξ)‖ := norm_mul_le _ _
      _ = ‖Theta L (t * ξ)‖ := by rw [norm_SB L hL, one_mul]
      _ ≤ (1 - ‖t * ξ‖)⁻¹ := norm_Theta_le L hL ht
  have h2 : ‖((s - t) * ξ) • (SB L * Theta L (t * ξ))‖
      ≤ ‖(s - t) * ξ‖ * (1 - ‖t * ξ‖)⁻¹ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hsb (norm_nonneg _)
  have h1 : ‖(1 : Matrix (ZMod L) (ZMod L) ℂ)‖ = 1 := norm_one
  calc ‖edgeKer L ξ s t‖
      = ‖(1 : Matrix (ZMod L) (ZMod L) ℂ)
          - ((s - t) * ξ) • (SB L * Theta L (t * ξ))‖ := by rw [edgeKer_eq L hL ht]
    _ ≤ ‖(1 : Matrix (ZMod L) (ZMod L) ℂ)‖
          + ‖((s - t) * ξ) • (SB L * Theta L (t * ξ))‖ := norm_sub_le _ _
    _ ≤ 1 + ‖(s - t) * ξ‖ * (1 - ‖t * ξ‖)⁻¹ := by rw [h1]; linarith

/-- Row-wise `l^1` form of `norm_edgeKer_le`. -/
theorem sum_norm_edgeKer_row_le (hL : 3 ≤ L) {ξ s t : ℂ} (ht : ‖t * ξ‖ < 1) (a : ZMod L) :
    ∑ b : ZMod L, ‖edgeKer L ξ s t a b‖ ≤ 1 + ‖(s - t) * ξ‖ * (1 - ‖t * ξ‖)⁻¹ :=
  (sum_norm_row_le L _ a).trans (norm_edgeKer_le L hL ht)

end Edge

section Operators

variable (L : ℕ) [NeZero L]

/-- The paper's edge parameter `xi_i = m(sigma_i) m(sigma_{i+1})` of Definition 5.2. -/
noncomputable def xiOf {n : ℕ} (m : Bool → ℂ) (σ : Fin n → Bool) (i : Fin n) : ℂ :=
  m (σ i) * m (σ (i + 1))

/-- **(5.17)**: the evolution kernel `U_{s,t,sigma}`. -/
noncomputable def Uker {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ)
    (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun a => ∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A b

/-- **(5.16)**: the generator `Theta_{t,sigma}`.  The `i`-th summand replaces the `i`-th
external index by a new one, which is `Function.update` here and `a^(i)` in the paper. -/
noncomputable def ThetaOp {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun a => ∑ i : Fin n, ∑ c : ZMod L,
    (ξ i * Theta L (t * ξ i) (a i) c) * A (Function.update a i c)

theorem Uker_apply {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (A : LoopArg L n → ℂ)
    (a : LoopArg L n) :
    Uker L ξ s t A a = ∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A b :=
  rfl

/-- `U_{s,t}` is linear in the tensor. -/
theorem Uker_add {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (A B : LoopArg L n → ℂ) :
    Uker L ξ s t (A + B) = Uker L ξ s t A + Uker L ξ s t B := by
  funext a
  simp only [Uker, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

theorem Uker_smul {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (c : ℂ) (A : LoopArg L n → ℂ) :
    Uker L ξ s t (c • A) = c • Uker L ξ s t A := by
  funext a
  simp only [Uker, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Lemma 7.1 / (7.1)**, with an explicit constant: if every edge factor has row
`l^1` norm at most `C`, then `U_{s,t,sigma}` has `max`-norm at most `C^n`.
Combined with (2.52) this is the paper's `(eta_s / eta_t)^n`. -/
theorem norm_Uker_apply_le (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {s t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) {C M : ℝ} (hM0 : 0 ≤ M)
    (hC : ∀ i, 1 + ‖(s - t) * ξ i‖ * (1 - ‖t * ξ i‖)⁻¹ ≤ C)
    {A : LoopArg L n → ℂ} (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L n) :
    ‖Uker L ξ s t A a‖ ≤ C ^ n * M := by
  have hrow : ∀ i : Fin n, ∑ c : ZMod L, ‖edgeKer L (ξ i) s t (a i) c‖ ≤ C :=
    fun i => (sum_norm_edgeKer_row_le L hL (ht i) (a i)).trans (hC i)
  have hstep : (∑ b : LoopArg L n, ∏ i, ‖edgeKer L (ξ i) s t (a i) (b i)‖) ≤ C ^ n := by
    rw [sum_prod_pi L (fun i c => ‖edgeKer L (ξ i) s t (a i) c‖)]
    calc (∏ i : Fin n, ∑ c : ZMod L, ‖edgeKer L (ξ i) s t (a i) c‖)
        ≤ ∏ _i : Fin n, C :=
          Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (fun i _ => hrow i)
      _ = C ^ n := by simp
  calc ‖Uker L ξ s t A a‖
      ≤ ∑ b : LoopArg L n, ‖(∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : LoopArg L n, (∏ i, ‖edgeKer L (ξ i) s t (a i) (b i)‖) * M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hA b) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (∑ b : LoopArg L n, ∏ i, ‖edgeKer L (ξ i) s t (a i) (b i)‖) * M := by
        rw [← Finset.sum_mul]
    _ ≤ C ^ n * M := mul_le_mul_of_nonneg_right hstep hM0

end Operators

end RBM
