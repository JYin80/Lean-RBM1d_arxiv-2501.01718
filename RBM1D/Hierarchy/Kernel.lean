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

* (5.16) the generator
  `(Theta_{t,sigma} . A)_a = sum_i sum_c (xi_i * Theta^(B)_{t xi_i} S^(B))_{a_i c} A_{a^(i)}`
  (**corrected**: the displayed (5.16) drops the trailing `S^(B)`; see below)
* (5.17) the propagator  `(U_{s,t,sigma} . A)_a = sum_b prod_i K_i(a_i, b_i) A_b`,
  where `K_i = (1 - s xi_i S^(B)) (1 - t xi_i S^(B))^{-1}`
  and `xi_i = m(sigma_i) m(sigma_{i+1})`.

The whole section rests on the single-edge identity (5.18)

  `(1 - s xi S^(B)) (1 - t xi S^(B))^{-1} = 1 - (s - t) xi  S^(B) Theta^(B)_{t xi}`,

after which Lemma 7.1 is just `norm_Theta_le` plus a product-sum interchange.

## The missing `S^(B)` in (5.16)

The displayed (5.16) writes the `i`-th kernel as `xi_i Theta^(B)_{t xi_i}`.  That is a typo in
the paper: the correct kernel is `xi_i Theta^(B)_{t xi_i} S^(B)`.  Three independent
corroborations, all recorded in `docs/paper-deltas.md` (#106):

* the paper's own Example 2.16 (p. 21) displays the kernel *with* the `S^(B)`;
* `RBM.Gauss.couplingLen_two_eq_thetaGenLoop` -- the identity (5.19) between the `l_K = 2`
  coupling of (5.14) and the generator -- *forces* the `S^(B)`, because (5.14) carries the
  factor `S^(B)_{ab}` that glues the two cut loops;
* `d/dt U_{s,t,sigma} = Theta_{t,sigma} . U_{s,t,sigma}` forces it through (5.18), whose right
  side is `1 - (s-t) xi S^(B) Theta^(B)_{t xi}`.

The correction is *invisible to every row-sum argument*: `S^(B)` is row-stochastic
(`RBM.sum_SB_row`), so `Theta^(B)_xi S^(B)` and `Theta^(B)_xi` have the same row sums
(`RBM.sum_Theta_mul_SB_row`) and the same row `l^1` bound
(`RBM.sum_norm_Theta_mul_SB_row_le`).  Hence `RBM.sum_ThetaOp_row`,
`RBM.SumZero_ThetaOp` and the `l^infty` bounds of `RBM1D/Hierarchy/SumZero.lean` hold
verbatim for the corrected generator.

## Deviation from the paper's notation

The paper carries the sign vector `sigma` and forms `xi_i = m(sigma_i) m(sigma_{i+1})`.
Here the edge parameters `xi : Fin n -> C` are taken as *data*; `RBM.xiOf` recovers the
paper's choice.  This is strictly more general and keeps the sign bookkeeping out of the
analytic lemmas.  Recorded in `docs/paper-deltas.md` as a modelling choice, not an error.

## Main results

* `RBM.edgeKer_eq`             : (5.18)
* `RBM.norm_edgeKer_le`, `RBM.sum_norm_edgeKer_row_le` : the edge factor is bounded
* `RBM.Uker`, `RBM.ThetaOp`    : (5.17), (5.16) (the latter corrected, see below)
* `RBM.sum_Theta_mul_SB_row`, `RBM.sum_norm_Theta_mul_SB_row_le` : the correction of (5.16)
  is invisible to row sums
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
  have h2 : ((∑ b : ZMod L, ‖M a b‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h2

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

/-- The edge factors compose.  This is the `n = 1` case of the semigroup law. -/
theorem edgeKer_mul (hL : 3 ≤ L) {ξ s u t : ℂ} (hu : ‖u * ξ‖ < 1) (ht : ‖t * ξ‖ < 1) :
    edgeKer L ξ u t * edgeKer L ξ s u = edgeKer L ξ s t := by
  set P : Matrix (ZMod L) (ZMod L) ℂ := 1 - (s * ξ) • SB L with hP
  set Q : Matrix (ZMod L) (ZMod L) ℂ := 1 - (u * ξ) • SB L with hQ
  set Tt : Matrix (ZMod L) (ZMod L) ℂ := Theta L (t * ξ) with hTt
  set Tu : Matrix (ZMod L) (ZMod L) ℂ := Theta L (u * ξ) with hTu
  have h1 : Commute Tt P :=
    (Commute.one_right Tt).sub_right ((Theta_commute_SB L hL ht).smul_right (s * ξ))
  have h2 : Commute Q P :=
    (Commute.one_left P).sub_left
      ((Commute.one_right ((u * ξ) • SB L)).sub_right
        (((Commute.refl (SB L)).smul_left (u * ξ)).smul_right (s * ξ)))
  have h3 : Commute Tt Tu := Theta_commute L hL ht hu
  have h4 : Q * Tu = 1 := mul_Theta L hL hu
  calc edgeKer L ξ u t * edgeKer L ξ s u = Q * Tt * (P * Tu) := rfl
    _ = Q * (Tt * P) * Tu := by noncomm_ring
    _ = Q * (P * Tt) * Tu := by rw [h1.eq]
    _ = (Q * P) * (Tt * Tu) := by noncomm_ring
    _ = (P * Q) * (Tu * Tt) := by rw [h2.eq, h3.eq]
    _ = P * (Q * Tu) * Tt := by noncomm_ring
    _ = P * Tt := by rw [h4, Matrix.mul_one]

theorem sum_edgeKer_mul (hL : 3 ≤ L) {ξ s u t : ℂ} (hu : ‖u * ξ‖ < 1) (ht : ‖t * ξ‖ < 1)
    (x y : ZMod L) :
    ∑ c : ZMod L, edgeKer L ξ u t x c * edgeKer L ξ s u c y = edgeKer L ξ s t x y := by
  have h : (edgeKer L ξ u t * edgeKer L ξ s u) x y = edgeKer L ξ s t x y := by
    rw [edgeKer_mul L hL hu ht]
  rw [Matrix.mul_apply] at h
  exact h

end Edge

section Operators

variable (L : ℕ) [NeZero L]

/-- The paper's edge parameter `xi_i = m(sigma_i) m(sigma_{i+1})` of Definition 5.2. -/
noncomputable def xiOf {n : ℕ} [NeZero n] (m : Bool → ℂ) (σ : Fin n → Bool) (i : Fin n) : ℂ :=
  m (σ i) * m (σ (i + 1))

/-- **(5.17)**: the evolution kernel `U_{s,t,sigma}`. -/
noncomputable def Uker {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ)
    (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun a => ∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A b

/-! ### The kernel of the generator, `Theta^(B)_xi S^(B)`

`S^(B)` is symmetric, row-stochastic and commutes with `Theta^(B)_xi`, so appending it to
`Theta^(B)_xi` changes neither the symmetry, nor the row sums, nor the row `l^1` bound.  This
is why the typo in (5.16) is invisible to every argument in `RBM1D/Hierarchy/SumZero.lean`. -/

/-- The kernel of the generator is symmetric: both factors are, and they commute
(`RBM.Theta_commute_SB`). -/
theorem Theta_mul_SB_transpose (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (Theta L ξ * SB L)ᵀ = Theta L ξ * SB L := by
  rw [Matrix.transpose_mul, SB_transpose, Theta_transpose L hL hξ]
  exact (Theta_commute_SB L hL hξ).eq.symm

/-- **The row sums are unchanged by the `S^(B)`**: `S^(B)` is row-stochastic. -/
theorem sum_Theta_mul_SB_row (hL : 3 ≤ L) {ξ : ℂ} (x : ZMod L) :
    ∑ c : ZMod L, (Theta L ξ * SB L) x c = ∑ y : ZMod L, Theta L ξ x y := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, sum_SB_row L hL y, mul_one]

/-- The row `l^1` bound is unchanged by the `S^(B)`: `‖S^(B)‖ = 1`. -/
theorem sum_norm_Theta_mul_SB_row_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖(Theta L ξ * SB L) x c‖ ≤ (1 - ‖ξ‖)⁻¹ := by
  refine (sum_norm_row_le L _ x).trans ?_
  calc ‖Theta L ξ * SB L‖ ≤ ‖Theta L ξ‖ * ‖SB L‖ := norm_mul_le _ _
    _ = ‖Theta L ξ‖ := by rw [norm_SB L hL, mul_one]
    _ ≤ (1 - ‖ξ‖)⁻¹ := norm_Theta_le L hL hξ

/-- **(5.16), corrected**: the generator `Theta_{t,sigma}`.  The `i`-th summand replaces the
`i`-th external index by a new one, which is `Function.update` here and `a^(i)` in the paper.

The displayed (5.16) has `xi_i Theta^(B)_{t xi_i}` where this has
`xi_i Theta^(B)_{t xi_i} S^(B)`; see the module docstring and `docs/paper-deltas.md` #106 for
why the paper's display is a typo, and why the correction leaves every row-sum consequence
of (5.16) intact. -/
noncomputable def ThetaOp {n : ℕ} (ξ : Fin n → ℂ) (t : ℂ)
    (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun a => ∑ i : Fin n, ∑ c : ZMod L,
    (ξ i * (Theta L (t * ξ i) * SB L) (a i) c) * A (Function.update a i c)

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
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
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

/-- At `s = t` the evolution kernel is the identity. -/
theorem Uker_self (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) (A : LoopArg L n → ℂ) :
    Uker L ξ t t A = A := by
  funext a
  have hprod : ∀ b : LoopArg L n,
      (∏ i, edgeKer L (ξ i) t t (a i) (b i)) = if a = b then (1 : ℂ) else 0 := by
    intro b
    have hone : ∀ i : Fin n,
        edgeKer L (ξ i) t t (a i) (b i) = if a i = b i then (1 : ℂ) else 0 := by
      intro i
      rw [edgeKer_self L hL (ht i), Matrix.one_apply]
    rw [Finset.prod_congr rfl fun i _ => hone i, Fintype.prod_boole]
    congr 1
    simp [funext_iff]
  calc Uker L ξ t t A a
      = ∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) t t (a i) (b i)) * A b := rfl
    _ = ∑ b : LoopArg L n, (if a = b then A b else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hprod b]
        split <;> simp
    _ = A a := by simp

/-- **The semigroup law** `U_{u,t} . U_{s,u} = U_{s,t}`, the `n`-fold version of
`edgeKer_mul`.  Together with `Uker_self` this is what makes `U` an evolution kernel. -/
theorem Uker_comp (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ} {s u t : ℂ}
    (hu : ∀ i, ‖u * ξ i‖ < 1) (ht : ∀ i, ‖t * ξ i‖ < 1) (A : LoopArg L n → ℂ) :
    Uker L ξ u t (Uker L ξ s u A) = Uker L ξ s t A := by
  funext a
  calc Uker L ξ u t (Uker L ξ s u A) a
      = ∑ c : LoopArg L n, (∏ i, edgeKer L (ξ i) u t (a i) (c i))
          * ∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) s u (c i) (b i)) * A b := rfl
    _ = ∑ c : LoopArg L n, ∑ b : LoopArg L n,
          (∏ i, edgeKer L (ξ i) u t (a i) (c i) * edgeKer L (ξ i) s u (c i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ b : LoopArg L n, ∑ c : LoopArg L n,
          (∏ i, edgeKer L (ξ i) u t (a i) (c i) * edgeKer L (ξ i) s u (c i) (b i)) * A b :=
        Finset.sum_comm
    _ = ∑ b : LoopArg L n, (∏ i, edgeKer L (ξ i) s t (a i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul,
          sum_prod_pi L (fun i x => edgeKer L (ξ i) u t (a i) x * edgeKer L (ξ i) s u x (b i))]
        congr 1
        exact Finset.prod_congr rfl fun i _ => sum_edgeKer_mul L hL (hu i) (ht i) (a i) (b i)
    _ = Uker L ξ s t A a := rfl

end Operators

end RBM
