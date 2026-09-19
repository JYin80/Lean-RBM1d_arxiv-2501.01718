/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel

/-!
# Definition 5.12: the sum-zero operator `Q_t`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Definition 5.12 and Lemma 5.13 (pp. 66-69).

For a tensor `A : (Z_L)^{n+1} -> C` the paper sets

* `(P . A)_{a_1} = sum_{a_2, ..., a_n} A_a`,  and `A` has the *sum-zero property* iff `P . A = 0`;
* `vartheta_{t,a} = (1-t)^{n-1} prod_{i=2}^n (Theta^(B)_t)_{a_1 a_i}`;
* `(Q_t . A)_a = A_a - (P . A)_{a_1} * vartheta_{t,a}`.

Since `sum_b (Theta^(B)_t)_{ab} = (1-t)^{-1}` (`RBM.sum_Theta_row`), one gets `P . vartheta = 1`
and hence `P . (Q_t . A) = 0`: `Q_t` projects onto the sum-zero tensors.  This is the device
that removes the `(eta_s / eta_t)` prefactor from Step 2, so that it does not accumulate over
the time-splitting of Theorem 2.21.

## Indexing convention

An `n`-loop with `n >= 1` is indexed here by `Fin (n+1) -> ZMod L`, with the distinguished
first index `a 0` playing the role of the paper's `a_1` and `Fin.cons` splitting off the
remaining `n` indices.  So the paper's `n` is this file's `n + 1`, and the paper's
`(1-t)^{n-1}` is `(1-t)^n` here.  Recorded in `docs/paper-deltas.md` as a modelling choice.

## Main results

* `RBM.Psum`, `RBM.SumZero`, `RBM.vartheta`, `RBM.Qop` : Definition 5.12
* `RBM.Psum_vartheta`  : `P . vartheta_t = 1`
* `RBM.SumZero_Qop`    : `P . (Q_t . A) = 0`
* `RBM.norm_vartheta_le`, `RBM.norm_Qop_apply_le` : the bounds behind Lemma 5.13 (5.87)
* `RBM.sum_ThetaOp_row` : the row-sum identity of p. 66
-/

namespace RBM

open Matrix Finset
open scoped Matrix.Norms.Operator

variable (L : ℕ) [NeZero L]

/-- Definition 5.12: `(P . A)_{a_1} = sum_{a_2, ..., a_n} A_a`. -/
def Psum {n : ℕ} (A : LoopArg L (n + 1) → ℂ) (x : ZMod L) : ℂ :=
  ∑ r : LoopArg L n, A (Fin.cons x r)

/-- Definition 5.12: the sum-zero property. -/
def SumZero {n : ℕ} (A : LoopArg L (n + 1) → ℂ) : Prop := ∀ x, Psum L A x = 0

/-- Definition 5.12: `vartheta_{t,a} = (1-t)^{n-1} prod_{i=2}^n (Theta^(B)_t)_{a_1 a_i}`. -/
noncomputable def vartheta {n : ℕ} (t : ℂ) (a : LoopArg L (n + 1)) : ℂ :=
  (1 - t) ^ n * ∏ i : Fin n, Theta L t (a 0) (a i.succ)

/-- Definition 5.12: `(Q_t . A)_a = A_a - (P . A)_{a_1} * vartheta_{t,a}`. -/
noncomputable def Qop {n : ℕ} (t : ℂ) (A : LoopArg L (n + 1) → ℂ) :
    LoopArg L (n + 1) → ℂ :=
  fun a => A a - Psum L A (a 0) * vartheta L t a

theorem vartheta_cons {n : ℕ} (t : ℂ) (x : ZMod L) (r : LoopArg L n) :
    vartheta L t (Fin.cons x r) = (1 - t) ^ n * ∏ i : Fin n, Theta L t x (r i) := by
  simp [vartheta]

/-- `P . vartheta_t = 1`: the reference tensor has total mass one in every slot. -/
theorem Psum_vartheta (hL : 3 ≤ L) {n : ℕ} {t : ℂ} (ht : ‖t‖ < 1) (x : ZMod L) :
    Psum L (vartheta L (n := n) t) x = 1 := by
  have hne : (1 : ℂ) - t ≠ 0 := one_sub_ne_zero ht
  rw [Psum, Finset.sum_congr rfl fun r _ => vartheta_cons L t x r, ← Finset.mul_sum,
    sum_prod_pi L (fun (_ : Fin n) (c : ZMod L) => Theta L t x c),
    Finset.prod_congr rfl fun (i : Fin n) _ => sum_Theta_row L hL ht x,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp

/-- `Q_t` lands in the sum-zero tensors. -/
theorem SumZero_Qop (hL : 3 ≤ L) {n : ℕ} {t : ℂ} (ht : ‖t‖ < 1)
    (A : LoopArg L (n + 1) → ℂ) : SumZero L (Qop L t A) := by
  intro x
  have hstep : ∀ r : LoopArg L n,
      Qop L t A (Fin.cons x r) = A (Fin.cons x r) - Psum L A x * vartheta L t (Fin.cons x r) := by
    intro r
    rw [Qop]
    simp
  have hv : ∑ r : LoopArg L n, vartheta L t (Fin.cons x r) = 1 := Psum_vartheta L hL ht x
  rw [Psum, Finset.sum_congr rfl fun r _ => hstep r, Finset.sum_sub_distrib, ← Finset.mul_sum, hv,
    mul_one]
  exact sub_self _

/-- `Q_t` acts as the identity on tensors that already have the sum-zero property. -/
theorem Qop_of_sumZero {n : ℕ} {t : ℂ} {A : LoopArg L (n + 1) → ℂ} (hA : SumZero L A) :
    Qop L t A = A := by
  funext a
  rw [Qop, hA (a 0), zero_mul, sub_zero]

/-- The entries of `vartheta_t` are bounded; the first half of Lemma 5.13 (5.87). -/
theorem norm_vartheta_le (hL : 3 ≤ L) {n : ℕ} {t : ℂ} (ht : ‖t‖ < 1)
    (a : LoopArg L (n + 1)) :
    ‖vartheta L t a‖ ≤ ‖1 - t‖ ^ n * ((1 - ‖t‖)⁻¹) ^ n := by
  have hb : ∏ i : Fin n, ‖Theta L t (a 0) (a i.succ)‖ ≤ ((1 - ‖t‖)⁻¹) ^ n := by
    calc ∏ i : Fin n, ‖Theta L t (a 0) (a i.succ)‖
        ≤ ∏ _i : Fin n, (1 - ‖t‖)⁻¹ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
            (fun i _ => norm_Theta_apply_le L hL ht _ _)
      _ = ((1 - ‖t‖)⁻¹) ^ n := by simp
  rw [vartheta, norm_mul, norm_pow, norm_prod]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- The second half of Lemma 5.13 (5.87): `Q_t` is bounded in the max norm. -/
theorem norm_Qop_apply_le {n : ℕ} {t : ℂ} (A : LoopArg L (n + 1) → ℂ)
    (a : LoopArg L (n + 1)) :
    ‖Qop L t A a‖ ≤ ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by
  rw [Qop]
  calc ‖A a - Psum L A (a 0) * vartheta L t a‖
      ≤ ‖A a‖ + ‖Psum L A (a 0) * vartheta L t a‖ := norm_sub_le _ _
    _ = ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by rw [norm_mul]

/-- The row-sum identity of p. 66: the row sums of `xi * Theta^(B)_{t xi}` do not depend on
the row.  This is the reason `P . A = 0` is preserved by the generator `Theta_{t,sigma}`. -/
theorem sum_ThetaOp_row (hL : 3 ≤ L) {ξ t : ℂ} (h : ‖t * ξ‖ < 1) (x : ZMod L) :
    ∑ c : ZMod L, ξ * Theta L (t * ξ) x c = ξ / (1 - t * ξ) := by
  rw [← Finset.mul_sum, sum_Theta_row L hL h, div_eq_mul_inv]

/-- `P` is additive. -/
theorem Psum_add {n : ℕ} (A B : LoopArg L (n + 1) → ℂ) :
    Psum L (A + B) = Psum L A + Psum L B := by
  funext x
  simp [Psum, Finset.sum_add_distrib]

/-- `P` is homogeneous. -/
theorem Psum_smul {n : ℕ} (c : ℂ) (A : LoopArg L (n + 1) → ℂ) :
    Psum L (c • A) = c • Psum L A := by
  funext x
  simp [Psum, Finset.mul_sum]

end RBM
