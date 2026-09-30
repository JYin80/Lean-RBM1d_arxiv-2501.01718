/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel

/-!
# Definition 5.12: the sum-zero operator `Q_t`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Definition 5.12 and Lemma 5.13.

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
`(1-t)^{n-1}` is `(1-t)^n` here.

## Main results

* `RBM.Psum`, `RBM.SumZero`, `RBM.vartheta`, `RBM.Qop` : Definition 5.12
* `RBM.Psum_vartheta`  : `P . vartheta_t = 1`
* `RBM.SumZero_Qop`    : `P . (Q_t . A) = 0`
* `RBM.norm_Qop_apply_le` : the bound behind Lemma 5.13 (5.87)
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
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow,
    mul_inv_cancel₀ hne, one_pow]

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

/-- The second half of Lemma 5.13 (5.87): `Q_t` is bounded in the max norm. -/
theorem norm_Qop_apply_le {n : ℕ} {t : ℂ} (A : LoopArg L (n + 1) → ℂ)
    (a : LoopArg L (n + 1)) :
    ‖Qop L t A a‖ ≤ ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by
  rw [Qop]
  calc ‖A a - Psum L A (a 0) * vartheta L t a‖
      ≤ ‖A a‖ + ‖Psum L A (a 0) * vartheta L t a‖ := norm_sub_le _ _
    _ = ‖A a‖ + ‖Psum L A (a 0)‖ * ‖vartheta L t a‖ := by rw [norm_mul]

/-! ### The sum-zero property is preserved by the generator

This is the identity of §5.5 that makes the whole `Q_t` device work: because the row sums
of `xi * Theta^(B)_{t xi}` do not depend on the row, applying `Theta_{t,sigma}` to a
sum-zero tensor gives a sum-zero tensor, and hence `P . ([Q_t, Theta_{t,sigma}] . A) = 0`,
which is (5.90). -/

/-- The map `(r, c) |-> (update r j c, r j)` is an involution of `(Fin n -> Z_L) x Z_L`;
this is the re-indexing behind the sum-zero property (5.90). -/
theorem sum_sum_update_swap {n : ℕ} (j : Fin n) (F : ZMod L → ZMod L → LoopArg L n → ℂ) :
    ∑ r : LoopArg L n, ∑ c : ZMod L, F (r j) c (Function.update r j c)
      = ∑ r : LoopArg L n, ∑ c : ZMod L, F c (r j) r := by
  have hinv : Function.Involutive
      (fun p : LoopArg L n × ZMod L => (Function.update p.1 j p.2, p.1 j)) := by
    intro p
    refine Prod.ext ?_ ?_
    · funext i
      simp only [Function.update_apply]
      by_cases h : i = j <;> simp [h]
    · simp
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective _ hinv.bijective _ _ ?_
  intro p
  simp

theorem update_cons_zero {n : ℕ} (x c : ZMod L) (r : LoopArg L n) :
    Function.update (Fin.cons x r : LoopArg L (n + 1)) 0 c = Fin.cons c r := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ k => simp [Function.update_apply, (Fin.succ_ne_zero k)]

theorem update_cons_succ {n : ℕ} (x c : ZMod L) (r : LoopArg L n) (j : Fin n) :
    Function.update (Fin.cons x r : LoopArg L (n + 1)) j.succ c
      = Fin.cons x (Function.update r j c) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Function.update_apply, (Fin.succ_ne_zero j).symm]
  | succ k =>
      by_cases h : k = j
      · subst h; simp
      · have hk : k.succ ≠ j.succ := fun hh => h (by simpa using hh)
        simp [Function.update_apply, hk, h]

/-- `P` is compatible with subtraction. -/
theorem Psum_sub {n : ℕ} (A B : LoopArg L (n + 1) → ℂ) :
    Psum L (A - B) = Psum L A - Psum L B := by
  funext x
  simp [Psum, Finset.sum_sub_distrib]

/-! ### The two-slot version, (5.104)

`E (x) E` of Definition 5.4 carries two loop index tuples, so the martingale estimate of
§5.5 needs `Q_t` applied in each slot separately.  Nothing below depends on Definition 5.4
itself: these are statements about an arbitrary two-tensor, so they do not depend on the
`E (x) E` layer. -/

section TwoSlot

variable {n m : ℕ}

/-- `Q_t` applied in the first slot. -/
noncomputable def Qop₁ (t : ℂ) (A : LoopArg L (n + 1) → LoopArg L (m + 1) → ℂ) :
    LoopArg L (n + 1) → LoopArg L (m + 1) → ℂ :=
  fun a b => Qop L t (fun a' => A a' b) a

/-- `Q_t` applied in the second slot. -/
noncomputable def Qop₂ (t : ℂ) (A : LoopArg L (n + 1) → LoopArg L (m + 1) → ℂ) :
    LoopArg L (n + 1) → LoopArg L (m + 1) → ℂ :=
  fun a b => Qop L t (fun b' => A a b') b

end TwoSlot

end RBM
