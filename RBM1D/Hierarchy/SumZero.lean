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

/-! ### The sum-zero property is preserved by the generator

This is the identity on p. 66 that makes the whole `Q_t` device work: because the row sums
of `xi * Theta^(B)_{t xi}` do not depend on the row, applying `Theta_{t,sigma}` to a
sum-zero tensor gives a sum-zero tensor, and hence `P . ([Q_t, Theta_{t,sigma}] . A) = 0`,
which is (5.90). -/

/-- The map `(r, c) |-> (update r j c, r j)` is an involution of `(Fin n -> Z_L) x Z_L`;
this is the re-indexing behind `SumZero_ThetaOp`. -/
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

/-- The `i = 1` summand of (5.16), after summing out the slots `2..n`. -/
theorem Psum_ThetaOp_zero_term {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ)
    (A : LoopArg L (n + 1) → ℂ) (x : ZMod L) :
    (∑ r : LoopArg L n, ∑ c : ZMod L,
        (ξ 0 * Theta L (t * ξ 0) ((Fin.cons x r : LoopArg L (n + 1)) 0) c)
          * A (Function.update (Fin.cons x r : LoopArg L (n + 1)) 0 c))
      = ∑ c : ZMod L, (ξ 0 * Theta L (t * ξ 0) x c) * Psum L A c := by
  have hstep : ∀ (r : LoopArg L n) (c : ZMod L),
      (ξ 0 * Theta L (t * ξ 0) ((Fin.cons x r : LoopArg L (n + 1)) 0) c)
          * A (Function.update (Fin.cons x r : LoopArg L (n + 1)) 0 c)
        = (ξ 0 * Theta L (t * ξ 0) x c) * A (Fin.cons c r) := by
    intro r c
    rw [Fin.cons_zero, update_cons_zero L x c r]
  rw [Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => hstep r c,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_sum]
  rfl

/-- The `i >= 2` summands of (5.16), after summing out the slots `2..n`.  Each contributes
the *same* multiple of `(P . A)_{a_1}`, because the row sums of `Theta^(B)` do not depend
on the row -- this is the identity on p. 66. -/
theorem Psum_ThetaOp_succ_term (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) (A : LoopArg L (n + 1) → ℂ) (x : ZMod L) (j : Fin n) :
    (∑ r : LoopArg L n, ∑ c : ZMod L,
        (ξ j.succ * Theta L (t * ξ j.succ) ((Fin.cons x r : LoopArg L (n + 1)) j.succ) c)
          * A (Function.update (Fin.cons x r : LoopArg L (n + 1)) j.succ c))
      = (ξ j.succ * (1 - t * ξ j.succ)⁻¹) * Psum L A x := by
  have hsym : ∀ y c : ZMod L,
      Theta L (t * ξ j.succ) c y = Theta L (t * ξ j.succ) y c := by
    intro y c
    have h := congrFun (congrFun (Theta_transpose L hL (ht j.succ)) y) c
    simpa [Matrix.transpose_apply] using h
  have hcol : ∀ y : ZMod L, ∑ c : ZMod L, ξ j.succ * Theta L (t * ξ j.succ) c y
      = ξ j.succ * (1 - t * ξ j.succ)⁻¹ := by
    intro y
    rw [← Finset.mul_sum, Finset.sum_congr rfl fun c _ => hsym y c,
      sum_Theta_row L hL (ht j.succ) y]
  have hstep : ∀ (r : LoopArg L n) (c : ZMod L),
      (ξ j.succ * Theta L (t * ξ j.succ) ((Fin.cons x r : LoopArg L (n + 1)) j.succ) c)
          * A (Function.update (Fin.cons x r : LoopArg L (n + 1)) j.succ c)
        = (ξ j.succ * Theta L (t * ξ j.succ) (r j) c)
            * A (Fin.cons x (Function.update r j c)) := by
    intro r c
    rw [Fin.cons_succ, update_cons_succ L x c r j]
  rw [Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => hstep r c,
    sum_sum_update_swap L j
      (fun y c r => (ξ j.succ * Theta L (t * ξ j.succ) y c) * A (Fin.cons x r))]
  calc ∑ r : LoopArg L n, ∑ c : ZMod L,
        (ξ j.succ * Theta L (t * ξ j.succ) c (r j)) * A (Fin.cons x r)
      = ∑ r : LoopArg L n, (∑ c : ZMod L, ξ j.succ * Theta L (t * ξ j.succ) c (r j))
          * A (Fin.cons x r) :=
        Finset.sum_congr rfl fun r _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ r : LoopArg L n, (ξ j.succ * (1 - t * ξ j.succ)⁻¹) * A (Fin.cons x r) :=
        Finset.sum_congr rfl fun r _ => by rw [hcol (r j)]
    _ = (ξ j.succ * (1 - t * ξ j.succ)⁻¹) * Psum L A x := by
        rw [← Finset.mul_sum]
        rfl

/-- **p. 66**, sharp form: the action of the generator on the slot sums.  The first slot
contributes a `Theta^(B)`-average of `P . A`, every other slot contributes the constant
`xi_i / (1 - t xi_i)` times `P . A` at the same point. -/
theorem Psum_ThetaOp_eq (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) (A : LoopArg L (n + 1) → ℂ) (x : ZMod L) :
    Psum L (ThetaOp L ξ t A) x
      = (∑ c : ZMod L, (ξ 0 * Theta L (t * ξ 0) x c) * Psum L A c)
        + (∑ j : Fin n, ξ j.succ * (1 - t * ξ j.succ)⁻¹) * Psum L A x := by
  have hexp : ∀ r : LoopArg L n, ThetaOp L ξ t A (Fin.cons x r)
      = ∑ i : Fin (n + 1), ∑ c : ZMod L,
          (ξ i * Theta L (t * ξ i) ((Fin.cons x r : LoopArg L (n + 1)) i) c)
            * A (Function.update (Fin.cons x r : LoopArg L (n + 1)) i c) :=
    fun r => rfl
  rw [Psum, Finset.sum_congr rfl fun r _ => hexp r, Finset.sum_comm, Fin.sum_univ_succ,
    Psum_ThetaOp_zero_term L ξ t A x,
    Finset.sum_congr rfl fun j _ => Psum_ThetaOp_succ_term L hL ht A x j,
    ← Finset.sum_mul]

/-- **p. 66**: `P . A = 0` implies `P . (Theta_{t,sigma} . A) = 0`. -/
theorem SumZero_ThetaOp (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) {A : LoopArg L (n + 1) → ℂ} (hA : SumZero L A) :
    SumZero L (ThetaOp L ξ t A) := by
  intro x
  rw [Psum_ThetaOp_eq L hL ht A x, hA x, mul_zero,
    Finset.sum_congr rfl fun c _ => by rw [hA c, mul_zero]]
  simp

/-- The deterministic content of **(5.99)**: the slot sums of `Theta_{t,sigma} . A` are
controlled by the slot sums of `A`, with an explicit constant. -/
theorem norm_Psum_ThetaOp_le (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) (A : LoopArg L (n + 1) → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, ‖Psum L A y‖ ≤ M) (x : ZMod L) :
    ‖Psum L (ThetaOp L ξ t A) x‖
      ≤ (‖ξ 0‖ * (1 - ‖t * ξ 0‖)⁻¹ + ∑ j : Fin n, ‖ξ j.succ‖ * ‖(1 - t * ξ j.succ)⁻¹‖) * M := by
  have h0 : ‖∑ c : ZMod L, (ξ 0 * Theta L (t * ξ 0) x c) * Psum L A c‖
      ≤ (‖ξ 0‖ * (1 - ‖t * ξ 0‖)⁻¹) * M := by
    calc ‖∑ c : ZMod L, (ξ 0 * Theta L (t * ξ 0) x c) * Psum L A c‖
        ≤ ∑ c : ZMod L, ‖(ξ 0 * Theta L (t * ξ 0) x c) * Psum L A c‖ := norm_sum_le _ _
      _ ≤ ∑ c : ZMod L, (‖ξ 0‖ * ‖Theta L (t * ξ 0) x c‖) * M := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left (hM c) (by positivity)
      _ = (‖ξ 0‖ * ∑ c : ZMod L, ‖Theta L (t * ξ 0) x c‖) * M := by
          rw [Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ (‖ξ 0‖ * (1 - ‖t * ξ 0‖)⁻¹) * M := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          exact mul_le_mul_of_nonneg_left (sum_norm_Theta_row_le L hL (ht 0) x) (norm_nonneg _)
  have h1 : ‖(∑ j : Fin n, ξ j.succ * (1 - t * ξ j.succ)⁻¹) * Psum L A x‖
      ≤ (∑ j : Fin n, ‖ξ j.succ‖ * ‖(1 - t * ξ j.succ)⁻¹‖) * M := by
    rw [norm_mul]
    refine mul_le_mul ?_ (hM x) (norm_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)
    calc ‖∑ j : Fin n, ξ j.succ * (1 - t * ξ j.succ)⁻¹‖
        ≤ ∑ j : Fin n, ‖ξ j.succ * (1 - t * ξ j.succ)⁻¹‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖ξ j.succ‖ * ‖(1 - t * ξ j.succ)⁻¹‖ := by
          exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  rw [Psum_ThetaOp_eq L hL ht A x, add_mul]
  exact (norm_add_le _ _).trans (add_le_add h0 h1)

/-- `P` is compatible with subtraction. -/
theorem Psum_sub {n : ℕ} (A B : LoopArg L (n + 1) → ℂ) :
    Psum L (A - B) = Psum L A - Psum L B := by
  funext x
  simp [Psum, Finset.sum_sub_distrib]

/-- The commutator `[Q_t, Theta_{t,sigma}]` of (5.89). -/
noncomputable def commQT {n : ℕ} (ξ : Fin (n + 1) → ℂ) (t : ℂ)
    (A : LoopArg L (n + 1) → ℂ) : LoopArg L (n + 1) → ℂ :=
  Qop L t (ThetaOp L ξ t A) - ThetaOp L ξ t (Qop L t A)

/-- **(5.90)**: the commutator `[Q_t, Theta_{t,sigma}]` always lands in the sum-zero
tensors.  Both summands do: `Q_t . X` is sum-zero for every `X` (`SumZero_Qop`), and
`Theta_{t,sigma} . (Q_t . A)` is sum-zero because `Q_t . A` is (`SumZero_ThetaOp`). -/
theorem SumZero_commQT (hL : 3 ≤ L) {n : ℕ} {ξ : Fin (n + 1) → ℂ} {t : ℂ}
    (ht : ∀ i, ‖t * ξ i‖ < 1) (htt : ‖t‖ < 1) (A : LoopArg L (n + 1) → ℂ) :
    SumZero L (commQT L ξ t A) := by
  intro x
  rw [commQT, Psum_sub]
  have h1 : Psum L (Qop L t (ThetaOp L ξ t A)) x = 0 :=
    SumZero_Qop L hL htt (ThetaOp L ξ t A) x
  have h2 : Psum L (ThetaOp L ξ t (Qop L t A)) x = 0 :=
    SumZero_ThetaOp L hL ht (SumZero_Qop L hL htt A) x
  simp [h1, h2]

end RBM
