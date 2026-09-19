/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.ChainExpand
import RBM1D.Green.EntryBound

/-!
# Appendix A: the induction (A.7) and Lemma A.2

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Appendix A (pp. 84--89): the assembly of the perturbative estimates of
`Loop/ChainExpand.lean` into the induction (A.7) and the `n`-chain estimate **Lemma A.2**,
(A.3) and (A.4).  Appendix A is not used for the main theorems.

Everything is deterministic, for a fixed Hermitian `H`.  `Φ` stands for `W ℓ_t η_t`, and `≺` is
replaced by `≤` with explicit constants.  The inputs of the paper are **hypotheses**:
* Theorem 2.3: `G_{ii} ≠ 0`, `|1/G_{ii}| ≤ K`, and `Ξ^(d)_1, Ξ^(o)_1 ≤ B₀` (the base case);
* the loop bound (2.77) (assumption of Lemma 2.18), `RBM.LoopBound`, used for `2n`-loops;
* [39, Lemma 3.3] as used in (A.16) and (A.19): `RBM.ChainLDE16`, `RBM.ChainLDE19`.

## Main definitions

* `RBM.LoopBound`, `RBM.ChainLDE16`, `RBM.ChainLDE19` : the inputs above.
* `RBM.chainCM`, `RBM.chainCD`, `RBM.chainXb`, `RBM.chainYb`, `RBM.chainNext`,
  `RBM.chainScale` : the explicit constants of one step of (A.7).
* `RBM.chainBound`, `RBM.chainScaleUpTo` : the constants of Lemma A.2 (by recursion on the
  level); they depend only on `n, K, B₀, κ₁, κ₂, Λ`.

## Main results

* `RBM.norm_gchainMinor_sub_gchain_le_of_ne` : `|(C^(ii)_n - C_n)_{xy}| Φ^n ≤ c_D (B + Ξ^(o)_n)`
  for `x, y ≠ i` under the induction hypothesis -- linear in the unknown `Ξ^(o)_n`.
* `RBM.norm_quad_gchain_le` : (A.15) + (A.16) + the comparison replacing (A.12): the
  self-consistent bound for the symmetric `2n`-diagonals `(C_n E_c C_n†)_{ii}`.
* `RBM.norm_gchain_off_le` : (A.11) + (A.18)--(A.20) + the comparison replacing (A.13): the
  self-consistent bound for `(C_n)_{ij}`.
* `RBM.bootstrap_A14_A17` : the real-number bootstrap that closes (A.14) and (A.17).
* `RBM.XiDiag_XiOff_step` : **the induction step (A.7)**.
* `RBM.XiDiag_XiOff_le_chainBound` : (A.7) iterated from the base case.
* `RBM.lemma_A2` : **Lemma A.2**, (A.3) and (A.4).
* Auxiliary: `RBM.sum_Sblk_mul_eq` (`∑_k S_{ik} f(k) = ∑_c S^(B)_{[i]c} ⟨f⟩_c`, the last step of
  (A.20) left open in `ChainExpand.lean`), `RBM.sqrt_sum_Sblk_quad_le` (positivity of
  `C E C†`), `RBM.normSq_gchain_double_le` (the Cauchy--Schwarz reduction of (A.14) to
  symmetric chains).

## Deviations from the paper

* **(A.12) and (A.13) are replaced by one-sided comparisons.**  The paper expands
  `C^(ii)` fully via (4.9) ((A.25), (A.26)) and needs the rungs
  `Ξ^(d)_{2n+1} ≺ Ξ^(d)_{2n} (Wℓη)^{1/2}` and `Ξ^(o)_l ≺ (Wℓη)^{1/2}` (`l > n`).  Here the
  `i`-th row and column of `C^(ii)_n` vanish and off them
  `|C^(ii)_n - C_n| ≤ c_D(B + Ξ^(o)_n)Φ^{-n}` (a single application of the telescoping identity, `norm_gchainMinor_sub_gchain_le_of_ne`),
  so entrywise `|C^(ii)_{kl}|² ≤ 2|C_{kl}|² + 2 M_D²`.  This bounds the `G^(i)`-loops and
  `(C^(ii)† E_c C^(ii))_{jj}` from above by the `G`-loops and `2n`-chain diagonals plus
  `O((B + Ξ^(o)_n)² Φ^{-2n})`, which is all (A.14) and (A.17) use.  The `(A.25)` bound and the
  rungs `XiDiag_two_mul_add_one_le`, `XiOff_le_sqrt` are therefore not needed.
* **The error term of (A.16).**  The paper bounds `(∑_{kl} S_{ik}|X_{kl}|² S_{li})^{1/2}` by
  `4n`-loops.  Here `X = C^(ii) E_c C^(ii)†` is positive semidefinite, `|X_{kl}|² ≤ X_{kk}X_{ll}`,
  so the error is at most `κ ∑_k S_{ik} X_{kk}`, a constant times the main term.
* **The self-consistent step.**  (A.14) and (A.17) become the pair of inequalities of
  `bootstrap_A14_A17` for `X = Ξ^(d)_{2n}`, `Y = Ξ^(o)_n`, closed by requiring
  `Φ ≥ chainScale …` (in the paper `Φ ≥ W^c` beats every `W^ε`, so this is implicit).
* **Extra hypotheses.**  `Φ ≤ W` (the paper's `Wℓη ≤ W`, used in (A.15) and for `Ξ^(d)_2`);
  `G_{ii} ≠ 0` separately from `|1/G_{ii}| ≤ K` (in Lean `0⁻¹ = 0`); `3 ≤ L` (row sums of
  `S^(B)`); `Im z ≠ 0` (invertibility of `H - z`, `H - z̄`).
* **"Under the assumptions of Lemma 2.18"** is replaced by the consequences actually used,
  listed above.  `2n - 1` is handled by `XiDiag_add_le` as in the paper.
-/

namespace RBM

open Matrix Finset

/-! ### Averaging against `S` -/

section Average

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
/-- `∑_k S_{ik} f(k) = ∑_c S^(B)_{[i] c} ∑_k E_c(k) f(k)`: averaging against the variance
profile is averaging the block averages against `S^(B)`. -/
theorem sum_Sblk_mul_eq (i : ZMod L × Fin W) (f : ZMod L × Fin W → ℝ) :
    ∑ k, Sblk L W i k * f k = ∑ c, sbKre L (i.1 - c) * ∑ k, eblkW W c k * f k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eblkW, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Sblk]
  ring

omit [NeZero L] [NeZero W] in
theorem Sblk_symm (i j : ZMod L × Fin W) : Sblk L W j i = Sblk L W i j := by
  rw [Sblk, Sblk, ← neg_sub, sbKre_neg]

omit [NeZero W] in
/-- A weighted `S`-average of block averages is bounded by any common bound of the block
averages. -/
theorem sum_Sblk_mul_le (hL : 3 ≤ L) (i : ZMod L × Fin W) {f : ZMod L × Fin W → ℝ} {M : ℝ}
    (hM : ∀ c, ∑ k, eblkW W c k * f k ≤ M) : ∑ k, Sblk L W i k * f k ≤ M := by
  rw [sum_Sblk_mul_eq]
  calc ∑ c, sbKre L (i.1 - c) * ∑ k, eblkW W c k * f k ≤ ∑ c, sbKre L (i.1 - c) * M :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hM c) (sbKre_nonneg _)
    _ = M := by rw [← Finset.sum_mul, sum_sbKre_sub_left hL, one_mul]

/-- `∑_k S_{ik} f'(k) ≤ 2 ∑_k S_{ik} f(k) + 2M²` as soon as `f' ≤ 2f + 2M²` pointwise. -/
theorem sum_Sblk_mul_le_two_mul (hL : 3 ≤ L) (i : ZMod L × Fin W) {f f' : ZMod L × Fin W → ℝ}
    {M : ℝ} (h : ∀ k, f' k ≤ 2 * f k + 2 * M ^ 2) :
    ∑ k, Sblk L W i k * f' k ≤ 2 * ∑ k, Sblk L W i k * f k + 2 * M ^ 2 := by
  calc ∑ k, Sblk L W i k * f' k ≤ ∑ k, Sblk L W i k * (2 * f k + 2 * M ^ 2) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (Sblk_nonneg i k)
    _ = 2 * ∑ k, Sblk L W i k * f k + 2 * M ^ 2 * ∑ k, Sblk L W i k := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
    _ = 2 * ∑ k, Sblk L W i k * f k + 2 * M ^ 2 := by rw [sum_Sblk_row hL i, mul_one]

end Average

/-! ### Entrywise perturbation and the quadratic forms `C E C†` -/

section Perturb

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|c'|² ≤ 2|c|² + 2M²` if `|c' - c| ≤ M`. -/
theorem sq_norm_le_of_norm_sub_le {c c' : ℂ} {M : ℝ} (h : ‖c' - c‖ ≤ M) :
    ‖c'‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * M ^ 2 := by
  have h1 : ‖c'‖ ≤ ‖c‖ + M := by
    have := norm_sub_norm_le c' c
    linarith
  have h0 := norm_nonneg c'
  have h2 := mul_le_mul h1 h1 h0 (h0.trans h1)
  nlinarith [sq_nonneg (‖c‖ - M)]

/-- The entrywise bound `|A'_{kl}|² ≤ 2|A_{kl}|² + 2M²` passes to the diagonal of
`A' E_b A'†`. -/
theorem norm_quad_Eblk_le_of_sq (A A' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) {M : ℝ}
    (h : ∀ k l, ‖A' k l‖ ^ 2 ≤ 2 * ‖A k l‖ ^ 2 + 2 * M ^ 2) (b : ZMod L)
    (x : ZMod L × Fin W) :
    ‖(A' * Eblk L W b * A'ᴴ) x x‖ ≤ 2 * ‖(A * Eblk L W b * Aᴴ) x x‖ + 2 * M ^ 2 := by
  rw [norm_quad_Eblk_apply_self, norm_quad_Eblk_apply_self]
  calc ∑ k, eblkW W b k * ‖A' x k‖ ^ 2 ≤ ∑ k, eblkW W b k * (2 * ‖A x k‖ ^ 2 + 2 * M ^ 2) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h x k) (eblkW_nonneg b k)
    _ = 2 * ∑ k, eblkW W b k * ‖A x k‖ ^ 2 + 2 * M ^ 2 * ∑ k, eblkW W b k := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
    _ = 2 * ∑ k, eblkW W b k * ‖A x k‖ ^ 2 + 2 * M ^ 2 := by rw [sum_eblkW b, mul_one]

omit [NeZero W] in
/-- The block average of the diagonal of `C E_a C†` is the `2`-block trace
`Tr(E_c C E_a C†)`. -/
theorem sum_eblkW_norm_quad_eq (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a c : ZMod L) :
    ∑ k, eblkW W c k * ‖(C * Eblk L W a * Cᴴ) k k‖
      = ‖Matrix.trace (Eblk L W c * C * Eblk L W a * Cᴴ)‖ := by
  rw [trace_Eblk_mul_Eblk_mul_conjTranspose, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (eblkW_nonneg c k)
      (Finset.sum_nonneg fun l _ => mul_nonneg (eblkW_nonneg a l) (sq_nonneg _)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_quad_Eblk_apply_self]

omit [NeZero W] in
/-- **The positivity step behind (A.16)**: for the positive semidefinite `X = C E_b C†`,
`|X_{kl}|² ≤ X_{kk} X_{ll}`, hence
`(∑_{kl} S_{ik} |X_{kl}|² S_{li})^{1/2} ≤ ∑_k S_{ik} |X_{kk}|`.  So the large-deviation error in
(A.16) is at most a constant times the main term. -/
theorem sqrt_sum_Sblk_quad_le (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L)
    (i : ZMod L × Fin W) :
    √(∑ k, ∑ l, Sblk L W i k * ‖(C * Eblk L W b * Cᴴ) k l‖ ^ 2 * Sblk L W l i)
      ≤ ∑ k, Sblk L W i k * ‖(C * Eblk L W b * Cᴴ) k k‖ := by
  set X := C * Eblk L W b * Cᴴ
  have hT : 0 ≤ ∑ k, Sblk L W i k * ‖X k k‖ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg i k) (norm_nonneg _)
  rw [Real.sqrt_le_left hT, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
  have hcs := normSq_mul_Eblk_mul_le C Cᴴ b k l
  rw [conjTranspose_conjTranspose] at hcs
  rw [Sblk_symm i l]
  have hk := Sblk_nonneg (L := L) (W := W) i k
  have hl := Sblk_nonneg (L := L) (W := W) i l
  calc Sblk L W i k * ‖X k l‖ ^ 2 * Sblk L W i l
      ≤ Sblk L W i k * (‖X k k‖ * ‖X l l‖) * Sblk L W i l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs hk) hl
    _ = Sblk L W i k * ‖X k k‖ * (Sblk L W i l * ‖X l l‖) := by ring

omit [NeZero W] in
/-- `|∑_k S_{ik} X_{kk}| ≤ ∑_k S_{ik} |X_{kk}|`. -/
theorem norm_sum_Svar_le (X : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (i : ZMod L × Fin W) :
    ‖∑ k, Svar L W i k * X k k‖ ≤ ∑ k, Sblk L W i k * ‖X k k‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Svar_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Sblk_nonneg i k)]

omit [NeZero W] in
/-- **(A.16) with the large-deviation bound [39, Lemma 3.3] as a hypothesis, closed up**:
if `|(H X H)_{ii} - ∑_k S_{ik} X_{kk}| ≤ κ (∑_{kl} S_{ik}|X_{kl}|² S_{li})^{1/2}` for
`X = C E_b C†`, then `|(H X H)_{ii}| ≤ (1 + κ) ∑_k S_{ik} |X_{kk}|`. -/
theorem norm_quad_H_le_of_LDE (C Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L)
    (i : ZMod L × Fin W) {κ : ℝ} (hκ : 0 ≤ κ)
    (hLDE : ‖(Hm * C * Eblk L W b * Cᴴ * Hm) i i
        - ∑ k, Svar L W i k * (C * Eblk L W b * Cᴴ) k k‖
      ≤ κ * √(∑ k, ∑ l, Sblk L W i k * ‖(C * Eblk L W b * Cᴴ) k l‖ ^ 2 * Sblk L W l i)) :
    ‖(Hm * C * Eblk L W b * Cᴴ * Hm) i i‖
      ≤ (1 + κ) * ∑ k, Sblk L W i k * ‖(C * Eblk L W b * Cᴴ) k k‖ := by
  have h1 := norm_sum_Svar_le (C * Eblk L W b * Cᴴ) i
  have h2 := mul_le_mul_of_nonneg_left (sqrt_sum_Sblk_quad_le C b i) hκ
  have h3 := norm_le_insert' ((Hm * C * Eblk L W b * Cᴴ * Hm) i i)
    (∑ k, Svar L W i k * (C * Eblk L W b * Cᴴ) k k)
  linarith

end Perturb

/-! ### `C^(ii)_n - C_n` off the `i`-th row and column -/

/-- **The product rule for the off-diagonal ratios at level `n`**: if `Ξ^(o)_l ≤ B` for
`l ≤ n - 1`, then every product with `l₁ + l₂ ≤ n + 1` obeys
`Ξ^(o)_{l₁} Ξ^(o)_{l₂} ≤ B (B + Ξ^(o)_n)` -- at most one factor can be `Ξ^(o)_n`, and then the
other one is `Ξ^(o)_1`.  (The level-`n` analogue of the trichotomy (A.27).) -/
theorem mul_le_of_add_le_succ {X : ℕ → ℝ} {B : ℝ} {n : ℕ} (hn : 2 ≤ n) (hB : 0 ≤ B)
    (hX0 : ∀ l, 0 ≤ X l) (hlow : ∀ l, 1 ≤ l → l ≤ n - 1 → X l ≤ B) {l₁ l₂ : ℕ} (h1 : 1 ≤ l₁)
    (h2 : 1 ≤ l₂) (hs : l₁ + l₂ ≤ n + 1) : X l₁ * X l₂ ≤ B * (B + X n) := by
  have hXn := hX0 n
  rcases Nat.lt_or_ge l₁ n with h | h
  · have hx1 := hlow l₁ h1 (by omega)
    have hx2 : X l₂ ≤ B + X n := by
      rcases Nat.lt_or_ge l₂ n with h' | h'
      · linarith [hlow l₂ h2 (by omega)]
      · rw [show l₂ = n by omega]; linarith
    exact mul_le_mul hx1 hx2 (hX0 _) hB
  · rw [show l₁ = n by omega, show l₂ = 1 by omega]
    have hx1 := hlow 1 le_rfl (by omega)
    nlinarith

section MinorBound

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W} {Φ : ℝ}

/-- **(A.26) off the `i`-th row and column**: for `x ≠ i`, `y ≠ i`,
`|(C^(ii)_m - C_m)_{xy}| Φ^m ≤ K ∑_{k<m} Ξ^(o)_{k+1} (1+KD)^{m-k-1} ∑_{q=1}^{m-k} Ξ^(o)_q`,
if `Ξ^(d)_p ≤ D` for `2 ≤ p ≤ m` and `|1/G_{ii}| ≤ K`.  The proof is that of
`norm_gchainMinor_sub_gchain_diag_le` (which is the case `x = y`). -/
theorem norm_gchainMinor_sub_gchain_le_sum {K D : ℝ} (hΦ : 0 < Φ) (hD : 0 ≤ D)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {x y : ZMod L × Fin W} (hx : i ≠ x) (hy : i ≠ y)
    {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1)
    (hXd : ∀ p, 2 ≤ p → p ≤ tau.length → XiDiag L W H z Φ p ≤ D) :
    ‖gchainMinor L W H z i tau a x y - gchain L W H z tau a x y‖ * Φ ^ tau.length
      ≤ K * ∑ k ∈ Finset.range tau.length, XiOff L W H z Φ (k + 1)
          * ((1 + K * D) ^ (tau.length - k - 1)
            * ∑ q ∈ Finset.Icc 1 (tau.length - k), XiOff L W H z Φ q) := by
  rw [gchainMinor_apply_expand h, sub_sub_cancel_left, norm_neg, Finset.mul_sum]
  set m := tau.length with hm
  have hsq : √Φ * √Φ = Φ := Real.mul_self_sqrt hΦ.le
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hlenP : (tau.take (k + 1)).length = k + 1 := by
    simp only [List.length_take]; omega
  have hwfP : (tau.take (k + 1)).length = (a.take k).length + 1 := by
    simp only [List.length_take]; omega
  have hlenS : (tau.drop k).length = m - k := by
    rw [List.length_drop, hm]
  have hwfS : (tau.drop k).length = (a.drop k).length + 1 := by
    simp only [List.length_drop]; omega
  have hP := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ) hlenP hwfP (Ne.symm hx)
  rw [show k + 1 - 1 = k by omega] at hP
  have hS := norm_gchainMinorTail_le_sum hΦ hD hGinv hy m hXd (m - k) (tau.drop k) (a.drop k)
    hlenS hwfS (by omega)
  have hg := hGinv (tau.getD k false)
  set P := ‖gchain L W H z (tau.take (k + 1)) (a.take k) x i‖
  set T := ‖gchainMinorTail L W H z i (tau.drop k) (a.drop k) i y‖
  have hpow : Φ ^ m = Φ ^ k * Φ ^ (m - k - 1) * Φ := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [div_eq_mul_inv, norm_mul, norm_mul, hpow]
  have e : P * (T * ‖(Gsig H z (tau.getD k false) i i)⁻¹‖) * (Φ ^ k * Φ ^ (m - k - 1) * Φ)
      = (P * (Φ ^ k * √Φ)) * (T * (Φ ^ (m - k - 1) * √Φ))
          * ‖(Gsig H z (tau.getD k false) i i)⁻¹‖ := by
    linear_combination (-(P * T * ‖(Gsig H z (tau.getD k false) i i)⁻¹‖ * Φ ^ k
      * Φ ^ (m - k - 1))) * hsq
  rw [e]
  have hT0 : 0 ≤ T * (Φ ^ (m - k - 1) * √Φ) := by positivity
  have hK : 0 ≤ K := (norm_nonneg _).trans hg
  have hB0 : 0 ≤ XiOff L W H z Φ (k + 1) * ((1 + K * D) ^ (m - k - 1)
      * ∑ q ∈ Finset.Icc 1 (m - k), XiOff L W H z Φ q) :=
    mul_nonneg (XiOff_nonneg hΦ.le _) (mul_nonneg (pow_nonneg (by nlinarith [mul_nonneg hK hD]) _)
      (Finset.sum_nonneg fun q _ => XiOff_nonneg hΦ.le q))
  calc (P * (Φ ^ k * √Φ)) * (T * (Φ ^ (m - k - 1) * √Φ)) * ‖(Gsig H z (tau.getD k false) i i)⁻¹‖
      ≤ XiOff L W H z Φ (k + 1) * ((1 + K * D) ^ (m - k - 1)
          * ∑ q ∈ Finset.Icc 1 (m - k), XiOff L W H z Φ q) * K :=
        mul_le_mul (mul_le_mul hP hS hT0 (XiOff_nonneg hΦ.le _)) hg (norm_nonneg _) hB0
    _ = K * (XiOff L W H z Φ (k + 1) * ((1 + K * D) ^ (m - k - 1)
          * ∑ q ∈ Finset.Icc 1 (m - k), XiOff L W H z Φ q)) := by ring

/-- **`C^(ii)_n - C_n` under the induction hypothesis (A.7)**: for `x ≠ i`, `y ≠ i` and a
well-formed `n`-chain, `n ≥ 2`,
`|(C^(ii)_n - C_n)_{xy}| Φ^n ≤ K n² (1 + KB)^{n-1} B (B + Ξ^(o)_n)`,
if `Ξ^(d)_p ≤ B` for `2 ≤ p ≤ n`, `Ξ^(o)_l ≤ B` for `l ≤ n - 1` and `|1/G_{ii}| ≤ K`.
The bound is *linear* in the unknown `Ξ^(o)_n` (`mul_le_of_add_le_succ`). -/
theorem norm_gchainMinor_sub_gchain_le_of_ne {K B : ℝ} (hΦ : 0 < Φ) (hB : 0 ≤ B)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {x y : ZMod L × Fin W} (hx : i ≠ x) (hy : i ≠ y)
    {n : ℕ} (hn : 2 ≤ n) {tau : List Bool} {a : List (ZMod L)} (hlen : tau.length = n)
    (h : tau.length = a.length + 1)
    (hXd : ∀ p, 2 ≤ p → p ≤ n → XiDiag L W H z Φ p ≤ B)
    (hXo : ∀ l, 1 ≤ l → l ≤ n - 1 → XiOff L W H z Φ l ≤ B) :
    ‖gchainMinor L W H z i tau a x y - gchain L W H z tau a x y‖ * Φ ^ n
      ≤ K * n ^ 2 * (1 + K * B) ^ (n - 1) * B * (B + XiOff L W H z Φ n) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true)
  have hKB : 1 ≤ 1 + K * B := by nlinarith [mul_nonneg hK hB]
  have hX0 : ∀ l, 0 ≤ XiOff L W H z Φ l := XiOff_nonneg hΦ.le
  have hY := hX0 n
  have hbase := norm_gchainMinor_sub_gchain_le_sum hΦ hB hGinv hx hy h
    (fun p hp2 hp => hXd p hp2 (by omega))
  rw [hlen] at hbase
  refine hbase.trans ?_
  have hterm : ∀ k ∈ Finset.range n, XiOff L W H z Φ (k + 1)
      * ((1 + K * B) ^ (n - k - 1) * ∑ q ∈ Finset.Icc 1 (n - k), XiOff L W H z Φ q)
        ≤ (1 + K * B) ^ (n - 1) * (n * (B * (B + XiOff L W H z Φ n))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hprod : ∀ q ∈ Finset.Icc 1 (n - k),
        XiOff L W H z Φ (k + 1) * XiOff L W H z Φ q ≤ B * (B + XiOff L W H z Φ n) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      exact mul_le_of_add_le_succ hn hB hX0 hXo (by omega) hq.1 (by omega)
    have hsum : XiOff L W H z Φ (k + 1) * ∑ q ∈ Finset.Icc 1 (n - k), XiOff L W H z Φ q
        ≤ n * (B * (B + XiOff L W H z Φ n)) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum hprod).trans ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast (by omega : n - k + 1 - 1 ≤ n)
    have hpow : (1 + K * B) ^ (n - k - 1) ≤ (1 + K * B) ^ (n - 1) :=
      pow_le_pow_right₀ hKB (by omega)
    have hs0 : 0 ≤ XiOff L W H z Φ (k + 1) * ∑ q ∈ Finset.Icc 1 (n - k), XiOff L W H z Φ q :=
      mul_nonneg (hX0 _) (Finset.sum_nonneg fun q _ => hX0 q)
    calc XiOff L W H z Φ (k + 1)
          * ((1 + K * B) ^ (n - k - 1) * ∑ q ∈ Finset.Icc 1 (n - k), XiOff L W H z Φ q)
        = (1 + K * B) ^ (n - k - 1)
          * (XiOff L W H z Φ (k + 1) * ∑ q ∈ Finset.Icc 1 (n - k), XiOff L W H z Φ q) := by
          ring
      _ ≤ (1 + K * B) ^ (n - 1) * (n * (B * (B + XiOff L W H z Φ n))) :=
          mul_le_mul hpow hsum hs0 (by positivity)
  calc K * ∑ k ∈ Finset.range n, XiOff L W H z Φ (k + 1)
        * ((1 + K * B) ^ (n - k - 1) * ∑ q ∈ Finset.Icc 1 (n - k), XiOff L W H z Φ q)
      ≤ K * ∑ k ∈ Finset.range n, (1 + K * B) ^ (n - 1) * (n * (B * (B + XiOff L W H z Φ n))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hK
    _ = K * n ^ 2 * (1 + K * B) ^ (n - 1) * B * (B + XiOff L W H z Φ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end MinorBound

/-! ### The constants of the induction step -/

/-- The constant of (A.11) at level `n`:
`|(C_n - C^(i)_n)_{ij}| Φ^{n-1/2} ≤ B ((1+KB)^{n-1} - 1)`. -/
noncomputable def chainCM (K B : ℝ) (n : ℕ) : ℝ := B * ((1 + K * B) ^ (n - 1) - 1)

/-- The constant of `norm_gchainMinor_sub_gchain_le_of_ne`:
`|(C^(ii)_n - C_n)_{xy}| Φ^n ≤ K n² (1+KB)^{n-1} B (B + Ξ^(o)_n)`. -/
noncomputable def chainCD (K B : ℝ) (n : ℕ) : ℝ := K * n ^ 2 * (1 + K * B) ^ (n - 1) * B

theorem chainCM_nonneg {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (n : ℕ) : 0 ≤ chainCM K B n := by
  unfold chainCM
  have : 1 ≤ (1 + K * B) ^ (n - 1) := one_le_pow₀ (by nlinarith [mul_nonneg hK hB])
  nlinarith

theorem chainCD_nonneg {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (n : ℕ) : 0 ≤ chainCD K B n := by
  unfold chainCD
  have : 0 ≤ (1 + K * B) ^ (n - 1) := pow_nonneg (by nlinarith [mul_nonneg hK hB]) _
  positivity

/-- The bound on `Ξ^(d)_{2n}` produced by the step (`bootstrap_A14_A17`), with
`α = B²(1+κ₁)`. -/
noncomputable def chainXb (K B κ₁ Λ : ℝ) (n : ℕ) : ℝ :=
  2 * (B ^ 2 + 5 * chainCM K B n ^ 2 + 2 * (B ^ 2 * (1 + κ₁)) * Λ + 8 * (B + chainCM K B n) ^ 2)

/-- The bound on `Ξ^(o)_n` produced by the step, with `β = B κ₂`. -/
noncomputable def chainYb (K B κ₁ κ₂ Λ : ℝ) (n : ℕ) : ℝ :=
  2 * (B + chainCM K B n) + 4 * (B * κ₂) ^ 2 + chainXb K B κ₁ Λ n

/-- The new bound after the induction step (A.7) at level `n`. -/
noncomputable def chainNext (K B κ₁ κ₂ Λ : ℝ) (n : ℕ) : ℝ :=
  B + chainXb K B κ₁ Λ n + chainYb K B κ₁ κ₂ Λ n

/-- How large `Φ = Wℓη` must be for the step (A.7) at level `n` (in the paper `Φ ≥ W^c`
dominates every `W^ε`, so this is automatic there). -/
noncomputable def chainScale (K B κ₁ κ₂ : ℝ) (n : ℕ) : ℝ :=
  2 * chainCD K B n ^ 2 * (16 * (B * κ₂) ^ 2 + 128 * (B ^ 2 * (1 + κ₁)) * (B * κ₂) ^ 2
    + B ^ 2 * (1 + κ₁))

/-- **The self-consistent step of (A.14), (A.17)**, as a statement about real numbers.  If
`X ≤ B² + c_M² + 2c_M X^{1/2} + α(2Λ + 2D(B+Y)²/Φ)` and `Y ≤ c_M + β(2X + 2D(B+Y)²/Φ)^{1/2}`,
and `Φ` is large, `2D(16β² + 128αβ² + α) ≤ Φ`, then `X` and `Y` are bounded by explicit
constants.  The two inequalities are linear in `X`, `Y²` up to the small factor `Φ⁻¹`, so no
continuity argument is needed. -/
theorem bootstrap_A14_A17 {X Y B cM D α β Λ Φ : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hB : 0 ≤ B)
    (hcM : 0 ≤ cM) (hD : 0 ≤ D) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hΦ : 0 < Φ)
    (hXi : X ≤ B ^ 2 + cM ^ 2 + 2 * cM * √X + α * (2 * Λ + 2 * D * (B + Y) ^ 2 / Φ))
    (hYi : Y ≤ cM + β * √(2 * X + 2 * D * (B + Y) ^ 2 / Φ))
    (hsmall : 2 * D * (16 * β ^ 2 + 128 * α * β ^ 2 + α) ≤ Φ) :
    X ≤ 2 * (B ^ 2 + 5 * cM ^ 2 + 2 * α * Λ + 8 * (B + cM) ^ 2) ∧
      Y ≤ 2 * (B + cM) + 4 * β ^ 2 + 2 * (B ^ 2 + 5 * cM ^ 2 + 2 * α * Λ + 8 * (B + cM) ^ 2) := by
  set q := 2 * D / Φ with hq
  have hq0 : 0 ≤ q := by positivity
  have hqZ : 2 * D * (B + Y) ^ 2 / Φ = q * (B + Y) ^ 2 := by rw [hq]; ring
  rw [hqZ] at hXi hYi
  have hs : q * (16 * β ^ 2 + 128 * α * β ^ 2 + α) ≤ 1 := by
    rw [hq, div_mul_eq_mul_div, div_le_one hΦ]; linarith
  have hb2 : 0 ≤ β ^ 2 := sq_nonneg β
  have hq1 := mul_nonneg hq0 hα
  have hq2 := mul_nonneg hq0 hb2
  have hq3 := mul_nonneg hq0 (mul_nonneg hα hb2)
  have h1 : 16 * β ^ 2 * q ≤ 1 := by nlinarith
  have h2 : 128 * α * β ^ 2 * q ≤ 1 := by nlinarith
  have h3 : α * q ≤ 1 := by nlinarith
  set u := √X with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg X
  have hu2 : u ^ 2 = X := Real.sq_sqrt hX0
  set Z := B + Y with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hV0 : 0 ≤ 2 * X + q * Z ^ 2 := by positivity
  have hbeta : β * √(2 * X + q * Z ^ 2) ≤ 2 * β * u + Z / 4 := by
    have hsq : (β * √(2 * X + q * Z ^ 2)) ^ 2 ≤ (2 * β * u + Z / 4) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hV0]
      have hZq : β ^ 2 * q * Z ^ 2 ≤ Z ^ 2 / 16 := by
        nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg Z)]
      nlinarith [mul_nonneg (mul_nonneg hβ hu0) hZ0, mul_nonneg hb2 hX0]
    exact le_of_sq_le_sq hsq (by positivity)
  have hZb : Z ≤ 2 * (B + cM) + 4 * β * u := by linarith
  have hZ2 : Z ^ 2 ≤ 8 * (B + cM) ^ 2 + 32 * β ^ 2 * X := by
    calc Z ^ 2 ≤ (2 * (B + cM) + 4 * β * u) ^ 2 := pow_le_pow_left₀ hZ0 hZb 2
      _ = 8 * (B + cM) ^ 2 + 32 * β ^ 2 * u ^ 2 - (2 * (B + cM) - 4 * β * u) ^ 2 := by ring
      _ ≤ 8 * (B + cM) ^ 2 + 32 * β ^ 2 * u ^ 2 := by
          linarith [sq_nonneg (2 * (B + cM) - 4 * β * u)]
      _ = 8 * (B + cM) ^ 2 + 32 * β ^ 2 * X := by rw [hu2]
  have hαq : α * (q * Z ^ 2) ≤ 8 * (B + cM) ^ 2 + X / 4 := by
    have e : α * (q * Z ^ 2) ≤ α * q * (8 * (B + cM) ^ 2 + 32 * β ^ 2 * X) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hZ2 (mul_nonneg hα hq0)
    have e2 : α * q * (8 * (B + cM) ^ 2) ≤ 1 * (8 * (B + cM) ^ 2) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have e3 : α * q * (32 * β ^ 2 * X) = 128 * α * β ^ 2 * q * X / 4 := by ring
    have e4 := mul_le_mul_of_nonneg_right h2 hX0
    have e5 : α * q * (8 * (B + cM) ^ 2 + 32 * β ^ 2 * X)
        = α * q * (8 * (B + cM) ^ 2) + α * q * (32 * β ^ 2 * X) := by ring
    linarith
  have h2cM : 2 * cM * u ≤ 4 * cM ^ 2 + X / 4 := by
    have e : 4 * cM ^ 2 + X / 4 - 2 * cM * u = (u / 2 - 2 * cM) ^ 2 := by rw [← hu2]; ring
    linarith [sq_nonneg (u / 2 - 2 * cM)]
  have hsplit : α * (2 * Λ + q * Z ^ 2) = 2 * α * Λ + α * (q * Z ^ 2) := by ring
  have hXb : X ≤ 2 * (B ^ 2 + 5 * cM ^ 2 + 2 * α * Λ + 8 * (B + cM) ^ 2) := by linarith
  refine ⟨hXb, ?_⟩
  have h4 : 4 * β * u ≤ 4 * β ^ 2 + X := by
    have e : 4 * β ^ 2 + X - 4 * β * u = (2 * β - u) ^ 2 := by rw [← hu2]; ring
    linarith [sq_nonneg (2 * β - u)]
  linarith

/-! ### The inputs of Lemma A.2 -/

section Inputs

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- **The loop bound (2.77)**, i.e. the part of the assumptions of Lemma 2.18 used in
Appendix A: every `m`-`G` loop satisfies `|L_{σ,a}| Φ^{m-1} ≤ Λ` (with `Φ = Wℓ_tη_t`, and `≺`
replaced by an explicit constant `Λ`). -/
def LoopBound (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (Φ Λ : ℝ) (m : ℕ) :
    Prop :=
  ∀ I : LoopIdx (ZMod L), I.σ.length = m → I.a.length = m → ‖gloop L W H z I‖ * Φ ^ (m - 1) ≤ Λ

/-- **The large-deviation input of (A.16)** ([39, Lemma 3.3]) for `n`-chains, with `≺`
replaced by an explicit constant `κ`: for `X = C^(ii)_n E_c C^(ii)†_n`, which does not depend on
the `i`-th row of `H`,
`|(H X H)_{ii} - ∑_k S_{ik} X_{kk}| ≤ κ (∑_{kl} S_{ik} |X_{kl}|² S_{li})^{1/2}`. -/
def ChainLDE16 (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (κ : ℝ) (n : ℕ) :
    Prop :=
  ∀ (tau : List Bool) (a : List (ZMod L)), tau.length = n → tau.length = a.length + 1 →
    ∀ (i : ZMod L × Fin W) (c : ZMod L),
      ‖(H * gchainMinor L W H z i tau a * Eblk L W c * (gchainMinor L W H z i tau a)ᴴ * H) i i
          - ∑ k, Svar L W i k * (gchainMinor L W H z i tau a * Eblk L W c
            * (gchainMinor L W H z i tau a)ᴴ) k k‖
        ≤ κ * √(∑ k, ∑ l, Sblk L W i k * ‖(gchainMinor L W H z i tau a * Eblk L W c
            * (gchainMinor L W H z i tau a)ᴴ) k l‖ ^ 2 * Sblk L W l i)

/-- **The large-deviation input of (A.19)** ([39, Lemma 3.3]) for `n`-chains, with `≺`
replaced by an explicit constant `κ`:
`|(H C^(ii)_n)_{ij}| ≤ κ (∑_k S_{ik} |(C^(ii)_n)_{kj}|²)^{1/2}`
for `i ≠ j`. -/
def ChainLDE19 (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (κ : ℝ) (n : ℕ) :
    Prop :=
  ∀ (tau : List Bool) (a : List (ZMod L)), tau.length = n → tau.length = a.length + 1 →
    ∀ (i j : ZMod L × Fin W), i ≠ j →
      ‖(H * gchainMinor L W H z i tau a) i j‖
        ≤ κ * √(∑ k, Sblk L W i k * ‖gchainMinor L W H z i tau a k j‖ ^ 2)

end Inputs

section Step

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W} {Φ : ℝ}

omit [NeZero W] in
/-- Entrywise comparison of `C^(ii)` with `C`: the `i`-th row and column of `C^(ii)` vanish,
and off them the two differ by at most `M`. -/
theorem sq_norm_gchainMinor_le (hG : ∀ s, Gsig H z s i i ≠ 0) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) {M : ℝ}
    (hM : ∀ x y, i ≠ x → i ≠ y →
      ‖gchainMinor L W H z i tau a x y - gchain L W H z tau a x y‖ ≤ M)
    (k l : ZMod L × Fin W) :
    ‖gchainMinor L W H z i tau a k l‖ ^ 2 ≤ 2 * ‖gchain L W H z tau a k l‖ ^ 2 + 2 * M ^ 2 := by
  have hzero : ‖gchainMinor L W H z i tau a k l‖ ^ 2 = 0 ∨ (i ≠ k ∧ i ≠ l) := by
    by_cases hl : l = i
    · left; rw [hl, gchainMinor_col_self hG h k]; simp
    · by_cases hk : k = i
      · left; rw [hk, gchainMinor_row_self hG tau a hl]; simp
      · right; exact ⟨Ne.symm hk, Ne.symm hl⟩
  rcases hzero with h0 | ⟨hk, hl⟩
  · rw [h0]; positivity
  · exact sq_norm_le_of_norm_sub_le (hM k l hk hl)

omit [NeZero W] in
theorem isUnit_det_Gsig (hH : H.IsHermitian) (hz : z.im ≠ 0) (s : Bool) :
    IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det := by
  cases s
  · exact isUnit_det_sub_smul_one hH (by simpa using hz)
  · exact isUnit_det_sub_smul_one hH hz

/-- `C^(ii)_n` is close to `C_n` off the `i`-th row and column, in the form used below. -/
theorem norm_gchainMinor_sub_gchain_le_div {K B : ℝ} (hΦ : 0 < Φ) (hB : 0 ≤ B)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {n : ℕ} (hn : 2 ≤ n) {tau : List Bool}
    {a : List (ZMod L)} (hlen : tau.length = n) (h : tau.length = a.length + 1)
    (hXd : ∀ p, 2 ≤ p → p ≤ n → XiDiag L W H z Φ p ≤ B)
    (hXo : ∀ l, 1 ≤ l → l ≤ n - 1 → XiOff L W H z Φ l ≤ B) :
    ∀ x y, i ≠ x → i ≠ y → ‖gchainMinor L W H z i tau a x y - gchain L W H z tau a x y‖
      ≤ chainCD K B n * (B + XiOff L W H z Φ n) / Φ ^ n := by
  intro x y hx hy
  rw [le_div_iff₀ (by positivity), chainCD]
  exact norm_gchainMinor_sub_gchain_le_of_ne hΦ hB hGinv hx hy hn hlen h hXd hXo

/-- **(A.15) + (A.16) + (A.12), deterministic form: the `2n`-diagonal of a symmetric chain.**
For a well-formed `n`-chain `C`, `n ≥ 2`, under the induction hypothesis (A.7)
(`Ξ^(o)_l ≤ B` for `l ≤ n - 1`, `Ξ^(d)_p ≤ B` for `p ≤ 2n - 2`), `|1/G_{ii}| ≤ K`, the loop bound
`|L_{σ,a}| Φ^{2n-1} ≤ Λ` for `2n`-loops (the assumption (2.77) of Lemma 2.18), and the
large-deviation bound (A.16) with constant `κ` for `X = C^(ii) E_c C^(ii)†`,
`|(C E_c C†)_{ii}| Φ^{2n-1}
  ≤ B² + c_M² + 2 c_M (Ξ^(d)_{2n})^{1/2} + B²(1+κ)(2Λ + 2 c_D² (B + Ξ^(o)_n)² Φ⁻¹)`,
with `c_M = chainCM K B n`, `c_D = chainCD K B n`.  Here `Φ ≤ W` is the paper's
`Wℓη ≤ W`. -/
theorem norm_quad_gchain_le (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0)
    (hG : ∀ s, Gsig H z s i i ≠ 0) {K B κ Λ : ℝ} (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K)
    (hΦ : 0 < Φ) (hΦW : Φ ≤ W) (hB : 0 ≤ B) (hκ : 0 ≤ κ) {n : ℕ} (hn : 2 ≤ n)
    (hXd : ∀ p, 1 ≤ p → p ≤ 2 * n - 2 → XiDiag L W H z Φ p ≤ B)
    (hXo : ∀ l, 1 ≤ l → l ≤ n - 1 → XiOff L W H z Φ l ≤ B)
    (hLoop : ∀ I : LoopIdx (ZMod L), I.σ.length = 2 * n → I.a.length = 2 * n →
      ‖gloop L W H z I‖ * Φ ^ (2 * n - 1) ≤ Λ)
    {tau : List Bool} {a : List (ZMod L)} (hlen : tau.length = n) (h : tau.length = a.length + 1)
    (c : ZMod L)
    (hLDE : ‖(H * gchainMinor L W H z i tau a * Eblk L W c * (gchainMinor L W H z i tau a)ᴴ
          * H) i i
        - ∑ k, Svar L W i k * (gchainMinor L W H z i tau a * Eblk L W c
          * (gchainMinor L W H z i tau a)ᴴ) k k‖
      ≤ κ * √(∑ k, ∑ l, Sblk L W i k * ‖(gchainMinor L W H z i tau a * Eblk L W c
          * (gchainMinor L W H z i tau a)ᴴ) k l‖ ^ 2 * Sblk L W l i)) :
    ‖(gchain L W H z tau a * Eblk L W c * (gchain L W H z tau a)ᴴ) i i‖ * Φ ^ (2 * n - 1)
      ≤ B ^ 2 + chainCM K B n ^ 2 + 2 * chainCM K B n * √(XiDiag L W H z Φ (2 * n))
        + B ^ 2 * (1 + κ)
          * (2 * Λ + 2 * chainCD K B n ^ 2 * (B + XiOff L W H z Φ n) ^ 2 / Φ) := by
  obtain ⟨s, tau', rfl⟩ : ∃ s tau', tau = s :: tau' := by
    cases tau with
    | nil => simp at hlen; omega
    | cons s tau' => exact ⟨s, tau', rfl⟩
  obtain ⟨b, a', rfl⟩ : ∃ b a', a = b :: a' := by
    cases a with
    | nil => simp only [List.length_cons, List.length_nil] at h hlen; omega
    | cons b a' => exact ⟨b, a', rfl⟩
  have h' : tau'.length = a'.length + 1 := by simpa using h
  have hlen' : tau'.length = n - 1 := by simp at hlen; omega
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true)
  have hinv := isUnit_det_Gsig hH hz
  set C := gchain L W H z (s :: tau') (b :: a') with hCdef
  set C' := gchainMinorTail L W H z i (s :: tau') (b :: a') with hC'def
  set Cm := gchainMinor L W H z i (s :: tau') (b :: a') with hCmdef
  set X := XiDiag L W H z Φ (2 * n) with hXdef
  set Y := XiOff L W H z Φ n with hYdef
  set cM := chainCM K B n with hcM
  set cD := chainCD K B n with hcD
  have hcM0 : 0 ≤ cM := chainCM_nonneg hK hB n
  have hX0 : 0 ≤ X := XiDiag_nonneg hΦ.le _
  have hY0 : 0 ≤ Y := XiOff_nonneg hΦ.le _
  set P := Φ ^ (2 * n - 1) with hPdef
  have hP0 : 0 < P := by positivity
  set s₀ := Φ ^ (n - 1) * √Φ with hs₀def
  have hs₀ : 0 < s₀ := by positivity
  have hs₀P : s₀ ^ 2 = P := by
    rw [hs₀def, mul_pow, Real.sq_sqrt hΦ.le, ← pow_mul, ← pow_succ]
    congr 1; omega
  have hΦnP : (Φ ^ n) ^ 2 = P * Φ := by
    rw [← pow_mul, ← pow_succ]; congr 1; omega
  have hΦn1P : (Φ ^ (n - 1)) ^ 2 * Φ = P := by
    rw [← pow_mul, ← pow_succ]; congr 1; omega
  -- (A.11)
  have hA11 : ∀ j, j ≠ i → ‖C i j - C' i j‖ ≤ cM / s₀ := by
    intro j hj
    have := norm_gchainMinorTail_sub_gchain_le (O := B) hΦ hB hGinv (Ne.symm hj) s b h'
      (fun p hp2 hp => hXd p (by omega) (by omega)) (fun l hl1 hl => hXo l hl1 (by omega))
    rw [hlen'] at this
    rw [le_div_iff₀ hs₀, norm_sub_rev]
    exact this
  -- (A.15)
  have h15 := norm_quad_Eblk_sub_le C C' c i hA11
  have hC'ii : C' i i = 0 := gchainMinorTail_col_self hG s b h' i
  rw [hC'ii, norm_zero] at h15
  have hwf : (s :: tau').length = (b :: a').length + 1 := h
  have hCii : ‖C i i‖ * Φ ^ (n - 1) ≤ B :=
    (norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) hlen hwf i).trans
      (hXd n (by omega) (by omega))
  obtain ⟨hd₁, hd₂, -, -⟩ := length_double hwf c
  have hQX : ‖(C * Eblk L W c * Cᴴ) i i‖ * P ≤ X := by
    rw [hCdef, gchain_mul_Eblk_mul_conjTranspose hH hwf c]
    have := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (n := 2 * n)
      (hd₁.trans (by rw [hlen])) hd₂ i
    exact this
  -- (A.16)
  have hq := gchainMinorTail_quad_apply_self hH hinv hG s b h' c
  have hHX := norm_quad_H_le_of_LDE Cm H c i hκ hLDE
  have hGii : ‖Gsig H z s i i‖ ≤ B := by
    have := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (n := 1) (tau := [s])
      (a := []) rfl rfl i
    simp only [gchain_single, Nat.sub_self, pow_zero, mul_one] at this
    exact this.trans (hXd 1 le_rfl (by omega))
  -- `C^(ii)` against `C`
  have hMD := norm_gchainMinor_sub_gchain_le_div hΦ hB hGinv hn hlen hwf
    (fun p hp2 hp => hXd p (by omega) (by omega)) hXo
  have hpt := sq_norm_gchainMinor_le hG hwf hMD
  have hT := sum_Sblk_mul_le_two_mul hL i (fun k => norm_quad_Eblk_le_of_sq C Cm hpt c k)
  -- the loop bound
  have hloopS : ∑ k, Sblk L W i k * ‖(C * Eblk L W c * Cᴴ) k k‖ ≤ Λ / P := by
    refine sum_Sblk_mul_le hL i fun c' => ?_
    rw [sum_eblkW_norm_quad_eq, hCdef, trace_Eblk_gchain_Eblk_conjTranspose hH hwf,
      le_div_iff₀ hP0]
    refine hLoop _ ?_ ?_
    · simp only [List.length_append, List.length_reverse, List.length_map]; omega
    · simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
      simp at hlen; omega
  -- assembling
  set T := ∑ k, Sblk L W i k * ‖(Cm * Eblk L W c * Cmᴴ) k k‖ with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg i k) (norm_nonneg _)
  have hTP : T * P ≤ 2 * Λ + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ := by
    have e : (cD * (B + Y) / Φ ^ n) ^ 2 * P = cD ^ 2 * (B + Y) ^ 2 / Φ := by
      rw [div_pow, hΦnP]
      field_simp
    have h1 : T * P ≤ (2 * (Λ / P) + 2 * (cD * (B + Y) / Φ ^ n) ^ 2) * P :=
      mul_le_mul_of_nonneg_right (hT.trans (by linarith)) hP0.le
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hP0.ne', mul_assoc, e] at h1
    linarith [show 2 * (cD ^ 2 * (B + Y) ^ 2 / Φ) = 2 * cD ^ 2 * (B + Y) ^ 2 / Φ by ring]
  have hd : ‖(C' * Eblk L W c * C'ᴴ) i i‖ * P
      ≤ B ^ 2 * (1 + κ) * (2 * Λ + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) := by
    rw [hq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    have hG2 : ‖Gsig H z s i i‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hGii 2
    calc ‖Gsig H z s i i‖ ^ 2 * ‖(H * Cm * Eblk L W c * Cmᴴ * H) i i‖ * P
        ≤ B ^ 2 * ((1 + κ) * T) * P :=
          mul_le_mul_of_nonneg_right (mul_le_mul hG2 hHX (norm_nonneg _) (sq_nonneg _)) hP0.le
      _ = B ^ 2 * (1 + κ) * (T * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hTP (by positivity)
  -- the three terms of (A.15)
  have ha : (W : ℝ)⁻¹ * |‖C i i‖ ^ 2 - 0 ^ 2| * P ≤ B ^ 2 := by
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero, abs_of_nonneg (sq_nonneg _)]
    have hWΦ : (W : ℝ)⁻¹ ≤ Φ⁻¹ := inv_anti₀ hΦ hΦW
    have hC2 : (‖C i i‖ * Φ ^ (n - 1)) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (by positivity) hCii 2
    calc (W : ℝ)⁻¹ * ‖C i i‖ ^ 2 * P ≤ Φ⁻¹ * ‖C i i‖ ^ 2 * P := by gcongr
      _ = (‖C i i‖ * Φ ^ (n - 1)) ^ 2 := by
          rw [← hΦn1P]; field_simp
      _ ≤ B ^ 2 := hC2
  have hb : (cM / s₀) ^ 2 * P = cM ^ 2 := by
    rw [div_pow, hs₀P, div_mul_cancel₀ _ hP0.ne']
  have hc : 2 * √(∑ j ∈ Finset.univ.erase i, eblkW W c j * ‖C i j‖ ^ 2) * (cM / s₀) * P
      ≤ 2 * cM * √X := by
    have hsum : ∑ j ∈ Finset.univ.erase i, eblkW W c j * ‖C i j‖ ^ 2 ≤ X / P := by
      rw [le_div_iff₀ hP0]
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hP0.le) hQX
      rw [norm_quad_Eblk_apply_self]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => mul_nonneg (eblkW_nonneg c j) (sq_nonneg _))
    have hsq : √(∑ j ∈ Finset.univ.erase i, eblkW W c j * ‖C i j‖ ^ 2) ≤ √X / s₀ := by
      refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
      rw [Real.sqrt_div' _ hP0.le, ← hs₀P, Real.sqrt_sq hs₀.le]
    calc 2 * √(∑ j ∈ Finset.univ.erase i, eblkW W c j * ‖C i j‖ ^ 2) * (cM / s₀) * P
        ≤ 2 * (√X / s₀) * (cM / s₀) * P := by gcongr
      _ = 2 * cM * √X := by
          rw [← hs₀P]; field_simp
  have hQ := norm_le_insert' ((C * Eblk L W c * Cᴴ) i i) ((C' * Eblk L W c * C'ᴴ) i i)
  have h15P := mul_le_mul_of_nonneg_right h15 hP0.le
  rw [add_mul, add_mul] at h15P
  nlinarith

/-- **(A.11) + (A.18)--(A.20), deterministic form: the off-diagonal entries of an `n`-chain.**
For a well-formed `n`-chain, `n ≥ 2`, `i ≠ j`, under the induction hypothesis (A.7),
`|1/G_{ii}| ≤ K`, and the large-deviation bound (A.19) with constant `κ`,
`|(H C^(ii)_n)_{ij}| ≤ κ (∑_k S_{ik} |(C^(ii)_n)_{kj}|²)^{1/2}`:
`|(C_n)_{ij}| Φ^{n-1/2} ≤ c_M + B κ (2 Ξ^(d)_{2n} + 2 c_D² (B + Ξ^(o)_n)² Φ⁻¹)^{1/2}`.
The `k`-sum is an `S`-average of diagonal entries of the `2n`-chains `C† E_c C` (up to the
`C^(ii) - C` error), which is why the paper's (A.20) is a bound by `2n`-chain diagonals. -/
theorem norm_gchain_off_le (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0)
    (hG : ∀ s, Gsig H z s i i ≠ 0) {K B κ : ℝ} (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K)
    (hΦ : 0 < Φ) (hB : 0 ≤ B) (hκ : 0 ≤ κ) {n : ℕ} (hn : 2 ≤ n)
    (hXd : ∀ p, 1 ≤ p → p ≤ 2 * n - 2 → XiDiag L W H z Φ p ≤ B)
    (hXo : ∀ l, 1 ≤ l → l ≤ n - 1 → XiOff L W H z Φ l ≤ B)
    {tau : List Bool} {a : List (ZMod L)} (hlen : tau.length = n) (h : tau.length = a.length + 1)
    {j : ZMod L × Fin W} (hij : i ≠ j)
    (hLDE : ‖(H * gchainMinor L W H z i tau a) i j‖
      ≤ κ * √(∑ k, Sblk L W i k * ‖gchainMinor L W H z i tau a k j‖ ^ 2)) :
    ‖gchain L W H z tau a i j‖ * (Φ ^ (n - 1) * √Φ)
      ≤ chainCM K B n + B * κ * √(2 * XiDiag L W H z Φ (2 * n)
          + 2 * chainCD K B n ^ 2 * (B + XiOff L W H z Φ n) ^ 2 / Φ) := by
  obtain ⟨s, tau', rfl⟩ : ∃ s tau', tau = s :: tau' := by
    cases tau with
    | nil => simp at hlen; omega
    | cons s tau' => exact ⟨s, tau', rfl⟩
  obtain ⟨b, a', rfl⟩ : ∃ b a', a = b :: a' := by
    cases a with
    | nil => simp only [List.length_cons, List.length_nil] at h hlen; omega
    | cons b a' => exact ⟨b, a', rfl⟩
  have h' : tau'.length = a'.length + 1 := by simpa using h
  have hlen' : tau'.length = n - 1 := by simp at hlen; omega
  have hwf : (s :: tau').length = (b :: a').length + 1 := h
  have hinv := isUnit_det_Gsig hH hz
  set C := gchain L W H z (s :: tau') (b :: a') with hCdef
  set C' := gchainMinorTail L W H z i (s :: tau') (b :: a') with hC'def
  set Cm := gchainMinor L W H z i (s :: tau') (b :: a') with hCmdef
  set X := XiDiag L W H z Φ (2 * n) with hXdef
  set Y := XiOff L W H z Φ n with hYdef
  set cD := chainCD K B n with hcD
  have hX0 : 0 ≤ X := XiDiag_nonneg hΦ.le _
  set P := Φ ^ (2 * n - 1) with hPdef
  have hP0 : 0 < P := by positivity
  set s₀ := Φ ^ (n - 1) * √Φ with hs₀def
  have hs₀ : 0 < s₀ := by positivity
  have hs₀P : s₀ ^ 2 = P := by
    rw [hs₀def, mul_pow, Real.sq_sqrt hΦ.le, ← pow_mul, ← pow_succ]
    congr 1; omega
  have hΦnP : (Φ ^ n) ^ 2 = P * Φ := by
    rw [← pow_mul, ← pow_succ]; congr 1; omega
  -- (A.11)
  have hA11 : ‖C' i j - C i j‖ * s₀ ≤ chainCM K B n := by
    have := norm_gchainMinorTail_sub_gchain_le (O := B) hΦ hB hGinv hij s b h'
      (fun p hp2 hp => hXd p (by omega) (by omega)) (fun l hl1 hl => hXo l hl1 (by omega))
    rw [hlen'] at this
    exact this
  -- (A.18)
  have hA18 : C' i j = -Gsig H z s i i * (H * Cm) i j :=
    gchainMinorTail_apply_eq hinv hG s tau' (b :: a') (Ne.symm hij)
  have hGii : ‖Gsig H z s i i‖ ≤ B := by
    have := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (n := 1) (tau := [s])
      (a := []) rfl rfl i
    simp only [gchain_single, Nat.sub_self, pow_zero, mul_one] at this
    exact this.trans (hXd 1 le_rfl (by omega))
  -- (A.19): the `S`-average of the column
  have hMD := norm_gchainMinor_sub_gchain_le_div hΦ hB hGinv hn hlen hwf
    (fun p hp2 hp => hXd p (by omega) (by omega)) hXo
  have hpt := sq_norm_gchainMinor_le hG hwf hMD
  have hcol := sum_Sblk_mul_le_two_mul hL i (f := fun k => ‖C k j‖ ^ 2)
    (f' := fun k => ‖Cm k j‖ ^ 2) (fun k => hpt k j)
  have hCC : ∑ k, Sblk L W i k * ‖C k j‖ ^ 2 ≤ X / P := by
    refine sum_Sblk_mul_le hL i fun c => ?_
    rw [← norm_quad_Eblk_apply_self', hCdef, conjTranspose_gchain_mul_Eblk_mul hH hwf c,
      le_div_iff₀ hP0]
    obtain ⟨-, -, hd₃, hd₄⟩ := length_double hwf c
    exact norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (n := 2 * n)
      (hd₃.trans (by rw [hlen])) hd₄ j
  have hV : ∑ k, Sblk L W i k * ‖Cm k j‖ ^ 2
      ≤ (2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) / P := by
    have e : 2 * (cD * (B + Y) / Φ ^ n) ^ 2 = 2 * cD ^ 2 * (B + Y) ^ 2 / Φ / P := by
      rw [div_pow, hΦnP]; field_simp
    have e2 : (2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) / P
        = 2 * (X / P) + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ / P := by ring
    rw [e2, ← e]
    linarith
  have hsqrt : √(∑ k, Sblk L W i k * ‖Cm k j‖ ^ 2)
      ≤ √(2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) / s₀ := by
    refine (Real.sqrt_le_sqrt hV).trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ hP0.le, ← hs₀P, Real.sqrt_sq hs₀.le]
  have hC'ij : ‖C' i j‖ * s₀ ≤ B * κ * √(2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) := by
    rw [hA18, norm_mul, norm_neg]
    have h1 := mul_le_mul hGii hLDE (norm_nonneg _) hB
    have h2 := mul_le_mul_of_nonneg_left hsqrt hκ
    calc ‖Gsig H z s i i‖ * ‖(H * Cm) i j‖ * s₀
        ≤ B * (κ * √(∑ k, Sblk L W i k * ‖Cm k j‖ ^ 2)) * s₀ :=
          mul_le_mul_of_nonneg_right h1 hs₀.le
      _ ≤ B * (κ * (√(2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) / s₀)) * s₀ := by gcongr
      _ = B * κ * √(2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) := by
          field_simp
  have hsplit := norm_le_insert' (C i j) (C' i j)
  rw [norm_sub_rev] at hsplit
  nlinarith

/-- `√(ab) ≤ a + b` for `a, b ≥ 0`. -/
theorem sqrt_mul_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ a + b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg ha hb]

/-- A diagonal entry of a `2n`-chain is bounded by the symmetric `n`-chain quadratic forms
(Cauchy--Schwarz, the reduction at the start of the proof of (A.14)). -/
theorem normSq_gchain_double_le (hH : H.IsHermitian) {n : ℕ} (hn : 1 ≤ n) {tau : List Bool}
    {a : List (ZMod L)} (hlen : tau.length = 2 * n) (h : tau.length = a.length + 1)
    (x : ZMod L × Fin W) {R : ℝ}
    (hR : ∀ (tau' : List Bool) (a' : List (ZMod L)), tau'.length = n →
      tau'.length = a'.length + 1 → ∀ c,
        ‖(gchain L W H z tau' a' * Eblk L W c * (gchain L W H z tau' a')ᴴ) x x‖ ≤ R) :
    ‖gchain L W H z tau a x x‖ ^ 2 ≤ R * R := by
  obtain ⟨tau₁, tau₂, a₁, a₂, b, rfl, rfl, hl₁, hl₂, h₁, h₂⟩ :=
    exists_chain_split (p := n) (q := n) hn hn (by omega) h
  rw [gchain_append_Eblk h₁]
  have hcs := normSq_mul_Eblk_mul_le (gchain L W H z tau₁ a₁) (gchain L W H z tau₂ a₂) b x x
  have hC3 : (gchain L W H z (tau₂.map (!·)).reverse a₂.reverse)ᴴ = gchain L W H z tau₂ a₂ := by
    rw [← gchain_conjTranspose hH h₂, conjTranspose_conjTranspose]
  have e : (gchain L W H z tau₂ a₂)ᴴ * Eblk L W b * gchain L W H z tau₂ a₂
      = gchain L W H z (tau₂.map (!·)).reverse a₂.reverse * Eblk L W b
        * (gchain L W H z (tau₂.map (!·)).reverse a₂.reverse)ᴴ := by
    rw [hC3, gchain_conjTranspose hH h₂]
  rw [e] at hcs
  have h1 := hR tau₁ a₁ hl₁ h₁ b
  have h2 := hR ((tau₂.map (!·)).reverse) a₂.reverse (by simpa using hl₂) (by simpa using h₂) b
  exact hcs.trans (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))

/-- **The induction step (A.7), deterministic form.**  Let `n ≥ 2` and suppose
`Ξ^(o)_l ≤ B` for `1 ≤ l ≤ n - 1` and `Ξ^(d)_p ≤ B` for `1 ≤ p ≤ 2n - 2`.  Suppose
`G_{ii} ≠ 0`, `|1/G_{ii}| ≤ K` (the paper's `1/G_{ii} = O(1)`), the `2n`-loop bound
`LoopBound … Λ (2n)` ((2.77)), the large-deviation bounds `ChainLDE16 … κ₁ n`,
`ChainLDE19 … κ₂ n` ([39, Lemma 3.3] in (A.16), (A.19)), `Φ ≤ W` (`Wℓη ≤ W`) and
`Φ ≥ chainScale K B κ₁ κ₂ n`.  Then `Ξ^(o)_l ≤ B'` for `1 ≤ l ≤ n` and `Ξ^(d)_p ≤ B'` for
`1 ≤ p ≤ 2n`, with the explicit `B' = chainNext K B κ₁ κ₂ Λ n`.  This contains (A.14) and
(A.17). -/
theorem XiDiag_XiOff_step (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0)
    (hG : ∀ s i, Gsig H z s i i ≠ 0) {K B κ₁ κ₂ Λ : ℝ}
    (hGinv : ∀ s i, ‖(Gsig H z s i i)⁻¹‖ ≤ K) (hΦ : 0 < Φ) (hΦW : Φ ≤ W) (hB : 0 ≤ B)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) {n : ℕ} (hn : 2 ≤ n)
    (hLoop : LoopBound L W H z Φ Λ (2 * n)) (hLDE16 : ChainLDE16 L W H z κ₁ n)
    (hLDE19 : ChainLDE19 L W H z κ₂ n) (hscale : chainScale K B κ₁ κ₂ n ≤ Φ)
    (hXd : ∀ p, 1 ≤ p → p ≤ 2 * n - 2 → XiDiag L W H z Φ p ≤ B)
    (hXo : ∀ l, 1 ≤ l → l ≤ n - 1 → XiOff L W H z Φ l ≤ B) :
    (∀ p, 1 ≤ p → p ≤ 2 * n → XiDiag L W H z Φ p ≤ chainNext K B κ₁ κ₂ Λ n) ∧
      (∀ l, 1 ≤ l → l ≤ n → XiOff L W H z Φ l ≤ chainNext K B κ₁ κ₂ Λ n) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true 0)
  have hΛ : 0 ≤ Λ := (mul_nonneg (norm_nonneg _) (pow_nonneg hΦ.le _)).trans
    (hLoop ⟨List.replicate (2 * n) true, List.replicate (2 * n) 0⟩ (by simp) (by simp))
  set X := XiDiag L W H z Φ (2 * n) with hXdef
  set Y := XiOff L W H z Φ n with hYdef
  set cM := chainCM K B n with hcM
  set cD := chainCD K B n with hcD
  have hcM0 : 0 ≤ cM := chainCM_nonneg hK hB n
  have hX0 : 0 ≤ X := XiDiag_nonneg hΦ.le _
  have hY0 : 0 ≤ Y := XiOff_nonneg hΦ.le _
  have hα : 0 ≤ B ^ 2 * (1 + κ₁) := by positivity
  have hβ : 0 ≤ B * κ₂ := mul_nonneg hB hκ₂
  set R := B ^ 2 + cM ^ 2 + 2 * cM * √X
    + B ^ 2 * (1 + κ₁) * (2 * Λ + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) with hRdef
  have hR0 : 0 ≤ R := by
    have h1 : 0 ≤ 2 * cM * √X := by positivity
    have h2 : 0 ≤ B ^ 2 * (1 + κ₁) * (2 * Λ + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) :=
      mul_nonneg hα (by positivity)
    positivity
  set P := Φ ^ (2 * n - 1) with hPdef
  have hP0 : 0 < P := by positivity
  -- (A.14): the self-consistent inequality for `Ξ^(d)_{2n}`
  have hXi : X ≤ R := by
    refine XiDiag_le hR0 (fun tau a hlen h x => ?_) (by omega)
    have hsym : ∀ (tau' : List Bool) (a' : List (ZMod L)), tau'.length = n →
        tau'.length = a'.length + 1 → ∀ c,
          ‖(gchain L W H z tau' a' * Eblk L W c * (gchain L W H z tau' a')ᴴ) x x‖ ≤ R / P := by
      intro tau' a' hl' h' c
      rw [le_div_iff₀ hP0]
      exact norm_quad_gchain_le hL hH hz (fun s => hG s x) (fun s => hGinv s x) hΦ hΦW hB hκ₁
        hn hXd hXo hLoop hl' h' c (hLDE16 tau' a' hl' h' x c)
    have hsq := normSq_gchain_double_le hH (by omega) hlen h x hsym
    rw [← sq] at hsq
    have := le_of_sq_le_sq hsq (div_nonneg hR0 hP0.le)
    rwa [le_div_iff₀ hP0] at this
  -- (A.17): the self-consistent inequality for `Ξ^(o)_n`
  have hYi : Y ≤ cM + B * κ₂ * √(2 * X + 2 * cD ^ 2 * (B + Y) ^ 2 / Φ) := by
    refine XiOff_le (by positivity) (fun tau a hlen h x y hxy => ?_) (by omega)
    exact norm_gchain_off_le hL hH hz (fun s => hG s x) (fun s => hGinv s x) hΦ hB hκ₂ hn hXd
      hXo hlen h hxy (hLDE19 tau a hlen h x y hxy)
  obtain ⟨hXb, hYb⟩ := bootstrap_A14_A17 hX0 hY0 hB hcM0 (sq_nonneg cD) hα hβ hΦ hXi hYi hscale
  have hXb' : X ≤ chainXb K B κ₁ Λ n := hXb
  have hYb' : Y ≤ chainYb K B κ₁ κ₂ Λ n := hYb
  have hXb0 : 0 ≤ chainXb K B κ₁ Λ n := hX0.trans hXb'
  have hYb0 : 0 ≤ chainYb K B κ₁ κ₂ Λ n := hY0.trans hYb'
  have hnext : chainNext K B κ₁ κ₂ Λ n = B + chainXb K B κ₁ Λ n + chainYb K B κ₁ κ₂ Λ n := rfl
  refine ⟨fun p hp1 hp => ?_, fun l hl1 hl => ?_⟩
  · rcases Nat.lt_or_ge p (2 * n - 1) with h1 | h1
    · linarith [hXd p hp1 (by omega)]
    · rcases Nat.lt_or_ge p (2 * n) with h2 | h2
      · have hp' : p = (n - 1) + n := by omega
        have hadd := XiDiag_add_le (L := L) (W := W) (H := H) (z := z) hH hΦ.le
          (p := n - 1) (q := n) (by omega) (by omega)
        rw [← hp', show 2 * (n - 1) = 2 * n - 2 by omega] at hadd
        have hB2 := hXd (2 * n - 2) (by omega) le_rfl
        have hmul : XiDiag L W H z Φ (2 * n - 2) * X ≤ B * chainXb K B κ₁ Λ n :=
          mul_le_mul hB2 hXb' hX0 hB
        have := (Real.sqrt_le_sqrt hmul).trans (sqrt_mul_le_add hB hXb0)
        linarith
      · rw [show p = 2 * n by omega]
        linarith
  · rcases Nat.lt_or_ge l n with h1 | h1
    · linarith [hXo l hl1 (by omega)]
    · rw [show l = n by omega]
      linarith

end Step

/-! ### Lemma A.2 -/

/-- The bounds of the induction (A.7): `chainBound … m` bounds `Ξ^(o)_l` for `l ≤ m + 1` and
`Ξ^(d)_p` for `p ≤ 2m + 2` (the hypothesis of (A.7) at level `n = m + 2`).  The base value
`B₀ + 2B₀²` covers `Ξ^(d)_1`, `Ξ^(o)_1` (Theorem 2.3) and `Ξ^(d)_2` (p. 85);
`Λ n` is the bound for `2n`-loops. -/
noncomputable def chainBound (K B₀ κ₁ κ₂ : ℝ) (Λ : ℕ → ℝ) : ℕ → ℝ
  | 0 => B₀ + 2 * B₀ ^ 2
  | m + 1 => chainNext K (chainBound K B₀ κ₁ κ₂ Λ m) κ₁ κ₂ (Λ (m + 2)) (m + 2)

/-- The size of `Φ` needed for the first `m` steps of (A.7). -/
noncomputable def chainScaleUpTo (K B₀ κ₁ κ₂ : ℝ) (Λ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => max (chainScaleUpTo K B₀ κ₁ κ₂ Λ m)
      (chainScale K (chainBound K B₀ κ₁ κ₂ Λ m) κ₁ κ₂ (m + 2))

theorem chainScaleUpTo_mono (K B₀ κ₁ κ₂ : ℝ) (Λ : ℕ → ℝ) {m m' : ℕ} (h : m ≤ m') :
    chainScaleUpTo K B₀ κ₁ κ₂ Λ m ≤ chainScaleUpTo K B₀ κ₁ κ₂ Λ m' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_max_left _ _)

section LemmaA2

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {Φ : ℝ}

/-- **The induction (A.7), iterated.**  Under the inputs of Lemma A.2 (see `lemma_A2`), for
every `m`, if `Φ ≥ chainScaleUpTo … m` then `Ξ^(o)_l ≤ chainBound … m` for `1 ≤ l ≤ m + 1`
and `Ξ^(d)_p ≤ chainBound … m` for `1 ≤ p ≤ 2m + 2`. -/
theorem XiDiag_XiOff_le_chainBound (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0)
    (hG : ∀ s i, Gsig H z s i i ≠ 0) {K B₀ κ₁ κ₂ : ℝ} {Λ : ℕ → ℝ}
    (hGinv : ∀ s i, ‖(Gsig H z s i i)⁻¹‖ ≤ K) (hΦ : 0 < Φ) (hΦW : Φ ≤ W)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hd1 : XiDiag L W H z Φ 1 ≤ B₀) (ho1 : XiOff L W H z Φ 1 ≤ B₀)
    (hLoop : ∀ n, 2 ≤ n → LoopBound L W H z Φ (Λ n) (2 * n))
    (hLDE16 : ∀ n, 2 ≤ n → ChainLDE16 L W H z κ₁ n)
    (hLDE19 : ∀ n, 2 ≤ n → ChainLDE19 L W H z κ₂ n) :
    ∀ m, chainScaleUpTo K B₀ κ₁ κ₂ Λ m ≤ Φ →
      (∀ l, 1 ≤ l → l ≤ m + 1 → XiOff L W H z Φ l ≤ chainBound K B₀ κ₁ κ₂ Λ m) ∧
        (∀ p, 1 ≤ p → p ≤ 2 * m + 2 → XiDiag L W H z Φ p ≤ chainBound K B₀ κ₁ κ₂ Λ m) := by
  intro m
  induction m with
  | zero =>
    intro _
    have hB₀ : 0 ≤ B₀ := (XiDiag_nonneg hΦ.le 1).trans hd1
    have hd0 := XiDiag_nonneg (L := L) (W := W) (H := H) (z := z) hΦ.le 1
    have ho0 := XiOff_nonneg (L := L) (W := W) (H := H) (z := z) hΦ.le 1
    have hWΦ : (W : ℝ)⁻¹ * Φ ≤ 1 := by
      have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
      rw [inv_mul_le_iff₀ hW, mul_one]; exact hΦW
    have hd2 : XiDiag L W H z Φ 2 ≤ 2 * B₀ ^ 2 := by
      refine (XiDiag_two_le hΦ).trans ?_
      have h1 : XiDiag L W H z Φ 1 ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hd0 hd1 2
      have h2 : XiOff L W H z Φ 1 ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ ho0 ho1 2
      have h3 : (W : ℝ)⁻¹ * Φ * XiDiag L W H z Φ 1 ^ 2 ≤ 1 * B₀ ^ 2 :=
        mul_le_mul hWΦ h1 (sq_nonneg _) zero_le_one
      linarith
    have hB₀2 : 0 ≤ B₀ ^ 2 := sq_nonneg B₀
    refine ⟨fun l hl1 hl => ?_, fun p hp1 hp => ?_⟩
    · rw [show l = 1 by omega]
      show _ ≤ B₀ + 2 * B₀ ^ 2
      linarith
    · show _ ≤ B₀ + 2 * B₀ ^ 2
      rcases Nat.lt_or_ge p 2 with h | h
      · rw [show p = 1 by omega]; linarith
      · rw [show p = 2 by omega]; linarith
  | succ m ih =>
    intro hscale
    have hscale' : chainScaleUpTo K B₀ κ₁ κ₂ Λ m ≤ Φ := (le_max_left _ _).trans hscale
    have hstep : chainScale K (chainBound K B₀ κ₁ κ₂ Λ m) κ₁ κ₂ (m + 2) ≤ Φ :=
      (le_max_right _ _).trans hscale
    obtain ⟨hXo, hXd⟩ := ih hscale'
    have hB : 0 ≤ chainBound K B₀ κ₁ κ₂ Λ m :=
      (XiDiag_nonneg hΦ.le 1).trans (hXd 1 le_rfl (by omega))
    obtain ⟨hd, ho⟩ := XiDiag_XiOff_step hL hH hz hG hGinv hΦ hΦW hB hκ₁ hκ₂ (n := m + 2)
      (by omega) (hLoop (m + 2) (by omega)) (hLDE16 (m + 2) (by omega))
      (hLDE19 (m + 2) (by omega)) hstep (fun p hp1 hp => hXd p hp1 (by omega))
      (fun l hl1 hl => hXo l hl1 (by omega))
    exact ⟨fun l hl1 hl => ho l hl1 (by omega), fun p hp1 hp => hd p hp1 (by omega)⟩

/-- **Lemma A.2 (the `n`-chain estimate), deterministic form, (A.3) and (A.4).**  Let `H` be
Hermitian, `Im z ≠ 0`, `0 < Φ ≤ W` (`Φ` stands for `W ℓ_t η_t`), and assume, with `≺`
replaced by explicit constants:
* Theorem 2.3: `G_{ii} ≠ 0`, `|1/G_{ii}| ≤ K`, `Ξ^(d)_1 ≤ B₀`, `Ξ^(o)_1 ≤ B₀`;
* the loop bound (2.77) of Lemma 2.18: `|L_{σ,a}| Φ^{2n-1} ≤ Λ n` for `2n`-loops;
* [39, Lemma 3.3] as used in (A.16), (A.19): `ChainLDE16 … κ₁ n`, `ChainLDE19 … κ₂ n`.
Then for every `n ≥ 1` and `Φ ≥ chainScaleUpTo … n`, every well-formed `n`-chain obeys
`|(C_{σ,a})_{ii}| ≤ B_n Φ^{-(n-1)}` (A.3) and `|(C_{σ,a})_{ij}| ≤ B_n Φ^{-(n-1/2)}`, `i ≠ j` (A.4),
with the explicit constant `B_n = chainBound … n`, which depends only on
`n, K, B₀, κ₁, κ₂, Λ`. -/
theorem lemma_A2 (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0)
    (hG : ∀ s i, Gsig H z s i i ≠ 0) {K B₀ κ₁ κ₂ : ℝ} {Λ : ℕ → ℝ}
    (hGinv : ∀ s i, ‖(Gsig H z s i i)⁻¹‖ ≤ K) (hΦ : 0 < Φ) (hΦW : Φ ≤ W)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hd1 : XiDiag L W H z Φ 1 ≤ B₀) (ho1 : XiOff L W H z Φ 1 ≤ B₀)
    (hLoop : ∀ n, 2 ≤ n → LoopBound L W H z Φ (Λ n) (2 * n))
    (hLDE16 : ∀ n, 2 ≤ n → ChainLDE16 L W H z κ₁ n)
    (hLDE19 : ∀ n, 2 ≤ n → ChainLDE19 L W H z κ₂ n) {n : ℕ} (hn : 1 ≤ n)
    (hscale : chainScaleUpTo K B₀ κ₁ κ₂ Λ n ≤ Φ) {tau : List Bool} {a : List (ZMod L)}
    (hlen : tau.length = n) (h : tau.length = a.length + 1) :
    (∀ x, ‖gchain L W H z tau a x x‖ * Φ ^ (n - 1) ≤ chainBound K B₀ κ₁ κ₂ Λ n) ∧
      (∀ x y, x ≠ y →
        ‖gchain L W H z tau a x y‖ * (Φ ^ (n - 1) * √Φ) ≤ chainBound K B₀ κ₁ κ₂ Λ n) := by
  obtain ⟨ho, hd⟩ := XiDiag_XiOff_le_chainBound hL hH hz hG hGinv hΦ hΦW hκ₁ hκ₂ hd1 ho1 hLoop
    hLDE16 hLDE19 n hscale
  exact ⟨fun x => (norm_gchain_diag_le_XiDiag hlen h x).trans (hd n hn (by omega)),
    fun x y hxy => (norm_gchain_off_le_XiOff hlen h hxy).trans (ho n hn (by omega))⟩

end LemmaA2

end RBM
