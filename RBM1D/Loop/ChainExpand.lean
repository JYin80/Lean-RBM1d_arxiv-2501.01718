/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Chain
import RBM1D.Green.Minor
import Mathlib.Data.Fintype.Vector

/-!
# Appendix A: the deterministic core of the `G`-chain expansion

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Appendix A (pp. 84--89).  Appendix A is not used in the proof of the main
theorems; this file isolates everything in its proof of Lemma A.2 that is exact linear
algebra or deterministic real-number bookkeeping, for a **fixed deterministic Hermitian**
`H`.  There is no probability: the two probabilistic inputs of the paper,
`1/G_{ii} = O(1)` (from Theorem 2.3) and the large-deviation bound [39, Lemma 3.3] used in
(A.16), (A.19), are **explicit hypotheses** of the theorems that need them (`hGinv`, `hLDE`).
The paper's `≺` becomes `≤` with explicit constants, and `Φ` stands for `W ℓ_t η_t`.

## Main definitions

* `RBM.minorExt G i` : the minor resolvent `G^(i)` as an `N × N` matrix (zero `i`-th row and
  column); `minorExt_resolvent` identifies it with `(H^(i) - z)⁻¹` of (4.6).
* `RBM.fchain`, `RBM.gchainMinor`, `RBM.gchainMinorTail` : `C^(ii)_n` of (A.10) and `C^(i)_n`
  of (A.9); `C_n` of (A.8) is `RBM.gchain` (`Loop/Chain.lean`).
* `RBM.XiDiag`, `RBM.XiOff` : the ratios `Ξ^(d)_n`, `Ξ^(o)_n` of (A.5), (A.6).
* `RBM.compTerm`, `RBM.compSum` : the sum over `(n_1, …, n_k; ℓ)` with the indicator
  `1(ℓ + ∑ n_i = n + k)` of (A.24).

## Main results

1. Two-sided chain-to-loop (p. 85): `trace_Eblk_gchain_Eblk_conjTranspose`,
   `⟨E_{a₀} C E_b C†⟩ = L_{σ'',a''}`.
2. (A.5), (A.6): `norm_gchain_diag_le_XiDiag`, `norm_gchain_off_le_XiOff`, `XiDiag_le`, `XiOff_le`.
3. (A.8)--(A.10): the definitions above, with `gchainMinor_row_self`, `gchainMinor_col_self`,
   `gchainMinorTail_col_self`, `gchainMinor_mul_Eblk_mul_conjTranspose`
   (`C^(ii) E C^(ii)†` is a `2n`-chain of the same kind).
4. (A.18): `gchainMinorTail_apply_eq`, `gchainMinorTail_row_eq`; the exact part of (A.16):
   `gchainMinorTail_quad_apply_self`, and with the large-deviation input as a hypothesis
   `norm_gchainMinorTail_quad_sub_le`; the exact part of (A.19): `sum_Svar_normSq_eq`, and
   (A.18)+(A.19)+LDE ⟹ (A.20): `normSq_gchainMinorTail_le`.
5. Exact telescoping identities via (4.9): `gchainMinor_apply_eq_tail` ((4.9) for chains),
   `gchainMinor_apply_expand` (the identity behind (A.25), (A.26)),
   `gchainMinorTail_apply_expand` (behind (A.21)--(A.24)), `gchainMinorTail_two` (A.21),
   `gchainMinorTail_three` (A.22), `trace_gchainMinor_sub_mul_Eblk` (traced form, (A.25)).
   Bounds: `norm_gchainMinorTail_sub_gchain_le_A24` is (A.24) with the composition sum written
   out; `norm_gchainMinorTail_sub_gchain_le` is (A.24) ⟹ (A.11) (with `Ξ^(d) ≤ D`,
   `Ξ^(o) ≤ O`); `norm_gchainMinor_sub_gchain_diag_le` is (A.26) and
   `norm_gchainMinor_sub_gchain_diag_le_trichotomy` is (A.26) + (A.27) ⟹ (A.13).
6. (A.15): `quad_Eblk_apply_self_split` (the split) and `norm_quad_Eblk_sub_le` (the estimate
   that follows it).
7. Cauchy--Schwarz ladder: `normSq_mul_Eblk_mul_le`, `normSq_gchain_append_le`,
   `XiDiag_two_le` (p. 85, `Ξ^(d)_2`), `XiDiag_add_le` (`Ξ^(d)_{2n-1} ≤ (Ξ^(d)_{2n-2}Ξ^(d)_{2n})^{1/2}`),
   `normSq_triple_le`, `XiDiag_two_mul_add_one_le` (`Ξ^(d)_{2n+1} ≤ Ξ^(d)_{2n} Φ Λ^{1/2}`),
   `XiOff_add_le`, `XiOff_le_sqrt` (`Ξ^(o)_l ≤ Φ^{1/2}` for `n < l ≤ 2n`) and the trichotomy
   (A.27) `xi_trichotomy`.

## Deviations from the paper

* **Sign of (4.8)/(A.18).** With `G = (H - z)⁻¹` the correct identity is
  `(C^(i)_n)_{ij} = -(G_1)_{ii} (H C^(ii)_n)_{ij}`; the paper has no minus sign.  Only
  `|·|` of it is ever used.  (Same deviation as `green_off_diag_paper`, `Green/Minor.lean`.)
* **Convention for `G^(i)`.** `minorExt` is the `N × N` zero extension of the
  `(N-1) × (N-1)` matrix `(H^(i) - z)⁻¹` of (4.6), so that (A.9), (A.10) are products of
  `N × N` matrices.  The zero row/column need `G_{ii} ≠ 0`, a hypothesis where used.
* **Charges of `σ''` (p. 85).** `C†` has flipped charges (`G(σ)† = G(-σ)`), so
  `σ'' = (σ_1, …, σ_n, -σ_n, …, -σ_1)`; the paper omits the bars.
* **(A.19) row vs column.** `∑_k S_{ik} |C_{kj}|²` runs over the `j`-th *column* of `C`, i.e.
  `(C† E_a C)_{jj}`; the paper writes `(C E_a C†)_{jj}`.  Both are diagonal entries of
  `2n`-chains, so nothing downstream changes.
* **Explicit constants.** `≺` is replaced by `≤` with explicit constants depending on `n`,
  `K` (the bound on `|1/G_{ii}|`) and `D`; the factors `K^k` from `1/G_{ii}` are absorbed as
  `K Ξ^(d)_{n_r}` in the composition sum.  `XiDiag_two_le` keeps the factor `W⁻¹ Φ` in
  front of `(Ξ^(d)_1)²` (the paper drops it, `Φ = Wℓη ≤ W`), and `XiDiag_two_mul_add_one_le`
  keeps the `2`-loop bound `Λ` as a parameter (the paper uses `Λ = Φ⁻¹`).
* **Index ranges in (A.24).** In `compTerm` the length `ℓ` ranges over `[1, n]` rather than
  `[1, n-1]`; the extra terms vanish for `k ≥ 1` because of the indicator.
* **(A.25).** Only the exact traced identity is given; the paper's further expansion into
  products of diagonal chain entries (with `n_i ≤ 2n + 1`) is not written out as a bound.
-/

namespace RBM

open Matrix Finset

/-! ### The zero-extended minor resolvent -/

section MinorExt

variable {n : Type*} {R : Type*} [Field R]

/-- The minor resolvent `G^(i)` as an `N × N` matrix: the right-hand side of (4.9),
`G_{jk} - G_{ji} G_{ik} / G_{ii}`, at every pair of indices.  When `G_{ii} ≠ 0` its
`i`-th row and column vanish (`minorExt_row_self`, `minorExt_col_self`) and off them it is
`minorGreen`, the inverse of the minor (`minorExt_apply_val`, `minorExt_resolvent`).  This is
the convention in which the chains `C^(i)_n`, `C^(ii)_n` of (A.9), (A.10) are products of
`N × N` matrices. -/
def minorExt (G : Matrix n n R) (i : n) : Matrix n n R :=
  Matrix.of fun j k => G j k - G j i * G i k / G i i

@[simp] theorem minorExt_apply (G : Matrix n n R) (i j k : n) :
    minorExt G i j k = G j k - G j i * G i k / G i i := rfl

theorem minorExt_apply_val (G : Matrix n n R) (i : n) (j k : {a : n // a ≠ i}) :
    minorExt G i j.1 k.1 = minorGreen G i j k := rfl

theorem minorExt_row_self {G : Matrix n n R} {i : n} (hG : G i i ≠ 0) (k : n) :
    minorExt G i i k = 0 := by
  rw [minorExt_apply, mul_div_cancel_left₀ _ hG, sub_self]

theorem minorExt_col_self {G : Matrix n n R} {i : n} (hG : G i i ≠ 0) (j : n) :
    minorExt G i j i = 0 := by
  rw [minorExt_apply, mul_div_cancel_right₀ _ hG, sub_self]

/-- **(4.9) for a product**: `(G^(i) M)_{xy} = (G M)_{xy} - G_{xi} (G M)_{iy} / G_{ii}`.
No hypothesis is needed. -/
theorem minorExt_mul_apply [Fintype n] (G M : Matrix n n R) (i x y : n) :
    (minorExt G i * M) x y = (G * M) x y - G x i * (G * M) i y / G i i := by
  simp only [Matrix.mul_apply, minorExt_apply, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
    mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A matrix whose `i`-th row vanishes still has vanishing `i`-th row after right
multiplication. -/
theorem mul_apply_eq_zero_of_row [Fintype n] {A : Matrix n n R} {i : n} (hA : ∀ k, A i k = 0)
    (B : Matrix n n R) (y : n) : (A * B) i y = 0 := by
  simp [Matrix.mul_apply, hA]

/-- A matrix whose `i`-th column vanishes still has vanishing `i`-th column after left
multiplication. -/
theorem mul_apply_eq_zero_of_col [Fintype n] {B : Matrix n n R} {i : n} (hB : ∀ k, B k i = 0)
    (A : Matrix n n R) (x : n) : (A * B) x i = 0 := by
  simp [Matrix.mul_apply, hB]

/-- `(G^(i))† = (G†)^(i)`. -/
theorem minorExt_conjTranspose (G : Matrix n n ℂ) (i : n) :
    (minorExt G i)ᴴ = minorExt Gᴴ i := by
  ext j k
  simp only [conjTranspose_apply, minorExt_apply, star_sub, star_div₀, star_mul']
  ring

end MinorExt

section MinorExtComplex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For the resolvent, `minorExt` off the `i`-th row and column is the Green's function
`(H^(i) - z)⁻¹` of the minor, i.e. the paper's `G^(i)` of (4.6). -/
theorem minorExt_resolvent {H : Matrix n n ℂ} {z : ℂ}
    (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n) (hGii : green H z i i ≠ 0)
    (j k : {a : n // a ≠ i}) :
    minorExt (green H z) i j.1 k.1
      = ((H.submatrix Subtype.val Subtype.val - z • (1 : Matrix {a : n // a ≠ i} _ ℂ))⁻¹ :
          Matrix {a : n // a ≠ i} {a : n // a ≠ i} ℂ) j k := by
  rw [inv_minor_resolvent h i hGii, minorExt_apply_val]

/-- **The row form of (4.8)**: for every `k` (including `k = i`),
`G_{ik} = -G_{ii} (H G^(i))_{ik} + δ_{ik} G_{ii}`. -/
theorem green_row_eq {H : Matrix n n ℂ} {z : ℂ}
    (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n) (hGii : green H z i i ≠ 0) (k : n) :
    green H z i k
      = -green H z i i * (H * minorExt (green H z) i) i k
        + (if k = i then green H z i i else 0) := by
  by_cases hk : k = i
  · subst hk
    rw [mul_apply_eq_zero_of_col (minorExt_col_self hGii) H k]
    simp only [ite_true]
    ring
  · rw [ite_eq_right hk, add_zero, green_off_diag_paper h i hGii ⟨k, hk⟩]
    congr 1
    rw [Matrix.mul_apply]
    have := sum_subtype_ne i (fun l => H i l * minorExt (green H z) i l k)
    simp only [minorExt_row_self hGii, mul_zero, sub_zero] at this
    rw [← this]
    rfl

end MinorExtComplex

/-! ### Chains built from an arbitrary charge-indexed family -/

section FChain

variable (L W : ℕ) [NeZero L]

/-- The chain `F(s_1) E_{a_1} F(s_2) ⋯ E_{a_{n-1}} F(s_n)` for an arbitrary family
`F : Bool → Matrix`.  `F = G(·)` gives the `G`-chain (A.1), `F = G^(i)(·)` the chain
`C^(ii)_n` of (A.10). -/
noncomputable def fchain (F : Bool → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) :
    List Bool → List (ZMod L) → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ
  | [], _ => 1
  | s :: _, [] => F s
  | s :: tau, b :: a => F s * Eblk L W b * fchain F tau a

variable {L W} {F : Bool → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

@[simp] theorem fchain_nil (a : List (ZMod L)) : fchain L W F [] a = 1 := by
  cases a <;> rfl

@[simp] theorem fchain_single (s : Bool) (tau : List Bool) :
    fchain L W F (s :: tau) [] = F s := rfl

@[simp] theorem fchain_cons (s : Bool) (b : ZMod L) (tau : List Bool) (a : List (ZMod L)) :
    fchain L W F (s :: tau) (b :: a) = F s * Eblk L W b * fchain L W F tau a := rfl

/-- The `G`-chain of Definition A.1 is the chain of the family `G(·)`. -/
theorem gchain_eq_fchain [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (tau : List Bool) (a : List (ZMod L)) :
    gchain L W H z tau a = fchain L W (Gsig H z) tau a := by
  induction tau generalizing a with
  | nil => simp [gchain_nil]
  | cons s tau ih =>
    cases a with
    | nil => rfl
    | cons b a => rw [gchain_cons, fchain_cons, ih]

/-- **Concatenating two chains through one `E`**:
`C_{tau₁,a₁} E_b C_{tau₂,a₂} = C_{tau₁ ++ tau₂, a₁ ++ b :: a₂}`. -/
theorem fchain_append {tau₁ : List Bool} {a₁ : List (ZMod L)}
    (h : tau₁.length = a₁.length + 1) (b : ZMod L) (tau₂ : List Bool) (a₂ : List (ZMod L)) :
    fchain L W F (tau₁ ++ tau₂) (a₁ ++ b :: a₂)
      = fchain L W F tau₁ a₁ * Eblk L W b * fchain L W F tau₂ a₂ := by
  induction tau₁ generalizing a₁ with
  | nil => simp at h
  | cons t tau ih =>
    cases a₁ with
    | nil =>
      have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst htau
      rfl
    | cons c a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      rw [List.cons_append, List.cons_append, fchain_cons, fchain_cons, ih h']
      simp only [Matrix.mul_assoc]

/-- A chain of a family with `F(s)† = F(-s)` conjugates to the reversed, flipped chain. -/
theorem fchain_conjTranspose (hF : ∀ s, (F s)ᴴ = F (!s)) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) :
    (fchain L W F tau a)ᴴ = fchain L W F (tau.map (!·)).reverse a.reverse := by
  induction tau generalizing a with
  | nil => simp at h
  | cons t tau ih =>
    cases a with
    | nil =>
      have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst htau
      simp [hF]
    | cons c a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      have hlen : (tau.map (!·)).reverse.length = a.reverse.length + 1 := by
        simpa using h'
      rw [fchain_cons, conjTranspose_mul, conjTranspose_mul, ih h', Eblk_conjTranspose, hF]
      simp only [List.map_cons, List.reverse_cons]
      rw [fchain_append hlen, fchain_single, Matrix.mul_assoc]

omit [NeZero L] in
/-- A well-formed chain has length at least one. -/
theorem length_pos_of_wf {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) : tau ≠ [] := by
  rintro rfl
  simp at h

end FChain

/-! ### Item (1): the two-sided chain-to-loop identity -/

section TwoSided

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- `C E_b C'` for two `G`-chains is a `G`-chain. -/
theorem gchain_append_Eblk {tau₁ : List Bool} {a₁ : List (ZMod L)}
    (h : tau₁.length = a₁.length + 1) (b : ZMod L) (tau₂ : List Bool) (a₂ : List (ZMod L)) :
    gchain L W H z (tau₁ ++ tau₂) (a₁ ++ b :: a₂)
      = gchain L W H z tau₁ a₁ * Eblk L W b * gchain L W H z tau₂ a₂ := by
  simp only [gchain_eq_fchain]
  exact fchain_append h b tau₂ a₂

/-- `C E_b C†` is the `G`-chain with charges `(σ_1, …, σ_n, -σ_n, …, -σ_1)` and labels
`(a_1, …, a_{n-1}, b, a_{n-1}, …, a_1)`. -/
theorem gchain_mul_Eblk_mul_conjTranspose (hH : H.IsHermitian) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (b : ZMod L) :
    gchain L W H z tau a * Eblk L W b * (gchain L W H z tau a)ᴴ
      = gchain L W H z (tau ++ (tau.map (!·)).reverse) (a ++ b :: a.reverse) := by
  rw [gchain_conjTranspose hH h, gchain_append_Eblk h]

/-- **Item (1), p. 85: the two-sided chain-to-loop identity**
`⟨E_{a₀} C_{σ,a} E_b C_{σ,a}†⟩ = L_{σ'', a''}` with
`σ'' = (σ_1, …, σ_n, -σ_n, …, -σ_1)` and `a'' = (a_1, …, a_{n-1}, b, a_{n-1}, …, a_1, a₀)`.
(The paper writes `σ''` without the bars on the second half; `G(σ)† = G(-σ)` flips them.) -/
theorem trace_Eblk_gchain_Eblk_conjTranspose (hH : H.IsHermitian) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (a₀ b : ZMod L) :
    Matrix.trace (Eblk L W a₀ * gchain L W H z tau a * Eblk L W b
        * (gchain L W H z tau a)ᴴ)
      = gloop L W H z ⟨tau ++ (tau.map (!·)).reverse, a ++ b :: a.reverse ++ [a₀]⟩ := by
  have hlen : (tau ++ (tau.map (!·)).reverse).length = (a ++ b :: a.reverse).length + 1 := by
    simp [h]
    omega
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    gchain_mul_Eblk_mul_conjTranspose hH h, trace_gchain_mul_Eblk hlen]

end TwoSided

/-! ### Item (3): the chains `C_n`, `C^(i)_n`, `C^(ii)_n` of (A.8)--(A.10) -/

section MinorChains

variable (L W : ℕ) [NeZero L]

/-- **(A.10)** `C^(ii)_n = G^(i)_1 E_{a_1} G^(i)_2 ⋯ E_{a_{n-1}} G^(i)_n`: every `G` replaced by
its minor resolvent. -/
noncomputable def gchainMinor (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (i : ZMod L × Fin W) : List Bool → List (ZMod L) → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  fchain L W (fun s => minorExt (Gsig H z s) i)

/-- **(A.9)** `C^(i)_n = G_1 E_{a_1} G^(i)_2 ⋯ E_{a_{n-1}} G^(i)_n`: every `G` but the first
replaced by its minor resolvent. -/
noncomputable def gchainMinorTail (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (i : ZMod L × Fin W) : List Bool → List (ZMod L) → Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ
  | [], _ => 1
  | s :: _, [] => Gsig H z s
  | s :: tau, b :: a => Gsig H z s * Eblk L W b * gchainMinor L W H z i tau a

variable {L W} {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W}

@[simp] theorem gchainMinor_nil (a : List (ZMod L)) : gchainMinor L W H z i [] a = 1 :=
  fchain_nil a

@[simp] theorem gchainMinor_single (s : Bool) (tau : List Bool) :
    gchainMinor L W H z i (s :: tau) [] = minorExt (Gsig H z s) i := rfl

@[simp] theorem gchainMinor_cons (s : Bool) (b : ZMod L) (tau : List Bool) (a : List (ZMod L)) :
    gchainMinor L W H z i (s :: tau) (b :: a)
      = minorExt (Gsig H z s) i * Eblk L W b * gchainMinor L W H z i tau a := rfl

@[simp] theorem gchainMinorTail_single (s : Bool) (tau : List Bool) :
    gchainMinorTail L W H z i (s :: tau) [] = Gsig H z s := rfl

@[simp] theorem gchainMinorTail_cons (s : Bool) (b : ZMod L) (tau : List Bool)
    (a : List (ZMod L)) :
    gchainMinorTail L W H z i (s :: tau) (b :: a)
      = Gsig H z s * Eblk L W b * gchainMinor L W H z i tau a := rfl

/-- The `i`-th row of `C^(ii)_n` vanishes off the diagonal (for `n = 0` the chain is `1`). -/
theorem gchainMinor_row_self (hG : ∀ s, Gsig H z s i i ≠ 0) (tau : List Bool)
    (a : List (ZMod L)) {j : ZMod L × Fin W} (hj : j ≠ i) :
    gchainMinor L W H z i tau a i j = 0 := by
  cases tau with
  | nil => simp [Matrix.one_apply_ne (Ne.symm hj)]
  | cons s tau =>
    cases a with
    | nil => exact minorExt_row_self (hG s) j
    | cons b a =>
      rw [gchainMinor_cons, Matrix.mul_assoc]
      exact mul_apply_eq_zero_of_row (minorExt_row_self (hG s)) _ j

/-- The `i`-th column of a well-formed `C^(ii)_n` vanishes. -/
theorem gchainMinor_col_self (hG : ∀ s, Gsig H z s i i ≠ 0) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (x : ZMod L × Fin W) :
    gchainMinor L W H z i tau a x i = 0 := by
  induction tau generalizing a x with
  | nil => simp at h
  | cons s tau ih =>
    cases a with
    | nil => exact minorExt_col_self (hG s) x
    | cons b a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      rw [gchainMinor_cons]
      exact mul_apply_eq_zero_of_col (fun k => ih h' k) _ x

/-- The `i`-th column of a well-formed `C^(i)_n`, `n ≥ 2`, vanishes. -/
theorem gchainMinorTail_col_self (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (b : ZMod L)
    {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1)
    (x : ZMod L × Fin W) :
    gchainMinorTail L W H z i (s :: tau) (b :: a) x i = 0 := by
  rw [gchainMinorTail_cons]
  exact mul_apply_eq_zero_of_col (fun k => gchainMinor_col_self hG h k) _ x

/-- `C^(ii)_n` of a family with `G(σ)† = G(-σ)` conjugates to the reversed, flipped chain;
in particular `C^(ii)_n E_a C^(ii)_n†` is again a `C^(ii)`-chain (of length `2n`). -/
theorem gchainMinor_conjTranspose (hH : H.IsHermitian) {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) :
    (gchainMinor L W H z i tau a)ᴴ = gchainMinor L W H z i (tau.map (!·)).reverse a.reverse :=
  fchain_conjTranspose (fun s => by rw [minorExt_conjTranspose, Gsig_conjTranspose hH]) h

/-- `C^(ii) E_b C^(ii)†` is the `C^(ii)`-chain of the doubled charges and labels. -/
theorem gchainMinor_mul_Eblk_mul_conjTranspose (hH : H.IsHermitian) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (b : ZMod L) :
    gchainMinor L W H z i tau a * Eblk L W b * (gchainMinor L W H z i tau a)ᴴ
      = gchainMinor L W H z i (tau ++ (tau.map (!·)).reverse) (a ++ b :: a.reverse) := by
  rw [gchainMinor_conjTranspose hH h]
  exact (fchain_append h b _ _).symm

end MinorChains

/-! ### Item (4): (A.18), and the exact parts of (A.16) and (A.19) -/

section A18

variable {L W : ℕ} [NeZero L] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
  {i : ZMod L × Fin W}

/-- The row form of (4.8) for `G(σ)`. -/
theorem Gsig_row_eq (hinv : ∀ s : Bool,
      IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det)
    (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (k : ZMod L × Fin W) :
    Gsig H z s i k
      = -Gsig H z s i i * (H * minorExt (Gsig H z s) i) i k
        + (if k = i then Gsig H z s i i else 0) :=
  green_row_eq (hinv s) i (hG s) k

/-- **(A.18)**: `(C^(i)_n)_{ij} = -(G_1)_{ii} (H C^(ii)_n)_{ij}` for `j ≠ i`.
This is (4.8) applied to the first factor; the paper's (A.18) has no minus sign, see the
module docstring.  The inputs are that `H - z` and `H - z̄` are invertible and that the
diagonal entries `G(±)_{ii}` do not vanish. -/
theorem gchainMinorTail_apply_eq (hinv : ∀ s : Bool,
      IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det)
    (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (tau : List Bool) (a : List (ZMod L))
    {j : ZMod L × Fin W} (hj : j ≠ i) :
    gchainMinorTail L W H z i (s :: tau) a i j
      = -Gsig H z s i i * (H * gchainMinor L W H z i (s :: tau) a) i j := by
  cases a with
  | nil =>
    rw [gchainMinorTail_single, gchainMinor_single, Gsig_row_eq hinv hG s j,
      ite_eq_right hj, add_zero]
  | cons b a =>
    have hY : (Eblk L W b * gchainMinor L W H z i tau a) i j = 0 := by
      rw [Eblk, diagonal_mul, gchainMinor_row_self hG tau a hj, mul_zero]
    have hH : H * gchainMinor L W H z i (s :: tau) (b :: a)
        = H * minorExt (Gsig H z s) i * (Eblk L W b * gchainMinor L W H z i tau a) := by
      rw [gchainMinor_cons]
      simp only [Matrix.mul_assoc]
    have hterm : ∀ k, Gsig H z s i k * (Eblk L W b * gchainMinor L W H z i tau a) k j
        = -Gsig H z s i i * ((H * minorExt (Gsig H z s) i) i k
            * (Eblk L W b * gchainMinor L W H z i tau a) k j)
          + (if k = i then Gsig H z s i i * (Eblk L W b * gchainMinor L W H z i tau a) i j
              else 0) := by
      intro k
      rw [Gsig_row_eq hinv hG s k]
      split_ifs with hk
      · subst hk; ring
      · ring
    rw [gchainMinorTail_cons, hH, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply,
      Finset.mul_sum]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hY,
      mul_zero, add_zero]

/-- For `n ≥ 2` the identity (A.18) holds on the whole `i`-th row, `j = i` included
(both sides vanish there). -/
theorem gchainMinorTail_row_eq (hinv : ∀ s : Bool,
      IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det)
    (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (b : ZMod L) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (j : ZMod L × Fin W) :
    gchainMinorTail L W H z i (s :: tau) (b :: a) i j
      = -Gsig H z s i i * (H * gchainMinor L W H z i (s :: tau) (b :: a)) i j := by
  by_cases hj : j = i
  · rw [hj]
    have hcol : ∀ x, gchainMinor L W H z i (s :: tau) (b :: a) x i = 0 :=
      gchainMinor_col_self hG (by simpa using h)
    rw [gchainMinorTail_col_self hG s b h, mul_apply_eq_zero_of_col hcol, mul_zero]
  · exact gchainMinorTail_apply_eq hinv hG s tau (b :: a) hj

/-- A diagonal entry of `A D A†` only sees the `i`-th row of `A`. -/
theorem quad_apply_self_of_row {n : Type*} [Fintype n] {A B D : Matrix n n ℂ} {i : n} {c : ℂ}
    (hrow : ∀ j, A i j = c * B i j) :
    (A * D * Aᴴ) i i = c * star c * (B * D * Bᴴ) i i := by
  simp only [Matrix.mul_apply, conjTranspose_apply, hrow, star_mul', Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The exact part of (A.16)**: for `n ≥ 2`,
`(C^(i)_n E_c C^(i)_n†)_{ii} = |G_{ii}|² (H C^(ii)_n E_c C^(ii)_n† H)_{ii}`. -/
theorem gchainMinorTail_quad_apply_self (hH : H.IsHermitian) (hinv : ∀ s : Bool,
      IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det)
    (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (b : ZMod L) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (c : ZMod L) :
    (gchainMinorTail L W H z i (s :: tau) (b :: a) * Eblk L W c
        * (gchainMinorTail L W H z i (s :: tau) (b :: a))ᴴ) i i
      = (Complex.normSq (Gsig H z s i i) : ℂ)
        * (H * gchainMinor L W H z i (s :: tau) (b :: a) * Eblk L W c
            * (gchainMinor L W H z i (s :: tau) (b :: a))ᴴ * H) i i := by
  rw [quad_apply_self_of_row (gchainMinorTail_row_eq hinv hG s b h), conjTranspose_mul, hH.eq]
  have hn : -Gsig H z s i i * star (-Gsig H z s i i)
      = (Complex.normSq (Gsig H z s i i) : ℂ) := by
    rw [star_neg, neg_mul_neg, Complex.star_def, Complex.mul_conj]
  rw [hn]
  simp only [Matrix.mul_assoc]

/-- **(A.16) with [39, Lemma 3.3] as an explicit hypothesis**: if the quadratic form
`(H X H)_{ii}`, `X = C^(ii) E_c C^(ii)†`, is within `ε` of `∑_k S_{ik} X_{kk}` (the paper's
large-deviation input, which uses that `C^(ii)` does not depend on the `i`-th row of `H`), then
`(C^(i) E_c C^(i)†)_{ii}` is within `|G_{ii}|² ε` of `|G_{ii}|² ∑_k S_{ik} X_{kk}`. -/
theorem norm_gchainMinorTail_quad_sub_le (hH : H.IsHermitian) (hinv : ∀ s : Bool,
      IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det)
    (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (b : ZMod L) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (c : ZMod L) {ε : ℝ}
    (hLDE : ‖(H * (gchainMinor L W H z i (s :: tau) (b :: a) * Eblk L W c
        * (gchainMinor L W H z i (s :: tau) (b :: a))ᴴ) * H) i i
      - ∑ k, Svar L W i k * (gchainMinor L W H z i (s :: tau) (b :: a) * Eblk L W c
          * (gchainMinor L W H z i (s :: tau) (b :: a))ᴴ) k k‖ ≤ ε) :
    ‖(gchainMinorTail L W H z i (s :: tau) (b :: a) * Eblk L W c
        * (gchainMinorTail L W H z i (s :: tau) (b :: a))ᴴ) i i
      - (Complex.normSq (Gsig H z s i i) : ℂ) * ∑ k, Svar L W i k
          * (gchainMinor L W H z i (s :: tau) (b :: a) * Eblk L W c
            * (gchainMinor L W H z i (s :: tau) (b :: a))ᴴ) k k‖
      ≤ ‖Gsig H z s i i‖ ^ 2 * ε := by
  rw [gchainMinorTail_quad_apply_self hH hinv hG s b h c, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hLDE) (sq_nonneg _)
  simp only [Matrix.mul_assoc]

/-- **The exact part of (A.19)**:
`∑_k S_{ik} |C_{kj}|² = ∑_c S^(B)_{[i] c} (C† E_c C)_{jj}`.  (The paper writes
`(C E_c C†)_{jj}`, i.e. the `j`-th *row*; the sum over `k` runs over the `j`-th *column*,
which is what `C† E_c C` records.  Both are diagonal entries of a `2n`-chain.) -/
theorem sum_Svar_normSq_eq (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (i j : ZMod L × Fin W) :
    ∑ k, Svar L W i k * (Complex.normSq (C k j) : ℂ)
      = ∑ c, SB L i.1 c * (Cᴴ * Eblk L W c * C) j j := by
  have hq : ∀ c, (Cᴴ * Eblk L W c * C) j j
      = ∑ k, (if k.1 = c then (W : ℂ)⁻¹ * (Complex.normSq (C k j) : ℂ) else 0) := by
    intro c
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Eblk, mul_diagonal, conjTranspose_apply, Complex.star_def]
    split_ifs
    · rw [← Complex.mul_conj]; ring
    · ring
  simp only [hq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  show SB L i.1 k.1 * (W : ℂ)⁻¹ * _ = _
  ring

/-- **(A.18) + (A.19) + [39, Lemma 3.3] ⟹ (A.20)**, deterministically: whatever
large-deviation bound `|(H C^(ii))_{ij}|² ≤ K |∑_k S_{ik}|C^(ii)_{kj}|²|` is fed in (the
paper's use of [39, Lemma 3.3], here an explicit hypothesis), the entry `C^(i)_{ij}` obeys the
same bound times `|G_{ii}|²`, with the `k`-sum rewritten as `2n`-chain diagonals. -/
theorem normSq_gchainMinorTail_le (hinv : ∀ s : Bool,
      IsUnit (H - (if s then z else (starRingEnd ℂ) z) • (1 : Matrix _ _ ℂ)).det)
    (hG : ∀ s, Gsig H z s i i ≠ 0) (s : Bool) (tau : List Bool) (a : List (ZMod L))
    {j : ZMod L × Fin W} (hj : j ≠ i) {K : ℝ}
    (hLDE : ‖(H * gchainMinor L W H z i (s :: tau) a) i j‖ ^ 2
      ≤ K * ‖∑ k, Svar L W i k
          * (Complex.normSq (gchainMinor L W H z i (s :: tau) a k j) : ℂ)‖) :
    ‖gchainMinorTail L W H z i (s :: tau) a i j‖ ^ 2
      ≤ ‖Gsig H z s i i‖ ^ 2 * K * ‖∑ c, SB L i.1 c
          * ((gchainMinor L W H z i (s :: tau) a)ᴴ * Eblk L W c
              * gchainMinor L W H z i (s :: tau) a) j j‖ := by
  rw [gchainMinorTail_apply_eq hinv hG s tau a hj, norm_mul, norm_neg, mul_pow,
    ← sum_Svar_normSq_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left hLDE (by positivity)

end A18

/-! ### Item (6): the diagonal split (A.15) -/

section A15

variable {L W : ℕ} [NeZero L]

/-- The weight `E_a(j) = W⁻¹ 1(j ∈ I_a)` of (2.5), as a real number. -/
noncomputable def eblkW (W : ℕ) (a : ZMod L) (j : ZMod L × Fin W) : ℝ :=
  if j.1 = a then (W : ℝ)⁻¹ else 0

omit [NeZero L] in
theorem Eblk_apply_self (a : ZMod L) (j : ZMod L × Fin W) :
    Eblk L W a j j = (eblkW W a j : ℂ) := by
  rw [Eblk, diagonal_apply_eq, eblkW]
  split_ifs <;> simp

omit [NeZero L] in
theorem eblkW_nonneg (a : ZMod L) (j : ZMod L × Fin W) : 0 ≤ eblkW W a j := by
  unfold eblkW
  split_ifs <;> positivity

omit [NeZero L] in
theorem eblkW_le (a : ZMod L) (j : ZMod L × Fin W) : eblkW W a j ≤ (W : ℝ)⁻¹ := by
  unfold eblkW
  split_ifs
  · exact le_rfl
  · positivity

/-- `∑_j E_a(j) = 1`: the block `I_a` has `W` sites. -/
theorem sum_eblkW [NeZero W] (a : ZMod L) : ∑ j : ZMod L × Fin W, eblkW W a j = 1 := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : ZMod L, (∑ _y : Fin W, eblkW W a (x, _y)) = if x = a then 1 else 0 := by
    intro x
    simp only [eblkW]
    split_ifs
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne W) : (W : ℝ) ≠ 0)
    · exact Finset.sum_const_zero
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `(C E_a C†)_{ii} = ∑_j E_a(j) |C_{ij}|²`: a nonnegative real. -/
theorem quad_Eblk_apply_self (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a : ZMod L)
    (i : ZMod L × Fin W) :
    (C * Eblk L W a * Cᴴ) i i = ((∑ j, eblkW W a j * Complex.normSq (C i j) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Eblk, mul_diagonal, conjTranspose_apply, ← Complex.mul_conj, Complex.star_def, eblkW]
  split_ifs <;> push_cast <;> ring

/-- **(A.15), the diagonal split**:
`(C E_a C†)_{ii} = W⁻¹ 1(i ∈ I_a) |C_{ii}|² + ∑_{j ≠ i} C_{ij} E_a(j) C†_{ji}`. -/
theorem quad_Eblk_apply_self_split (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (a : ZMod L) (i : ZMod L × Fin W) :
    (C * Eblk L W a * Cᴴ) i i
      = Eblk L W a i i * (Complex.normSq (C i i) : ℂ)
        + ∑ j ∈ Finset.univ.erase i, C i j * Eblk L W a j j * Cᴴ j i := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · rw [Eblk, mul_diagonal, conjTranspose_apply, diagonal_apply_eq, ← Complex.mul_conj,
      Complex.star_def]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Eblk, mul_diagonal, diagonal_apply_eq]

/-- `||c|² - |c'|²| ≤ 2|c||c - c'| + |c - c'|²`. -/
theorem abs_normSq_sub_normSq_le (c c' : ℂ) :
    |‖c‖ ^ 2 - ‖c'‖ ^ 2| ≤ 2 * ‖c‖ * ‖c - c'‖ + ‖c - c'‖ ^ 2 := by
  have h1 := abs_norm_sub_norm_le c c'
  have hc := norm_nonneg c
  have hc' := norm_nonneg c'
  have hd := norm_nonneg (c - c')
  rw [abs_le] at h1 ⊢
  obtain ⟨h1l, h1r⟩ := h1
  constructor <;> nlinarith

/-- Weighted Cauchy--Schwarz with total weight at most one:
`∑ e_j u_j ≤ (∑ e_j u_j²)^{1/2}`. -/
theorem sum_mul_le_sqrt_of_sum_le_one {ι : Type*} (s : Finset ι) {e u : ι → ℝ}
    (he : ∀ j ∈ s, 0 ≤ e j) (he1 : ∑ j ∈ s, e j ≤ 1) :
    ∑ j ∈ s, e j * u j ≤ √(∑ j ∈ s, e j * u j ^ 2) := by
  have hcs : (∑ j ∈ s, e j * u j) ^ 2 ≤ (∑ j ∈ s, e j) * ∑ j ∈ s, e j * u j ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s he
      (fun j hj => mul_nonneg (he j hj) (sq_nonneg _)) (fun j _ => by nlinarith [sq_nonneg (u j)])
  have hnn : 0 ≤ ∑ j ∈ s, e j * u j ^ 2 :=
    Finset.sum_nonneg fun j hj => mul_nonneg (he j hj) (sq_nonneg _)
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt (hcs.trans ?_))
  calc (∑ j ∈ s, e j) * ∑ j ∈ s, e j * u j ^ 2 ≤ 1 * ∑ j ∈ s, e j * u j ^ 2 :=
        mul_le_mul_of_nonneg_right he1 hnn
    _ = _ := one_mul _

/-- **The estimate following (A.15)**: if the `i`-th rows of `C` and `C'` differ by at most
`M` off the diagonal, then
`|(C E_a C†)_{ii} - (C' E_a C'†)_{ii}|
  ≤ W⁻¹ ||C_{ii}|² - |C'_{ii}|²| + M² + 2 (∑_{j≠i} E_a(j)|C_{ij}|²)^{1/2} M`.
The paper applies it with `C = C_n`, `C' = C^(i)_n` (for which `C'_{ii} = 0`,
`gchainMinorTail_col_self`) and `M` the bound (A.11). -/
theorem norm_quad_Eblk_sub_le [NeZero W] (C C' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (a : ZMod L) (i : ZMod L × Fin W) {M : ℝ} (hM : ∀ j, j ≠ i → ‖C i j - C' i j‖ ≤ M) :
    ‖(C * Eblk L W a * Cᴴ) i i - (C' * Eblk L W a * C'ᴴ) i i‖
      ≤ (W : ℝ)⁻¹ * |‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2| + M ^ 2
        + 2 * √(∑ j ∈ Finset.univ.erase i, eblkW W a j * ‖C i j‖ ^ 2) * M := by
  have hM0 : ∀ j, j ≠ i → 0 ≤ M := fun j hj => (norm_nonneg _).trans (hM j hj)
  rw [quad_Eblk_apply_self, quad_Eblk_apply_self, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  simp only [Complex.normSq_eq_norm_sq, ← mul_sub]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  set s := Finset.univ.erase i with hs
  have hdiag : |eblkW W a i * (‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2)|
      ≤ (W : ℝ)⁻¹ * |‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2| := by
    rw [abs_mul, abs_of_nonneg (eblkW_nonneg a i)]
    exact mul_le_mul_of_nonneg_right (eblkW_le a i) (abs_nonneg _)
  have hterm : ∀ j ∈ s, |eblkW W a j * (‖C i j‖ ^ 2 - ‖C' i j‖ ^ 2)|
      ≤ 2 * M * (eblkW W a j * ‖C i j‖) + M ^ 2 * eblkW W a j := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [abs_mul, abs_of_nonneg (eblkW_nonneg a j)]
    have h1 := abs_normSq_sub_normSq_le (C i j) (C' i j)
    have h2 : 2 * ‖C i j‖ * ‖C i j - C' i j‖ + ‖C i j - C' i j‖ ^ 2
        ≤ 2 * ‖C i j‖ * M + M ^ 2 := by
      have := hM j hji
      have := norm_nonneg (C i j - C' i j)
      have := norm_nonneg (C i j)
      nlinarith
    have he := eblkW_nonneg (W := W) a j
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) he]
  have hsum_e : ∑ j ∈ s, eblkW W a j ≤ 1 := by
    rw [← sum_eblkW (W := W) a]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => eblkW_nonneg a j)
  have hcs := sum_mul_le_sqrt_of_sum_le_one s (e := eblkW W a) (u := fun j => ‖C i j‖)
    (fun j _ => eblkW_nonneg a j) hsum_e
  by_cases hs0 : s = ∅
  · rw [hs0, Finset.sum_empty, add_zero, Finset.sum_empty, Real.sqrt_zero]
    nlinarith [sq_nonneg M]
  · obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    have hM0' : 0 ≤ M := hM0 j0 (Finset.ne_of_mem_erase hj0)
    calc |eblkW W a i * (‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2)
          + ∑ j ∈ s, eblkW W a j * (‖C i j‖ ^ 2 - ‖C' i j‖ ^ 2)|
        ≤ |eblkW W a i * (‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2)|
          + ∑ j ∈ s, |eblkW W a j * (‖C i j‖ ^ 2 - ‖C' i j‖ ^ 2)| :=
          (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ (W : ℝ)⁻¹ * |‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2|
          + ∑ j ∈ s, (2 * M * (eblkW W a j * ‖C i j‖) + M ^ 2 * eblkW W a j) :=
          add_le_add hdiag (Finset.sum_le_sum hterm)
      _ = (W : ℝ)⁻¹ * |‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2|
          + 2 * M * ∑ j ∈ s, eblkW W a j * ‖C i j‖ + M ^ 2 * ∑ j ∈ s, eblkW W a j := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
      _ ≤ (W : ℝ)⁻¹ * |‖C i i‖ ^ 2 - ‖C' i i‖ ^ 2|
          + 2 * M * √(∑ j ∈ s, eblkW W a j * ‖C i j‖ ^ 2) + M ^ 2 * 1 := by
          gcongr
      _ = _ := by ring

end A15

/-! ### Item (5): the exact telescoping identities behind (A.21)--(A.26) -/

section Telescope

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W}

/-- Pushing a left factor through a column expansion. -/
theorem mul_apply_of_expand {n ι : Type*} [Fintype n] (A B C : Matrix n n ℂ) (s : Finset ι)
    (P : ι → Matrix n n ℂ) (q : ι → ℂ) (i x y : n)
    (hB : ∀ l, B l y = C l y - ∑ k ∈ s, P k l i * q k) :
    (A * B) x y = (A * C) x y - ∑ k ∈ s, (A * P k) x i * q k := by
  simp only [Matrix.mul_apply, hB, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

omit [NeZero W] in
/-- **(4.9) for chains**: `C^(ii) = C^(i) - G_1 e_i e_iᵀ C^(i) / (G_1)_{ii}`, entrywise
`(C^(ii))_{xy} = (C^(i))_{xy} - (G_1)_{xi} (C^(i))_{iy} / (G_1)_{ii}`.  No hypothesis. -/
theorem gchainMinor_apply_eq_tail (s : Bool) (tau : List Bool) (a : List (ZMod L))
    (x y : ZMod L × Fin W) :
    gchainMinor L W H z i (s :: tau) a x y
      = gchainMinorTail L W H z i (s :: tau) a x y
        - Gsig H z s x i * gchainMinorTail L W H z i (s :: tau) a i y / Gsig H z s i i := by
  cases a with
  | nil => rfl
  | cons b a =>
    rw [gchainMinor_cons, gchainMinorTail_cons, Matrix.mul_assoc, minorExt_mul_apply,
      Matrix.mul_assoc]

/-- `C^(i)_n - C_n = G_1 E_{a_1} (C^(ii)_{n-1} - C_{n-1})`, the second half of the
recursion. -/
theorem gchainMinorTail_sub_gchain (s : Bool) (b : ZMod L) (tau : List Bool)
    (a : List (ZMod L)) :
    gchainMinorTail L W H z i (s :: tau) (b :: a) - gchain L W H z (s :: tau) (b :: a)
      = Gsig H z s * Eblk L W b * (gchainMinor L W H z i tau a - gchain L W H z tau a) := by
  rw [gchainMinorTail_cons, gchain_cons, Matrix.mul_sub]

/-- **The exact telescoping identity for `C^(ii)`** (the identity behind (A.25), (A.26)):
for a well-formed chain of length `n`,
`(C^(ii)_n)_{xy} = (C_n)_{xy} - ∑_{k=1}^{n} (C_{[1,k]})_{xi} (C^(i)_{[k,n]})_{iy} / (G_k)_{ii}`,
where `C_{[1,k]} = G_1 E_{a_1} ⋯ G_k` and `C^(i)_{[k,n]} = G_k E_{a_k} G^(i)_{k+1} ⋯ G^(i)_n`.
Positions are `0`-based in the formula (`k ∈ range n`). -/
theorem gchainMinor_apply_expand {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) (x y : ZMod L × Fin W) :
    gchainMinor L W H z i tau a x y
      = gchain L W H z tau a x y
        - ∑ k ∈ Finset.range tau.length,
            gchain L W H z (tau.take (k + 1)) (a.take k) x i
              * (gchainMinorTail L W H z i (tau.drop k) (a.drop k) i y
                  / Gsig H z (tau.getD k false) i i) := by
  induction tau generalizing a x with
  | nil => simp at h
  | cons s tau ih =>
    cases a with
    | nil =>
      have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst htau
      rw [show ([s] : List Bool).length = 1 from rfl, Finset.sum_range_one]
      simp only [gchainMinor_single, minorExt_apply, List.take_succ_cons, List.take_zero,
        List.drop_zero, List.getD_cons_zero, gchain_single, gchainMinorTail_single]
      ring
    | cons b a =>
      have h' : tau.length = a.length + 1 := by simpa using h
      rw [gchainMinor_apply_eq_tail, gchainMinorTail_cons,
        mul_apply_of_expand _ _ _ _ _ _ i x y (fun l => ih h' l),
        List.length_cons, Finset.sum_range_succ', gchain_cons]
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        List.getD_cons_succ, List.getD_cons_zero, gchain_cons, gchain_single,
        gchainMinorTail_cons]
      ring

/-- **The exact telescoping identity for `C^(i)`** (the identity behind (A.21)--(A.24)):
for a well-formed chain of length `n ≥ 2`,
`(C^(i)_n)_{xy} = (C_n)_{xy} - ∑_{k=2}^{n} (C_{[1,k]})_{xi} (C^(i)_{[k,n]})_{iy} / (G_k)_{ii}`.
Iterating it (the `C^(i)_{[k,n]}` on the right are shorter chains of the same kind) produces
the paper's sum over `(n_1, …, n_k; ℓ)` with `ℓ + ∑ n_i = n + k`. -/
theorem gchainMinorTail_apply_expand (s : Bool) (b : ZMod L) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (x y : ZMod L × Fin W) :
    gchainMinorTail L W H z i (s :: tau) (b :: a) x y
      = gchain L W H z (s :: tau) (b :: a) x y
        - ∑ k ∈ Finset.range tau.length,
            gchain L W H z ((s :: tau).take (k + 2)) ((b :: a).take (k + 1)) x i
              * (gchainMinorTail L W H z i ((s :: tau).drop (k + 1)) ((b :: a).drop (k + 1)) i y
                  / Gsig H z ((s :: tau).getD (k + 1) false) i i) := by
  rw [gchainMinorTail_cons, mul_apply_of_expand _ _ _ _ _ _ i x y
    (fun l => gchainMinor_apply_expand h l y), gchain_cons]
  simp only [List.take_succ_cons, List.drop_succ_cons, List.getD_cons_succ, gchain_cons]

/-- **(A.21)**: `(C^(i)_2)_{xy} - (C_2)_{xy} = -(G_1 E_{a_1} G_2)_{xi} (G_2)_{iy} / (G_2)_{ii}`
(the paper states it at `x = i`, `y = j`). -/
theorem gchainMinorTail_two (s₁ s₂ : Bool) (b : ZMod L) (x y : ZMod L × Fin W) :
    gchainMinorTail L W H z i [s₁, s₂] [b] x y - gchain L W H z [s₁, s₂] [b] x y
      = -(gchain L W H z [s₁, s₂] [b] x i * Gsig H z s₂ i y / Gsig H z s₂ i i) := by
  rw [gchainMinorTail_apply_expand s₁ b (tau := [s₂]) (a := []) rfl]
  simp only [List.length_cons, List.length_nil, Finset.sum_range_one, List.take_succ_cons,
    List.take_zero, List.drop_succ_cons, List.drop_zero, List.getD_cons_succ,
    List.getD_cons_zero, gchainMinorTail_single, zero_add]
  ring

/-- **(A.22)**: the exact expansion for `n = 3`,
`(C^(i)_3)_{xy} - (C_3)_{xy} = -(G_1EG_2)_{xi}(G_2EG_3)_{iy}/(G_2)_{ii}
  - (G_1EG_2EG_3)_{xi}(G_3)_{iy}/(G_3)_{ii}
  + (G_1EG_2)_{xi}(G_2EG_3)_{ii}(G_3)_{iy}/((G_2)_{ii}(G_3)_{ii})`. -/
theorem gchainMinorTail_three (s₁ s₂ s₃ : Bool) (b₁ b₂ : ZMod L) (x y : ZMod L × Fin W) :
    gchainMinorTail L W H z i [s₁, s₂, s₃] [b₁, b₂] x y - gchain L W H z [s₁, s₂, s₃] [b₁, b₂] x y
      = -(gchain L W H z [s₁, s₂] [b₁] x i * gchain L W H z [s₂, s₃] [b₂] i y
            / Gsig H z s₂ i i)
        - gchain L W H z [s₁, s₂, s₃] [b₁, b₂] x i * Gsig H z s₃ i y / Gsig H z s₃ i i
        + gchain L W H z [s₁, s₂] [b₁] x i * gchain L W H z [s₂, s₃] [b₂] i i
            * Gsig H z s₃ i y / (Gsig H z s₂ i i * Gsig H z s₃ i i) := by
  rw [gchainMinorTail_apply_expand s₁ b₁ (tau := [s₂, s₃]) (a := [b₂]) rfl]
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.getD_cons_succ, List.getD_cons_zero, gchainMinorTail_single, zero_add]
  have h2 := gchainMinorTail_two (H := H) (z := z) (i := i) s₂ s₃ b₂ i y
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  ring

end Telescope

/-! ### Item (2): the normalized ratios `Ξ^(d)_n`, `Ξ^(o)_n` of (A.5), (A.6) -/

section Xi

variable (L W : ℕ) [NeZero L]

/-- **(A.5)** `Ξ^(d)_n = max_{σ,a} max_i |(C_{σ,a})_{ii}| Φ^{n-1}`, with `Φ` standing for
`W ℓ_t η_t`.  The maximum runs over charges `σ ∈ {±}^n` and labels `a ∈ Z_L^{n-1}`. -/
noncomputable def XiDiag (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (Φ : ℝ)
    (n : ℕ) : ℝ :=
  ⨆ q : List.Vector Bool n × List.Vector (ZMod L) (n - 1) × (ZMod L × Fin W),
    ‖gchain L W H z q.1.toList q.2.1.toList q.2.2 q.2.2‖ * Φ ^ (n - 1)

/-- **(A.6)** `Ξ^(o)_n = max_{σ,a} max_{i≠j} |(C_{σ,a})_{ij}| Φ^{n-1/2}`. -/
noncomputable def XiOff (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (Φ : ℝ)
    (n : ℕ) : ℝ :=
  ⨆ q : List.Vector Bool n × List.Vector (ZMod L) (n - 1)
      × {p : (ZMod L × Fin W) × (ZMod L × Fin W) // p.1 ≠ p.2},
    ‖gchain L W H z q.1.toList q.2.1.toList q.2.2.1.1 q.2.2.1.2‖ * (Φ ^ (n - 1) * √Φ)

variable {L W} {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {Φ : ℝ}

/-- Every diagonal entry of a well-formed `n`-chain is controlled by `Ξ^(d)_n`. -/
theorem norm_gchain_diag_le_XiDiag {n : ℕ} {tau : List Bool} {a : List (ZMod L)}
    (hn : tau.length = n) (h : tau.length = a.length + 1) (x : ZMod L × Fin W) :
    ‖gchain L W H z tau a x x‖ * Φ ^ (n - 1) ≤ XiDiag L W H z Φ n := by
  subst hn
  exact le_ciSup (f := fun q : List.Vector Bool tau.length
      × List.Vector (ZMod L) (tau.length - 1) × (ZMod L × Fin W) =>
      ‖gchain L W H z q.1.toList q.2.1.toList q.2.2 q.2.2‖ * Φ ^ (tau.length - 1))
    (Set.finite_range _).bddAbove ⟨⟨tau, rfl⟩, ⟨a, by omega⟩, x⟩

/-- Every off-diagonal entry of a well-formed `n`-chain is controlled by `Ξ^(o)_n`. -/
theorem norm_gchain_off_le_XiOff {n : ℕ} {tau : List Bool} {a : List (ZMod L)}
    (hn : tau.length = n) (h : tau.length = a.length + 1) {x y : ZMod L × Fin W} (hxy : x ≠ y) :
    ‖gchain L W H z tau a x y‖ * (Φ ^ (n - 1) * √Φ) ≤ XiOff L W H z Φ n := by
  subst hn
  exact le_ciSup (f := fun q : List.Vector Bool tau.length
      × List.Vector (ZMod L) (tau.length - 1)
      × {p : (ZMod L × Fin W) × (ZMod L × Fin W) // p.1 ≠ p.2} =>
      ‖gchain L W H z q.1.toList q.2.1.toList q.2.2.1.1 q.2.2.1.2‖ * (Φ ^ (tau.length - 1) * √Φ))
    (Set.finite_range _).bddAbove ⟨⟨tau, rfl⟩, ⟨a, by omega⟩, ⟨(x, y), hxy⟩⟩

theorem XiDiag_nonneg (hΦ : 0 ≤ Φ) (n : ℕ) : 0 ≤ XiDiag L W H z Φ n :=
  Real.iSup_nonneg fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg hΦ _)

theorem XiOff_nonneg (hΦ : 0 ≤ Φ) (n : ℕ) : 0 ≤ XiOff L W H z Φ n :=
  Real.iSup_nonneg fun _ =>
    mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg hΦ _) (Real.sqrt_nonneg _))

/-- `Ξ^(d)_n ≤ B` as soon as every diagonal entry of every well-formed `n`-chain is. -/
theorem XiDiag_le {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (tau : List Bool) (a : List (ZMod L)), tau.length = n → tau.length = a.length + 1 →
      ∀ x, ‖gchain L W H z tau a x x‖ * Φ ^ (n - 1) ≤ B) (hn : 1 ≤ n) :
    XiDiag L W H z Φ n ≤ B :=
  Real.iSup_le (fun q => h q.1.toList q.2.1.toList q.1.toList_length
    (by rw [q.1.toList_length, q.2.1.toList_length]; omega) q.2.2) hB

/-- `Ξ^(o)_n ≤ B` as soon as every off-diagonal entry of every well-formed `n`-chain is. -/
theorem XiOff_le {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (tau : List Bool) (a : List (ZMod L)), tau.length = n → tau.length = a.length + 1 →
      ∀ x y, x ≠ y → ‖gchain L W H z tau a x y‖ * (Φ ^ (n - 1) * √Φ) ≤ B) (hn : 1 ≤ n) :
    XiOff L W H z Φ n ≤ B :=
  Real.iSup_le (fun q => h q.1.toList q.2.1.toList q.1.toList_length
    (by rw [q.1.toList_length, q.2.1.toList_length]; omega) _ _ q.2.2.2) hB

end Xi

/-! ### (A.24) ⟹ (A.11): the perturbation bound, deterministically -/

section A11

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W} {Φ : ℝ}

/-- The arithmetic behind (A.24):
`∑_{k<N} D · O(1+KD)^{N-1-k} · K = O((1+KD)^N - 1)`. -/
theorem sum_renewal_geom (K D O : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, D * (O * (1 + K * D) ^ (N - 1 - k) * K)
      = O * ((1 + K * D) ^ N - 1) := by
  have h1 : ∑ k ∈ Finset.range N, (1 + K * D) ^ (N - 1 - k)
      = ∑ k ∈ Finset.range N, (1 + K * D) ^ k :=
    Finset.sum_range_reflect (fun k => (1 + K * D) ^ k) N
  have h2 := geom_sum_mul (1 + K * D) N
  calc ∑ k ∈ Finset.range N, D * (O * (1 + K * D) ^ (N - 1 - k) * K)
      = K * D * O * ∑ k ∈ Finset.range N, (1 + K * D) ^ (N - 1 - k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = O * ((∑ k ∈ Finset.range N, (1 + K * D) ^ k) * (1 + K * D - 1)) := by
        rw [h1]; ring
    _ = _ := by rw [h2]

/-- **One step of (A.24)**: the difference `C^(i)_n - C_n` at `(i, j)`, bounded through the
telescoping identity by diagonal chain entries (`Ξ^(d)_{n_1} ≤ D`), the inverse diagonal
resolvent entries (`|1/G_{ii}| ≤ K`, the paper's `1/G_{ii} = O(1)`) and the shorter
`C^(i)`-chains (inductive input `hIH`). -/
theorem norm_gchainMinorTail_sub_le_of {K D O : ℝ} (hΦ : 0 < Φ) (hD : 0 ≤ D)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (s : Bool) (b : ZMod L)
    {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1)
    (hXd : ∀ p, 2 ≤ p → p ≤ tau.length + 1 → XiDiag L W H z Φ p ≤ D)
    (hIH : ∀ (tau' : List Bool) (a' : List (ZMod L)), tau'.length = a'.length + 1 →
      tau'.length ≤ tau.length →
      ‖gchainMinorTail L W H z i tau' a' i j‖ * (Φ ^ (tau'.length - 1) * √Φ)
        ≤ O * (1 + K * D) ^ (tau'.length - 1)) :
    ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j - gchain L W H z (s :: tau) (b :: a) i j‖
        * (Φ ^ tau.length * √Φ)
      ≤ O * ((1 + K * D) ^ tau.length - 1) := by
  rw [gchainMinorTail_apply_expand s b h, sub_sub_cancel_left, norm_neg]
  set N := tau.length with hN
  have hsq : 0 ≤ √Φ := Real.sqrt_nonneg Φ
  have hterm : ∀ k ∈ Finset.range N,
      ‖gchain L W H z ((s :: tau).take (k + 2)) ((b :: a).take (k + 1)) i i
          * (gchainMinorTail L W H z i ((s :: tau).drop (k + 1)) ((b :: a).drop (k + 1)) i j
            / Gsig H z ((s :: tau).getD (k + 1) false) i i)‖ * (Φ ^ N * √Φ)
        ≤ D * (O * (1 + K * D) ^ (N - 1 - k) * K) := by
    intro k hk
    rw [Finset.mem_range] at hk
    set P := gchain L W H z ((s :: tau).take (k + 2)) ((b :: a).take (k + 1)) i i
    set S := gchainMinorTail L W H z i ((s :: tau).drop (k + 1)) ((b :: a).drop (k + 1)) i j
    set g := Gsig H z ((s :: tau).getD (k + 1) false) i i
    have hlenP : ((s :: tau).take (k + 2)).length = k + 2 := by
      simp only [List.length_take, List.length_cons]; omega
    have hwfP : ((s :: tau).take (k + 2)).length = ((b :: a).take (k + 1)).length + 1 := by
      simp only [List.length_take, List.length_cons]; omega
    have hlenS : ((s :: tau).drop (k + 1)).length = N - k := by
      simp only [List.length_drop, List.length_cons]; omega
    have hwfS : ((s :: tau).drop (k + 1)).length = ((b :: a).drop (k + 1)).length + 1 := by
      simp only [List.length_drop, List.length_cons]; omega
    have hP : ‖P‖ * Φ ^ (k + 1) ≤ D := by
      have := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) hlenP hwfP i
      exact this.trans (hXd (k + 2) (by omega) (by omega))
    have hS : ‖S‖ * (Φ ^ (N - 1 - k) * √Φ) ≤ O * (1 + K * D) ^ (N - 1 - k) := by
      have := hIH _ _ hwfS (by omega)
      rwa [hlenS, show N - k - 1 = N - 1 - k by omega] at this
    have hg : ‖g⁻¹‖ ≤ K := hGinv _
    have hpow : Φ ^ N = Φ ^ (k + 1) * Φ ^ (N - 1 - k) := by
      rw [← pow_add]; congr 1; omega
    rw [div_eq_mul_inv, norm_mul, norm_mul, hpow]
    have e : ‖P‖ * (‖S‖ * ‖g⁻¹‖) * (Φ ^ (k + 1) * Φ ^ (N - 1 - k) * √Φ)
        = (‖P‖ * Φ ^ (k + 1)) * ((‖S‖ * (Φ ^ (N - 1 - k) * √Φ)) * ‖g⁻¹‖) := by ring
    rw [e]
    have hS0 : 0 ≤ ‖S‖ * (Φ ^ (N - 1 - k) * √Φ) := by positivity
    exact mul_le_mul hP (mul_le_mul hS hg (norm_nonneg _)
      (le_trans hS0 hS)) (by positivity) hD
  calc ‖∑ k ∈ Finset.range N,
          gchain L W H z ((s :: tau).take (k + 2)) ((b :: a).take (k + 1)) i i
            * (gchainMinorTail L W H z i ((s :: tau).drop (k + 1)) ((b :: a).drop (k + 1)) i j
              / Gsig H z ((s :: tau).getD (k + 1) false) i i)‖ * (Φ ^ N * √Φ)
      ≤ (∑ k ∈ Finset.range N,
          ‖gchain L W H z ((s :: tau).take (k + 2)) ((b :: a).take (k + 1)) i i
            * (gchainMinorTail L W H z i ((s :: tau).drop (k + 1)) ((b :: a).drop (k + 1)) i j
              / Gsig H z ((s :: tau).getD (k + 1) false) i i)‖) * (Φ ^ N * √Φ) :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ ≤ ∑ k ∈ Finset.range N, D * (O * (1 + K * D) ^ (N - 1 - k) * K) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum hterm
    _ = O * ((1 + K * D) ^ N - 1) := sum_renewal_geom K D O N

/-- The shorter `C^(i)`-chains in (A.24) are bounded by induction on the length:
`|(C^(i)_m)_{ij}| Φ^{m-1/2} ≤ O (1 + KD)^{m-1}` for `m ≤ n`, if `Ξ^(d)_p ≤ D` (`2 ≤ p ≤ n`),
`Ξ^(o)_ℓ ≤ O` (`ℓ ≤ n`) and `|1/G_{ii}| ≤ K`. -/
theorem norm_gchainMinorTail_le {K D O : ℝ} (hΦ : 0 < Φ) (hD : 0 ≤ D)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j) (n : ℕ)
    (hXd : ∀ p, 2 ≤ p → p ≤ n → XiDiag L W H z Φ p ≤ D)
    (hXo : ∀ l, 1 ≤ l → l ≤ n → XiOff L W H z Φ l ≤ O) :
    ∀ (m : ℕ) (tau : List Bool) (a : List (ZMod L)), tau.length = m →
      tau.length = a.length + 1 → m ≤ n →
      ‖gchainMinorTail L W H z i tau a i j‖ * (Φ ^ (m - 1) * √Φ) ≤ O * (1 + K * D) ^ (m - 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro tau a hm hwf hmn
    subst hm
    cases tau with
    | nil => simp at hwf
    | cons s tau =>
      cases a with
      | nil =>
        have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using hwf)
        subst htau
        have h1 : 1 ≤ n := by simpa using hmn
        have := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ) (n := 1)
          (tau := [s]) (a := []) rfl rfl hj
        rw [gchain_single] at this
        rw [gchainMinorTail_single]
        exact (this.trans (hXo 1 le_rfl h1)).trans_eq (by simp)
      | cons b a =>
        have hwf' : tau.length = a.length + 1 := by simpa using hwf
        rw [List.length_cons] at hmn ihm ⊢
        rw [Nat.add_sub_cancel]
        have hC := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ)
          (tau := s :: tau) (a := b :: a) rfl hwf hj
        rw [List.length_cons, Nat.add_sub_cancel] at hC
        have hD' := norm_gchainMinorTail_sub_le_of (O := O) hΦ hD hGinv s b hwf'
          (fun p hp2 hpn => hXd p hp2 (by omega))
          (fun tau' a' hwf'' hlen => ihm tau'.length (by omega) tau' a' rfl hwf'' (by omega))
        have hsplit : ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j‖
            ≤ ‖gchain L W H z (s :: tau) (b :: a) i j‖
              + ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j
                  - gchain L W H z (s :: tau) (b :: a) i j‖ := by
          have := norm_add_le (gchain L W H z (s :: tau) (b :: a) i j)
            (gchainMinorTail L W H z i (s :: tau) (b :: a) i j
              - gchain L W H z (s :: tau) (b :: a) i j)
          rwa [add_sub_cancel] at this
        have hpos : 0 ≤ Φ ^ tau.length * √Φ := by positivity
        calc ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ)
            ≤ ‖gchain L W H z (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ)
              + ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j
                  - gchain L W H z (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ) := by
              rw [← add_mul]; exact mul_le_mul_of_nonneg_right hsplit hpos
          _ ≤ O + O * ((1 + K * D) ^ tau.length - 1) :=
              add_le_add (hC.trans (hXo _ (by omega) hmn)) hD'
          _ = O * (1 + K * D) ^ tau.length := by ring

/-- **(A.11), deterministic form.**  For a well-formed `n`-chain, `n ≥ 2`, and `i ≠ j`,
`|(C_n)_{ij} - (C^(i)_n)_{ij}| Φ^{n-1/2} ≤ O ((1 + KD)^{n-1} - 1)`,
provided `|1/G_{ii}| ≤ K`, `Ξ^(d)_p ≤ D` for `2 ≤ p ≤ n` and `Ξ^(o)_ℓ ≤ O` for
`ℓ ≤ n - 1` -- exactly the inputs the paper takes from the induction hypothesis (A.7) after
(A.24).  With `Φ = Wℓη` this is `(C_n)_{ij} - (C^(i)_n)_{ij} = O((Wℓη)^{-n+1/2})`. -/
theorem norm_gchainMinorTail_sub_gchain_le {K D O : ℝ} (hΦ : 0 < Φ) (hD : 0 ≤ D) (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j)
    (s : Bool) (b : ZMod L) {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1)
    (hXd : ∀ p, 2 ≤ p → p ≤ tau.length + 1 → XiDiag L W H z Φ p ≤ D)
    (hXo : ∀ l, 1 ≤ l → l ≤ tau.length → XiOff L W H z Φ l ≤ O) :
    ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j - gchain L W H z (s :: tau) (b :: a) i j‖
        * (Φ ^ tau.length * √Φ)
      ≤ O * ((1 + K * D) ^ tau.length - 1) :=
  norm_gchainMinorTail_sub_le_of hΦ hD hGinv s b h hXd
    (fun tau' a' hwf hlen => norm_gchainMinorTail_le hΦ hD hGinv hj tau.length
      (fun p hp2 hpn => hXd p hp2 (by omega)) hXo tau'.length tau' a' rfl hwf hlen)

end A11

/-! ### Item (7): the Cauchy--Schwarz ladder of pp. 85, 88 and the trichotomy (A.27) -/

section Ladder

variable {L W : ℕ} [NeZero L]

omit [NeZero L] in
theorem Eblk_eq_diagonal (b : ZMod L) :
    Eblk L W b = diagonal fun k => (eblkW W b k : ℂ) := by
  rw [Eblk]
  congr 1
  funext k
  unfold eblkW
  split_ifs <;> simp

/-- `|(C E_a C†)_{xx}| = ∑_k E_a(k) |C_{xk}|²`. -/
theorem norm_quad_Eblk_apply_self (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b : ZMod L) (x : ZMod L × Fin W) :
    ‖(C * Eblk L W b * Cᴴ) x x‖ = ∑ k, eblkW W b k * ‖C x k‖ ^ 2 := by
  rw [quad_Eblk_apply_self, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · simp only [Complex.normSq_eq_norm_sq]
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (eblkW_nonneg b k) (Complex.normSq_nonneg _)

/-- `|(C† E_a C)_{yy}| = ∑_k E_a(k) |C_{ky}|²`. -/
theorem norm_quad_Eblk_apply_self' (C : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b : ZMod L) (y : ZMod L × Fin W) :
    ‖(Cᴴ * Eblk L W b * C) y y‖ = ∑ k, eblkW W b k * ‖C k y‖ ^ 2 := by
  have := norm_quad_Eblk_apply_self Cᴴ b y
  rw [conjTranspose_conjTranspose] at this
  rw [this]
  simp only [conjTranspose_apply, norm_star]

/-- **Cauchy--Schwarz for a chain split at one `E`**:
`|(A E_b B)_{xy}|² ≤ |(A E_b A†)_{xx}| |(B† E_b B)_{yy}|`.  Both factors on the right are
diagonal entries of chains of twice the length of `A`, `B`. -/
theorem normSq_mul_Eblk_mul_le (A B : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b : ZMod L) (x y : ZMod L × Fin W) :
    ‖(A * Eblk L W b * B) x y‖ ^ 2
      ≤ ‖(A * Eblk L W b * Aᴴ) x x‖ * ‖(Bᴴ * Eblk L W b * B) y y‖ := by
  rw [norm_quad_Eblk_apply_self, norm_quad_Eblk_apply_self']
  have hexp : (A * Eblk L W b * B) x y = ∑ k, A x k * (eblkW W b k : ℂ) * B k y := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Eblk_eq_diagonal, mul_diagonal]
  have hle : ‖(A * Eblk L W b * B) x y‖ ≤ ∑ k, eblkW W b k * (‖A x k‖ * ‖B k y‖) := by
    rw [hexp]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (eblkW_nonneg b k)]
    ring
  have hcs : (∑ k, eblkW W b k * (‖A x k‖ * ‖B k y‖)) ^ 2
      ≤ (∑ k, eblkW W b k * ‖A x k‖ ^ 2) * ∑ k, eblkW W b k * ‖B k y‖ ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun k _ => mul_nonneg (eblkW_nonneg b k) (sq_nonneg _))
      (fun k _ => mul_nonneg (eblkW_nonneg b k) (sq_nonneg _))
      (fun k _ => le_of_eq (by ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hcs

omit [NeZero L] in
/-- Splitting a well-formed chain of length `p + q` into a `p`-chain and a `q`-chain. -/
theorem exists_chain_split {tau : List Bool} {a : List (ZMod L)} {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hlen : tau.length = p + q) (h : tau.length = a.length + 1) :
    ∃ (tau₁ tau₂ : List Bool) (a₁ a₂ : List (ZMod L)) (b : ZMod L),
      tau = tau₁ ++ tau₂ ∧ a = a₁ ++ b :: a₂ ∧ tau₁.length = p ∧ tau₂.length = q ∧
      tau₁.length = a₁.length + 1 ∧ tau₂.length = a₂.length + 1 := by
  have hpa : p - 1 < a.length := by omega
  refine ⟨tau.take p, tau.drop p, a.take (p - 1), a.drop p, a[p - 1], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (List.take_append_drop p tau).symm
  · have e := List.drop_eq_getElem_cons hpa
    rw [show p - 1 + 1 = p by omega] at e
    rw [← e, List.take_append_drop]
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

variable [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {Φ : ℝ}

/-- The `2q`-chain `C_{τ,a}† E_b C_{τ,a}`. -/
theorem conjTranspose_gchain_mul_Eblk_mul (hH : H.IsHermitian) {tau : List Bool}
    {a : List (ZMod L)} (h : tau.length = a.length + 1) (b : ZMod L) :
    (gchain L W H z tau a)ᴴ * Eblk L W b * gchain L W H z tau a
      = gchain L W H z ((tau.map (!·)).reverse ++ tau) (a.reverse ++ b :: a) := by
  have hlen : (tau.map (!·)).reverse.length = a.reverse.length + 1 := by simpa using h
  rw [gchain_conjTranspose hH h, gchain_append_Eblk hlen]

/-- **The chain Cauchy--Schwarz inequality**: an entry of a `(p+q)`-chain is bounded by
diagonal entries of a `2p`- and a `2q`-chain. -/
theorem normSq_gchain_append_le (hH : H.IsHermitian) {tau₁ tau₂ : List Bool}
    {a₁ a₂ : List (ZMod L)} (h₁ : tau₁.length = a₁.length + 1)
    (h₂ : tau₂.length = a₂.length + 1) (b : ZMod L) (x y : ZMod L × Fin W) :
    ‖gchain L W H z (tau₁ ++ tau₂) (a₁ ++ b :: a₂) x y‖ ^ 2
      ≤ ‖gchain L W H z (tau₁ ++ (tau₁.map (!·)).reverse) (a₁ ++ b :: a₁.reverse) x x‖
        * ‖gchain L W H z ((tau₂.map (!·)).reverse ++ tau₂) (a₂.reverse ++ b :: a₂) y y‖ := by
  rw [gchain_append_Eblk h₁, ← gchain_mul_Eblk_mul_conjTranspose hH h₁,
    ← conjTranspose_gchain_mul_Eblk_mul hH h₂]
  exact normSq_mul_Eblk_mul_le _ _ b x y

omit [NeZero L] [NeZero W] in
/-- The doubled chain is well formed and has length `2p`. -/
theorem length_double {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1)
    (b : ZMod L) :
    (tau ++ (tau.map (!·)).reverse).length = 2 * tau.length ∧
      (tau ++ (tau.map (!·)).reverse).length = (a ++ b :: a.reverse).length + 1 ∧
      ((tau.map (!·)).reverse ++ tau).length = 2 * tau.length ∧
      ((tau.map (!·)).reverse ++ tau).length = (a.reverse ++ b :: a).length + 1 := by
  simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons]
  omega

/-- **The Cauchy--Schwarz ladder, diagonal version** (p. 88):
`Ξ^(d)_{p+q} ≤ (Ξ^(d)_{2p} Ξ^(d)_{2q})^{1/2}`.  With `p = n - 1`, `q = n` this is the paper's
`Ξ^(d)_{2n-1} ≺ (Ξ^(d)_{2n-2} Ξ^(d)_{2n})^{1/2}`. -/
theorem XiDiag_add_le (hH : H.IsHermitian) (hΦ : 0 ≤ Φ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    XiDiag L W H z Φ (p + q)
      ≤ √(XiDiag L W H z Φ (2 * p) * XiDiag L W H z Φ (2 * q)) := by
  refine XiDiag_le (Real.sqrt_nonneg _) (fun tau a hlen h x => ?_) (by omega)
  obtain ⟨tau₁, tau₂, a₁, a₂, b, rfl, rfl, hl₁, hl₂, h₁, h₂⟩ :=
    exists_chain_split hp hq hlen h
  obtain ⟨d₁, w₁, -, -⟩ := length_double h₁ b
  obtain ⟨-, -, d₂, w₂⟩ := length_double h₂ b
  have X₁ := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (d₁.trans (by rw [hl₁])) w₁ x
  have X₂ := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (d₂.trans (by rw [hl₂])) w₂ x
  have hcs := normSq_gchain_append_le hH h₁ h₂ b x x (H := H) (z := z)
  rw [Real.le_sqrt (by positivity) (le_trans (by positivity) (mul_le_mul X₁ X₂ (by positivity)
    (le_trans (by positivity) X₁)))]
  have hpow : (Φ ^ (p + q - 1)) ^ 2 = Φ ^ (2 * p - 1) * Φ ^ (2 * q - 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  calc (‖gchain L W H z (tau₁ ++ tau₂) (a₁ ++ b :: a₂) x x‖ * Φ ^ (p + q - 1)) ^ 2
      = ‖gchain L W H z (tau₁ ++ tau₂) (a₁ ++ b :: a₂) x x‖ ^ 2 * (Φ ^ (p + q - 1)) ^ 2 := by
        ring
    _ ≤ (‖gchain L W H z (tau₁ ++ (tau₁.map (!·)).reverse) (a₁ ++ b :: a₁.reverse) x x‖
          * ‖gchain L W H z ((tau₂.map (!·)).reverse ++ tau₂) (a₂.reverse ++ b :: a₂) x x‖)
          * (Φ ^ (2 * p - 1) * Φ ^ (2 * q - 1)) := by
        rw [hpow]; exact mul_le_mul_of_nonneg_right hcs (by positivity)
    _ = (‖gchain L W H z (tau₁ ++ (tau₁.map (!·)).reverse) (a₁ ++ b :: a₁.reverse) x x‖
          * Φ ^ (2 * p - 1))
        * (‖gchain L W H z ((tau₂.map (!·)).reverse ++ tau₂) (a₂.reverse ++ b :: a₂) x x‖
          * Φ ^ (2 * q - 1)) := by ring
    _ ≤ XiDiag L W H z Φ (2 * p) * XiDiag L W H z Φ (2 * q) :=
        mul_le_mul X₁ X₂ (by positivity) (le_trans (by positivity) X₁)

/-- **The Cauchy--Schwarz ladder, off-diagonal version** (p. 89, "for `l_j > n` the bound
follows from applying the Cauchy--Schwarz inequality"):
`Ξ^(o)_{p+q} ≤ (Ξ^(d)_{2p} Ξ^(d)_{2q} Φ)^{1/2}`. -/
theorem XiOff_add_le (hH : H.IsHermitian) (hΦ : 0 ≤ Φ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    XiOff L W H z Φ (p + q)
      ≤ √(XiDiag L W H z Φ (2 * p) * XiDiag L W H z Φ (2 * q) * Φ) := by
  refine XiOff_le (Real.sqrt_nonneg _) (fun tau a hlen h x y _ => ?_) (by omega)
  obtain ⟨tau₁, tau₂, a₁, a₂, b, rfl, rfl, hl₁, hl₂, h₁, h₂⟩ :=
    exists_chain_split hp hq hlen h
  obtain ⟨d₁, w₁, -, -⟩ := length_double h₁ b
  obtain ⟨-, -, d₂, w₂⟩ := length_double h₂ b
  have X₁ := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (d₁.trans (by rw [hl₁])) w₁ x
  have X₂ := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (d₂.trans (by rw [hl₂])) w₂ y
  have hcs := normSq_gchain_append_le hH h₁ h₂ b x y (H := H) (z := z)
  have hX : 0 ≤ XiDiag L W H z Φ (2 * p) * XiDiag L W H z Φ (2 * q) :=
    le_trans (by positivity) (mul_le_mul X₁ X₂ (by positivity) (le_trans (by positivity) X₁))
  rw [Real.le_sqrt (by positivity) (mul_nonneg hX hΦ)]
  have hpow : (Φ ^ (p + q - 1) * √Φ) ^ 2 = Φ ^ (2 * p - 1) * Φ ^ (2 * q - 1) * Φ := by
    rw [mul_pow, Real.sq_sqrt hΦ, ← pow_mul, ← pow_add]; congr 2; omega
  calc (‖gchain L W H z (tau₁ ++ tau₂) (a₁ ++ b :: a₂) x y‖ * (Φ ^ (p + q - 1) * √Φ)) ^ 2
      = ‖gchain L W H z (tau₁ ++ tau₂) (a₁ ++ b :: a₂) x y‖ ^ 2
          * (Φ ^ (p + q - 1) * √Φ) ^ 2 := by ring
    _ ≤ (‖gchain L W H z (tau₁ ++ (tau₁.map (!·)).reverse) (a₁ ++ b :: a₁.reverse) x x‖
          * ‖gchain L W H z ((tau₂.map (!·)).reverse ++ tau₂) (a₂.reverse ++ b :: a₂) y y‖)
          * (Φ ^ (2 * p - 1) * Φ ^ (2 * q - 1) * Φ) := by
        rw [hpow]; exact mul_le_mul_of_nonneg_right hcs (by positivity)
    _ = (‖gchain L W H z (tau₁ ++ (tau₁.map (!·)).reverse) (a₁ ++ b :: a₁.reverse) x x‖
          * Φ ^ (2 * p - 1))
        * (‖gchain L W H z ((tau₂.map (!·)).reverse ++ tau₂) (a₂.reverse ++ b :: a₂) y y‖
          * Φ ^ (2 * q - 1)) * Φ := by ring
    _ ≤ XiDiag L W H z Φ (2 * p) * XiDiag L W H z Φ (2 * q) * Φ :=
        mul_le_mul_of_nonneg_right (mul_le_mul X₁ X₂ (by positivity)
          (le_trans (by positivity) X₁)) hΦ

end Ladder

section Ladder2

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {Φ : ℝ}

omit [NeZero W] in
/-- The entry of a chain split at one `E`. -/
theorem mul_Eblk_mul_apply (A B : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L)
    (x y : ZMod L × Fin W) :
    (A * Eblk L W b * B) x y = ∑ k, A x k * (eblkW W b k : ℂ) * B k y := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Eblk_eq_diagonal, mul_diagonal]

/-- **The base case of p. 85**: the diagonal part of a `2`-chain, split at the diagonal,
`Ξ^(d)_2 ≤ W⁻¹ Φ (Ξ^(d)_1)² + (Ξ^(o)_1)²`.  (The paper states `Ξ^(d)_2 ≺ (Ξ^(d)_1)² + (Ξ^(o)_1)²`,
which is this with `Φ = Wℓη ≤ W`.) -/
theorem XiDiag_two_le (hΦ : 0 < Φ) :
    XiDiag L W H z Φ 2
      ≤ (W : ℝ)⁻¹ * Φ * XiDiag L W H z Φ 1 ^ 2 + XiOff L W H z Φ 1 ^ 2 := by
  have hd0 := XiDiag_nonneg (L := L) (W := W) (H := H) (z := z) hΦ.le 1
  have ho0 := XiOff_nonneg (L := L) (W := W) (H := H) (z := z) hΦ.le 1
  refine XiDiag_le (by positivity) (fun tau a hlen h x => ?_) (by norm_num)
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.mp hlen
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (by simpa using h.symm)
  have hd : ∀ (s : Bool) (y : ZMod L × Fin W), ‖Gsig H z s y y‖ ≤ XiDiag L W H z Φ 1 := by
    intro s y
    have := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (n := 1) (tau := [s])
      (a := []) rfl rfl y
    simpa using this
  have ho : ∀ (s : Bool) (y w : ZMod L × Fin W), y ≠ w →
      ‖Gsig H z s y w‖ * √Φ ≤ XiOff L W H z Φ 1 := by
    intro s y w hyw
    have := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ) (n := 1) (tau := [s])
      (a := []) rfl rfl hyw
    simpa using this
  have hsq : 0 < √Φ := Real.sqrt_pos.mpr hΦ
  rw [show ([s₁, s₂] : List Bool) = s₁ :: [s₂] from rfl, gchain_cons, gchain_single,
    mul_Eblk_mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  set G₁ := Gsig H z s₁
  set G₂ := Gsig H z s₂
  have hdiag : ‖G₁ x x * (eblkW W b x : ℂ) * G₂ x x‖ ≤ (W : ℝ)⁻¹ * XiDiag L W H z Φ 1 ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eblkW_nonneg b x)]
    have := mul_le_mul (hd s₁ x) (hd s₂ x) (norm_nonneg _) hd0
    have he := eblkW_le (W := W) b x
    have he0 := eblkW_nonneg (W := W) b x
    calc ‖G₁ x x‖ * eblkW W b x * ‖G₂ x x‖ = eblkW W b x * (‖G₁ x x‖ * ‖G₂ x x‖) := by ring
      _ ≤ (W : ℝ)⁻¹ * XiDiag L W H z Φ 1 ^ 2 := by
        rw [sq]; exact mul_le_mul he this (by positivity) (by positivity)
  have hoff : ∀ k ∈ Finset.univ.erase x, ‖G₁ x k * (eblkW W b k : ℂ) * G₂ k x‖ * Φ
      ≤ eblkW W b k * XiOff L W H z Φ 1 ^ 2 := by
    intro k hk
    have hkx : k ≠ x := Finset.ne_of_mem_erase hk
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eblkW_nonneg b k)]
    have h1 := ho s₁ x k (Ne.symm hkx)
    have h2 := ho s₂ k x hkx
    have hmul : √Φ * √Φ = Φ := Real.mul_self_sqrt hΦ.le
    have := mul_le_mul h1 h2 (by positivity) ho0
    have he0 := eblkW_nonneg (W := W) b k
    calc ‖G₁ x k‖ * eblkW W b k * ‖G₂ k x‖ * Φ
        = eblkW W b k * ((‖G₁ x k‖ * √Φ) * (‖G₂ k x‖ * √Φ)) := by
          linear_combination (-(‖G₁ x k‖ * eblkW W b k * ‖G₂ k x‖)) * hmul
      _ ≤ eblkW W b k * XiOff L W H z Φ 1 ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_left this he0
  have hsum_e : ∑ k ∈ Finset.univ.erase x, eblkW W b k ≤ 1 := by
    rw [← sum_eblkW (W := W) b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => eblkW_nonneg b j)
  calc ‖G₁ x x * (eblkW W b x : ℂ) * G₂ x x
          + ∑ k ∈ Finset.univ.erase x, G₁ x k * (eblkW W b k : ℂ) * G₂ k x‖ * Φ ^ (2 - 1)
      ≤ (‖G₁ x x * (eblkW W b x : ℂ) * G₂ x x‖
          + ∑ k ∈ Finset.univ.erase x, ‖G₁ x k * (eblkW W b k : ℂ) * G₂ k x‖) * Φ := by
        rw [show 2 - 1 = 1 from rfl, pow_one]
        exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans
          (add_le_add le_rfl (norm_sum_le _ _))) hΦ.le
    _ = ‖G₁ x x * (eblkW W b x : ℂ) * G₂ x x‖ * Φ
          + ∑ k ∈ Finset.univ.erase x, ‖G₁ x k * (eblkW W b k : ℂ) * G₂ k x‖ * Φ := by
        rw [add_mul, Finset.sum_mul]
    _ ≤ (W : ℝ)⁻¹ * XiDiag L W H z Φ 1 ^ 2 * Φ
          + ∑ k ∈ Finset.univ.erase x, eblkW W b k * XiOff L W H z Φ 1 ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hdiag hΦ.le) (Finset.sum_le_sum hoff)
    _ ≤ (W : ℝ)⁻¹ * XiDiag L W H z Φ 1 ^ 2 * Φ + 1 * XiOff L W H z Φ 1 ^ 2 := by
        rw [← Finset.sum_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsum_e (by positivity))
    _ = _ := by ring

omit [NeZero W] in
/-- `⟨E_b G E_c G†⟩ = ∑_k E_b(k) ∑_l E_c(l) |G_{kl}|²`. -/
theorem trace_Eblk_mul_Eblk_mul_conjTranspose (G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b c : ZMod L) :
    Matrix.trace (Eblk L W b * G * Eblk L W c * Gᴴ)
      = ((∑ k, eblkW W b k * ∑ l, eblkW W c l * ‖G k l‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_assoc, Matrix.mul_assoc, Eblk_eq_diagonal (b := b),
    diagonal_mul, ← Matrix.mul_assoc, quad_Eblk_apply_self]
  simp only [Complex.normSq_eq_norm_sq]
  push_cast
  ring

omit [NeZero W] in
/-- **The triple-product Cauchy--Schwarz inequality** of p. 88,
`∑ f(x) g(y) h(x,y) ≤ ‖f‖₂ ‖g‖₂ ‖h‖₂`, in chain form:
`|(A E_b G E_c B)_{xy}|² ≤ |(A E_b A†)_{xx}| |(B† E_c B)_{yy}| |⟨E_b G E_c G†⟩|`. -/
theorem normSq_triple_le (A G B : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b c : ZMod L)
    (x y : ZMod L × Fin W) :
    ‖(A * Eblk L W b * (G * Eblk L W c * B)) x y‖ ^ 2
      ≤ ‖(A * Eblk L W b * Aᴴ) x x‖ * ‖(Bᴴ * Eblk L W c * B) y y‖
        * ‖Matrix.trace (Eblk L W b * G * Eblk L W c * Gᴴ)‖ := by
  rw [norm_quad_Eblk_apply_self, norm_quad_Eblk_apply_self',
    trace_Eblk_mul_Eblk_mul_conjTranspose, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (eblkW_nonneg b k)
      (Finset.sum_nonneg fun l _ => mul_nonneg (eblkW_nonneg c l) (sq_nonneg _)))]
  set eb := eblkW W b
  set ec := eblkW W c
  have hexp : (A * Eblk L W b * (G * Eblk L W c * B)) x y
      = ∑ k, ∑ l, A x k * (eb k : ℂ) * (G k l * (ec l : ℂ) * B l y) := by
    rw [mul_Eblk_mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_Eblk_mul_apply, Finset.mul_sum]
  have hle : ‖(A * Eblk L W b * (G * Eblk L W c * B)) x y‖
      ≤ ∑ q : (ZMod L × Fin W) × (ZMod L × Fin W),
          eb q.1 * ec q.2 * (‖A x q.1‖ * ‖G q.1 q.2‖ * ‖B q.2 y‖) := by
    rw [hexp]
    refine le_trans ?_ (le_of_eq (Fintype.sum_prod_type _).symm)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (eblkW_nonneg b k),
      abs_of_nonneg (eblkW_nonneg c l)]
    ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ :
      Finset ((ZMod L × Fin W) × (ZMod L × Fin W)))
    (r := fun q => eb q.1 * ec q.2 * (‖A x q.1‖ * ‖G q.1 q.2‖ * ‖B q.2 y‖))
    (f := fun q => eb q.1 * ‖A x q.1‖ ^ 2 * (ec q.2 * ‖B q.2 y‖ ^ 2))
    (g := fun q => eb q.1 * (ec q.2 * ‖G q.1 q.2‖ ^ 2))
    (fun q _ => mul_nonneg (mul_nonneg (eblkW_nonneg b _) (sq_nonneg _))
      (mul_nonneg (eblkW_nonneg c _) (sq_nonneg _)))
    (fun q _ => mul_nonneg (eblkW_nonneg b _) (mul_nonneg (eblkW_nonneg c _) (sq_nonneg _)))
    (fun q _ => le_of_eq (by ring))
  have hf : ∑ q : (ZMod L × Fin W) × (ZMod L × Fin W),
      eb q.1 * ‖A x q.1‖ ^ 2 * (ec q.2 * ‖B q.2 y‖ ^ 2)
        = (∑ k, eb k * ‖A x k‖ ^ 2) * ∑ l, ec l * ‖B l y‖ ^ 2 := by
    rw [Finset.sum_mul_sum]
    exact Fintype.sum_prod_type _
  have hg : ∑ q : (ZMod L × Fin W) × (ZMod L × Fin W), eb q.1 * (ec q.2 * ‖G q.1 q.2‖ ^ 2)
      = ∑ k, eb k * ∑ l, ec l * ‖G k l‖ ^ 2 := by
    refine (Fintype.sum_prod_type _).trans ?_
    simp only [Finset.mul_sum]
  rw [hf, hg] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hcs

/-- The `2`-loop `⟨E_b G(σ) E_c G(σ)†⟩` is `L_{(σ,-σ),(c,b)}`. -/
theorem trace_Eblk_Gsig_Eblk_conjTranspose (hH : H.IsHermitian) (σ : Bool) (b c : ZMod L) :
    Matrix.trace (Eblk L W b * Gsig H z σ * Eblk L W c * (Gsig H z σ)ᴴ)
      = gloop L W H z ⟨[σ, !σ], [c, b]⟩ := by
  have := trace_Eblk_gchain_Eblk_conjTranspose (H := H) (z := z) hH (tau := [σ]) (a := [])
    rfl b c
  simpa using this

/-- **The second rung of the ladder** (p. 88): splitting a `(2n+1)`-chain into two `n`-chains
and one `1`-chain, `Ξ^(d)_{2n+1} ≤ Ξ^(d)_{2n} Φ Λ^{1/2}`, where `Λ` bounds the `2`-loops
`L_{(σ,-σ),(c,b)}`.  With the paper's `2`-loop bound `Λ = (Wℓη)^{-1} = Φ⁻¹` this is
`Ξ^(d)_{2n+1} ≺ Ξ^(d)_{2n} (Wℓη)^{1/2}`. -/
theorem XiDiag_two_mul_add_one_le (hH : H.IsHermitian) (hΦ : 0 ≤ Φ) {Λ : ℝ}
    (hΛ : ∀ (σ : Bool) (b c : ZMod L), ‖gloop L W H z ⟨[σ, !σ], [c, b]⟩‖ ≤ Λ) {n : ℕ}
    (hn : 1 ≤ n) :
    XiDiag L W H z Φ (2 * n + 1) ≤ XiDiag L W H z Φ (2 * n) * Φ * √Λ := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ true 0 0)
  have hX0 := XiDiag_nonneg (L := L) (W := W) (H := H) (z := z) hΦ (2 * n)
  refine XiDiag_le (by positivity) (fun tau a hlen h x => ?_) (by omega)
  obtain ⟨tau₁, tau₂', a₁, a₂', b, rfl, rfl, hl₁, hl₂, h₁, h₂'⟩ :=
    exists_chain_split (p := n) (q := n + 1) hn (by omega) (by rw [hlen]; ring) h
  obtain ⟨σ, tau₂, rfl⟩ : ∃ σ tau₂, tau₂' = σ :: tau₂ := by
    cases tau₂' with
    | nil => simp at hl₂
    | cons σ tau₂ => exact ⟨σ, tau₂, rfl⟩
  obtain ⟨c, a₂, rfl⟩ : ∃ c a₂, a₂' = c :: a₂ := by
    cases a₂' with
    | nil =>
      simp only [List.length_cons, List.length_nil, zero_add, Nat.add_eq_right,
        List.length_eq_zero_iff] at h₂'
      subst h₂'
      simp at hl₂
      omega
    | cons c a₂ => exact ⟨c, a₂, rfl⟩
  have h₂ : tau₂.length = a₂.length + 1 := by simpa using h₂'
  have hl₂' : tau₂.length = n := by simpa using hl₂
  obtain ⟨d₁, w₁, -, -⟩ := length_double h₁ b
  obtain ⟨-, -, d₂, w₂⟩ := length_double h₂ c
  have X₁ := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (d₁.trans (by rw [hl₁])) w₁ x
  have X₂ := norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) (d₂.trans (by rw [hl₂'])) w₂ x
  have hcs := normSq_triple_le (gchain L W H z tau₁ a₁) (Gsig H z σ) (gchain L W H z tau₂ a₂)
    b c x x
  rw [gchain_mul_Eblk_mul_conjTranspose hH h₁, conjTranspose_gchain_mul_Eblk_mul hH h₂,
    trace_Eblk_Gsig_Eblk_conjTranspose hH, ← gchain_cons, ← gchain_append_Eblk h₁] at hcs
  have hpow : (Φ ^ (2 * n + 1 - 1)) ^ 2 = Φ ^ (2 * n - 1) * Φ ^ (2 * n - 1) * Φ ^ 2 := by
    rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow (XiDiag L W H z Φ (2 * n) * Φ), Real.sq_sqrt hΛ0]
  set P₁ := ‖gchain L W H z (tau₁ ++ (tau₁.map (!·)).reverse) (a₁ ++ b :: a₁.reverse) x x‖
  set P₂ := ‖gchain L W H z ((tau₂.map (!·)).reverse ++ tau₂) (a₂.reverse ++ c :: a₂) x x‖
  set T := ‖gloop L W H z ⟨[σ, !σ], [c, b]⟩‖
  have hT := hΛ σ b c
  calc (‖gchain L W H z (tau₁ ++ σ :: tau₂) (a₁ ++ b :: c :: a₂) x x‖
          * Φ ^ (2 * n + 1 - 1)) ^ 2
      = ‖gchain L W H z (tau₁ ++ σ :: tau₂) (a₁ ++ b :: c :: a₂) x x‖ ^ 2
          * (Φ ^ (2 * n + 1 - 1)) ^ 2 := by ring
    _ ≤ P₁ * P₂ * T * (Φ ^ (2 * n - 1) * Φ ^ (2 * n - 1) * Φ ^ 2) := by
        rw [hpow]; exact mul_le_mul_of_nonneg_right hcs (by positivity)
    _ = (P₁ * Φ ^ (2 * n - 1)) * (P₂ * Φ ^ (2 * n - 1)) * T * Φ ^ 2 := by ring
    _ ≤ XiDiag L W H z Φ (2 * n) * XiDiag L W H z Φ (2 * n) * Λ * Φ ^ 2 := by
        gcongr
    _ = (XiDiag L W H z Φ (2 * n) * Φ) ^ 2 * Λ := by ring

end Ladder2

/-- **The trichotomy (A.27)**, as a statement about real numbers.  If
`Ξ^(o)_l ≤ 1` for `l ≤ n - 1` and `Ξ^(o)_l ≤ Φ^{1/2}` for `n < l ≤ 2n` (the latter from the
Cauchy--Schwarz ladder, `XiOff_add_le`), then every product with `l₁ + l₂ ≤ 2n + 1`,
`l₁ ≤ l₂ ≤ 2n` satisfies `Ξ^(o)_{l₁} Ξ^(o)_{l₂} ≤ ((Ξ^(o)_n)² + 1) Φ^{1/2}`. -/
theorem xi_trichotomy {X : ℕ → ℝ} {Φ : ℝ} {n : ℕ} (hΦ : 1 ≤ Φ) (hX0 : ∀ l, 0 ≤ X l)
    (hlow : ∀ l, l ≤ n - 1 → X l ≤ 1) (hhigh : ∀ l, n < l → l ≤ 2 * n → X l ≤ √Φ)
    {l₁ l₂ : ℕ} (h12 : l₁ ≤ l₂) (hsum : l₁ + l₂ ≤ 2 * n + 1) (hl₂ : l₂ ≤ 2 * n) :
    X l₁ * X l₂ ≤ (X n ^ 2 + 1) * √Φ := by
  have hs1 : 1 ≤ √Φ := Real.one_le_sqrt.mpr hΦ
  have hxn : X n ≤ X n ^ 2 + 1 := by nlinarith [sq_nonneg (X n - 1)]
  have hxn0 := hX0 n
  -- `X l ≤ X n ^ 2 + 1` for every `l ≤ n`
  have hle_n : ∀ l, l ≤ n → X l ≤ X n ^ 2 + 1 := by
    intro l hl
    rcases Nat.lt_or_ge l n with h | h
    · exact (hlow l (by omega)).trans (by nlinarith [sq_nonneg (X n)])
    · rw [show l = n by omega]; exact hxn
  rcases Nat.lt_or_ge n l₂ with h2 | h2
  · -- `l₂ > n`, hence `l₁ ≤ n`
    have := mul_le_mul (hle_n l₁ (by omega)) (hhigh l₂ h2 hl₂) (hX0 _) (by positivity)
    exact this
  · rcases Nat.lt_or_ge l₂ n with h3 | h3
    · -- both below `n`
      have := mul_le_mul (hlow l₁ (by omega)) (hlow l₂ (by omega)) (hX0 _) zero_le_one
      nlinarith [sq_nonneg (X n)]
    · -- `l₂ = n`
      have hl2n : l₂ = n := by omega
      rw [hl2n]
      rcases Nat.lt_or_ge l₁ n with h4 | h4
      · have := mul_le_mul (hlow l₁ (by omega)) hxn (hX0 _) zero_le_one
        nlinarith [sq_nonneg (X n)]
      · rw [show l₁ = n by omega, ← sq]
        nlinarith [sq_nonneg (X n)]

section A13

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W} {Φ : ℝ}

/-- **The off-diagonal bound for `l > n`** (p. 89): if `Ξ^(d)_k ≤ 1` for `2 ≤ k ≤ 2n`, then
`Ξ^(o)_l ≤ Φ^{1/2}` for `2 ≤ l ≤ 2n`, by the Cauchy--Schwarz ladder `XiOff_add_le`. -/
theorem XiOff_le_sqrt (hH : H.IsHermitian) (hΦ : 0 ≤ Φ) {n : ℕ}
    (hd : ∀ k, 2 ≤ k → k ≤ 2 * n → XiDiag L W H z Φ k ≤ 1) {l : ℕ} (hl2 : 2 ≤ l)
    (hl : l ≤ 2 * n) : XiOff L W H z Φ l ≤ √Φ := by
  have h := XiOff_add_le (L := L) (W := W) (H := H) (z := z) hH hΦ (p := l / 2) (q := l - l / 2)
    (by omega) (by omega)
  rw [show l / 2 + (l - l / 2) = l by omega] at h
  refine h.trans (Real.sqrt_le_sqrt ?_)
  have h1 := hd (2 * (l / 2)) (by omega) (by omega)
  have h2 := hd (2 * (l - l / 2)) (by omega) (by omega)
  have h20 := XiDiag_nonneg (L := L) (W := W) (H := H) (z := z) hΦ (2 * (l - l / 2))
  calc XiDiag L W H z Φ (2 * (l / 2)) * XiDiag L W H z Φ (2 * (l - l / 2)) * Φ
      ≤ 1 * 1 * Φ := mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h20 zero_le_one) hΦ
    _ = Φ := by ring

/-- **The exact identity behind (A.25)**: tracing the telescoping identity against `E_b`,
`⟨(C^(ii)_n - C_n) E_b⟩ = -∑_{k=1}^{n} (C^(i)_{[k,n]} E_b C_{[1,k]})_{ii} / (G_k)_{ii}`.
Each `C^(i)_{[k,n]} E_b C_{[1,k]}` is a chain of length `n + 1` (with minor resolvents after
its first factor), whose `C^(i)` part is expanded again by `gchainMinorTail_apply_expand`. -/
theorem trace_gchainMinor_sub_mul_Eblk {tau : List Bool} {a : List (ZMod L)}
    (h : tau.length = a.length + 1) (b : ZMod L) :
    Matrix.trace ((gchainMinor L W H z i tau a - gchain L W H z tau a) * Eblk L W b)
      = -∑ k ∈ Finset.range tau.length,
          (gchainMinorTail L W H z i (tau.drop k) (a.drop k) * Eblk L W b
            * gchain L W H z (tau.take (k + 1)) (a.take k)) i i
            / Gsig H z (tau.getD k false) i i := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Eblk_eq_diagonal, mul_diagonal, Matrix.sub_apply,
    gchainMinor_apply_expand h, sub_sub_cancel_left, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_diagonal]
  ring

/-- **The `C^(i)`-chains with non-uniform off-diagonal input**:
`|(C^(i)_m)_{ij}| Φ^{m-1/2} ≤ (1 + KD)^{m-1} ∑_{q=1}^{m} Ξ^(o)_q`, if `Ξ^(d)_p ≤ D` for
`2 ≤ p ≤ n`, `m ≤ n` and `|1/G_{ii}| ≤ K`.  This is what (A.26) needs, where the `Ξ^(o)_l`
with `l > n` are not `O(1)`. -/
theorem norm_gchainMinorTail_le_sum {K D : ℝ} (hΦ : 0 < Φ) (hD : 0 ≤ D)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j) (n : ℕ)
    (hXd : ∀ p, 2 ≤ p → p ≤ n → XiDiag L W H z Φ p ≤ D) :
    ∀ (m : ℕ) (tau : List Bool) (a : List (ZMod L)), tau.length = m →
      tau.length = a.length + 1 → m ≤ n →
      ‖gchainMinorTail L W H z i tau a i j‖ * (Φ ^ (m - 1) * √Φ)
        ≤ (1 + K * D) ^ (m - 1) * ∑ q ∈ Finset.Icc 1 m, XiOff L W H z Φ q := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true)
  have hX0 : ∀ q, 0 ≤ XiOff L W H z Φ q := XiOff_nonneg hΦ.le
  have hS0 : ∀ m, 0 ≤ ∑ q ∈ Finset.Icc 1 m, XiOff L W H z Φ q :=
    fun m => Finset.sum_nonneg fun q _ => hX0 q
  have hSmono : ∀ m m', m ≤ m' → ∑ q ∈ Finset.Icc 1 m, XiOff L W H z Φ q
      ≤ ∑ q ∈ Finset.Icc 1 m', XiOff L W H z Φ q := fun m m' hmm' =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hmm')
      (fun q _ _ => hX0 q)
  have h1 : 1 ≤ 1 + K * D := by nlinarith [mul_nonneg hK hD]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro tau a hm hwf hmn
    subst hm
    cases tau with
    | nil => simp at hwf
    | cons s tau =>
      cases a with
      | nil =>
        have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using hwf)
        subst htau
        have := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ) (n := 1)
          (tau := [s]) (a := []) rfl rfl hj
        rw [gchain_single] at this
        rw [gchainMinorTail_single]
        refine this.trans (le_of_eq ?_)
        simp
      | cons b a =>
        have hwf' : tau.length = a.length + 1 := by simpa using hwf
        rw [List.length_cons] at hmn ihm ⊢
        rw [Nat.add_sub_cancel]
        set S := ∑ q ∈ Finset.Icc 1 tau.length, XiOff L W H z Φ q with hS
        have hC := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ)
          (tau := s :: tau) (a := b :: a) rfl hwf hj
        rw [List.length_cons, Nat.add_sub_cancel] at hC
        have hD' := norm_gchainMinorTail_sub_le_of (O := S) hΦ hD hGinv s b hwf'
          (fun p hp2 hpn => hXd p hp2 (by omega))
          (fun tau' a' hwf'' hlen => ((ihm tau'.length (by omega) tau' a' rfl hwf''
            (by omega)).trans (mul_le_mul_of_nonneg_left (hSmono _ _ hlen)
              (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + K * D) _))).trans_eq (mul_comm _ _))
        have hsplit : ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j‖
            ≤ ‖gchain L W H z (s :: tau) (b :: a) i j‖
              + ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j
                  - gchain L W H z (s :: tau) (b :: a) i j‖ := by
          have := norm_add_le (gchain L W H z (s :: tau) (b :: a) i j)
            (gchainMinorTail L W H z i (s :: tau) (b :: a) i j
              - gchain L W H z (s :: tau) (b :: a) i j)
          rwa [add_sub_cancel] at this
        have hpos : 0 ≤ Φ ^ tau.length * √Φ := by positivity
        have hSsucc : ∑ q ∈ Finset.Icc 1 (tau.length + 1), XiOff L W H z Φ q
            = S + XiOff L W H z Φ (tau.length + 1) := by
          rw [hS, Finset.sum_Icc_succ_top (by omega)]
        have hpow1 : 1 ≤ (1 + K * D) ^ tau.length := one_le_pow₀ h1
        rw [hSsucc]
        calc ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ)
            ≤ ‖gchain L W H z (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ)
              + ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j
                  - gchain L W H z (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ) := by
              rw [← add_mul]; exact mul_le_mul_of_nonneg_right hsplit hpos
          _ ≤ XiOff L W H z Φ (tau.length + 1) + S * ((1 + K * D) ^ tau.length - 1) :=
              add_le_add hC hD'
          _ ≤ (1 + K * D) ^ tau.length * (S + XiOff L W H z Φ (tau.length + 1)) := by
              nlinarith [hX0 (tau.length + 1), hS0 tau.length]

/-- **(A.26), deterministic form**: for `j ≠ i`, the diagonal entry `(j, j)` of `C^(ii)_m - C_m`
is a sum of products of **two** off-diagonal ratios `Ξ^(o)_{l₁} Ξ^(o)_{l₂}` with
`l₁ + l₂ ≤ m + 1`:
`|(C^(ii)_m - C_m)_{jj}| Φ^m ≤ K ∑_{k<m} Ξ^(o)_{k+1} (1+KD)^{m-k-1} ∑_{q=1}^{m-k} Ξ^(o)_q`,
if `Ξ^(d)_p ≤ D` for `2 ≤ p ≤ m` and `|1/G_{ii}| ≤ K`.  (In the paper `m = 2n`.) -/
theorem norm_gchainMinor_sub_gchain_diag_le {K D : ℝ} (hΦ : 0 < Φ) (hD : 0 ≤ D)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j)
    {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1)
    (hXd : ∀ p, 2 ≤ p → p ≤ tau.length → XiDiag L W H z Φ p ≤ D) :
    ‖gchainMinor L W H z i tau a j j - gchain L W H z tau a j j‖ * Φ ^ tau.length
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
  have hP := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ) hlenP hwfP (Ne.symm hj)
  rw [show k + 1 - 1 = k by omega] at hP
  have hS := norm_gchainMinorTail_le_sum hΦ hD hGinv hj m hXd (m - k) (tau.drop k) (a.drop k)
    hlenS hwfS (by omega)
  rw [show m - k - 1 = m - k - 1 from rfl] at hS
  have hg := hGinv (tau.getD k false)
  set P := ‖gchain L W H z (tau.take (k + 1)) (a.take k) j i‖
  set T := ‖gchainMinorTail L W H z i (tau.drop k) (a.drop k) i j‖
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

/-- **(A.26) + (A.27) ⟹ (A.13), deterministic form.**  For a well-formed chain of length
`m = 2n`, `j ≠ i`, with `Ξ^(d)_p ≤ D` (`2 ≤ p ≤ 2n`), `|1/G_{ii}| ≤ K`, `1 ≤ Φ`, and the
trichotomy inputs `Ξ^(o)_l ≤ 1` for `l ≤ n - 1`, `Ξ^(o)_l ≤ Φ^{1/2}` for `n < l ≤ 2n`:
`|(C^(ii)_{2n} - C_{2n})_{jj}| Φ^{2n} ≤ c_{n,K,D} ((Ξ^(o)_n)² + 1) Φ^{1/2}`,
which is (A.13) with `Φ = Wℓη` (`c` explicit, not optimized). -/
theorem norm_gchainMinor_sub_gchain_diag_le_trichotomy {K D : ℝ} (hΦ : 1 ≤ Φ) (hD : 0 ≤ D)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j) {n : ℕ}
    {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1)
    (hlen : tau.length = 2 * n)
    (hXd : ∀ p, 2 ≤ p → p ≤ 2 * n → XiDiag L W H z Φ p ≤ D)
    (hlow : ∀ l, l ≤ n - 1 → XiOff L W H z Φ l ≤ 1)
    (hhigh : ∀ l, n < l → l ≤ 2 * n → XiOff L W H z Φ l ≤ √Φ) :
    ‖gchainMinor L W H z i tau a j j - gchain L W H z tau a j j‖ * Φ ^ (2 * n)
      ≤ K * (∑ k ∈ Finset.range (2 * n), (1 + K * D) ^ (2 * n - k - 1) * ((2 * n - k : ℕ) : ℝ))
        * ((XiOff L W H z Φ n ^ 2 + 1) * √Φ) := by
  have hΦ0 : 0 < Φ := by linarith
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true)
  have hX0 : ∀ q, 0 ≤ XiOff L W H z Φ q := XiOff_nonneg hΦ0.le
  have h1 : 0 ≤ 1 + K * D := by nlinarith [mul_nonneg hK hD]
  have hbase := norm_gchainMinor_sub_gchain_diag_le hΦ0 hD hGinv hj h
    (fun p hp2 hp => hXd p hp2 (by omega))
  rw [hlen] at hbase
  refine hbase.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hprod : ∀ q ∈ Finset.Icc 1 (2 * n - k),
      XiOff L W H z Φ (k + 1) * XiOff L W H z Φ q ≤ (XiOff L W H z Φ n ^ 2 + 1) * √Φ := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rcases le_total (k + 1) q with hkq | hkq
    · exact xi_trichotomy hΦ hX0 hlow hhigh hkq (by omega) (by omega)
    · rw [mul_comm]
      exact xi_trichotomy hΦ hX0 hlow hhigh hkq (by omega) (by omega)
  have hsum : XiOff L W H z Φ (k + 1) * ∑ q ∈ Finset.Icc 1 (2 * n - k), XiOff L W H z Φ q
      ≤ ((2 * n - k : ℕ) : ℝ) * ((XiOff L W H z Φ n ^ 2 + 1) * √Φ) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hprod).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 2
  calc XiOff L W H z Φ (k + 1) * ((1 + K * D) ^ (2 * n - k - 1)
        * ∑ q ∈ Finset.Icc 1 (2 * n - k), XiOff L W H z Φ q)
      = (1 + K * D) ^ (2 * n - k - 1)
          * (XiOff L W H z Φ (k + 1) * ∑ q ∈ Finset.Icc 1 (2 * n - k), XiOff L W H z Φ q) := by
        ring
    _ ≤ (1 + K * D) ^ (2 * n - k - 1)
          * (((2 * n - k : ℕ) : ℝ) * ((XiOff L W H z Φ n ^ 2 + 1) * √Φ)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg h1 _)
    _ = _ := by ring

end A13

/-! ### The composition sum of (A.24) -/

section Compositions

variable (Dg Of : ℕ → ℝ)

/-- The `k`-th layer of the sum (A.24):
`∑_{n_1, …, n_k ∈ [2, M]} ∑_{ℓ ∈ [1, M]} ∏_r Dg(n_r) · Of(ℓ) · 1(ℓ + ∑_r n_r = m + k)`. -/
noncomputable def compTerm (M m k : ℕ) : ℝ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 2 M), ∑ ℓ ∈ Finset.Icc 1 M,
    (∏ r, Dg (v r)) * Of ℓ * (if ℓ + ∑ r, v r = m + k then 1 else 0)

/-- The truncated sum `∑_{k < Kc}` of the layers (the `k = 0` layer is `Of(m)`). -/
noncomputable def compSum (Kc M m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range Kc, compTerm Dg Of M m k

theorem two_mul_le_sum_of_mem_piFinset {k M : ℕ} {v : Fin k → ℕ}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 2 M)) : 2 * k ≤ ∑ r, v r := by
  have h : ∑ _r : Fin k, 2 ≤ ∑ r, v r :=
    Finset.sum_le_sum fun r _ => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv r)).1
  simpa [mul_comm] using h

/-- Summing over `piFinset` on `Fin (k+1)` splits off the first coordinate. -/
theorem sum_piFinset_succ {β : Type*} [DecidableEq β] (s : Finset β) (k : ℕ)
    (g : (Fin (k + 1) → β) → ℝ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin (k + 1) => s), g v
      = ∑ p ∈ s, ∑ w ∈ Fintype.piFinset (fun _ : Fin k => s), g (Fin.cons p w) := by
  rw [← Finset.sum_product' (f := fun p w => g (Fin.cons p w))]
  refine Finset.sum_nbij' (fun v => (v 0, Fin.tail v)) (fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [Fintype.mem_piFinset] at hv
    exact Finset.mem_product.mpr ⟨hv 0, Fintype.mem_piFinset.mpr fun r => hv r.succ⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    rw [Fintype.mem_piFinset] at h2 ⊢
    intro r
    refine Fin.cases ?_ (fun r => ?_) r
    · simpa using h1
    · simpa using h2 r
  · intro v _
    exact Fin.cons_self_tail v
  · intro x _
    simp
  · intro v _
    simp

theorem compTerm_zero_layer (M m : ℕ) :
    compTerm Dg Of M m 0 = if m ∈ Finset.Icc 1 M then Of m else 0 := by
  unfold compTerm
  rw [Fintype.piFinset_of_isEmpty, Finset.univ_unique, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, add_zero, one_mul,
    mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' _ _ _

/-- **The renewal structure of (A.24)**: the layers `k ≥ 1` are obtained by choosing the first
part `n_1 = p` and a composition of `m + 1 - p` with one part fewer. -/
theorem sum_compTerm_succ (Kc M m : ℕ) :
    ∑ k ∈ Finset.range Kc, compTerm Dg Of M m (k + 1)
      = ∑ p ∈ Finset.Icc 2 M, Dg p * compSum Dg Of Kc M (m + 1 - p) := by
  unfold compSum compTerm
  simp only [sum_piFinset_succ, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have h2k := two_mul_le_sum_of_mem_piFinset hw
  have hp2 := (Finset.mem_Icc.mp hp).1
  have hℓ1 := (Finset.mem_Icc.mp hℓ).1
  have hiff : (ℓ + (p + ∑ r, w r) = m + (k + 1)) ↔ (ℓ + ∑ r, w r = m + 1 - p + k) := by
    omega
  rw [if_congr hiff rfl rfl]
  ring

theorem compSum_zero_right (Kc M : ℕ) : compSum Dg Of Kc M 0 = 0 := by
  unfold compSum compTerm
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun v hv =>
    Finset.sum_eq_zero fun ℓ hℓ => ?_
  have h2k := two_mul_le_sum_of_mem_piFinset hv
  have hℓ1 := (Finset.mem_Icc.mp hℓ).1
  rw [ite_eq_right (by omega), mul_zero]

theorem compTerm_nonneg (hD : ∀ p, 0 ≤ Dg p) (hO : ∀ l, 0 ≤ Of l) (M m k : ℕ) :
    0 ≤ compTerm Dg Of M m k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => hD _) (hO _)) (by split_ifs <;> norm_num)

theorem compSum_mono (hD : ∀ p, 0 ≤ Dg p) (hO : ∀ l, 0 ≤ Of l) {Kc Kc' : ℕ} (h : Kc ≤ Kc')
    (M m : ℕ) : compSum Dg Of Kc M m ≤ compSum Dg Of Kc' M m :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun k _ _ => compTerm_nonneg Dg Of hD hO M m k)

theorem compSum_nonneg (hD : ∀ p, 0 ≤ Dg p) (hO : ∀ l, 0 ≤ Of l) (Kc M m : ℕ) :
    0 ≤ compSum Dg Of Kc M m :=
  Finset.sum_nonneg fun k _ => compTerm_nonneg Dg Of hD hO M m k

/-- `compSum (Kc + 1) = Of(m) + ∑_p Dg(p) compSum Kc (m + 1 - p)` (for `1 ≤ m ≤ M`). -/
theorem compSum_succ {Kc M m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    compSum Dg Of (Kc + 1) M m
      = Of m + ∑ p ∈ Finset.Icc 2 M, Dg p * compSum Dg Of Kc M (m + 1 - p) := by
  rw [compSum, Finset.sum_range_succ', ← sum_compTerm_succ, compTerm_zero_layer,
    ite_eq_left (Finset.mem_Icc.mpr ⟨hm, hmM⟩)]
  ring

/-- Comparing the renewal step with the recursion of `compSum`. -/
theorem sum_range_le_sum_Icc (hD : ∀ p, 0 ≤ Dg p) (hO : ∀ l, 0 ≤ Of l) {N n : ℕ}
    (hN : N + 1 ≤ n) :
    ∑ k ∈ Finset.range N, Dg (k + 2) * compSum Dg Of (N - k) n (N - k)
      ≤ ∑ p ∈ Finset.Icc 2 n, Dg p * compSum Dg Of N n (N + 1 + 1 - p) := by
  calc ∑ k ∈ Finset.range N, Dg (k + 2) * compSum Dg Of (N - k) n (N - k)
      ≤ ∑ k ∈ Finset.range N, Dg (k + 2) * compSum Dg Of N n (N + 1 + 1 - (k + 2)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [show N + 1 + 1 - (k + 2) = N - k by omega]
        exact mul_le_mul_of_nonneg_left (compSum_mono Dg Of hD hO (by omega) _ _) (hD _)
    _ = ∑ p ∈ (Finset.range N).image (· + 2), Dg p * compSum Dg Of N n (N + 1 + 1 - p) :=
        (Finset.sum_image (g := (· + 2)) (f := fun p => Dg p * compSum Dg Of N n (N + 1 + 1 - p))
          (fun x _ y _ hxy => Nat.add_right_cancel hxy)).symm
    _ ≤ ∑ p ∈ Finset.Icc 2 n, Dg p * compSum Dg Of N n (N + 1 + 1 - p) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ =>
          mul_nonneg (hD p) (compSum_nonneg Dg Of hD hO _ _ _))
        intro p hp
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
        rw [Finset.mem_range] at hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

end Compositions

/-! ### (A.24) with the composition sum written out -/

section A24

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ} {i : ZMod L × Fin W} {Φ : ℝ}

/-- One step of (A.24) with non-uniform input: the renewal identity bounds `C^(i)_n - C_n` by
`∑_k K Ξ^(d)_{k+2} B(n-1-k)`, where `B` bounds the shorter `C^(i)`-chains. -/
theorem norm_gchainMinorTail_sub_le_sum {K : ℝ} (hΦ : 0 < Φ)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (s : Bool) (b : ZMod L)
    {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1) (B : ℕ → ℝ)
    (hIH : ∀ (tau' : List Bool) (a' : List (ZMod L)), tau'.length = a'.length + 1 →
      tau'.length ≤ tau.length →
      ‖gchainMinorTail L W H z i tau' a' i j‖ * (Φ ^ (tau'.length - 1) * √Φ) ≤ B tau'.length) :
    ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j - gchain L W H z (s :: tau) (b :: a) i j‖
        * (Φ ^ tau.length * √Φ)
      ≤ ∑ k ∈ Finset.range tau.length,
          K * XiDiag L W H z Φ (k + 2) * B (tau.length - k) := by
  rw [gchainMinorTail_apply_expand s b h, sub_sub_cancel_left, norm_neg]
  set N := tau.length with hN
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  set P := gchain L W H z ((s :: tau).take (k + 2)) ((b :: a).take (k + 1)) i i
  set S := gchainMinorTail L W H z i ((s :: tau).drop (k + 1)) ((b :: a).drop (k + 1)) i j
  set g := Gsig H z ((s :: tau).getD (k + 1) false) i i
  have hlenP : ((s :: tau).take (k + 2)).length = k + 2 := by
    simp only [List.length_take, List.length_cons]; omega
  have hwfP : ((s :: tau).take (k + 2)).length = ((b :: a).take (k + 1)).length + 1 := by
    simp only [List.length_take, List.length_cons]; omega
  have hlenS : ((s :: tau).drop (k + 1)).length = N - k := by
    simp only [List.length_drop, List.length_cons]; omega
  have hwfS : ((s :: tau).drop (k + 1)).length = ((b :: a).drop (k + 1)).length + 1 := by
    simp only [List.length_drop, List.length_cons]; omega
  have hP : ‖P‖ * Φ ^ (k + 1) ≤ XiDiag L W H z Φ (k + 2) :=
    norm_gchain_diag_le_XiDiag (H := H) (z := z) (Φ := Φ) hlenP hwfP i
  have hS : ‖S‖ * (Φ ^ (N - 1 - k) * √Φ) ≤ B (N - k) := by
    have := hIH _ _ hwfS (by omega)
    rwa [hlenS, show N - k - 1 = N - 1 - k by omega] at this
  have hg : ‖g⁻¹‖ ≤ K := hGinv _
  have hpow : Φ ^ N = Φ ^ (k + 1) * Φ ^ (N - 1 - k) := by
    rw [← pow_add]; congr 1; omega
  rw [div_eq_mul_inv, norm_mul, norm_mul, hpow]
  have e : ‖P‖ * (‖S‖ * ‖g⁻¹‖) * (Φ ^ (k + 1) * Φ ^ (N - 1 - k) * √Φ)
      = (‖P‖ * Φ ^ (k + 1)) * (‖S‖ * (Φ ^ (N - 1 - k) * √Φ)) * ‖g⁻¹‖ := by ring
  rw [e]
  have hS0 : 0 ≤ ‖S‖ * (Φ ^ (N - 1 - k) * √Φ) := by positivity
  have hX0 := XiDiag_nonneg (L := L) (W := W) (H := H) (z := z) hΦ.le (k + 2)
  calc (‖P‖ * Φ ^ (k + 1)) * (‖S‖ * (Φ ^ (N - 1 - k) * √Φ)) * ‖g⁻¹‖
      ≤ XiDiag L W H z Φ (k + 2) * B (N - k) * K :=
        mul_le_mul (mul_le_mul hP hS hS0 hX0) hg (norm_nonneg _)
          (mul_nonneg hX0 (hS0.trans hS))
    _ = K * XiDiag L W H z Φ (k + 2) * B (N - k) := by ring

/-- The shorter `C^(i)`-chains are bounded by the composition sum:
`|(C^(i)_m)_{ij}| Φ^{m-1/2} ≤ ∑_{k<m} ∑_{n_r, ℓ} ∏_r K Ξ^(d)_{n_r} · Ξ^(o)_ℓ · 1(ℓ + ∑ n_r = m + k)`. -/
theorem norm_gchainMinorTail_le_compSum {K : ℝ} (hΦ : 0 < Φ)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j) (n : ℕ) :
    ∀ (m : ℕ) (tau : List Bool) (a : List (ZMod L)), tau.length = m →
      tau.length = a.length + 1 → m ≤ n →
      ‖gchainMinorTail L W H z i tau a i j‖ * (Φ ^ (m - 1) * √Φ)
        ≤ compSum (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ) m n m := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true)
  have hD : ∀ p, 0 ≤ K * XiDiag L W H z Φ p := fun p => mul_nonneg hK (XiDiag_nonneg hΦ.le p)
  have hO : ∀ l, 0 ≤ XiOff L W H z Φ l := XiOff_nonneg hΦ.le
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro tau a hm hwf hmn
    subst hm
    cases tau with
    | nil => simp at hwf
    | cons s tau =>
      cases a with
      | nil =>
        have htau : tau = [] := List.eq_nil_of_length_eq_zero (by simpa using hwf)
        subst htau
        have h1 : 1 ≤ n := by simpa using hmn
        have := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ) (n := 1)
          (tau := [s]) (a := []) rfl rfl hj
        rw [gchain_single] at this
        rw [gchainMinorTail_single, show ([s] : List Bool).length = 0 + 1 from rfl,
          compSum_succ _ _ le_rfl h1]
        simp only [compSum, Finset.range_zero, Finset.sum_empty, mul_zero,
          Finset.sum_const_zero, add_zero]
        simpa using this
      | cons b a =>
        have hwf' : tau.length = a.length + 1 := by simpa using hwf
        rw [List.length_cons] at hmn ihm ⊢
        rw [Nat.add_sub_cancel]
        have hC := norm_gchain_off_le_XiOff (H := H) (z := z) (Φ := Φ)
          (tau := s :: tau) (a := b :: a) rfl hwf hj
        rw [List.length_cons, Nat.add_sub_cancel] at hC
        have hD' := norm_gchainMinorTail_sub_le_sum hΦ hGinv s b hwf'
          (fun q => compSum (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ) q n q)
          (fun tau' a' hwf'' hlen => ihm tau'.length (by omega) tau' a' rfl hwf'' (by omega))
        have hsplit : ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j‖
            ≤ ‖gchain L W H z (s :: tau) (b :: a) i j‖
              + ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j
                  - gchain L W H z (s :: tau) (b :: a) i j‖ := by
          have := norm_add_le (gchain L W H z (s :: tau) (b :: a) i j)
            (gchainMinorTail L W H z i (s :: tau) (b :: a) i j
              - gchain L W H z (s :: tau) (b :: a) i j)
          rwa [add_sub_cancel] at this
        have hpos : 0 ≤ Φ ^ tau.length * √Φ := by positivity
        rw [compSum_succ _ _ (by omega) hmn]
        calc ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ)
            ≤ ‖gchain L W H z (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ)
              + ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j
                  - gchain L W H z (s :: tau) (b :: a) i j‖ * (Φ ^ tau.length * √Φ) := by
              rw [← add_mul]; exact mul_le_mul_of_nonneg_right hsplit hpos
          _ ≤ XiOff L W H z Φ (tau.length + 1)
              + ∑ k ∈ Finset.range tau.length, K * XiDiag L W H z Φ (k + 2)
                  * compSum (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ)
                      (tau.length - k) n (tau.length - k) := add_le_add hC hD'
          _ ≤ _ := add_le_add le_rfl
              (sum_range_le_sum_Icc (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ) hD hO
                hmn)

/-- **(A.24)**, with the combinatorial constraint written out: for a well-formed chain of
length `n ≥ 2` and `i ≠ j`,
`|(C_n)_{ij} - (C^(i)_n)_{ij}| Φ^{n-1/2}
  ≤ ∑_{k=1}^{n-1} ∑_{n_1, …, n_k ∈ [2, n]} ∑_{ℓ ∈ [1, n]}
      ∏_r (K Ξ^(d)_{n_r}) · Ξ^(o)_ℓ · 1(ℓ + ∑_r n_r = n + k)`,
where `K` bounds `|1/G_{ii}|` (the paper's `1/G_{ii} = O(1)`).  No other input is needed: the
`Ξ`'s are the ratios (A.5), (A.6) themselves. -/
theorem norm_gchainMinorTail_sub_gchain_le_A24 {K : ℝ} (hΦ : 0 < Φ)
    (hGinv : ∀ s, ‖(Gsig H z s i i)⁻¹‖ ≤ K) {j : ZMod L × Fin W} (hj : i ≠ j) (s : Bool)
    (b : ZMod L) {tau : List Bool} {a : List (ZMod L)} (h : tau.length = a.length + 1) :
    ‖gchainMinorTail L W H z i (s :: tau) (b :: a) i j - gchain L W H z (s :: tau) (b :: a) i j‖
        * (Φ ^ tau.length * √Φ)
      ≤ ∑ k ∈ Finset.Ico 1 (tau.length + 1),
          compTerm (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ)
            (tau.length + 1) (tau.length + 1) k := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hGinv true)
  have hD : ∀ p, 0 ≤ K * XiDiag L W H z Φ p := fun p => mul_nonneg hK (XiDiag_nonneg hΦ.le p)
  have hO : ∀ l, 0 ≤ XiOff L W H z Φ l := XiOff_nonneg hΦ.le
  set N := tau.length with hN
  have hstep := norm_gchainMinorTail_sub_le_sum hΦ hGinv (j := j) s b h
    (fun q => compSum (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ) q (N + 1) q)
    (fun tau' a' hwf hlen => norm_gchainMinorTail_le_compSum hΦ hGinv hj (N + 1)
      tau'.length tau' a' rfl hwf (by omega))
  have hcmp := sum_range_le_sum_Icc (fun p => K * XiDiag L W H z Φ p) (XiOff L W H z Φ) hD hO
    (N := N) (n := N + 1) le_rfl
  refine hstep.trans (hcmp.trans (le_of_eq ((sum_compTerm_succ (fun p => K * XiDiag L W H z Φ p)
    (XiOff L W H z Φ) N (N + 1) (N + 1)).symm.trans ?_)))
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm 1 k]

end A24

end RBM
